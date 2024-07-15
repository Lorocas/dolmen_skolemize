open Dolmen_std

module TptpParser =
  Dolmen_tptp_v6_3_0.Make (Dolmen.Std.Loc) (Dolmen.Std.Id) (Dolmen.Std.Term)
    (Dolmen.Std.Statement)

module S = Set.Make (struct
    type t = Id.t
    let compare = Id.compare
  end)

(* let fresh_var_counter = ref 0 *)
let fresh_const_counter = ref 0
let fresh_func_counter = ref 0
(* let term_to_string term = Format.asprintf "%a" Term.print term *)
let name_to_string name = Format.asprintf "%a" Name.print name (* Nom des axiomes et de la conjecture *)
(* let statement_to_string stmt = Format.asprintf "%a" Statement.print stmt *)

(* let fresh_var () =
  incr fresh_var_counter;
  Id.mk Id.var ("X_" ^ string_of_int !fresh_var_counter)
;; *)

let term_to_string term = Format.asprintf "%a" Term.print term;;

(** [contains_substring] returns a [bool]. Returns [true] if [sub] is a substring of [s], [false] otherwise. *)
let contains_substring s sub =
  let len_s = String.length s in
  let len_sub = String.length sub in
  let rec aux i =
    if i > len_s - len_sub then false
    else if String.sub s i len_sub = sub then true
    else aux (i + 1)
  in
  aux 0
;;

(** [modify_string] adds [`] before [∀] and [∃], and replace points by commas *)
let modify_string s =
  let len = String.length s in
  let buffer = Buffer.create len in
  let quantifiers = ["∀"; "∃"; "=="] in
  let rec aux i =
    if i >= len then ()
    else
      let found = List.find_opt (fun q ->
        let len_q = String.length q in
        i + len_q <= len && String.sub s i len_q = q
      ) quantifiers in
      match found with
      | Some q ->
          if q = "==" then begin 
            Buffer.add_char buffer '='; 
            aux (i + String.length q)
          end
          else begin
          Buffer.add_char buffer '`';
          Buffer.add_string buffer q;
          aux (i + String.length q)
          end
      | None ->
          let c = s.[i] in
          if c = '.' then Buffer.add_char buffer ',' (* Remplace les points par des virgules *)
          else Buffer.add_char buffer c;
          aux (i + 1)
  in
  aux 0;
  Buffer.contents buffer
;;

let fresh_const () =
  incr fresh_const_counter;
  Id.mk Id.term ("c_" ^ string_of_int !fresh_const_counter)
;;

let fresh_func () =
  incr fresh_func_counter;
  Id.mk Id.term ("f_" ^ string_of_int !fresh_func_counter)
;;

(* let rec collect_free_vars term =
  match term.Term.term with
  | Term.Symbol id -> S.singleton id
  | Term.Builtin _ -> S.empty
  | Term.Colon (t, _) -> collect_free_vars t
  | Term.App (f, args) ->
    List.fold_left
      (fun acc t -> S.union acc (collect_free_vars t))
      (collect_free_vars f)
      args
  | Term.Binder (_, vars, body) ->
    let bound_vars =
      List.fold_left (fun acc v -> S.union acc (collect_free_vars v)) S.empty vars
    in
    S.diff (collect_free_vars body) bound_vars
  | Term.Match (t, cases) ->
    List.fold_left
      (fun acc (pat, body) ->
        S.union acc (S.union (collect_free_vars pat) (collect_free_vars body)))
      (collect_free_vars t)
      cases
;; *)

let extract_id_from_var v =
  match v.Term.term with
  | Term.Symbol id -> Some id
  | Term.Colon (var, _) ->
    (match var.Term.term with
     | Term.Symbol id -> Some id
     | _ -> None)
  | _ -> None
;;

let rec substitute subst term =
  match term.Term.term with
  | Term.Symbol id ->
    (try List.assoc id subst with
     | Not_found -> term)
  | Term.App (f, args) ->
    Term.apply (substitute subst f) (List.map (substitute subst) args)
  | Term.Binder (b, vars, body) ->
    let new_subst =
      List.filter
        (fun (id, _) -> not (List.exists (fun v -> extract_id_from_var v = Some id) vars))
        subst
    in
    let new_body = substitute new_subst body in
    { term with Term.term = Term.Binder (b, vars, new_body) }
  | _ -> term
;;

let rec transform_connectives term =
  match term.Term.term with
  | Term.App (f, args) ->
    (match f.Term.term with
    (* Changement de l'implication et l'équivalence *)
     (* | Term.Builtin Term.Imply ->
       (match args with
        | [ a; b ] ->
          (* Remplacement de 'a => b' par '~a | b' *)
          Term.or_
            ~loc:term.Term.loc
            [ Term.not_ ~loc:term.Term.loc (transform_connectives a)
            ; transform_connectives b
            ]
        | _ -> term)
     | Term.Builtin Term.Equiv ->
       (match args with
        | [ a; b ] ->
          let left =
            Term.or_
              ~loc:term.Term.loc
              [ Term.not_ ~loc:term.Term.loc (transform_connectives a)
              ; transform_connectives b
              ]
          in
          let right =
            Term.or_
              ~loc:term.Term.loc
              [ Term.not_ ~loc:term.Term.loc (transform_connectives b)
              ; transform_connectives a
              ]
          in
          Term.and_ ~loc:term.Term.loc [ left; right ]
        | _ -> term) *)
     | _ ->
       Term.apply
         ~loc:term.Term.loc
         (transform_connectives f)
         (List.map transform_connectives args))
  | Term.Binder (b, vars, body) ->
    { term with Term.term = Term.Binder (b, vars, transform_connectives body) }
  | _ -> term
;;

let rec skolemize_term is_conjecture univ_vars term =
  match term.Term.term with
  | Term.Binder (Term.Ex, bound_vars, body) ->
    if is_conjecture && S.is_empty univ_vars
    then (
      (* Pour les conjectures avec un quantificateur existentiel externe *)
      let skolem_terms =
        List.map (fun _ -> Term.const ~loc:term.Term.loc (fresh_const ())) bound_vars
      in
      let subst =
        List.map2
          (fun v t -> Option.get (extract_id_from_var v), t)
          bound_vars
          skolem_terms
      in
      skolemize_term true S.empty (substitute subst body))
    else if (not is_conjecture) || not (S.is_empty univ_vars)
    then (
      (* Pour les axiomes ou les quantificateurs existentiels internes *)
      let skolem_terms =
        List.map
          (fun _ ->
            if S.is_empty univ_vars
            then Term.const ~loc:term.Term.loc (fresh_const ())
            else
              Term.apply
                ~loc:term.Term.loc
                (Term.const ~loc:term.Term.loc (fresh_func ()))
                (List.map (Term.const ~loc:term.Term.loc) (S.elements univ_vars)))
          bound_vars
      in
      let subst =
        List.map2
          (fun v t -> Option.get (extract_id_from_var v), t)
          bound_vars
          skolem_terms
      in
      skolemize_term is_conjecture univ_vars (substitute subst body))
    else (
      (* Pour les conjectures avec un quantificateur existentiel interne *)
      let new_univ_vars =
        List.fold_left
          (fun acc v ->
            match extract_id_from_var v with
            | Some id -> S.add id acc
            | None -> acc)
          univ_vars
          bound_vars
      in
      Term.exists ~loc:term.Term.loc bound_vars (skolemize_term true new_univ_vars body))
  | Term.Binder (Term.All, bound_vars, body) ->
    let new_univ_vars =
      List.fold_left
        (fun acc v ->
          match extract_id_from_var v with
          | Some id -> S.add id acc
          | None -> acc)
        univ_vars
        bound_vars
    in
    Term.forall
      ~loc:term.Term.loc
      bound_vars
      (skolemize_term is_conjecture new_univ_vars body)
  | Term.App (f, args) ->
    Term.apply
      ~loc:term.Term.loc
      (skolemize_term is_conjecture univ_vars f)
      (List.map (skolemize_term is_conjecture univ_vars) args)
  | _ -> term
;;

let skolemize_statement stmt =
  match stmt.Statement.descr with
  | Statement.Antecedent t ->
    let skolemized = skolemize_term false S.empty t in
    { stmt with
      Statement.descr = Statement.Antecedent (transform_connectives skolemized)
    }
  (* Skolemize or not the conjecture *)
  (* | Statement.Consequent t ->
    let skolemized = skolemize_term true S.empty t in
    { stmt with
      Statement.descr = Statement.Consequent (transform_connectives skolemized)
    } *)
  | Statement.Plain t ->
    let skolemized = skolemize_term false S.empty t in
    { stmt with Statement.descr = Statement.Plain (transform_connectives skolemized) }
  | Statement.Clause l ->
    let skolemized = List.map (skolemize_term false S.empty) l in
    { stmt with
      Statement.descr = Statement.Clause (List.map transform_connectives skolemized)
    }
  | _ -> stmt
;;

let rec print_term fmt term =
  match term.Term.term with
  | Term.Symbol id -> Format.fprintf fmt "%a" Id.print id
  | Term.Builtin b ->
    (match b with
     | Term.And -> Format.fprintf fmt "&"
     | Term.Or -> Format.fprintf fmt "|"
     | Term.Not -> Format.fprintf fmt "~"
     | Term.Imply -> Format.fprintf fmt "=>"
     | Term.Equiv -> Format.fprintf fmt "<=>"
     | Term.Eq -> Format.fprintf fmt "="
     | Term.Distinct -> Format.fprintf fmt "!="
     | _ -> Format.fprintf fmt "%a" Term.print term)
  | Term.App (f, args) ->
    (match f.Term.term with
     | Term.Builtin Term.And | Term.Builtin Term.Or ->
       Format.fprintf
         fmt
         "(%a)"
         (Format.pp_print_list
            ~pp_sep:(fun fmt () -> Format.fprintf fmt " %a " print_term f)
            print_term)
         args
     | Term.Builtin Term.Not ->
       (match args with
        | [ arg ] -> Format.fprintf fmt "~ %a" print_term arg
        | _ ->
          Format.fprintf
            fmt
            "%a(%a)"
            print_term
            f
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
               print_term)
            args)
     | Term.Builtin Term.Eq ->
       (match args with
        | [ left; right ] ->
          Format.fprintf fmt "(%a = %a)" print_term left print_term right
        | _ ->
          Format.fprintf
            fmt
            "%a(%a)"
            print_term
            f
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
               print_term)
            args)
      | Term.Builtin Term.Distinct ->
       (match args with
        | [ left; right ] ->
          Format.fprintf fmt "(%a != %a)" print_term left print_term right
        | _ ->
          Format.fprintf
            fmt
            "%a(%a)"
            print_term
            f
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
               print_term)
            args)
      | Term.Builtin Term.Imply ->
       (match args with
        | [ left; right ] ->
          Format.fprintf fmt "(%a => %a)" print_term left print_term right
        | _ ->
          Format.fprintf
            fmt
            "%a(%a)"
            print_term
            f
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
               print_term)
            args)
      | Term.Builtin Term.Equiv ->
       (match args with
        | [ left; right ] ->
          Format.fprintf fmt "(%a <=> %a)" print_term left print_term right
        | _ ->
          Format.fprintf
            fmt
            "%a(%a)"
            print_term
            f
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
               print_term)
            args)
     | _ ->
       Format.fprintf
         fmt
         "%a(%a)"
         print_term
         f
         (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",") print_term)
         args)
  | Term.Binder (Term.All, vars, body) ->
    Format.fprintf
      fmt
      "! [%a] : %a"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",") print_term)
      vars
      print_term
      body
  | Term.Binder (Term.Ex, vars, body) ->
    Format.fprintf
      fmt
      "? [%a] : %a"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",") print_term)
      vars
      print_term
      body
  | Term.Colon (var, ty) -> Format.fprintf fmt "%a: %a" print_term var print_term ty
  | _ -> Format.fprintf fmt "%a" Term.print term
;;

(** [buffer_contains] vérifie si la séquence [seq] est dans le buffer [buffer] *)
let buffer_contains buffer seq =
  let str = Buffer.contents buffer in
  try
    let len = String.length seq in
    let rec aux i =
      if i + len > String.length str then false
      else if String.sub str i len = seq then true
      else aux (i + 1)
    in
    aux 0
  with Invalid_argument _ -> false
;;

(** [print_statement] écrit les axiomes et conjectures ans le nouveau fichier.
    NOTE : seul le cas des antécédents (axiomes) réécrit l'axiome avec un nouveau nom 
  *)
let print_statement fmt stmt =
  let name =
    match stmt.Statement.id with
    | Some id -> name_to_string (Id.name id) (* Nom de l'axiome *)
    | None -> "unknown"
  in
  let buffer = Buffer.create 16 in
  let buf_formatter = Format.formatter_of_buffer buffer in
  match stmt.Statement.descr with
  | Statement.Antecedent t -> 
    (* Utilise print_term pour écrire dans le tampon *)
    (* Format.fprintf fmt "@.DEBUG2 | %a@.@." Term.print t; *)
    print_term buf_formatter t;
    Format.pp_print_flush buf_formatter ();
    (* Vérifie si la sortie contient "f_" *)
    let contains_f_ = buffer_contains buffer "f_" in
    let contains_c_ = buffer_contains buffer "c_" in (* If the constant are considered as a skolem formula *)
    (* Formate en fonction du résultat de la vérification *)
    if contains_f_ || contains_c_ then begin
      Format.fprintf fmt "fof(sk_%s, axiom, %a)." name print_term t;
      (* write_signature name t *)
    end
      (* write_signature TODO *)
    else
      Format.fprintf fmt "fof(%s, axiom, %a)." name print_term t;
  | Statement.Consequent t ->
    Format.fprintf fmt "@.fof(%s, conjecture, %a)." name print_term t
  | Statement.Plain t -> Format.fprintf fmt "fof(%s, plain, %a)." name print_term t
  | Statement.Clause l ->
    Format.fprintf
      fmt
      "cnf(%s, axiom, %a)."
      name
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ") print_term)
      l
  | _ -> Format.fprintf fmt "%a" Statement.print stmt
;;

let output_skolemized_statements out statements =
  let fmt = Format.formatter_of_out_channel out in
  (* List.iter
    (fun stmt ->
      Format.fprintf fmt "@.DEBUG | %a@.@." Statement.print stmt;)
    statements; *)
  List.iter
    (fun stmt ->
      print_statement fmt stmt;
      Format.fprintf fmt "@.")
    statements
;;

(** [write_signature] writes the signature to a file named 'signature.lp'. 
    NOTE: the file is created in the same repersitory of the executable 'dolmen_skolemize' *)
let write_builtin fmt name s =
  (* Printf.printf "WRITE_BUILTIN | %s\n" name; *)
  let builtin = Format.sprintf "symbol %s : ϵ %s;" name s in
  Format.fprintf fmt "%s\n" builtin;
  Format.fprintf fmt "builtin \"Axiom\" ≔ %s;\n" name;
  Format.fprintf fmt "builtin \"SkolemizedAxiom\" ≔ sk_%s;@." name;
;;

(** [print_builtin] writes all the necessary axioms and builtin to use SKonverto *)
let print_builtin fmt stmt =
  match stmt.Statement.descr with
  | Statement.Antecedent t ->
    (* Printf.printf "@.@.@.@.BIG TRY | "; *)
    let s = (term_to_string t) in
    let sub = "∃" in
    let result = contains_substring s sub in
    if result then 
      let new_s = modify_string s in
      (* Format.fprintf fmt "%s@." new_s; *)
      let name =
        match stmt.Statement.id with
        | Some id -> name_to_string (Id.name id) (* Name of the axiom *)
        | None -> "unknown"
      in
      write_builtin fmt name new_s;
      (* Format.fprintf fmt "%a@." Term.print t; *)
      (* Printf.printf "%s@." (term_to_string t); *)
  | _ -> ()
;;

(* Add all the skolem formula in the signature file *)
let rec add_skolem_formula fmt n b =
  if b then 
    if n = 0 then ()
    else begin
      Format.fprintf fmt "builtin \"Skolem\" ≔ f_%d;\n" n; 
      (* Printf.printf "f_%d printed!" n; *)
      add_skolem_formula fmt (n-1) true;
    end
  else 
    if n = 0 then ()
    else begin
      Format.fprintf fmt "builtin \"Skolem\" ≔ c_%d;\n" n; 
      (* Printf.printf "c_%d printed!" n; *)
      add_skolem_formula fmt (n-1) false;
    end
;;

(** [output_builtin] iterates print of the statements in the file [out] of all the statements in [statements] *)
let output_builtin out statements = 
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "require open Logic.Zenon.FOL Logic.Zenon.LL Logic.Zenon.ND Logic.Zenon.ND_eps Logic.Zenon.ND_eps_full Logic.Zenon.ND_eps_aux Logic.Zenon.LL_ND Logic.Zenon.zen;\n\n";
  Format.fprintf fmt "require open skolem.signature;\nrequire open skolem.proof;\n\n\n// Axioms\n\n";
  List.iter
    (fun stmt ->
      print_builtin fmt stmt;
      Format.fprintf fmt "")
    statements;
  Format.fprintf fmt "@.@.// Other builtin@.@.builtin \"Formula\" ≔ zenon_G;\nbuiltin \"⇒\" ≔ ⇒;\nbuiltin \"∀\" ≔ ∀;\nbuiltin \"∃\" ≔ ∃;\nbuiltin \"τ\" ≔ τ;\nbuiltin \"ϵ\" ≔ ϵ;\nbuiltin \"⊥\" ≔ ⊥;\nbuiltin \"∃E\" ≔ ∃E;\nbuiltin \"κ\" ≔ κ;\n";
  add_skolem_formula fmt (!fresh_func_counter) true;
  add_skolem_formula fmt (!fresh_const_counter) false;
;;

(* NOTE: Possibility to add an argument to choose the signature file. *)
let () =
  if Array.length Sys.argv < 3
  then Printf.printf "Usage: %s <input_file> <output_file>\n" Sys.argv.(0)
  else (
    (* Read arguments *)
    let context_mode = ref false in
    let input_file = ref "" in
    let output_file = ref "" in

    (* Parse command line arguments *)
    let i = ref 1 in
    while !i < Array.length Sys.argv do
      match Sys.argv.(!i) with
      | "-context" -> context_mode := true; incr i
      | arg ->
        if !input_file = "" then input_file := arg
        else if !output_file = "" then output_file := arg;
        incr i
    done;

    (* Check if input and output files are provided *)
    if !input_file = "" || !output_file = ""
    then Printf.printf "Usage: %s <input_file> <output_file>\n" Sys.argv.(0)
    else 
      let _, statements = TptpParser.parse_file !input_file in

      (* Parse and skolemize the problem *)
      let skolemized_statements = List.map skolemize_statement statements in
      if !output_file = "-"
      then output_skolemized_statements stdout skolemized_statements
      else begin
        let out = open_out !output_file in
        (* output_essai out statements; *)
        output_skolemized_statements out skolemized_statements;
        close_out out;
        if !output_file <> "-" then 
          if !context_mode then 
            Printf.printf "Skolemized TPTP file written %s/%s\n" (Sys.getcwd ()) !output_file
      end;

      (* Creation of the file 'builtin.lp' *)
      let file_name_builtin = "builtin.lp" in
      if Sys.file_exists file_name_builtin then Sys.remove file_name_builtin;
      let builtin_file = open_out_gen [Open_creat; Open_text; Open_append] 0o666 file_name_builtin in

      (* Update of the file 'builtin.lp' *)
      output_builtin builtin_file statements;
      close_out builtin_file;
      if file_name_builtin <> "-" then 
        if !context_mode then 
          Printf.printf "Builtin written to %s/%s\n" (Sys.getcwd ()) file_name_builtin;
    
  )
;;
