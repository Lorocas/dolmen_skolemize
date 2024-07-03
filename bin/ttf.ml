open Dolmen

(* Instantiate a module for parsing TPTP files *)
module TptpParser = Dolmen.Tptp.Latest.Make (Std.Loc) (Std.Id) (Std.Term) (Std.Statement)
module State = Dolmen_loop.State
module Typer_aux = Dolmen_loop.Typer.Typer (State)
module Typer = Dolmen_loop.Typer.Make (Std.Expr) (Std.Expr.Print) (State) (Typer_aux)
module Id = Std.Id
module Term = Std.Term
module Statement = Std.Statement
module Name = Std.Name
module Namespace = Std.Namespace

(* Helper functions *)
(* let fresh_var_counter = ref 0 *)
let fresh_const_counter = ref 0
let fresh_func_counter = ref 0

(* let fresh_var () =
  incr fresh_var_counter;
  Id.mk Id.var ("X_" ^ string_of_int !fresh_var_counter)
;; *)

let fresh_const () =
  incr fresh_const_counter;
  Id.mk Id.term ("c_" ^ string_of_int !fresh_const_counter)
;;

let fresh_func () =
  incr fresh_func_counter;
  Id.mk Id.term ("f_" ^ string_of_int !fresh_func_counter)
;;

let term_to_string term = Format.asprintf "%a" Term.print term
let name_to_string name = Format.asprintf "%a" Name.print name
(* let statement_to_string stmt = Format.asprintf "%a" Statement.print stmt *)

(* Collect free variables *)
module S = Set.Make (struct
    type t = Id.t
    let compare = Id.compare
  end)

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

(* Substitute terms *)
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

(* Transform connectives *)
let rec transform_connectives term =
  Printf.printf "Transforming connectives in term: %s\n" (term_to_string term);
  match term.Term.term with
  | Term.App (f, args) ->
    (match f.Term.term with
     | Term.Builtin Term.Imply ->
       Printf.printf "Found implication in term: %s\n" (term_to_string term);
       (match args with
        | [ a; b ] ->
          Term.or_
            ~loc:term.Term.loc
            [ Term.not_ ~loc:term.Term.loc (transform_connectives a)
            ; transform_connectives b
            ]
        | _ -> term)
     | Term.Builtin Term.Equiv ->
       Printf.printf "Found equivalence in term: %s\n" (term_to_string term);
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
        | _ -> term)
     | _ ->
       Term.apply
         ~loc:term.Term.loc
         (transform_connectives f)
         (List.map transform_connectives args))
  | Term.Binder (b, vars, body) ->
    { term with Term.term = Term.Binder (b, vars, transform_connectives body) }
  | _ -> term
;;

(* Skolemize term *)
let rec skolemize_term is_conjecture univ_vars term =
  Printf.printf "Skolemizing term: %s\n" (term_to_string term);
  match term.Term.term with
  | Term.Binder (Term.Ex, bound_vars, body) ->
    if is_conjecture && S.is_empty univ_vars
    then (
      Printf.printf
        "Skolemizing conjecture with existential quantifier: %s\n"
        (term_to_string term);
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
      Printf.printf
        "Skolemizing axiom or internal existential quantifier: %s\n"
        (term_to_string term);
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
      Printf.printf
        "Skolemizing conjecture with internal existential quantifier: %s\n"
        (term_to_string term);
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

(* Skolemize statement *)
let skolemize_statement stmt =
  let skolemize_formula t =
    let skolemized = skolemize_term false S.empty t in
    transform_connectives skolemized
  in
  match stmt.Statement.descr with
  | Statement.Antecedent t ->
    { stmt with Statement.descr = Statement.Antecedent (skolemize_formula t) }
  | Statement.Consequent t ->
    { stmt with Statement.descr = Statement.Consequent (skolemize_formula t) }
  | Statement.Plain t ->
    { stmt with Statement.descr = Statement.Plain (skolemize_formula t) }
  | Statement.Clause l ->
    { stmt with Statement.descr = Statement.Clause (List.map skolemize_formula l) }
  | _ -> stmt
;;

(* Print term *)
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
        | [ arg ] -> Format.fprintf fmt "~%a" print_term arg
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
      "![%a]: (%a)"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",") print_term)
      vars
      print_term
      body
  | Term.Binder (Term.Ex, vars, body) ->
    Format.fprintf
      fmt
      "?[%a]: (%a)"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",") print_term)
      vars
      print_term
      body
  | Term.Colon (var, ty) -> Format.fprintf fmt "%a: %a" print_term var print_term ty
  | _ -> Format.fprintf fmt "%a" Term.print term
;;

let get_role stmt =
  match stmt.Statement.descr with
  | Statement.Antecedent _ -> "axiom"
  | Statement.Consequent _ -> "conjecture"
  | Statement.Plain _ -> "plain"
  | Statement.Clause _ -> "axiom"
  | Statement.Decls _ -> "type"
  | _ -> "plain"
;;

(* Get formula type *)
(* let get_formula_type stmt =
  let rec find_type = function
    | [] -> "fof" (* Default to "fof" if no type attribute is found *)
    | term :: rest ->
      (match term.Term.term with
       | Term.App ({ Term.term = Term.Symbol id; _ }, [ arg ])
         when Id.equal id Id.tptp_kind ->
         (match arg.Term.term with
          | Term.Symbol kind_id -> name_to_string (Id.name kind_id)
          | _ -> find_type rest)
       | _ -> find_type rest)
  in
  find_type stmt.Statement.attrs
;; *)

(* Print statement *)
let print_statement fmt stmt =
  let name =
    match stmt.Statement.id with
    | Some id -> name_to_string (Id.name id)
    | None -> "unknown"
  in
  let role = get_role stmt in
  match stmt.Statement.descr with
  | Statement.Antecedent t -> Format.fprintf fmt "fof(%s, %s, %a)." name role print_term t
  | Statement.Consequent t -> Format.fprintf fmt "fof(%s, %s, %a)." name role print_term t
  | Statement.Plain t -> Format.fprintf fmt "fof(%s, %s, %a)." name role print_term t
  | Statement.Clause l ->
    Format.fprintf
      fmt
      "cnf(%s, %s, %a)."
      name
      role
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " | ") print_term)
      l
  | Statement.Decls { contents; _ } ->
    List.iter
      (function
        | Statement.Abstract { id; ty; _ } ->
          Format.fprintf fmt "tff(%s, type, %a: %a).@." name Id.print id print_term ty
        | _ -> ())
      contents
  | _ -> Format.fprintf fmt "%a" Statement.print stmt
;;

(* Output skolemized statements *)
let output_skolemized_statements out statements =
  let fmt = Format.formatter_of_out_channel out in
  List.iter
    (fun stmt ->
      print_statement fmt stmt;
      Format.fprintf fmt "@.")
    statements
;;

(* Parse and skolemize *)
let parse_and_skolemize filename =
  let _, statements = TptpParser.parse_file filename in
  List.map skolemize_statement statements
;;

(* Main function *)
let () =
  if Array.length Sys.argv < 3
  then Printf.printf "Usage: %s <input_file> <output_file>\n" Sys.argv.(0)
  else (
    let input_file = Sys.argv.(1) in
    let output_file = Sys.argv.(2) in
    let skolemized_statements = parse_and_skolemize input_file in
    if output_file = "-"
    then output_skolemized_statements stdout skolemized_statements
    else (
      let out = open_out output_file in
      output_skolemized_statements out skolemized_statements;
      close_out out;
      if output_file <> "-"
      then Printf.printf "Skolemized TPTP file written to %s\n" output_file))
;;
