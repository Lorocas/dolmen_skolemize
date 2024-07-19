open Dolmen_std

(** [name_to_string name] converts a [name] to its [string] representation.
    @param name the [name] to convert.
    @return [string] representation of the name. 
*)
let name_to_string name = Format.asprintf "%a" Name.print name (* Nom des axiomes et de la conjecture *)

(* let statement_to_string stmt = Format.asprintf "%a" Statement.print stmt *)

(** [term_to_string term] converts a [term] to its [string] representation.
    @param term the [term] to convert.
    @return [string] representation of the [term]. 
*)
let term_to_string term = Format.asprintf "%a" Term.print term;;

(** [contains_substring s sub] checks if [sub] is a substring of [s]
    @param s the main [string].
    @param sub the substring to search for.
    @return [bool] [true] if [sub] is a substring of [s], [false] otherwise. 
*)
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

(** [modify_string s] modifies the input string by adding [`] before [∀] and [∃], replace [==] by [=], and replace periods with commas.
    @param s the input [string] to modify.
    @return modified [string] with the specified transformations. 
*)
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

(** [buffer_contains] checks if the [string] [seq] is in the buffer [buffer] 
    @param buffer [buffer]
    @param seq [string]
    @return [bool] [true] if [buffer] contains [seq], [false] otherwise
*)
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