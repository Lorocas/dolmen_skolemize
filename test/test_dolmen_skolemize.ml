open Alcotest

let find_files dir =
  let files = Sys.readdir dir in
  Array.fold_left (fun acc file ->
      if Filename.check_suffix file ".p" && not (Filename.check_suffix file "_dolmen.p") then
        file :: acc
      else
        acc
    ) [] files

let test_command file =
  let current_dir = Sys.getcwd () in
  let command = Printf.sprintf "%s/../bin/main.exe %s %s_dolmen.p"
                  (current_dir) (current_dir ^ "/../../../test/" ^ file) (current_dir ^ "/../../../test/" ^ Filename.chop_extension file) in
  let result = Sys.command command in
  (* Can be added or removed, because the current version of problems.p is wrong *)
  (* if (Filename.chop_extension file) = "new_example" then check int "command should NOT succeed" 2 result (* In the current version *)
  else  *)
    check int "command should succeed" 0 result
  
let () =
  let current_dir = Sys.getcwd () in
  let files = find_files (current_dir ^ "/../../../test") in
  let test_cases = List.map (fun file ->
      test_case (Printf.sprintf "Test | %s" file) `Quick (fun () -> test_command file)
    ) files in
  run "Dolmen Tests" [ "Command Tests", test_cases ]
