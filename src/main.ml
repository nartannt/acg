let () = print_endline "Hello, World!"

open Lambda_calc

let () =
  let test = Atom "test" in
  match test with
  | Atom _ -> print_string "module compiles too, right?"
  | _ -> print_string "interesting"
