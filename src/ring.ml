(* Copyright (c) 2025 Groupoid Infinity

   $ ocamlopt -o ring ring.ml
*)

type monomial = { coeff : int; vars : (string * int) list }
type poly = monomial list

let normalize (p : poly) : poly =
  let compare_vars v1 v2 = compare v1.vars v2.vars in
  let add_mono m1 m2 =
    if m1.vars = m2.vars then
      let c = m1.coeff + m2.coeff in
      if c = 0 then None else Some { coeff = c; vars = m1.vars }
    else None
  in
  let rec collect acc = function
    | [] -> acc
    | m :: rest ->
        let like, unlike = List.partition (fun m' -> m.vars = m'.vars) rest in
        let combined = List.fold_left (fun acc m' ->
          Option.value ~default:acc (add_mono acc m')
        ) m like in
        collect (if combined.coeff = 0 then acc else combined :: acc) unlike
  in
  collect [] (List.sort compare_vars p)

let equal p1 p2 = normalize p1 = normalize p2

let poly_to_string p =
  if p = [] then "0" else
  String.concat " + " (List.map (fun m ->
    let v = String.concat "" (List.map (fun (v, e) ->
      if e = 1 then v else v ^ "^" ^ string_of_int e) m.vars) in
    string_of_int m.coeff ^ (if v = "" then "" else "*" ^ v)
  ) p)

let () =
  let p1 = [{ coeff = 2; vars = [("x", 1)] }; { coeff = 1; vars = [] }] in
  let p2 = [{ coeff = 1; vars = [] }; { coeff = 2; vars = [("x", 1)] }] in
  Printf.printf "2x + 1 = 1 + 2x: %b (%s = %s)\n"
    (equal p1 p2) (poly_to_string (normalize p1)) (poly_to_string (normalize p2));

  let p3 = [{ coeff = 0; vars = [("x", 1)] }; { coeff = 1; vars = [] }] in
  let p4 = [{ coeff = 1; vars = [] }] in
  Printf.printf "0x + 1 = 1: %b (%s = %s)\n"
    (equal p3 p4) (poly_to_string (normalize p3)) (poly_to_string (normalize p4));

  let p5 = [] in
  let p6 = [{ coeff = 0; vars = [] }] in
  Printf.printf "[] = 0: %b (%s = %s)\n"
    (equal p5 p6) (poly_to_string (normalize p5)) (poly_to_string (normalize p6))
