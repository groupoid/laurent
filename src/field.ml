(* Copyright (c) 2025 Groupoid Infinity

   $ ocamlfind ocamlc -o field -package num -linkpkg field.ml
*)

open Num

type monomial = { coeff : num; vars : (string * int) list }
type poly = monomial list
type expr = Poly of poly | Frac of poly * poly


let (//) n d : num = Num.div_num n d

(* Multiply two monomials *)
let mul_monomial m1 m2 =
  let vars = List.sort compare
    (List.fold_left (fun acc (v, e) ->
       match List.assoc_opt v acc with
       | Some e' -> (v, e + e') :: List.remove_assoc v acc
       | None -> (v, e) :: acc
     ) m1.vars m2.vars) in
  { coeff = mult_num m1.coeff m2.coeff; vars }

(* Normalize a polynomial: combine like terms, remove zeros *)
let normalize_poly p =
  let sorted = List.sort (fun m1 m2 -> compare m1.vars m2.vars) p in
  let rec collect acc = function
    | [] -> List.rev acc
    | m :: rest ->
        if eq_num m.coeff (num_of_int 0) then collect acc rest
        else
          let like, unlike = List.partition (fun m' -> m.vars = m'.vars) rest in
          let coeff = List.fold_left (fun c m' -> add_num c m'.coeff) m.coeff like in
          if eq_num coeff (num_of_int 0) then collect acc unlike
          else collect ({ coeff; vars = m.vars } :: acc) unlike
  in
  collect [] sorted

(* Multiply two polynomials *)
let mul_poly p1 p2 =
  let products = List.concat_map (fun m1 -> List.map (fun m2 -> mul_monomial m1 m2) p2) p1 in
  normalize_poly products

(* Add two polynomials *)
let add_poly p1 p2 = normalize_poly (p1 @ p2)

let get_exp v vars =
  try List.assoc v vars with Not_found -> 0

let all_vars m1 m2 =
  let vars1 = List.map fst m1.vars in
  let vars2 = List.map fst m2.vars in
  List.sort_uniq compare (vars1 @ vars2)

(* Simplify an expression *)
let simplify = function
  | Poly p -> Poly (normalize_poly p)
  | Frac (n, d) ->
      let n' = normalize_poly n in
      let d' = normalize_poly d in
      if d' = [] then failwith "Division by zero"
      else if n' = [] then Poly []  (* Zero numerator *)
      else
        match n', d' with
        | [m1], [m2] ->
            let coeff = m1.coeff // m2.coeff in
            let vars = all_vars m1 m2 in
            let exps = List.map (fun v -> (v, get_exp v m1.vars - get_exp v m2.vars)) vars in
            let num_vars = List.filter (fun (v, e) -> e > 0) exps in
            let den_vars = List.map (fun (v, e) -> (v, -e)) (List.filter (fun (v, e) -> e < 0) exps) in
            if den_vars = [] then
              Poly [ { coeff; vars = num_vars } ]
            else
              Frac ([ { coeff; vars = num_vars } ], [ { coeff = num_of_int 1; vars = den_vars } ])
        | _ -> Frac (n', d')

let add_expr e1 e2 =
  match e1, e2 with
  | Poly p1, Poly p2 -> simplify (Poly (add_poly p1 p2))
  | Poly p, Frac (n, d) ->
      let n' = add_poly (mul_poly p d) n in
      simplify (Frac (n', d))
  | Frac (n, d), Poly p ->
      let n' = add_poly n (mul_poly p d) in
      simplify (Frac (n', d))
  | Frac (n1, d1), Frac (n2, d2) ->
      let num = add_poly (mul_poly n1 d2) (mul_poly n2 d1) in
      let den = mul_poly d1 d2 in
      simplify (Frac (num, den))

(* String representation *)
let string_of_monomial m =
  let c = string_of_num m.coeff in
  let v = String.concat "" (List.map (fun (v, e) ->
    if e = 1 then v else v ^ "^" ^ string_of_int e) m.vars) in
  if v = "" then c 
  else if eq_num m.coeff (num_of_int 1) then v
  else if eq_num m.coeff (num_of_int (-1)) then "-" ^ v
  else c ^ "*" ^ v

let string_of_poly p =
  if p = [] then "0" else
  String.concat " + " (List.map string_of_monomial p)

let string_of_expr = function
  | Poly p -> string_of_poly p
  | Frac (n, d) -> "(" ^ string_of_poly n ^ ") / (" ^ string_of_poly d ^ ")"

(* Test cases *)
let () =
  (* Basic: 1/x + 2/y *)
  let e1 = Frac ([{ coeff = num_of_int 1; vars = [] }], [{ coeff = num_of_int 1; vars = [("x", 1)] }]) in
  let e2 = Frac ([{ coeff = num_of_int 2; vars = [] }], [{ coeff = num_of_int 1; vars = [("y", 1)] }]) in
  Printf.printf "1/x + 2/y = %s\n" (string_of_expr (add_expr e1 e2));

  (* Division by zero *)
  let e3 = Frac ([{ coeff = num_of_int 1; vars = [] }], [{ coeff = num_of_int 0; vars = [] }]) in
  (try ignore (simplify e3); print_endline "Division by zero not caught!"
   with Failure msg -> Printf.printf "Caught division by zero: %s\n" msg);

  (* Basic: 0/x + 1/y *)
  let e4 = Frac ([{ coeff = num_of_int 0; vars = [] }], [{ coeff = num_of_int 1; vars = [("x", 1)] }]) in
  let e5 = Frac ([{ coeff = num_of_int 1; vars = [] }], [{ coeff = num_of_int 1; vars = [("y", 1)] }]) in
  Printf.printf "0/x + 1/y = %s\n" (string_of_expr (add_expr e4 e5));

  (* Complex: (x + 1)/(x - 1) + 2/y *)
  let e6 = Frac ([{ coeff = num_of_int 1; vars = [("x", 1)] }; { coeff = num_of_int 1; vars = [] }],
                 [{ coeff = num_of_int 1; vars = [("x", 1)] }; { coeff = num_of_int (-1); vars = [] }]) in
  let e7 = Frac ([{ coeff = num_of_int 2; vars = [] }], [{ coeff = num_of_int 1; vars = [("y", 1)] }]) in
  Printf.printf "(x + 1)/(x - 1) + 2/y = %s\n" (string_of_expr (add_expr e6 e7));

  (* Complex: x^2/y + (x + 1)/y^2 *)
  let e8 = Frac ([{ coeff = num_of_int 1; vars = [("x", 2)] }], [{ coeff = num_of_int 1; vars = [("y", 1)] }]) in
  let e9 = Frac ([{ coeff = num_of_int 1; vars = [("x", 1)] }; { coeff = num_of_int 1; vars = [] }],
                 [{ coeff = num_of_int 1; vars = [("y", 2)] }]) in
  Printf.printf "x^2/y + (x + 1)/y^2 = %s\n" (string_of_expr (add_expr e8 e9));

  let p1 = Poly [{coeff=num_of_int 1; vars=[("x",1)]}; {coeff=num_of_int 1; vars=[("y",1)]}] in
  let p2 = Poly [{coeff=num_of_int 2; vars=[("x",1)]}; {coeff=num_of_int 3; vars=[("y",1)]}] in
  Printf.printf "x + y + (2x + 3y) = %s\n" (string_of_expr (add_expr p1 p2));

  let p = Poly [{coeff=num_of_int 1; vars=[("x",1)]}] in
  let f = Frac ([{coeff=num_of_int 1; vars=[]}], [{coeff=num_of_int 1; vars=[("y",1)]}]) in
  Printf.printf "x + 1/y = %s\n" (string_of_expr (add_expr p f));

  let f1 = Frac ([{coeff=num_of_int 1; vars=[]}], [{coeff=num_of_int 1; vars=[("x",1)]}]) in
  let f2 = Frac ([{coeff=num_of_int (-1); vars=[]}], [{coeff=num_of_int 1; vars=[("x",1)]}]) in
  Printf.printf "1/x + (-1/x) = %s\n" (string_of_expr (add_expr f1 f2));

  let f = Frac ([], [{coeff=num_of_int 1; vars=[("x",1)]}]) in
  Printf.printf "0/x = %s\n" (string_of_expr (simplify f));

  let f1 = Frac ([{coeff=num_of_int 2; vars=[]}], [{coeff=num_of_int 3; vars=[]}]) in
  let f2 = Frac ([{coeff=num_of_int 1; vars=[]}], [{coeff=num_of_int 2; vars=[]}]) in
  Printf.printf "2/3 + 1/2 = %s\n" (string_of_expr (add_expr f1 f2));

  let f = Frac ([{coeff=num_of_int 3; vars=[("x",1); ("y",1)]}],
                [{coeff=num_of_int 6; vars=[("x",2); ("y",2)]}]) in
  Printf.printf "3xy / (6x^2 y^2) = %s\n" (string_of_expr (simplify f));

  let f1 = Frac ([{coeff=num_of_int (-1); vars=[("x",1)]}], [{coeff=num_of_int 1; vars=[("y",1)]}]) in
  let f2 = Frac ([{coeff=num_of_int 1; vars=[("x",1)]}], [{coeff=num_of_int (-1); vars=[("y",1)]}]) in
  Printf.printf "-x/y + x/(-y) = %s\n" (string_of_expr (add_expr f1 f2));

  let f = Frac ([{coeff=num_of_int 2; vars=[("x",2); ("y",1)]}],
              [{coeff=num_of_int 2; vars=[("x",2); ("y",1)]}]) in
  Printf.printf "2x^2 y / (2x^2 y) = %s\n" (string_of_expr (simplify f));

