open Num

(* Operator types *)
type op = Plus | Minus | Times | Div | Neg | Pow | Abs | Ln | Sin | Cos | Exp

let (//) n d : num = Num.div_num n d

(* Expression type *)
type expr =
  | Num of num          (* Rational number, e.g., 2/3 *)
  | Var of string       (* Variable, e.g., x *)
  | Op of op * expr * expr  (* Operation, e.g., 2 + 3, ln x *)

(* Result type *)
type result =
  | RNum of num         (* Simplified rational number *)
  | RExpr of expr       (* Unsimplified symbolic expression *)

(* Helper to convert result back to expr *)
let expr_of_result = function
  | RNum n -> Num n
  | RExpr e -> e

(* Convert float to num for approximations *)
let num_of_float f =
  let rat = approx_num_fix 10 f in  (* 10 decimal places precision *)
  if eq_num (num_of_string rat) (num_of_int 0) && f <> (num_of_string "0.0") then num_of_int 1 // num_of_int 10000  (* Small non-zero value *)
  else (num_of_string rat)

(* Main normalization function *)
let rec norm_num (e : expr) : result =
  match e with
  | Num n -> RNum n
  | Var v -> RExpr (Var v)
  | Op (op, e1, e2) ->
      let r1 = norm_num e1 in
      let r2 = norm_num e2 in
      match op with
      | Plus ->
          (match r1, r2 with
           | RNum n1, RNum n2 -> RNum (add_num n1 n2)
           | _ -> RExpr (Op (Plus, expr_of_result r1, expr_of_result r2)))
      | Minus ->
          (match r1, r2 with
           | RNum n1, RNum n2 -> RNum (sub_num n1 n2)
           | _ -> RExpr (Op (Minus, expr_of_result r1, expr_of_result r2)))
      | Times ->
          (match r1, r2 with
           | RNum n1, RNum n2 -> RNum (mult_num n1 n2)
           | _ -> RExpr (Op (Times, expr_of_result r1, expr_of_result r2)))
      | Div ->
          (match r1, r2 with
           | RNum n1, RNum n2 ->
               if eq_num n2 (num_of_int 0) then failwith "Division by zero"
               else RNum (n1 // n2)
           | _ -> RExpr (Op (Div, expr_of_result r1, expr_of_result r2)))
      | Pow ->
          (match r1, r2 with
           | RNum n1, RNum n2 ->
               if is_integer_num n2 then RNum (power_num n1 n2)
               else RNum (num_of_string (Printf.sprintf "%.0f" (float_of_num n1 ** float_of_num n2)))
           | _ -> RExpr (Op (Pow, expr_of_result r1, expr_of_result r2)))
      | Neg ->
          (match r1 with
           | RNum n1 -> RNum (minus_num n1)
           | _ -> RExpr (Op (Neg, expr_of_result r1, Num (num_of_int 1))))
      | Abs ->
          (match r1 with
           | RNum n1 -> RNum (abs_num n1)
           | _ -> RExpr (Op (Abs, expr_of_result r1, Num (num_of_int 1))))
      | Ln ->
          (match r1 with
           | RNum n1 ->
               if le_num n1 (num_of_int 0) then failwith "Log of non-positive number"
               else RNum (num_of_string (Printf.sprintf "%.0f" (log (float_of_num n1))))
           | _ -> RExpr (Op (Ln, expr_of_result r1, Num (num_of_int 1))))
      | Sin ->
          (match r1 with
           | RNum n1 -> RNum (num_of_string (Printf.sprintf "%.0f" (sin (float_of_num n1))))
           | _ -> RExpr (Op (Sin, expr_of_result r1, Num (num_of_int 1))))
      | Cos ->
          (match r1 with
           | RNum n1 -> RNum (num_of_string (Printf.sprintf "%.0f" (cos (float_of_num n1))))
           | _ -> RExpr (Op (Cos, expr_of_result r1, Num (num_of_int 1))))
      | Exp ->
          (match r1 with
           | RNum n1 -> RNum (num_of_string (Printf.sprintf "%.0f" (exp (float_of_num n1))))
           | _ -> RExpr (Op (Exp, expr_of_result r1, Num (num_of_int 1))))

(* String representation *)
let string_of_op = function
  | Plus -> "+" | Minus -> "-" | Times -> "*" | Div -> "/"
  | Neg -> "-" | Pow -> "^" | Abs -> "abs" | Ln -> "ln"
  | Sin -> "sin" | Cos -> "cos" | Exp -> "exp"

let rec string_of_expr = function
  | Num n -> string_of_num n
  | Var v -> v
  | Op (op, e1, e2) ->
      let s1 = string_of_expr e1 in
      let s2 = string_of_expr e2 in
      match op with
      | Neg | Abs | Ln | Sin | Cos | Exp -> string_of_op op ^ "(" ^ s1 ^ ")"
      | _ -> "(" ^ s1 ^ " " ^ string_of_op op ^ " " ^ s2 ^ ")"

let string_of_result = function
  | RNum n -> string_of_num n
  | RExpr e -> string_of_expr e

(* Test cases *)
let () =
  let tests = [
    Op (Plus, Num (num_of_int 2), Num (num_of_int 3));
    Op (Minus, Num (num_of_int 5), Num (num_of_int 2));
    Op (Times, Num (num_of_int 1 // num_of_int 2), Num (num_of_int 4));
    Op (Div, Num (num_of_int 2), Num (num_of_int 3));
    Op (Neg, Num (num_of_int 3), Num (num_of_int 1));
    Op (Abs, Num (num_of_int (-2)), Num (num_of_int 1));
    Op (Pow, Num (num_of_int 2), Num (num_of_int 3));
    Op (Pow, Num (num_of_int 2), Num (num_of_int 1 // num_of_int 2));
    Op (Ln, Num (num_of_int 1), Num (num_of_int 1));
    Op (Sin, Num (num_of_int 0), Num (num_of_int 1));
    Op (Cos, Num (num_of_int 0), Num (num_of_int 1));
    Op (Exp, Num (num_of_int 0), Num (num_of_int 1));
    Op (Plus, Var "x", Num (num_of_int 1));
    Op (Ln, Var "x", Num (num_of_int 1));
(*    (try norm_num (Op (Div, Num (num_of_int 1), Num (num_of_int 0))) |> string_of_result
     with Failure msg -> "Error: " ^ msg);
    (try norm_num (Op (Ln, Num (num_of_int 0), Num (num_of_int 1))) |> string_of_result
     with Failure msg -> "Error: " ^ msg) *)
  ] in
  List.iter (fun e ->
    let result = norm_num e in
    Printf.printf "%s = %s\n" (string_of_expr e) (string_of_result result))
    tests
