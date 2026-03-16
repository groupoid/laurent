%{
  open Inferer

  let rec mk_forall params body =
    match params with
    | [] -> body
    | (x, ty) :: rest -> Forall (x, ty, mk_forall rest body)

  let rec mk_lam params body =
    match params with
    | [] -> body
    | (x, ty) :: rest -> Lam (x, ty, mk_lam rest body)
%}

%token <string> IDENT
%token <int> NUMBER
%token LPARENS RPARENS LBRACE RBRACE PIPE
%token COLON COMMA LAM ARROW DEF DEFEQ
%token FORALL EXISTS PROP REAL NAT SET
%token GT LT EQ PLUS MINUS TIMES
%token EOF

%right ARROW
%left PLUS MINUS
%left TIMES
%left GT LT EQ

%start <Inferer.exp list> main

%%

typ:
  | PROP { Prop }
  | REAL { Real }
  | NAT { Nat }
  | SET typ { Set $2 }
  | typ ARROW typ { Forall ("_", $1, $3) }
  | LPARENS typ RPARENS { $2 }

param:
  | LPARENS IDENT COLON typ RPARENS { ($2, $4) }

params:
  | param { [$1] }
  | param params { $1 :: $2 }

exp:
  | IDENT { Var $1 }
  | NUMBER { if $1 = 0 then Zero else if $1 = 1 then One else RealConst (float_of_int $1) }
  | LAM params COMMA exp { mk_lam $2 $4 }
  | FORALL params COMMA exp { mk_forall $2 $4 }
  | exp exp %prec TIMES { App ($1, $2) }
  | exp PLUS exp { RealOps (Plus, $1, $3) }
  | exp MINUS exp { RealOps (Minus, $1, $3) }
  | exp TIMES exp { RealOps (Times, $1, $3) }
  | exp GT exp { RealIneq (Gt, $1, $3) }
  | exp LT exp { RealIneq (Lt, $1, $3) }
  | exp EQ exp { RealIneq (Eq, $1, $3) }
  | LBRACE IDENT COLON typ PIPE exp RBRACE { Set (Lam ($2, $4, $6)) }
  | LPARENS exp RPARENS { $2 }

definition:
  | DEF IDENT COLON typ DEFEQ exp { ($2, $4, $6) }

main:
  | definition main { let (name, ty, term) = $1 in term :: $2 }
  | exp main { $1 :: $2 }
  | EOF { [] }
