%{ 
open Printf
open Ast
%}

%token <string> OP
%token <string> ID
%token <int> NUM
%token <bool> BOOL
%token LET
%token DEF
%token LAMBDA
%token FORALL
%token NUM_T
%token BOOL_T
%token UNIT_T
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token COLON
%token ARROW
%token EOF

%start <Ast.program> prog
%start <Ast.expr> expr
%start <Ast.example> example
%start <Ast.constr> constr
%%

prog:
 | p = list(expr) EOF { p } ;

expr:
 | x = ID                { `Id x }
 | x = sexp(let_body)    { x }
 | x = sexp(def_body)    { x }
 | x = sexp(lambda_body) { x }
 | x = sexp(apply_body)  { x }
 | x = sexp(op_body)     { x }
 | x = constant          { (x :> expr) }

let_body:
 | LET; i = ID; b = expr; e = expr; { `Let (i, b, e) }

def_body:
 | DEF; i = ID; e = expr; { `Define (i, e) }

lambda_body:
 | LAMBDA; args = sexp(list(typed(ID))); e = expr; { `Lambda (args, e) }

apply_body:
 | f = expr; args = list(expr); { `Apply (f, args) }

op_body:
 | op_str = OP; args = list(expr); 
   { match operator_from_str op_str with
     | Some op -> `Op (op, args)
     | None -> begin
               printf "Parse error: Bad operator: %s\n" op_str;
               raise Parsing.Parse_error;
             end
   }

constant:
 | x = typed_list { `List x }
 | x = BOOL       { `Bool x }
 | x = NUM        { `Num x }

typed_list:
 | LBRACKET; RBRACKET; COLON; t = typ { ([], t) }
 | LBRACKET; items = nonempty_list(constant); RBRACKET;
   { let open Core.Std in
     let typeof_const (c: const) : typ = 
       match c with
       | `Num _ -> Num_t
       | `Bool _ -> Bool_t
       | `List (_, t) -> List_t t in
     match List.map ~f:typeof_const items with
     | x::xs -> if List.for_all xs ~f:((=) x) then (items, x) else 
                  begin
                    printf "Parse error: Inconsistent types in list.\n";
                    raise Parsing.Parse_error
                  end
   }

constr:
 | LPAREN; FORALL; vars = sexp(list(typed(ID))); body = expr; RPAREN { (body, vars) }

example:
 | lhs = example_lhs; ARROW; rhs = constant { (lhs, rhs) }

example_lhs:
 | LPAREN; f = ID; args = list(constant_or_apply); RPAREN { `Apply (`Id f, args) }

constant_or_apply:
 | LPAREN; f = ID; args = list(constant_or_apply); RPAREN { `Apply (`Id f, args) }
 | x = constant                                           { (x :> const_app) }

typ:
 | NUM_T;                                  { Num_t }
 | BOOL_T;                                 { Bool_t }
 | UNIT_T;                                 { Unit_t }
 | LBRACKET; t = typ; RBRACKET             { List_t t }
 | its = sexp(list(typ)); ARROW; ot = typ; { Arrow_t (its, ot) }

typed(X):
 | x = X; COLON; t = typ; { (x, t) }

sexp(X):
 | LPAREN; x = X; RPAREN; { x }
