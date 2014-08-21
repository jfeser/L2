%{
open Ast
%}

%token <string> OP
%token <string> ID
%token <int> NUM
%token <bool> BOOL
%token LET
%token LAMBDA
%token FORALL
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token COMMA
%token ARROW
%token EOF

%start <Ast.expr> expr_eof
%start <Ast.example> example_eof
%start <Ast.constr> constr_eof
%start <Ast.typ> typ_eof
%%

expr_eof:
 | x = expr; EOF { x }

example_eof:
 | x = example; EOF { x }

constr_eof:
 | x = constr; EOF { x }

typ_eof:
 | x = typ; EOF { x }

expr:
 | x = ID                { `Id x }
 | x = sexp(let_body)    { x }
 | x = sexp(lambda_body) { x }
 | x = sexp(apply_body)  { x }
 | x = sexp(op_body)     { x }
 | LBRACKET; x = list(expr); RBRACKET; { `List x }
 | x = BOOL                            { `Bool x }
 | x = NUM                             { `Num x }

let_body:
 | LET; i = ID; b = expr; e = expr; { `Let (i, b, e) }

lambda_body:
 | LAMBDA; args = sexp(list(ID)); body = expr; { `Lambda (args, body) }

apply_body:
 | f = expr; args = list(expr); { `Apply (f, args) }

op_body:
 | op_str = OP; args = list(expr); { `Op (Op.of_string op_str, args) }

constr:
 | LPAREN; FORALL; vars = sexp(list(ID)); body = expr; RPAREN { (body, vars) }

example:
 | lhs = expr; ARROW; rhs = expr { (lhs, rhs) }

typ:
 | x = simple_typ                                { x }
 | LPAREN; RPAREN; ARROW; output = typ;          { Arrow_t ([], output) }
 | input = simple_typ; ARROW; output = typ;      { Arrow_t ([input], output) }
 | inputs = sexp(typ_list); ARROW; output = typ; { Arrow_t (inputs, output) }

simple_typ:
 | x = ID                                           { match x with
                                                      | "num" -> Const_t Num
                                                      | "bool" -> Const_t Bool
                                                      | _ -> Var_t (Quant x) }
 | x = sexp(typ);                                   { x }
 | constr = ID; LBRACKET; arg = typ; RBRACKET       { App_t (constr, [arg]) }
 | constr = ID; LBRACKET; args = typ_list; RBRACKET { App_t (constr, args) }

typ_list:
 | x = typ; COMMA; y = typ       { [x; y] }
 | x = typ; COMMA; xs = typ_list { x::xs }

sexp(X):
 | LPAREN; x = X; RPAREN; { x }
