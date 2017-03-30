%{
open Ast
open Collections
%}

%token <string> ID
%token <int> NUM
%token <bool> BOOL

%token LET
%token IF
%token LAMBDA
%token FORALL
%token ADD
%token SUB
%token MUL
%token DIV
%token MOD
%token EQ
%token NEQ
%token GT
%token GE
%token LT
%token LE
%token AMP
%token AND
%token BAR
%token OR
%token NOT
%token CONS
%token RCONS
%token CAR
%token CDR
%token TREE
%token CHILDREN
%token VALUE
%token ARROW
%token LCBRACKET
%token RCBRACKET
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token COMMA
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

%inline binop:
 | MUL  { Mul }
 | DIV  { Div }
 | MOD  { Mod }
 | ADD  { Plus }
 | SUB  { Minus }
 | CONS { Cons }
 | EQ   { Eq }
 | NEQ  { Neq }
 | GT   { Gt }
 | GE   { Geq }
 | LT   { Lt }
 | LE   { Leq }
 | AMP  { And }
 | BAR  { Or }
 | AND  { And }
 | OR   { Or }

%inline unop:
 | NOT { Not }

%inline unop_call:
 | CAR { Car }
 | CDR { Cdr }
 | VALUE { Value }
 | CHILDREN { Children }

%inline binop_call:
 | RCONS { RCons }
 | TREE { Tree }

op:
 | x = binop      { x }
 | x = unop       { x }
 | x = unop_call  { x }
 | x = binop_call { x }
 | IF             { If }

expr:
 | x = ID                                          { `Id x }
 | x = sexp(let_body)                              { x }
 | x = sexp(lambda_body)                           { x }
 | x = sexp(call_body)                             { x }
 | x = BOOL                                        { `Bool x }
 | x = NUM                                         { `Num x }
 | x = tree;                                       { `Tree x }
 | LBRACKET; x = list(expr); RBRACKET;             { `List x }

tree:
 | LCBRACKET; RCBRACKET;                           { Tree.Empty }
 | LCBRACKET; x = expr; y = list(tree); RCBRACKET; { Tree.Node (x, y) }

let_body:
 | LET; i = ID; b = expr; e = expr;                { `Let (i, b, e) }

lambda_body:
 | LAMBDA; args = sexp(list(ID)); body = expr;     { `Lambda (args, body) }

call_body:
 | op = op; args = list(expr);                     { `Op (op, args) }
 | f = expr; args = list(expr);                    { `Apply (f, args) }

constr:
 | LPAREN; FORALL; vars = sexp(list(ID)); body = expr; RPAREN { (body, vars) }

example:
 | lhs = expr; ARROW; rhs = expr { (lhs, rhs) }

typ:
 | x = simple_typ                                   { x }
 | LPAREN; RPAREN; ARROW; output = typ;             { Arrow_t ([], output) }
 | input = simple_typ; ARROW; output = typ;         { Arrow_t ([input], output) }
 | inputs = sexp(typ_list); ARROW; output = typ;    { Arrow_t (inputs, output) }

simple_typ:
 | x = ID                                           { match x with
                                                      | "num" -> Const_t Num_t
                                                      | "bool" -> Const_t Bool_t
                                                      | _ -> Var_t (ref (Quant x)) }
 | x = sexp(typ);                                   { x }
 | constr = ID; LBRACKET; arg = typ; RBRACKET       { App_t (constr, [arg]) }
 | TREE; LBRACKET; arg = typ; RBRACKET              { App_t ("tree", [arg]) }
 | constr = ID; LBRACKET; args = typ_list; RBRACKET { App_t (constr, args) }

typ_list:
 | x = typ; COMMA; y = typ                          { [x; y] }
 | x = typ; COMMA; xs = typ_list                    { x::xs }

sexp(X):
 | LPAREN; x = X; RPAREN; { x }
