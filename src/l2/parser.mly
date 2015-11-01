%{
open Ast
open Collections
%}

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
%token LCBRACKET
%token RCBRACKET
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
 | x = sexp(call_body)   { x }
 | x = BOOL              { `Bool x }
 | x = NUM               { `Num x }
 | x = tree;             { `Tree x }
 | LBRACKET; x = list(expr); RBRACKET; { `List x }

tree:
 | LCBRACKET; RCBRACKET;                           { Tree.Empty }
 | LCBRACKET; x = expr; y = list(tree); RCBRACKET; { Tree.Node (x, y) }

let_body:
 | LET; i = ID; b = expr; e = expr; { `Let (i, b, e) }

lambda_body:
 | LAMBDA; args = sexp(list(ID)); body = expr; { `Lambda (args, body) }

call_body:
 | f = expr; args = list(expr);
   {
     match f with
     | `Id f_id ->
        (match f_id with
         | "+"        -> `Op (Plus, args)
         | "-"        -> `Op (Minus, args)
         | "*"        -> `Op (Mul, args)
         | "/"        -> `Op (Div, args)
         | "%"        -> `Op (Mod, args)
         | "="        -> `Op (Eq, args)
         | "!="       -> `Op (Neq, args)
         | "<"        -> `Op (Lt, args)
         | "<="       -> `Op (Leq, args)
         | ">"        -> `Op (Gt, args)
         | ">="       -> `Op (Geq, args)
         | "&"        -> `Op (And, args)
         | "|"        -> `Op (Or, args)
         | "~"        -> `Op (Not, args)
         | "if"       -> `Op (If, args)
         | "rcons"    -> `Op (RCons, args)
         | "cons"     -> `Op (Cons, args)
         | "car"      -> `Op (Car, args)
         | "cdr"      -> `Op (Cdr, args)
         | "tree"     -> `Op (Tree, args)
         | "children" -> `Op (Children, args)
         | "value"    -> `Op (Value, args)
         | _          -> `Apply (f, args))
     | _ -> `Apply (f, args)
   }

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
                                                      | "num" -> Const_t Num_t
                                                      | "bool" -> Const_t Bool_t
                                                      | _ -> Var_t (ref (Quant x)) }
 | x = sexp(typ);                                   { x }
 | constr = ID; LBRACKET; arg = typ; RBRACKET       { App_t (constr, [arg]) }
 | constr = ID; LBRACKET; args = typ_list; RBRACKET { App_t (constr, args) }

typ_list:
 | x = typ; COMMA; y = typ       { [x; y] }
 | x = typ; COMMA; xs = typ_list { x::xs }

sexp(X):
 | LPAREN; x = X; RPAREN; { x }
