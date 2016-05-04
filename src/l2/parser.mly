%{
open Ast
open Collections
%}

%token <string> ID
%token <int> NUM
%token <bool> BOOL

%token LET
%token IN
%token IF
%token THEN
%token ELSE
%token FUN
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
%token AND
%token OR
%token NOT
%token CONS
%token SEMI
%token ARROW
%token LCBRACKET
%token RCBRACKET
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token COMMA

%token EOF

%right OR
%right AND
%left EQ NEQ GT LT LE GE
%right CONS
%left ADD SUB
%left MUL DIV MOD
%nonassoc NOT

%start <Ast.expr> expr_eof
%start <Ast.expr> expr_ml_eof

%start <Ast.example> example_eof
%start <Ast.constr> constr_eof
%start <Ast.typ> typ_eof
%%

expr_eof:
 | x = expr; EOF { x }

expr_ml_eof:
 | x = expr_ml; EOF { x }

example_eof:
 | x = example; EOF { x }

constr_eof:
 | x = constr; EOF { x }

typ_eof:
 | x = typ; EOF { x }

expr_ml:
 | LET; x = ID; EQ; y = expr_ml; IN; z = expr_ml;         { `Let (x, y, z) }
 | IF; x = expr_ml; THEN; y = expr_ml; ELSE; z = expr_ml  { `Op (If, [x; y; z]) }
 | FUN; xs = nonempty_list(ID); ARROW; y = expr_ml        { `Lambda(xs, y) }
 | x = simple_expr_ml { x }
 
simple_expr_ml:
 | x = argument_ml                                                  { x }
 | x = argument_ml; ys = nonempty_list(argument_ml)                 { `Apply (x, ys) }
 | op = unop; x = simple_expr_ml;                                   { `Op (op, [x]) }
 | x = simple_expr_ml; op = binop; y = simple_expr_ml;              { `Op (op, [x; y]) }

argument_ml:
 | x = BOOL                                               { `Bool x }
 | x = NUM                                                { `Num x }
 | x = ID                                                        { `Id x }
 | x = sexp(expr_ml)                                                { x }
 | x = delimited(LBRACKET, separated_list(SEMI, expr_ml), RBRACKET) { `List x } 

%inline binop:
 | MUL { Mul }
 | DIV { Div }
 | MOD { Mod }
 | ADD { Plus }
 | SUB { Minus }
 | CONS { Cons }
 | EQ { Eq }
 | NEQ { Neq }
 | GT { Gt }
 | GE { Geq }
 | LT { Lt }
 | LE { Leq }
 | AND { And }
 | OR  { Or }

%inline unop:
 | NOT { Not }

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
 | op = binop; args = list(expr); { `Op (op, args) }
 | op = unop; args = list(expr);  { `Op (op, args) }
 | IF; args = list(expr);         { `Op (If, args) }
 | f = expr; args = list(expr);
   {
     match f with
     | `Id f_id ->
        (match f_id with
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
