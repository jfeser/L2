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
%token NIL
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

%start <Ast.expr list> prog
%start <Ast.expr> expr
%start <Ast.example> example
%%

prog:
 | p = list(expr) EOF { p } ;

expr:
 | LPAREN; LET; i = ID; b = expr; e = expr; RPAREN { `Let (i, b, e) }
 | LPAREN; DEF; i = ID; e = expr; RPAREN           { `Define (i, e) }
 | LPAREN; LAMBDA; LPAREN; args = list(typed_id); RPAREN; e = expr; RPAREN
   { `Lambda (args, e) }
 | LPAREN; f = expr; args = list(expr); RPAREN     { `Apply (f, args) }
 | LPAREN; op_str = OP; args = list(expr); RPAREN
   { match operator_from_str op_str with
     | Some op -> `Op (op, args)
     | None -> begin
               printf "Parse error: Bad operator: %s\n" op_str;
               raise Parsing.Parse_error;
             end
   }
 | LBRACKET; items = list(expr); RBRACKET { `List items }
 | NIL                                    { `Nil }
 | x = BOOL                               { `Bool x }
 | x = NUM                                { `Num x }
 | x = ID                                 { `Id x }

example:
 | lhs = example_lhs; ARROW; rhs = const { (lhs, rhs) }

example_lhs:
 | LPAREN; f = ID; args = list(const_or_apply); RPAREN { `Apply (`Id f, args) }

const_or_apply:
 | LPAREN; f = ID; args = list(const_or_apply); RPAREN { `Apply (`Id f, args) }
 | LBRACKET; items = list(const_or_apply); RBRACKET    { `List items }
 | NIL                                                 { `Nil }
 | x = BOOL                                            { `Bool x }
 | x = NUM                                             { `Num x }

const:
 | LBRACKET; items = list(const); RBRACKET { `List items }
 | NIL                                     { `Nil }
 | x = BOOL                                { `Bool x }
 | x = NUM                                 { `Num x }

typed_id:
 | i = ID; COLON; t = typ; { (i, t) }

typ:
 | NUM_T;                                            { Num_t }
 | BOOL_T;                                           { Bool_t }
 | UNIT_T;                                           { Unit_t }
 | LBRACKET; RBRACKET                                { Nil_t }
 | LBRACKET; t = typ; RBRACKET                       { List_t t }
 | LPAREN; its = list(typ); RPAREN; ARROW; ot = typ; { Arrow_t (its, ot) }
