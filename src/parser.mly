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
     | Some op -> if (List.length args) <> (operator_to_arity op)
                  then begin
                      printf "Parse error: Wrong # of arguments to: %s\n" 
                             op_str;
                      raise Parsing.Parse_error;
                    end
                  else `Op (op, args)
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

typed_id:
 | i = ID; COLON; t = typ; { (i, t) }

typ:
 | NUM_T;                                            { Num_t }
 | BOOL_T;                                           { Bool_t }
 | UNIT_T;                                           { Unit_t }
 | LBRACKET; RBRACKET                                { Nil_t }
 | LBRACKET; t = typ; RBRACKET                       { List_t t }
 | LPAREN; its = list(typ); RPAREN; ARROW; ot = typ; { Arrow_t (its, ot) }
