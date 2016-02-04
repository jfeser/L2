%{
open Component0
%}

%token <int> INPUT_VAR
%token <string> FREE_VAR
%token OUTPUT_VAR
%token <string> FUNC
%token <int> NUM
%token <bool> BOOL
%token COLON
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token COMMA
%token WHERE
%token EOF

%token INT_SORT
%token BOOL_SORT
%token LIST_SORT
%token STRING_SORT

%start <Component0.parsed_specification> specification_eof
%%

specification_eof:
 | x = specification; EOF { x }

specification:
 | t = term; WHERE; s = sort_defs { (t, s) }
 | t = term { (t, []) }

term:
 | x = variable { Variable x }
 | x = constant { Constant x }
 | x = delimited(LBRACKET, separated_list(COMMA, term), RBRACKET) {
       List.fold_right (fun e a -> Apply ("Cons", [e; a])) x (Constant Nil)
   }
 | f = FUNC; args = delimited(LPAREN, separated_list(COMMA, term), RPAREN) { Apply (f, args) }

sort_defs:
 | x = separated_list(COMMA, sort_def) { x }

sort_def:
 | v = variable; COLON; s = sort { (v, s) }

sort:
 | INT_SORT { Int }
 | BOOL_SORT { Bool }
 | LIST_SORT { List }
 | STRING_SORT { String }
 
variable:
 | x = INPUT_VAR { Input x }
 | x = FREE_VAR { Free x }
 | x = OUTPUT_VAR { Output }

constant:
 | x = BOOL { Bool x }
 | x = NUM { Int x }
