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
%token AND
%token COMMA
%token BOTTOM
%token WHERE
%token EOF

%token EQUALS
%token NOT_EQUALS
%token GREATER_THAN
%token LESS_THAN
%token GREATER_THAN_OR_EQUALS
%token LESS_THAN_OR_EQUALS
%token SUBSET
%token SUPERSET
%token NOT_SUBSET
%token NOT_SUPERSET

%token INT_SORT
%token BOOL_SORT
%token LIST_SORT
%token STRING_SORT

%start <Component0.conjunct> conjunction_eof
%start <Component0.predicate> predicate_eof
%start <Component0.parsed_specification> specification_eof
%%

specification_eof:
 | x = specification; EOF { x }

conjunction_eof:
 | x = conjunction; EOF { x }

predicate_eof:
 | x = predicate; EOF { x }

specification:
 | c = conjunction; WHERE; s = sort_defs { (c, s) }

conjunction:
 | x = separated_list(AND, predicate) { x }

predicate:
 | x1 = term; o = operator; x2 = term { Binary (o, x1, x2) }
 | LPAREN; x1 = term; o = operator; x2 = term; RPAREN { Binary (o, x1, x2) }

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

operator:
 | EQUALS { Eq }
 | NOT_EQUALS { Neq }
 | GREATER_THAN { Gt }
 | LESS_THAN { Lt }
 | GREATER_THAN_OR_EQUALS { Ge }
 | LESS_THAN_OR_EQUALS { Le }
 | SUBSET { Subset }
 | SUPERSET { Superset }
 | NOT_SUBSET { NotSubset }
 | NOT_SUPERSET { NotSuperset }
 
variable:
 | x = INPUT_VAR { Input x }
 | x = FREE_VAR { Free x }
 | x = OUTPUT_VAR { Output }

constant:
 | x = BOOL { Bool x }
 | x = NUM { Int x }
 | BOTTOM { Bottom }
