%{ open Component0 %}

%token <int> INPUT_VAR
%token <string> FREE_VAR
%token OUTPUT_VAR
%token <string> FUNC
%token <int> NUM
%token <bool> BOOL
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token AND
%token OR
%token COMMA
%token BOTTOM
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

%start <Component0.conjunct> conjunct_eof
%start <Component0.predicate> predicate_eof
%start <Component0.specification> specification_eof
%%

specification_eof:
 | x1 = delimited(LPAREN, separated_list(OR, delimited(LPAREN, conjunct, RPAREN)), RPAREN);
   AND;
   x2 = conjunct;
   EOF
   { { phi = x1; constraints = x2 } }

conjunct_eof:
 | x = conjunct; EOF { x }

predicate_eof:
 | x = predicate; EOF { x }

conjunct:
 | x = separated_list(AND, predicate) { x }

predicate:
 | x1 = term; o = operator; x2 = term { Binary (o, x1, x2) }
 | LPAREN; x1 = term; o = operator; x2 = term; RPAREN { Binary (o, x1, x2) }

term:
 | x = variable { Variable x }
 | x = constant { Constant x }
 | f = FUNC; args = delimited(LPAREN, separated_list(COMMA, term), RPAREN) { Apply (f, args) }

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
 | LBRACKET; RBRACKET { Nil }
 | BOTTOM { Bottom }
