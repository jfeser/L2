{
  open Parser_sexp

  exception SyntaxError of string
  let syntax_error char = raise (SyntaxError ("Unexpected character: " ^ char))
}

let white = [' ' '\t' '\n' '\r']+
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' ''']*

rule token = parse
 | white                 { token lexbuf } (* Eat whitespace. *)
 | "let"                 { LET }
 | "if"                  { IF }
 | "lambda"              { LAMBDA }
 | "forall"              { FORALL }
 | "||"                  { OR }
 | "&&"                  { AND }
 | "not"                 { NOT }
 | "car"                 { CAR }
 | "cdr"                 { CDR }
 | "tree"                { TREE }
 | "children"            { CHILDREN }
 | "value"               { VALUE }
 | "rcons"               { RCONS }
 | "+"                   { ADD }
 | "-"                   { SUB }
 | "*"                   { MUL }
 | "/"                   { DIV }
 | "%"                   { MOD }
 | "="                   { EQ }
 | "<>"                  { NEQ }
 | "!="                  { NEQ }
 | ">"                   { GT }
 | ">="                  { GE }
 | "<"                   { LT }
 | "<="                  { LE }
 | "&"                   { AMP }
 | "|"                   { BAR }
 | "~"                   { NOT }
 | "::"                  { CONS }
 | "cons"                { CONS }
 | "->"                  { ARROW }
 | '{'                   { LCBRACKET }
 | '}'                   { RCBRACKET }
 | "#t"                  { BOOL true }
 | "#f"                  { BOOL false }
 | "true"                { BOOL true }
 | "false"               { BOOL false }
 | '('                   { LPAREN }
 | ')'                   { RPAREN }
 | '['                   { LBRACKET }
 | ']'                   { RBRACKET }
 | ','                   { COMMA }
 | id as text            { ID text }
 | '-'?['0'-'9']+ as num { NUM (int_of_string num) }
 | eof                   { EOF }
 | _                     { syntax_error (Lexing.lexeme lexbuf) }

