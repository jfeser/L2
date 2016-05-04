{
  open Parser

  exception SyntaxError of string
  let syntax_error char = raise (SyntaxError ("Unexpected character: " ^ char))
}

let white = [' ' '\t' '\n' '\r']+
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
 | white                 { token lexbuf } (* Eat whitespace. *)
 | "(*"                  { comment lexbuf }
 | "let"                 { LET }
 | "in"                  { IN }
 | "if"                  { IF }
 | "then"                { THEN }
 | "else"                { ELSE }
 | "fun"                 { FUN }
 | "lambda"              { LAMBDA }
 | "forall"              { FORALL }
 | "+"                   { ADD }
 | "-"                   { SUB }
 | "*"                   { MUL }
 | "/"                   { DIV }
 | "%"                   { MOD }
 | "="                   { EQ }
 | "!="                  { NEQ }
 | ">"                   { GT }
 | ">="                  { GE }
 | "<"                   { LT }
 | "<="                  { LE }
 | "&"                   { AND }
 | "|"                   { OR }
 | "~"                   { NOT }
 | "::"                  { CONS }
 | ";"                   { SEMI }
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
and comment = parse
 | "*)"                  { token lexbuf }
 | _                     { comment lexbuf }

