{
  open Parser

  exception SyntaxError of string
  let syntax_error char = raise (SyntaxError ("Unexpected character: " ^ char))
}

let white = [' ' '\t' '\n' '\r']+
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* 
let operator = "+" | "-" | "*" | "/" | "%" | "=" | "!=" | ">" | ">=" | "<" | 
               "<=" | "&" | "|" | "~" | "cons" | "car" | "cdr" | "if" | "foldl"

rule token = parse
       | white             { token lexbuf } (* Eat whitespace. *)
       | "num"             { NUM_T }
       | "bool"            { BOOL_T }
       | "unit"            { UNIT_T }
       | "let"             { LET }
       | "define"          { DEF }
       | "lambda"          { LAMBDA }
       | "nil"             { NIL }
       | "->"              { ARROW }
       | ':'               { COLON }
       | operator as text  { OP text }
       | id as text        { ID text }
       | ['0'-'9']+ as num { NUM (int_of_string num) }
       | "#t"              { BOOL true }
       | "#f"              { BOOL false }
       | '('               { LPAREN }
       | ')'               { RPAREN }
       | '['               { LBRACKET }
       | ']'               { RBRACKET }
       | eof               { EOF }
       | _                 { syntax_error (Lexing.lexeme lexbuf) }
