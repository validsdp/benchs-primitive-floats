{
  open Parser
  open Lexing

  let incr_linenum lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

let var = ['_' 'a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9']*

rule token = parse
(* '#' [^'\n']* '\n' { incr_linenum lexbuf; token lexbuf } *)
| '\n' { incr_linenum lexbuf; token lexbuf }
| [' ' '\t'] { token lexbuf }
| ['0'-'9']+ { INT ( Big_int.big_int_of_string (lexeme lexbuf)) }
| "True" { TRUE }
| "False" { FALSE }
| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| '/' { DIV }
| '^' { POW }
| "PI" { PI }
| "powerRZ" { RPOWZ }
| "Z.abs" { ZABS }
| "IZR" { IZR }
| "Rabs" { RABS }
| "sqrt" { RSQRT }
| "cos" { RCOS }
| "sin" { RSIN }
| "tan" { RTAN }
| "atan" { RATAN }
| "exp" { REXP }
| "ln" { RLN }
| "->" { ARROW }
| "forall" { FORALL }
| "exists" { EXISTS }
| '(' { LPAREN }
| ')' { RPAREN }
| ':' { COLON }
| "<=" { LEQ }
| '<' { LESS }
| ">=" { GEQ }
| '>' { GTR }
| '=' { EQ }
| "<>" { NEQ }
| ',' { COMMA }
| "/\\" { AND }
| "\\/" { OR }
| "<->" { IFF }
| "~" { NOT }
| "%" { MOD1 }
| "R" { REAL }
| "Z" { ZINT }
| var { VAR (lexeme lexbuf) }
| eof { EOF }

{
}
