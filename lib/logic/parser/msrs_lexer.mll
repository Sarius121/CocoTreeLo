{
open Msrs_parser
exception Eof
}
rule token = parse
    [' ' '\t' '\n' ]     { token lexbuf }     (* skip blanks *)
    | '['            { LB }
    | ']'            { RB }
    | '('            { LP }
    | ')'            { RP }
    | ','            { COMMA }
    | "-->"           { ARROW }
    | "--"           { ACTION_ARROW_START }
    | "->"           { ACTION_ARROW_END }
    | ':'            { COLON }
    | eof            { raise Eof }
    | "rule"            { RULE }
    | "theory"            { THEORY }
    | "begin"            { BEGIN }
    | "end"            { END }
    | ['A'-'Z']['A'-'Z''a'-'z''0'-'9''_']* as str { UPPER_STRING(str) }
    | ['a'-'z''_']['A'-'Z''a'-'z''0'-'9''_']* as str { STRING(str) }
    | '-'?['0'-'9']+ as n {INT(int_of_string(n))}
