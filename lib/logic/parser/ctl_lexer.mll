{
open Ctl_parser
exception Eof
}
rule token = parse
    [' ' '\t' ]     { token lexbuf }     (* skip blanks *)
    | '\n' { EOL }
    | "\u{2200}" | "FORALL"            { FORALL }
    | "\u{2203}" | "EXISTS"            { EXISTS }
    | 'A'                 { A }
    | 'E'               { E }
    | 'U'            { U }
    | 'W'            { W }
    | 'X'            { X }
    | 'G'            { G }
    | 'F'            { F }
    | "AX"            { AX }
    | "EX"            { EX }
    | "AF"            { AF }
    | "EF"            { EF }
    | "AG"            { AG }
    | "EG"            { EG }
    | "&&"            { AND }
    | "||"            { OR }
    | '('            { LP }
    | ')'            { RP }
    | '.'            { DOT }
    | '!'           { NOT }
    | ','               { COMMA }
    | eof            { raise Eof }
    | ['A'-'Z''a'-'z']['A'-'Z''a'-'z''0'-'9']* as str { STRING(str) }
    | '-'?['0'-'9']* as n {INT(int_of_string(n))}
    | '"'([^'"']* as smt_expr)'"' { SMT(smt_expr) }