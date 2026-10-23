{
open Parser
exception Eof
}
rule token = parse
    [' ' '\t' '\n']     { token lexbuf }     (* skip blanks *)
    | eof            { raise Eof }
    | ':'   { COLON }
    | "-->"     { ARROW }
    | '<'       { STATE_START }
    | '>'       { STATE_END }
    | ';'       { SEMICOLON }
    | ','       { COMMA }
    | '('       { LP }
    | ')'       { RP }
    | '*'? "********** narrowing step" { SOLUTION_START }
    | "Int"                         { TYPE_INT }
    | (['A'-'Z']['A'-'Z''a'-'z''0'-'9''_']* as fact_name) "Fact" { TYPE_MS(fact_name) }
    | "no"(['A'-'Z']['A'-'Z''a'-'z''0'-'9''_']* as fact_name)   { EMPTY_MS(fact_name) }
    | "Rule variable bindings:"     { RULE_VARIABLE_BINDINGS }
    | "Subject variable bindings:" [^'*']* "state:"  { SUBJECT_VARIABLE_BINDINGS }
    | "accumulated substitution:"  { ACCUMULATED_SUBSTITUTION }
    | "variant unifier:" [^'*']* ("No more solutions." | '*')      { VARIANT_UNIFIER }
    | "rewrites: " ['0'-'9']+ "\nBye."          { END }
    | "rl [" (['A'-'Z''a'-'z''_']['A'-'Z''a'-'z''0'-'9''_']* as rule_name) "]" [^'.']* '.'     { RULE(rule_name) }
    | ['a'-'z''A'-'Z''@']['A'-'Z''a'-'z''0'-'9''_']* as str { STRING(str) }
    | '-'?['0'-'9']+ as n {INT(int_of_string(n))}