%token <string> STRING
%token <string> UPPER_STRING
%token <int> INT
%token LP RP LB RB COLON COMMA ARROW ACTION_ARROW_START ACTION_ARROW_END
%token RULE THEORY BEGIN END
%right COMMA        /* lowest precedence */
                    /* highest precedence */
%start main             /* the entry point */
%type <Multiset_rewrite_system.msrs> main
%%
main:
    | THEORY string BEGIN msrs_rules { ($2, $4) }
;
msrs_rules:
    | END                                                  { [] }
    | RULE string COLON multiset ARROW multiset msrs_rules { ($2, $4, $6, [])::$7 }
    | RULE string COLON multiset ACTION_ARROW_START multiset ACTION_ARROW_END multiset msrs_rules { ($2, $4, $8, $6)::$9 }
;
multiset:
    | LB RB                   { [] }
    | LB facts RB             { $2 }
;
facts:
    // | UPPER_STRING LP RP        { [($1, [])] } TODO
    | UPPER_STRING LP args RP        { [($1, $3)] }
    | facts COMMA facts         { $1 @ $3 }
;
args:
    | STRING                  { [Arg_terms.(Int (Var $1))] }
    | INT                   { [Arg_terms.(Int (Const $1))] }
    | args COMMA args         { $1 @ $3 }
;
string:
    | STRING        { $1 }
    | UPPER_STRING  { $1 }
;