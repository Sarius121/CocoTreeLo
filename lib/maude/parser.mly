%{
  open Logic
%}
%token <string> STRING
%token <string> RULE
%token <int> INT
%token <string> TYPE_MS
%token <string> EMPTY_MS
%token LP RP
%token TYPE_INT
%token STATE_START STATE_END COLON SEMICOLON ARROW COMMA
%token SOLUTION_START RULE_VARIABLE_BINDINGS SUBJECT_VARIABLE_BINDINGS ACCUMULATED_SUBSTITUTION VARIANT_UNIFIER
%token END
%right SEMICOLON
%right COMMA
%nonassoc COLON
%start main
%type <((string * Logic.Multiset_rewrite_system.term) list * Logic.Substitution.t * Logic.Substitution.t * string) list> main
%%
main:
    | solution END                 { [$1] }
    | solution main                { $1::$2 }
;
solution:
    | SOLUTION_START RULE
        RULE_VARIABLE_BINDINGS substitution
        SUBJECT_VARIABLE_BINDINGS
        state
        ACCUMULATED_SUBSTITUTION substitution
        VARIANT_UNIFIER                         { ($6, $8, $4, $2) }
;
state:
    | LP STATE_START structured_state STATE_END RP              { $3 }
;
structured_state:
    | ms_value SEMICOLON structured_state               { $1::$3 }
    | ms_value                                          { [$1] }
;
substitution:
    | substitution2         { $1 }
    |                       { Substitution.empty}
substitution2:
    | int_var ARROW int_value        { Substitution.add_arg (Substitution.empty) (fst $1) $3 }
    | ms_var ARROW ms_value        { Substitution.add_ms (Substitution.empty) (fst $1) (snd $3) }
    | int_var ARROW int_value substitution2        { Substitution.add_arg ($4) (fst $1) $3 }
    | ms_var ARROW ms_value substitution2       { Substitution.add_ms ($4) (fst $1) (snd $3) }
ms_value:
    | EMPTY_MS              { ($1, Multiset_rewrite_system.Const []) }
    | ms_value_facts              { (fst (List.hd $1), Multiset_rewrite_system.Const $1) }
    | LP ms_var COMMA ms_value_facts RP     { (snd $2, Multiset_rewrite_system.Union (Multiset_rewrite_system.Var (fst $2), Multiset_rewrite_system.Const $4)) }
    | ms_var                    { (snd $1, Multiset_rewrite_system.Var (fst $1)) }
;
ms_value_facts:
    | LP LP fact RP COMMA ms_value_facts RP   { $3::$6 }
    | LP fact RP                        { [$2] }
;
fact:
    | STRING args           { ($1, $2) }
;
args:
    | int_value                   { [$1] }
    | int_value args              { $1::$2 }
;
int_value:
    | INT                         { Arg_terms.(Int (Const $1)) }
    | int_var                         { Arg_terms.(Int (Var (fst $1))) }
;
int_var:
    | STRING COLON TYPE_INT    { ($1, "Int") }
;
ms_var:
    | STRING COLON TYPE_MS    { 
        let len = String.length $1 in
        if String.get $1 (len - 1) = 'M' then
            (String.sub $1 0 (len - 1) ^ "*", $3)
        else ($1, $3) }
;
