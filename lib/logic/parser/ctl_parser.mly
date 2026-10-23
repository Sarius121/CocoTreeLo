%token <string> STRING
%token <string> SMT
%token <int> INT
%token LP RP FORALL EXISTS A E AND OR X U W AX EX G F AG EG AF EF DOT NOT COMMA
%token EOL

/* precedences from low to hight */
%right FORALL EXISTS
%left OR
%left AND
%right A E AX EX AF EF AG EG

%nonassoc U W
%nonassoc X F G

%nonassoc NOT
%right COMMA

/* the entry points */
%start main
%type <Ctl.ctl> main
%%
main:
    ctl_leading_quantifiers EOL                { $1 }
;
ctl_leading_quantifiers:
    // STRING(string)                     { $1 }
    | LP ctl RP      { $2 }
    | FORALL STRING DOT ctl_leading_quantifiers  %prec FORALL    { Ctl.FORALL (true, $2, $4) }
    | EXISTS STRING DOT ctl_leading_quantifiers  %prec EXISTS    { Ctl.EXISTS (true, $2, $4) }
    | A ctl_path                { Ctl.A $2 }
    | E ctl_path                { Ctl.E $2 }
    | AX ctl                { Ctl.A (Ctl.X $2) }
    | EX ctl                { Ctl.E (Ctl.X $2) }
    | AF ctl                { Ctl.A (Ctl.U (Ctl.B (Sat.mk_bool true), $2)) }
    | EF ctl                { Ctl.E (Ctl.U (Ctl.B (Sat.mk_bool true), $2)) }
    | AG ctl                { Ctl.A (Ctl.W ($2, Ctl.B (Sat.mk_bool false))) }
    | EG ctl                { Ctl.E (Ctl.W ($2, Ctl.B (Sat.mk_bool false))) }
    | ctl AND ctl         { Ctl.AND ($1, $3) }
    | ctl OR ctl         { Ctl.OR ($1, $3) }
    | fact              { Ctl.FACT $1 }
    | NOT fact              { Ctl.NOTFACT $2 }
    | NOT STRING        { Ctl.NOTL $2 }
    | STRING             { Ctl.L $1 }
    | SMT               { Ctl.B (Sat.parse_smt $1 true) }
;
ctl:
    // STRING(string)                     { $1 }
    | LP ctl RP      { $2 }
    | FORALL STRING DOT ctl  %prec FORALL    { Ctl.FORALL (false, $2, $4) }
    | EXISTS STRING DOT ctl  %prec EXISTS    { Ctl.EXISTS (false, $2, $4) }
    | A ctl_path                { Ctl.A $2 }
    | E ctl_path                { Ctl.E $2 }
    | AX ctl                { Ctl.A (Ctl.X $2) }
    | EX ctl                { Ctl.E (Ctl.X $2) }
    | AF ctl                { Ctl.A (Ctl.U (Ctl.B (Sat.mk_bool true), $2)) }
    | EF ctl                { Ctl.E (Ctl.U (Ctl.B (Sat.mk_bool true), $2)) }
    | AG ctl                { Ctl.A (Ctl.W ($2, Ctl.B (Sat.mk_bool false))) }
    | EG ctl                { Ctl.E (Ctl.W ($2, Ctl.B (Sat.mk_bool false))) }
    | ctl AND ctl         { Ctl.AND ($1, $3) }
    | ctl OR ctl         { Ctl.OR ($1, $3) }
    | fact              { Ctl.FACT $1 }
    | NOT fact              { Ctl.NOTFACT $2 }
    | NOT STRING        { Ctl.NOTL $2 }
    | STRING             { Ctl.L $1 }
    | SMT               { Ctl.B (Sat.parse_smt $1 true) }
;
ctl_path:
    | LP ctl_path RP {$2}
    | X ctl         { Ctl.X $2 }
    | ctl U ctl         { Ctl.U ($1, $3) }
    | ctl W ctl         { Ctl.W ($1, $3) }
    | G ctl         { Ctl.W ($2, Ctl.B (Sat.mk_bool false)) }
    | F ctl         { Ctl.U (Ctl.B (Sat.mk_bool true), $2) }
;
fact:
    | STRING LP RP     { ($1, []) }
    | STRING LP args RP     { ($1, $3) }
;
args:
    | STRING                  { [Arg_terms.(Int (Var $1))] }
    | INT                     { [Arg_terms.(Int (Const $1))] }
    | args COMMA args         { $1 @ $3 }
;