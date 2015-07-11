%{
  open Syntax
%}

/* LEXEMES */

%token <Big_int.big_int> INT
%token TRUE FALSE
%token PLUS MINUS TIMES DIV POW
%token ZABS IZR RABS
%token RSQRT RPOWZ
%token RCOS RSIN RTAN RATAN REXP RLN
%token ARROW FORALL EXISTS
%token LPAREN RPAREN MOD1
%token COLON COMMA
%token LEQ LESS EQ NEQ GEQ GTR
%token AND OR IFF NOT
%token REAL ZINT PI
%token <Syntax.name> VAR
%token EOF

/* PRECEDENCE AND ASSOCIATIVITY */

%right FORALL EXISTS
%nonassoc IFF
%right ARROW
%right OR
%right AND
%right NOT
%nonassoc LEQ LESS EQ NEQ
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS UDIV
%right POW
%nonassoc ZABS IZR RABS RPOWZ RSQRT RCOS RSIN RTAN RATAN REXP RLN

/* TOP LEVEL RULE */

%start toplevel
%type <Syntax.stmt list> toplevel

%%

/* GRAMMAR */

toplevel:
| VAR COLON prop EOF { [($1, $3)] }
| vartuple COLON proptuple EOF {
    if List.length $1 = List.length $3 then
      List.map2 (fun a b -> (a, b)) $1 $3
    else
      failwith ("vartuple (before COLON) & proptuple (after COLON)"
		^ " must have same length.")
  }
;

varcomma:
| VAR COMMA VAR { [$1; $3] }
| varcomma COMMA VAR  { $1 @ [$3] }
;

vartuple:
| LPAREN varcomma RPAREN { $2 }
;

proptuple:
| prop TIMES prop { [$1; $3] }
| proptuple TIMES prop { $1 @ [$3] }
;

prop:
| TRUE { Ptrue }
| FALSE { Pfalse }
/* (FIXME)
| zint LEQ zint { Zle ($1, $3) }
| zint LESS zint { Zlt ($1, $3) }
| zint EQ zint { Zeq ($1, $3) }
| zint NEQ zint { Pnot (Zeq ($1, $3)) }
*/
| real LEQ real { Rle ($1, $3) }
| real LESS real { Rlt ($1, $3) }
| real EQ real { Req ($1, $3) }
| real NEQ real { Pnot (Req ($1, $3)) }
| real GEQ real { Rle ($3, $1) }
| real GTR real { Rlt ($3, $1) }

| real LEQ real LEQ real { Pand ((Rle ($1, $3)), (Rle ($3, $5))) }
| real LEQ real LESS real { Pand ((Rle ($1, $3)), (Rlt ($3, $5))) }
| real LESS real LESS real { Pand ((Rlt ($1, $3)), (Rlt ($3, $5))) }
| real LESS real LEQ real { Pand ((Rlt ($1, $3)), (Rle ($3, $5))) }

| NOT prop { Pnot $2 }
| prop AND prop { Pand ($1, $3) }
| prop OR prop { Por ($1, $3) }
| prop ARROW prop { Parrow ($1, $3) }
| prop IFF prop { Piff ($1, $3) }
| EXISTS ctxt COMMA prop %prec EXISTS
    { List.fold_right (fun a b -> Pexists (fst a, snd a, b)) $2 $4 }
| FORALL ctxt COMMA prop %prec FORALL
    { List.fold_right (fun a b -> Pforall (fst a, snd a, b)) $2 $4 }
| LPAREN prop RPAREN { $2 }
| LPAREN prop RPAREN MOD1 typ { $2 }
;

vars:
| VAR { [$1] }
| VAR vars { $1 :: $2 }
;

ctxt:
| vars COLON typ { List.map (fun v -> (v, $3)) $1 }
| LPAREN vars COLON typ RPAREN { List.map (fun v -> (v, $4)) $2 }
| LPAREN vars COLON typ RPAREN LPAREN ctxt RPAREN
    { List.append (List.map (fun v -> (v, $4)) $2) $7 }
;

/* (THE ORDER MATTERS!) */
zint:
| INT { Zint $1 }
| INT MOD1 ZINT { Zint $1 }
| VAR { Zvar $1 }
| zint PLUS zint { Zbin (Zadd, $1, $3) }
| zint MINUS zint { Zbin (Zsub, $1, $3) }
| MINUS zint %prec UMINUS { Zopp $2 }
| zint TIMES zint { Zbin (Zmul, $1, $3) }
| ZABS zint { Zabs $2 }
| zint POW zint { Zbin (Zpow, $1, $3) }
| LPAREN zint RPAREN { $2 }
| LPAREN zint RPAREN MOD1 typ { $2 }
;

real:
/* (OLD CODE)
| zint %prec POW { IZR $1 }
*/
| IZR zint { IZR $2 }
| INT { IZR (Zint $1) }
| INT MOD1 REAL { IZR (Zint $1) }
| PI { Rcst Pi }
| VAR { Rvar $1 }
| real PLUS real { Rbin (Radd, $1, $3) }
| real MINUS real { Rbin (Rsub, $1, $3) }
| MINUS real %prec UMINUS { Ropp $2 }
| real TIMES real { Rbin (Rmul, $1, $3) }
| real DIV real { Rbin (Rdiv, $1, $3) }
| DIV real %prec UDIV { Rinv $2 }
| RABS real { Rabs $2 }
| real POW zint { Rpow ($1, $3) }
| RPOWZ real zint { Rpow ($2, $3) }
| RSQRT real { Rfun (Rsqrt, $2) }
| RCOS real { Rfun (Rcos, $2) }
| RSIN real { Rfun (Rsin, $2) }
| RTAN real { Rfun (Rtan, $2) }
| RATAN real { Rfun (Ratan, $2) }
| REXP real { Rfun (Rexp, $2) }
| RLN  real { Rfun (Rln, $2) }
| LPAREN real RPAREN { $2 }
| LPAREN real RPAREN MOD1 typ { $2 }
;

typ:
/* | VAR { typ_of_string $1 } */
| REAL { Treal }
| ZINT { Tzint }
;

/* (FIXME)
scope:
| VAR { scope_of_string $1 }
;
*/

%%
