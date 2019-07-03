/*******************************************************************
 *  This is part of SymbolicKAT, it is distributed under the       *
 *  terms of the GNU Lesser General Public License version 3       *
 *           (see file LICENSE for more details)                   *
 *                                                                 *
 *  Copyright 2014: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *
 *******************************************************************/

%token <char> VAR
%token <char> PRD
%token ANY

%token LPAR RPAR ONE ZER PLS STR NEG EOF SEP LE EQ GT
%left PLS

%type <Kat.expr> expr
%type <Hypotheses.t> hyps
%start expr
%start hyps

%%

expr: 
| expr0 EOF { $1 }

expr2:
| ONE { Kat.Tst Kat.Top }
| ZER { Kat.Tst Kat.Bot }
| PRD { Kat.Tst (Kat.Prd $1) }
| NEG test2 { Kat.Tst (Kat.Neg $2) }
| VAR { Kat.Var $1 }
| expr2 STR { Kat.Str $1 }
| LPAR expr0 RPAR { $2 }

expr1:
| expr2 { $1 }
| expr2 expr1 { Kat.Dot($1,$2) }

expr0:
| expr1 { $1 }
| expr0 PLS expr0 { Kat.Pls($1,$3) }

test2:
| ONE { Kat.Top }
| ZER { Kat.Bot }
| PRD { Kat.Prd $1 }
| NEG test2 { Kat.Neg $2 }
| LPAR test0 RPAR { $2 }

test1:
| test2 { $1 }
| test2 test1 { Kat.Cnj($1,$2)  }

test0:
| test1 { $1 }
| test0 PLS test0 { Kat.Dsj($1,$3) }

hyp:
| expr0 LE expr0 { $1,`Le,$3 }
| expr0 GT expr0 { $3,`Le,$1 }
| expr0 EQ expr0 { $1,`Eq,$3 }

hyps:
| EOF { [] }
| hyp shyps EOF { $1::$2 }
    
shyps:
| { [] }
| SEP hyp shyps { $2::$3 }
