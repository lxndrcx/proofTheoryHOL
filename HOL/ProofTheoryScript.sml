(* Equivalence of Sequent Calculus and Natural Deduction
   Starting with intuitionistic propositional case
 *)

open HolKernel boolLib Parse bossLib;
open pred_setTheory bagTheory;

val _ = new_theory "ProofTheory";

val _ = Datatype `formula =
Var 'a
| Or formula formula
| And formula formula
| Imp formula formula
| Bot`;

val _ = set_fixity "Imp" (Infixr 460);
val _ = set_fixity "BiImp" (Infix (NONASSOC, 450) );
val _ = set_fixity "And" (Infixr 490);
val _ = set_fixity "Or" (Infixr 490);
val _ = set_fixity "Not" (Prefix 510);

val Not_def = Define `Not f = f Imp Bot`;
val BiImp_def = Define `f BiImp f' = (f Imp f') And (f' Imp f)`;
val Top_def = Define `Top = Bot Imp Bot`;


(** Natural Deduction for intuitionistic logic **)
(* NDi is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* D, D1, D2, D3 are used to represent the set of open/not-discharged assumptions in the deduction *)
(* In Troelstra & Schwichtenberg the deductions are trees, but to represent them this was here *)
(*     would have complicated things a lot, and they use this style in 2.1.8 anyway *)

val (NDi_rules, NDi_induct, NDi_cases) = Hol_reln `
(! (A :'a formula) (D :'a formula set). A IN D ==> NDi D A) (* Base case: A formula 'A' is deducible from any set 'D' containing 'A' *)
/\ (!A D. (NDi D Bot) ==> (NDi D A)) (* Intuitionistic Absurdity Rule *)
/\ (!A B D1 D2. (NDi D1 A) /\ (NDi D2 B) ==> (NDi (D1 UNION D2) (A And B))) (* And Introduction *)
/\ (!A B D. (NDi D (A And B)) ==> NDi D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (NDi D (A And B)) ==> NDi D B) (* And Elim Right Conjunct *)
/\ (!A B D1 D2. (NDi D1 B) /\ (D2 = (D1 DIFF {A})) ==> NDi D2 (A Imp B)) (* Imp Intro: T&S say A need not actually be in D1 *)
/\ (!A B D1 D2. (NDi D1 (A Imp B)) /\ (NDi D2 (A)) ==> NDi (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. NDi D A ==> NDi D (A Or B)) (* Or Intro right *)
/\ (!A B D. NDi D B ==> NDi D (A Or B)) (* Or Intro left *)
/\ (!A B C D1 D2 D3 D4. (NDi D1 (A Or B)) /\
(NDi D2 C) /\ (NDi D3 C) /\     (* T&S say A and B need not actually be in D2 and D3 respectively *)
(D4 = ((D1 UNION D2 UNION D3) DIFF {A;B}))
==> NDi D4 C)`;                         (* Or Elim *)

val NDThm = Define `NDThm A = NDi EMPTY A`;

(* Example deductions *)
val NDi_example1 = Q.prove(`NDThm (A Imp (B Imp A))`,
`NDi {A;B} A` by rw[NDi_rules] >>
`NDi ({A;B} DIFF {B}) (B Imp A)` by metis_tac[NDi_rules] >>
`NDi (({A;B} DIFF {B}) DIFF {A}) (A Imp (B Imp A))` by metis_tac[NDi_rules] >>
`(({A;B} DIFF {B}) DIFF {A}) = EMPTY` by (rw[]) >>
`NDi EMPTY (A Imp (B Imp A))` by metis_tac[] >>
 rw[NDThm]);

val NDi_example2 = Q.prove(`NDThm (Bot Imp A)`,
`NDi {Bot} Bot` by rw[NDi_rules] >>
`NDi {Bot} A` by rw[NDi_rules] >>
`{} = ({Bot} DIFF {Bot})` by rw[DIFF_DEF] >>
`NDi EMPTY (Bot Imp A)` by metis_tac[NDi_rules] >>
rw[NDThm]);

val NDi_example3 = Q.prove(`NDThm (A BiImp (Not (Not A)))`,

