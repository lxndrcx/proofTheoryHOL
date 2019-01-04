(* Equivalence of Sequent Calculus and Natural Deduction
   Starting with intuitionistic propositional case
 *)

open HolKernel boolLib Parse bossLib;
open bagTheory;
open pred_setTheory;

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


(** Natural Deduction for minimal logic **)
(* Nm is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* D, D1, D2, D3 are used to represent the set of open/not-discharged assumptions in the deduction *)
(* In Troelstra & Schwichtenberg the deductions are trees, but to represent them this was here *)
(*     would have complicated things a lot, and they use this style in 2.1.8 anyway *)

val (Nm_rules, Nm_induct, Nm_cases) = Hol_reln `
(! (A :'a formula) (D :'a formula set). A IN D ==> Nm D A) (* Base case: A formula 'A' is deducible from any set 'D' containing 'A' *)
/\ (!A B D1 D2. (Nm D1 A) /\ (Nm D2 B) ==> (Nm (D1 UNION D2) (A And B))) (* And Introduction *)
/\ (!A B D. (Nm D (A And B)) ==> Nm D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Nm D (A And B)) ==> Nm D B) (* And Elim Right Conjunct *)
/\ (!A B D1 D2. (Nm D1 B) /\ (D2 = (D1 DIFF {A})) ==> Nm D2 (A Imp B)) (* Imp Intro: T&S say A need not actually be in D1 *)
/\ (!A B D1 D2. (Nm D1 (A Imp B)) /\ (Nm D2 A) ==> Nm (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Nm D A ==> Nm D (A Or B)) (* Or Intro right *)
/\ (!A B D. Nm D B ==> Nm D (A Or B)) (* Or Intro left *)
/\ (!A B C D1 D2 D3 D4. (Nm D1 (A Or B)) /\
(Nm D2 C) /\ (Nm D3 C) /\     (* T&S say A and B need not actually be in D2 and D3 respectively *)
(D4 = ((D1 UNION D2 UNION D3) DIFF {A;B})) ==> Nm D4 C)`;                         (* Or Elim *)

(** Natural Deduction for intuitionistic logic **)
(* Ni is the 'deduciblility' relation for this system *)
val (Ni_rules, Ni_induct, Ni_cases) = Hol_reln `
(! (A :'a formula) (D :'a formula set). A IN D ==> Ni D A) (* Base case *)
/\ (!A B D1 D2. (Ni D1 A) /\ (Ni D2 B) ==> (Ni (D1 UNION D2) (A And B))) (* And Introduction *)
/\ (!A B D. (Ni D (A And B)) ==> Ni D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Ni D (A And B)) ==> Ni D B) (* And Elim Right Conjunct *)
/\ (!A B D1 D2. (Ni D1 B) /\ (D2 = (D1 DIFF {A})) ==> Ni D2 (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Ni D1 (A Imp B)) /\ (Ni D2 A) ==> Ni (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Ni D A ==> Ni D (A Or B)) (* Or Intro right *)
/\ (!A B D. Ni D B ==> Ni D (A Or B)) (* Or Intro left *)
/\ (!A B C D1 D2 D3 D4. (Ni D1 (A Or B)) /\
(Ni D2 C) /\ (Ni D3 C) /\
(D4 = ((D1 UNION D2 UNION D3) DIFF {A;B})) ==> Ni D4 C) (* Or Elim *)
/\ (!A D. (Ni D Bot) ==> (Ni D A))`; (* Intuitionistic Absurdity Rule *)

(** Natural Deduction for classical logic **)
(* Nc is the 'deduciblility' relation for this system *)
val (Nc_rules, Nc_induct, Nc_cases) = Hol_reln `
(! (A :'a formula) (D :'a formula set). A IN D ==> Nc D A) (* Base case *)
/\ (!A B D1 D2. (Nc D1 A) /\ (Nc D2 B) ==> (Nc (D1 UNION D2) (A And B))) (* And Introduction *)
/\ (!A B D. (Nc D (A And B)) ==> Nc D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Nc D (A And B)) ==> Nc D B) (* And Elim Right Conjunct *)
/\ (!A B D1 D2. (Nc D1 B) /\ (D2 = (D1 DIFF {A})) ==> Nc D2 (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Nc D1 (A Imp B)) /\ (Nc D2 A) ==> Nc (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Nc D A ==> Nc D (A Or B)) (* Or Intro right *)
/\ (!A B D. Nc D B ==> Nc D (A Or B)) (* Or Intro left *)
/\ (!A B C D1 D2 D3 D4. (Nc D1 (A Or B)) /\
(Nc D2 C) /\ (Nc D3 C) /\
(D4 = ((D1 UNION D2 UNION D3) DIFF {A;B})) ==> Nc D4 C) (* Or Elim *)
/\ (!A D. (Nc D Bot) ==> (Nc D A)) (* Intuitionistic Absurdity Rule *)
/\ (!A D1 D2. (Nc D1 (Not A)) /\ (D2 = (D1 DIFF {Not A})) ==> Nc D2 A) (* Classical absurdidty rule *)
`;

val NmThm = Define `NmThm A = Nm EMPTY A`;
val NiThm = Define `NiThm A = Ni EMPTY A`;
val NcThm = Define `NcThm A = Nc EMPTY A`;

(* Example deductions *)
val Nm_example = Q.prove(`NmThm (A Imp (B Imp A))`,
`Nm {A;B} A` by rw[Nm_rules] >>
`Nm ({A;B} DIFF {B}) (B Imp A)` by metis_tac[Nm_rules] >>
`Nm (({A;B} DIFF {B}) DIFF {A}) (A Imp (B Imp A))` by metis_tac[Nm_rules] >>
`(({A;B} DIFF {B}) DIFF {A}) = EMPTY` by (rw[]) >>
`Nm EMPTY (A Imp (B Imp A))` by metis_tac[] >>
 rw[NmThm]);

val Ni_example = Q.prove(`NiThm (Bot Imp A)`,
`Ni {Bot} Bot` by rw[Ni_rules] >>
`Ni {Bot} A` by rw[Ni_rules] >>
`{} = ({Bot} DIFF {Bot})` by rw[DIFF_DEF] >>
`Ni EMPTY (Bot Imp A)` by metis_tac[Ni_rules] >>
rw[NiThm]);

(* val Nm_NotNotElim = Q.prove(`NmThm (A BiImp (Not (Not A)))`, *)
(* rw[BiImp_def,NmThm,Not_def] >> *)
(* `Nm {A Imp Bot} (A Imp Bot)` by rw[Nm_rules] >> *)
(* `Nm {A} A` by rw[Nm_rules] >> *)
(* `{A Imp Bot;A} = ({A Imp Bot} UNION {A})` by simp[Once INSERT_DEF, Once UNION_DEF] >> *)
(* `Nm ({A Imp Bot} UNION {A}) Bot` by metis_tac[Nm_rules] >> *)
(* (* `Nm ({A; A Imp Bot}) Bot` by metis_tac[Nm_rules,INSERT_DEF,UNION_DEF]  why is this so hard to prove? *) *)
(* `Nm (({A Imp Bot} UNION {A}) DIFF {A Imp Bot}) ((A Imp Bot) Imp Bot)` by metis_tac[Nm_rules] >> *)
(* `Nm ((({A Imp Bot} UNION {A}) DIFF {A Imp Bot}) DIFF {A}) (A Imp ((A Imp Bot) Imp Bot))` by metis_tac[Nm_rules] *)
(* (* Stuck *) *)
(* ); *)

(* Need to make all the D's SING or EMPTY *)
val (Gi_rules, Gi_induct, Gi_cases) = Hol_reln `
(!A:'a formula. Gc {|A|} {|A|})            (* Ax *)
/\ (Gc {|Bot|} {||})            (* LBot *)
/\ (!A S D. Gc S D ==> Gc (BAG_INSERT A S) D) (* Left Weakening *)
/\ (!A S D. Gc S D ==> Gc S (BAG_INSERT A D)) (* Right Weakening *)
/\ (!A S D. (Gc S D) /\ (S A >= 2)
   ==> Gc (S - {|A|}) D) (* Left Contraction *)
/\ (!A S D. (Gc S D) /\ (D A >= 2)
   ==> Gc S (D - {|A|})) (* Right Contraction *)
/\ (!A B SD. (Gc (BAG_INSERT A S) D)
   ==> (Gc (BAG_INSERT (A And B) S) D)) (* Left And 1 *)
/\ (!A B SD. (Gc (BAG_INSERT B S) D)
   ==> (Gc (BAG_INSERT (A And B) S) D)) (* Left And 2 *)
/\ (!A B S. (Gc S {|A|}) /\ (Gc S {|B|})
   ==> (Gc S {|A And B|})) (* Right And *)
/\ (!A B SD. (Gc (BAG_INSERT A S) D /\ (Gc (BAG_INSERT B S) D
   ==> (Gc (BAG_INSERT (A Or B) S) D) (* Left Or *)
/\ (!A B S. (Gc S {|A|})
   ==> (Gc S {|A Or B|})) (* Right Or 1 *)
/\ (!A B S. (Gc S {|B|})
   ==> (Gc S {|A Or B|})) (* Right Or 2 *)
/\ (!A B SD. (Gc S {|A|} /\ (Gc (BAG_INSERT B S) D)
   ==> (Gc (BAG_INSERT (A Imp B) S) D) (* Left Imp *)
/\ (!A B S. (Gc (BAG_INSERT A S) {|B|})
   ==> (Gc S {|A Imp B|})) (* Right Imp *)
`;

val (Gc_rules, Gc_induct, Gc_cases) = Hol_reln `
(!A:'a formula. Gc {|A|} {|A|})            (* Ax *)
/\ (Gc {|Bot|} {||})            (* LBot *)
/\ (!A S D. Gc S D ==> Gc (BAG_INSERT A S) D) (* Left Weakening *)
/\ (!A S D. Gc S D ==> Gc S (BAG_INSERT A D)) (* Right Weakening *)
/\ (!A S D. (Gc S D) /\ (S A >= 2)
   ==> Gc (S - {|A|}) D) (* Left Contraction *)
/\ (!A S D. (Gc S D) /\ (D A >= 2)
   ==> Gc S (D - {|A|})) (* Right Contraction *)
/\ (!A B S D. (Gc (BAG_INSERT A S) D)
   ==> (Gc (BAG_INSERT (A And B) S) D)) (* Left And 1 *)
/\ (!A B S D. (Gc (BAG_INSERT B S) D)
   ==> (Gc (BAG_INSERT (A And B) S) D)) (* Left And 2 *)
/\ (!A B S D. (Gc S (BAG_INSERT A D)) /\ (Gc S (BAG_INSERT B D))
   ==> (Gc S (BAG_INSERT (A And B) D))) (* Right And *)
/\ (!A B S D. (Gc (BAG_INSERT A S) D) /\ (Gc (BAG_INSERT B S) D)
   ==> (Gc (BAG_INSERT (A Or B) S) D)) (* Left Or *)
/\ (!A B S D. (Gc S (BAG_INSERT A D))
   ==> (Gc S (BAG_INSERT (A Or B) D))) (* Right Or 1 *)
/\ (!A B S D. (Gc S (BAG_INSERT B D))
   ==> (Gc S (BAG_INSERT (A Or B) D))) (* Right Or 2 *)
/\ (!A B S D. (Gc S (BAG_INSERT A D)) /\ (Gc (BAG_INSERT B S) D)
   ==> (Gc (BAG_INSERT (A Imp B) S) D)) (* Left Imp *)
/\ (!A B S D. (Gc (BAG_INSERT A S) (BAG_INSERT B D))
   ==> (Gc S (BAG_INSERT (A Imp B) D))) (* Right Imp *)
`;
