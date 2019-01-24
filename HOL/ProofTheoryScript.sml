
(* ========================================================================== *)
(* Equivalence of Sequent Calculus and Natural Deduction                      *)
(* Working from Troelstra and Schwichtenburg - Basic Proof Theory 2nd Edition *)
(*                                                                            *)
(* ========================================================================== *)

open HolKernel boolLib Parse bossLib;
open bagLib bagSimps bagTheory;
open pred_setTheory pred_setLib;
open arithmeticTheory;

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
(* D, D1, D2, D3 are used to represent the set of open assumptions *)
(* I'm representing the deductions simply with unlabeled sets of
   open assumptions, as in T&S 2.1.8-2.1.9 (p.41--44) *)

val (Nm_rules, Nm_ind, Nm_cases) = Hol_reln `
(! (A :'a formula). Nm {A} A) (* Base case *)
/\ (!A B D1 D2. (Nm D1 A) /\ (Nm D2 B)
   ==> (Nm (D1 UNION D2) (A And B))) (* And Intro *)
/\ (!A B D. (Nm D (A And B)) ==> Nm D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Nm D (A And B)) ==> Nm D B) (* And Elim Right Conjunct *)
/\ (!A B D. (Nm (A INSERT D) B) ==> Nm D (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Nm D1 (A Imp B)) /\ (Nm D2 A)
   ==> Nm (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Nm D A ==> Nm D (A Or B)) (* Or Intro right *)
/\ (!A B D. Nm D B ==> Nm D (A Or B)) (* Or Intro left *)
/\ (!A B C D. (Nm D (A Or B)) /\
(Nm (A INSERT D) C) /\ (Nm (B INSERT D) C) ==> Nm D C)`; (* Or Elim *)

val [Nm_ax, Nm_andi, Nm_andel, Nm_ander,
     Nm_impi, Nm_impe, Nm_orir, Nm_oril, Nm_ore] = CONJUNCTS Nm_rules;

(* (** Natural Deduction for intuitionistic logic **) *)
(* (* Ni is the 'deduciblility' relation for this system *) *)
(* val (Ni_rules, Ni_ind, Ni_cases) = Hol_reln ` *)
(* (! (A :'a formula). Ni {A} A) (* Base case *) *)
(* /\ (!A B D1 D2. (Ni D1 A) /\ (Ni D2 B) *)
(*    ==> (Ni (D1 UNION D2) (A And B))) (* And Intro *) *)
(* /\ (!A B D. (Ni D (A And B)) ==> Ni D A) (* And Elimination Left Conjunct *) *)
(* /\ (!A B D. (Ni D (A And B)) ==> Ni D B) (* And Elim Right Conjunct *) *)
(* /\ (!A B D. (Ni D B) ==> Ni (D DIFF {A}) (A Imp B)) (* Imp Intro *) *)
(* /\ (!A B D1 D2. (Ni D1 (A Imp B)) /\ (Ni D2 A) *)
(*    ==> Ni (D1 UNION D2) B) (* Imp Elim *) *)
(* /\ (!A B D. Ni D A ==> Ni D (A Or B)) (* Or Intro right *) *)
(* /\ (!A B D. Ni D B ==> Ni D (A Or B)) (* Or Intro left *) *)
(* /\ (!A B C D1 D2 D3. (Ni D1 (A Or B)) /\ *)
(* (Ni D2 C) /\ (Ni D3 C) ==> Ni ((D1 UNION D2 UNION D3) DIFF {A;B}) C) (* Or Elim *) *)
(* /\ (!A D. (Ni D Bot) ==> (Ni D A))`; (* Intuitionistic Absurdity Rule *) *)

(* val [Ni_ax, Ni_andi, Ni_andel, Ni_ander, Ni_impi, Ni_impe, *)
(*      Ni_orir, Ni_oril, Ni_ore, Ni_absurd] = CONJUNCTS Ni_rules; *)

(* (** Natural Deduction for classical logic **) *)
(* (* Nc is the 'deduciblility' relation for this system *) *)
(* val (Nc_rules, Nc_ind, Nc_cases) = Hol_reln ` *)
(* (! (A :'a formula). Nc {A} A) (* Base case *) *)
(* /\ (!A B D1 D2. (Nc D1 A) /\ (Nc D2 B) *)
(*    ==> (Nc (D1 UNION D2) (A And B))) (* And Intro *) *)
(* /\ (!A B D. (Nc D (A And B)) ==> Nc D A) (* And Elimination Left Conjunct *) *)
(* /\ (!A B D. (Nc D (A And B)) ==> Nc D B) (* And Elim Right Conjunct *) *)
(* /\ (!A B D. (Nc D B) ==> Nc (D DIFF {A}) (A Imp B)) (* Imp Intro *) *)
(* /\ (!A B D1 D2. (Nc D1 (A Imp B)) /\ (Nc D2 A) *)
(*    ==> Nc (D1 UNION D2) B) (* Imp Elim *) *)
(* /\ (!A B D. Nc D A ==> Nc D (A Or B)) (* Or Intro right *) *)
(* /\ (!A B D. Nc D B ==> Nc D (A Or B)) (* Or Intro left *) *)
(* /\ (!A B C D1 D2 D3. (Nc D1 (A Or B)) /\ *)
(* (Nc D2 C) /\ (Nc D3 C) ==> Nc ((D1 UNION D2 UNION D3) DIFF {A;B}) C) (* Or Elim *) *)
(* /\ (!A D. (Nc D (Bot)) *)
(*    ==> Nc (D DIFF {Not A}) A)`; (* Classical absurdidty rule *) *)

(* val [Nc_ax, Nc_andi, Nc_andel, Nc_ander, Nc_impi, Nc_impe, *)
(*      Nc_orir, Nc_oril, Nc_ore, Nc_absurd] = CONJUNCTS Nc_rules; *)

val NmThm = Define `NmThm A = Nm EMPTY A`;
(* val NiThm = Define `NiThm A = Ni EMPTY A`; *)
(* val NcThm = Define `NcThm A = Nc EMPTY A`; *)

(* Example deductions *)
val Nm_example = Q.prove(`NmThm (A Imp (B Imp A))`,
`Nm {A} A` by rw[Nm_ax] >>
`Nm {B} B` by rw[Nm_ax] >>
`{A} UNION {B} = {A;B}` by simp[UNION_DEF,INSERT_DEF] >>
`Nm {A;B} (A And B)` by metis_tac[Nm_andi] >>
`Nm {A;B} (A)` by metis_tac[Nm_andel] >>
`Nm {A} (B Imp A)` by (irule Nm_impi >> simp[INSERT_COMM]) >>
`Nm {} (A Imp (B Imp A))` by metis_tac[Nm_impi] >>
 rw[NmThm]);

(* val Ni_example = Q.prove(`NiThm (Bot Imp A)`, *)
(* `Ni {Bot} Bot` by rw[Ni_rules] >> *)
(* `Ni {Bot} A` by rw[Ni_rules] >> *)
(* `{} = ({Bot} DIFF {Bot})` by rw[DIFF_DEF] >> *)
(* `Ni EMPTY (Bot Imp A)` by metis_tac[Ni_rules] >> *)
(* rw[NiThm]); *)

(** Sequent Calculus (Gentzen System) for minimal logic **)
(* Gm is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* S is used to represent the multiset of the Antecedent Context *)
(* The consequent is always a single formula in the minimal logic *)

val (Gm_rules, Gm_ind, Gm_cases) = Hol_reln `
(!(A:'a formula) Γ. (A <: Γ) ==> Gm Γ A) (* Ax *)
/\ (!A Γ C. (Gm ({|A;A|} + Γ) C)
   ==> Gm ({|A|} + Γ) C) (* Left Contraction *)
/\ (!A B Γ C. (Gm (BAG_INSERT A Γ) C)
   ==> (Gm (BAG_INSERT (A And B) Γ) C)) (* Left And 1 *)
/\ (!A B Γ C. (Gm (BAG_INSERT B Γ) C)
   ==> (Gm (BAG_INSERT (A And B) Γ) C)) (* Left And 2 *)
/\ (!A B Γ. (Gm Γ A) /\ (Gm Γ B)
   ==> (Gm Γ (A And B))) (* Right And *)
/\ (!A B Γ C. (Gm (BAG_INSERT A Γ) C)
    /\ (Gm (BAG_INSERT B Γ) C)
   ==> (Gm (BAG_INSERT (A Or B) Γ) C)) (* Left Or *)
/\ (!A B Γ. (Gm Γ A)
   ==> (Gm Γ (A Or B))) (* Right Or 1 *)
/\ (!A B Γ. (Gm Γ B)
   ==> (Gm Γ (A Or B))) (* Right Or 2 *)
/\ (!A B Γ C. (Gm Γ A) /\ (Gm (BAG_INSERT B Γ) C)
   ==> (Gm (BAG_INSERT (A Imp B) Γ) C)) (* Left Imp *)
/\ (!A B Γ. (Gm (BAG_INSERT A Γ) B)
   ==> (Gm Γ (A Imp B))) (* Right Imp *)
∧  (∀A B Γ Γ'. (Gm Γ A) ∧ (Gm (BAG_INSERT A Γ') B) ==> Gm (Γ + Γ') B)` (* Cut *)

val [Gm_ax, Gm_lc, Gm_landl, Gm_landr, Gm_rand,
     Gm_lor, Gm_rorl, Gm_rorr, Gm_limp, Gm_rimp, Gm_cut] = CONJUNCTS Gm_rules;

val GmThm = Define `GmThm A = Gm EMPTY_BAG A`;

val Gm_example1 =
    Q.prove(`GmThm ((A And B) Imp (B And A))`, rw[GmThm,Gm_rules]);

val Gm_example2 = Q.prove (`GmThm ((A Imp (A Imp B)) Imp (A Imp B))`,
rw[GmThm] >>
`Gm {|(A Imp A Imp B)|} (A Imp B)` suffices_by metis_tac[Gm_rules] >>
`Gm {|A;(A Imp A Imp B)|} (B)` suffices_by metis_tac[Gm_rules] >>
`Gm {|A|} (A)` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gm {|B;A|} (B)` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
(* `Gm {|A;B|} (B)` by simp[Gm_lw] >> *)
(* `Gm {|B;A|} (B)` by simp[BAG_INSERT_commutes] >> *)
`Gm {|(A Imp B);A|} (B)` by metis_tac[Gm_rules] >>
`Gm {|(A Imp A Imp B);A|} (B)` suffices_by metis_tac[BAG_INSERT_commutes] >>
metis_tac[Gm_rules]);

val Gm_land_commutes =
    Q.prove(`Gm {| A And B |} Δ ==> Gm {| B And A |} Δ`, rw[] >>
`Gm {|B|} B` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gm {|B And A|} B` by metis_tac[Gm_landl] >>
`Gm {|A|} A` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gm {|B And A|} A` by metis_tac[Gm_landr] >>
`Gm {|B And A|} (A And B)` by metis_tac[Gm_rand] >>
`Gm ({|B And A|} + {||}) Δ` by metis_tac[Gm_cut] >>
metis_tac[BAG_UNION_EMPTY]);

(** Sequent Calculus (Gentzen System) for intuitionistic logic **)
(* Gi is the 'deduciblility' relation for this system *)
(* S and D are used to represent the bag Antecedent and Consequent Contexts *)
(* The Consequent has at most one formula for intuitionistic logic *)

(* val (Gi_rules, Gi_ind, Gi_cases) = Hol_reln ` *)
(* (!A:'a formula. Gi {|A|} {|A|}) (* Ax *) *)
(* /\ (Gi {|Bot|} {||}) (* LBot *) *)
(* /\ (!Γ A Δ. Gi Γ Δ ==> Gi (BAG_INSERT A Γ) Δ) (* Left Weakening *) *)
(* /\ (!A Γ. Gi Γ EMPTY_BAG ==> Gi Γ {|A|}) (* Right Weakening *) *)
(* /\ (!A Γ Δ. (Gi ({|A;A|} + Γ) Δ) *)
(*     ==> Gi ({|A|} + Γ) Δ) (* Left Contraction *) *)
(* /\ (!A B Γ Δ. (Gi (BAG_INSERT A Γ) Δ) *)
(*    ==> (Gi (BAG_INSERT (A And B) Γ) Δ)) (* Left And 1 *) *)
(* /\ (!A B Γ Δ. (Gi (BAG_INSERT B Γ) Δ) *)
(*    ==> (Gi (BAG_INSERT (A And B) Γ) Δ)) (* Left And 2 *) *)
(* /\ (!A B Γ. (Gi Γ {|A|}) /\ (Gi Γ {|B|}) *)
(*    ==> (Gi Γ {|A And B|})) (* Right And *) *)
(* /\ (!A B Γ Δ. (Gi (BAG_INSERT A Γ) Δ) *)
(*     /\ (Gi (BAG_INSERT B Γ) Δ) *)
(*    ==> (Gi (BAG_INSERT (A Or B) Γ) Δ)) (* Left Or *) *)
(* /\ (!A B Γ. (Gi Γ {|A|}) *)
(*    ==> (Gi Γ {|A Or B|})) (* Right Or 1 *) *)
(* /\ (!A B Γ. (Gi Γ {|B|}) *)
(*    ==> (Gi Γ {|A Or B|})) (* Right Or 2 *) *)
(* /\ (!A B Γ Δ. (Gi Γ {|A|}) /\ (Gi (BAG_INSERT B Γ) Δ) *)
(*    ==> (Gi (BAG_INSERT (A Imp B) Γ) Δ)) (* Left Imp *) *)
(* /\ (!A B Γ. (Gi (BAG_INSERT A Γ) {|B|}) *)
(*    ==> (Gi Γ {|A Imp B|})) (* Right Imp *) *)
(* ∧  (∀A Δ Γ. (Gi Γ {|A|}) ∧ (Gi {|A|} Δ) ==> Gi Γ Δ)` (* Cut *) *)

(* val [Gi_ax, Gi_bot, Gi_lw, Gi_rw, Gi_lc, Gi_landl, Gi_landr, Gi_rand, Gi_lor, *)
(*      Gi_rorl, Gi_rorr, Gi_limp, Gi_rimp, Gi_cut] = CONJUNCTS Gi_rules; *)

(* val GiThm = Define `GiThm A = Gi EMPTY_BAG {|A|}` *)

(* val Gi_example1 = Q.prove(`Gi {|P And (Not P)|} {|Bot|}`, *)
(* `Gi {|P And Not P|} EMPTY_BAG` suffices_by metis_tac[Gi_rules] >> *)
(* `Gi {|Bot|} EMPTY_BAG` by metis_tac[Gi_rules] >> *)
(* `Gi {|P;Bot|} EMPTY_BAG` by metis_tac[Gi_lw] >> *)
(* `Gi ({|Bot;P|}) EMPTY_BAG` by metis_tac[BAG_INSERT_commutes] >> *)
(* `Gi {|P|} {|P|}` by metis_tac[Gi_ax] >> *)
(* `Gi {|P Imp Bot;P|} {||}` by metis_tac[Gi_rules,BAG_INSERT] >> *)
(* `Gi {|Not P;P|} {||}` by metis_tac[Not_def] >> *)
(* `Gi {|P And Not P;P|} {||}` by metis_tac[Gi_rules] >> *)
(* `Gi {|P And Not P;P And Not P|} {||}` *)
(*   by metis_tac[Gi_rules,BAG_INSERT_commutes] >> *)
(* `{|A;A|} = {|A;A|} + {||}` by simp[] >> *)
(* `{|A|} = {|A|} + {||}` by simp[] >> *)
(* qspecl_then [`P And Not P`,`{||}`,`{||}`] mp_tac (Gi_lc) >> *)
(* simp[] *)
(* ); *)

(* (** Sequent Calculus (Gentzen System) for classical logic **) *)
(* (* Gc is the 'deduciblility' relation for this system *) *)
(* (* Both contexts are arbitrary size finite bags *) *)
(* val (Gc_rules, Gc_ind, Gc_cases) = Hol_reln ` *)
(* (!A:'a formula. Gc {|A|} {|A|}) (* Ax *) *)
(* /\ (Gc {|Bot|} {||}) (* LBot *) *)
(* /\ (!Γ A Δ. Gc Γ Δ ==> Gc (BAG_INSERT A Γ) Δ) (* Left Weakening *) *)
(* /\ (!Γ Δ A. Gc Γ Δ ==> Gc Γ (BAG_INSERT A Δ)) (* Right Weakening *) *)
(* /\ (!A Γ Δ. (Gc ({|A;A|} + Γ) Δ)  *)
(*    ==> Gc ({|A|} + Γ) Δ) (* Left Contraction *) *)
(* /\ (!A Γ Δ. (Gc Γ ({|A;A|} + Δ)) *)
(*    ==> Gc Γ ({|A|} + Δ)) (* Right Contraction *) *)
(* /\ (!A B Γ Δ. (Gc (BAG_INSERT A Γ) Δ) *)
(*    ==> (Gc (BAG_INSERT (A And B) Γ) Δ)) (* Left And 1 *) *)
(* /\ (!A B Γ Δ. (Gc (BAG_INSERT B Γ) Δ) *)
(*    ==> (Gc (BAG_INSERT (A And B) Γ) Δ)) (* Left And 2 *) *)
(* /\ (!A B Γ Δ. (Gc Γ (BAG_INSERT A Δ)) /\ (Gc Γ (BAG_INSERT B Δ)) *)
(*    ==> (Gc Γ (BAG_INSERT (A And B) Δ))) (* Right And *) *)
(* /\ (!A B Γ Δ. (Gc (BAG_INSERT A Γ) Δ) /\ (Gc (BAG_INSERT B Γ) Δ) *)
(*    ==> (Gc (BAG_INSERT (A Or B) Γ) Δ)) (* Left Or *) *)
(* /\ (!A B Γ Δ. (Gc Γ (BAG_INSERT A Δ)) *)
(*    ==> (Gc Γ (BAG_INSERT (A Or B) Δ))) (* Right Or 1 *) *)
(* /\ (!A B Γ Δ. (Gc Γ (BAG_INSERT B Δ)) *)
(*    ==> (Gc Γ (BAG_INSERT (A Or B) Δ))) (* Right Or 2 *) *)
(* /\ (!A B Γ Δ. (Gc Γ (BAG_INSERT A Δ)) /\ (Gc (BAG_INSERT B Γ) Δ) *)
(*    ==> (Gc (BAG_INSERT (A Imp B) Γ) Δ)) (* Left Imp *) *)
(* /\ (!A B Γ Δ. (Gc (BAG_INSERT A Γ) (BAG_INSERT B Δ)) *)
(*    ==> (Gc Γ (BAG_INSERT (A Imp B) Δ))) (* Right Imp *) *)
(* ∧  (∀A Δ Δ' Γ Γ'. (Gc Γ (BAG_INSERT A Δ)) *)
(*      ∧ (Gc (BAG_INSERT A Γ') Δ') *)
(*      ==> Gc (Γ + Γ') (Δ + Δ'))` (* Cut *) *)

(* val [Gc_ax, Gc_bot, Gc_lw, Gc_rw, Gc_lc, Gc_rc, Gc_landl, Gc_landr, Gc_rand, *)
(*      Gc_lor, Gc_rorl, Gc_rorr, Gc_limp, Gc_rimp, Gc_cut] = CONJUNCTS Gc_rules; *)

(* val GcThm = Define `GcThm A = Gc EMPTY_BAG {|A|}`; *)

(* val Gc_example1 = Q.prove(`GcThm (((P Imp Q) Imp P) Imp P)`,rw[GcThm] >> *)
(* `Gc {|P|} {|P|}` by metis_tac[Gc_ax] >> *)
(* `Gc {|P|} {|Q;P|}` by metis_tac[Gc_rw] >> *)
(* `Gc {||} {|P Imp Q;P|}` by metis_tac[Gc_rimp] >> *)
(* `Gc {|(P Imp Q) Imp P|} {|P|}` by metis_tac[Gc_limp] >> *)
(* `Gc {||} {|((P Imp Q) Imp P) Imp P|}` by metis_tac[Gc_rimp]); *)


(* ========================================================================== *)
(* Proofs of equivalence of N and G Systems                                   *)
(*                                                                            *)
(*                                                                            *)
(* ========================================================================== *)
Theorem BAG_OF_SET_UNION `∀Γ Γ'. BAG_OF_SET (Γ ∪ Γ') = (BAG_MERGE (BAG_OF_SET Γ) (BAG_OF_SET Γ'))` (
 rpt strip_tac >> simp[UNION_DEF] >> simp[BAG_OF_SET] >> simp[BAG_MERGE] >>
 simp[FUN_EQ_THM] >> rw[] >> fs[]);

Theorem BAG_OF_SET_DIFF `BAG_OF_SET (Γ DIFF Γ') = BAG_FILTER (COMPL Γ') (BAG_OF_SET Γ)` (
simp[DIFF_DEF] >> simp[BAG_OF_SET] >> simp[BAG_FILTER_DEF] >> metis_tac[]);

Theorem BAG_OF_SET_INSERT
`!e s. BAG_OF_SET (e INSERT s) = BAG_MERGE {|e|} (BAG_OF_SET s)` (
rw[BAG_OF_SET,INSERT_DEF,BAG_MERGE,EMPTY_BAG] >>
rw[FUN_EQ_THM,BAG_INSERT] >> rw[] 
 >- (fs[IN_DEF] >>
     `s e = F` by metis_tac[] >>
     fs[COND_CLAUSES])
 >- (`(x = e) = F` by metis_tac[] >>
     fs[COND_CLAUSES])
 >- (`(x = e) = F` by metis_tac[] >>
     `(s x) = T` by metis_tac[] >>
     fs[COND_CLAUSES]));

Theorem BAG_MERGE_SUB_BAG_UNION `∀s t. ((BAG_MERGE s t) ≤ (s ⊎ t))` (
  simp[SUB_BAG] >> simp[BAG_MERGE,BAG_UNION] >> rw[BAG_INN]);

Theorem BAG_UNION_COMM `∀a b. a ⊎ b = b ⊎ a` (rw[BAG_UNION]);

Theorem BAG_MERGE_EMPTY `∀b. ((BAG_MERGE {||} b) = b) /\ ((BAG_MERGE b {||}) = b)` (rw[] >> simp[BAG_MERGE,FUN_EQ_THM,EMPTY_BAG]);

val Nm_D_FINITE = Q.prove(`!D A. Nm D A ==> FINITE D`,
                          Induct_on `Nm` >> rw[Nm_rules]);

Theorem BAG_INSERT_FILTER_COMP_OF_SET `∀s a. (BAG_INSERT a (BAG_FILTER (COMPL {a}) (BAG_OF_SET s))) = (BAG_OF_SET (a INSERT s))` (
  simp[BAG_OF_SET,BAG_INSERT,BAG_FILTER_DEF,COMPL_DEF,INSERT_DEF] >>
  rw[FUN_EQ_THM] >> metis_tac[]);

Theorem BAG_MERGE_ELBAG_SUB_BAG_INSERT `∀A b. (BAG_MERGE {|A|} b) ≤ (BAG_INSERT A b)` (
  rw[] >> simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG] >>
    simp[SUB_BAG,BAG_INN] >> rw[]);

(* val Gm_G_FINITE = Q.prove(`!Γ A. Gm Γ A ==> FINITE_BAG Γ`, *)
(*                           Induct_on `Gm` >> rw[Gm_rules]); *)

(* IN PROGRESS *)
(* val Gm_wk_BAG_OF_SET = Q.prove(`!Γ A. Gm Γ A ==> Gm (BAG_OF_SET (SET_OF_BAG Γ)) A`, *)

Theorem Gm_lw `∀Γ A. Gm Γ A ⇒ ∀Γ'. Γ ≤ Γ' ⇒ Gm Γ' A`
(Induct_on `Gm` >> rw[]
>- (irule Gm_ax >> fs[SUB_BAG, BAG_IN])
>- (‘∃Γ₂. Γ' = {|A|} ⊎ Γ₂’
       by (qexists_tac ‘Γ' - {|A|}’ >> irule SUB_BAG_DIFF_EQ >>
           metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gm_lc >> first_x_assum irule >> simp[] >> fs[])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A And B) Γ₂’
      by (qexists_tac ‘Γ' - {|A And B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gm_landl >> first_x_assum irule >> fs[SUB_BAG_INSERT])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A And B) Γ₂’
      by (qexists_tac ‘Γ' - {|A And B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gm_landr >> first_x_assum irule >> fs[SUB_BAG_INSERT])
>- (irule Gm_rand >> simp[])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A Or B) Γ₂’
      by (qexists_tac ‘Γ' - {|A Or B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> fs[SUB_BAG_INSERT] >> irule Gm_lor >> conj_tac >>
    first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
>- simp[Gm_rorl]
>- simp[Gm_rorr]
>- (‘∃Γ₂. Γ' = BAG_INSERT (A Imp B) Γ₂’
      by (qexists_tac ‘Γ' - {|A Imp B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gm_limp >> fs[SUB_BAG_INSERT])
>- simp[SUB_BAG_INSERT, Gm_rimp]
>- (rename [‘Γ₁ ⊎ Γ₂ ≤ Γ₃’] >>
    ‘∃Γ₀. Γ₃ = Γ₀ ⊎ Γ₁ ⊎ Γ₂’
      by metis_tac[SUB_BAG_EXISTS, COMM_BAG_UNION, ASSOC_BAG_UNION] >>
    rw[] >> irule Gm_cut >>
    rename [‘Gm (BAG_INSERT A _) B’] >> qexists_tac ‘A’ >>
    conj_tac >> first_x_assum irule >> fs[SUB_BAG_INSERT]));

val Gm_lw_BAG_MERGE = Q.prove(`!Γ₁ A. Gm Γ₁ A ==> !Γ₂. Gm (BAG_MERGE Γ₂ Γ₁) A`,
rw[] >> irule Gm_lw >> Q.EXISTS_TAC `Γ₁` >> simp[] >>
 simp[SUB_BAG] >> simp[BAG_INN_BAG_MERGE]);

val Gm_lw_BAG_UNION = Q.prove(`∀Γ A. Gm Γ A ==> ∀Γ'. Gm (Γ ⊎ Γ') A`,
  rw[] >> irule Gm_lw >> Q.EXISTS_TAC `Γ` >> simp[]);

val Gm_lw_BAG_INSERT = Q.prove(`∀Γ A. Gm Γ A ==> ∀B Γ'. Gm (BAG_INSERT B Γ) A`,
  rw[] >> irule Gm_lw >> Q.EXISTS_TAC `Γ` >> simp[SUB_BAG_INSERT_I]);

val DISTINCT_SUB_BAG = Define `∀a b. DISTINCT_SUB_BAG a b = (a ≤ b) /\ (BAG_ALL_DISTINCT a)`;

(* Theorem Gm_lc_BAG_MERGE `∀Γ Γ' A. Gm (Γ ⊎ Γ') A ==> Gm (BAG_MERGE Γ Γ') A` ( *)
(*   rw[] >> fs[BAG_UNION,BAG_MERGE] >> *)
(*   Cases_on `Γ'` >- fs[EMPTY_BAG] *)
(*     >- (Cases_on `Γ` *)
(*       >- (fs[EMPTY_BAG] >> fs[BAG_INSERT] >> *)

(* Theorem Gm_lc_SET_OF_BAG `∀Γ A. Gm Γ A ==> Gm (BAG_OF_SET (SET_OF_BAG Γ)) A` ( *)
(*   Induct_on `Gm` >> rw[Gm_rules] *)
(*     >- fs[BAG_OF_SET,SET_OF_BAG,BAG_INSERT,BAG_UNION] *)
(*     >- fs[BAG_OF_SET,SET_OF_BAG,BAG_INSERT,BAG_IN] *)

(*   rw[] >> simp[BAG_OF_SET,SET_OF_BAG] >> Cases_on `Γ` *)
(*     >- fs[EMPTY_BAG_alt] *)
(*     >- fs[BAG_INN,BAG_INSERT] *)

(* IN PROGRESS *)
Theorem Nm_Gm `∀Γ A. Nm Γ A ==> Gm (BAG_OF_SET Γ) A` (
 Induct_on `Nm ` >>
 rw[Gm_rules] >>
 >- (irule Gm_rand >> conj_tac
     >- (`Gm (BAG_OF_SET (Γ' ∪ Γ)) A` suffices_by metis_tac[UNION_COMM] >>
         simp[BAG_OF_SET_UNION] >>
         metis_tac[Gm_lw_BAG_MERGE])
     >- (simp[BAG_OF_SET_UNION] >>
             metis_tac[Gm_lw_BAG_MERGE]))
 >- (`Gm {|A|} A` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT] >>
     `Gm {|A And B|} A` by metis_tac[Gm_landl] >>
     `Gm ((BAG_OF_SET Γ) + {||}) A` by metis_tac[Gm_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (`Gm {|A'|} A'` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT] >>
     `Gm {|A And A'|} A'` by metis_tac[Gm_landr] >>
     `Gm ((BAG_OF_SET Γ) + {||}) A'` by metis_tac[Gm_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (irule Gm_rimp >>
     fs[BAG_OF_SET_INSERT] >>
     `(BAG_MERGE {|A|} (BAG_OF_SET Γ)) ≤ (BAG_INSERT A (BAG_OF_SET Γ))` by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT] >>
     metis_tac[Gm_lw])
 >- (simp[BAG_OF_SET_UNION] >>
    `Gm (BAG_INSERT A' (BAG_OF_SET Γ')) A'` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT] >>
    `Gm (BAG_INSERT (A Imp A') (BAG_OF_SET Γ')) A'` by metis_tac[Gm_limp] >>
    `Gm ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ')) A'` by metis_tac[Gm_cut] >>
    (* Needs Lemma *)
    )
  >- (fs[BAG_OF_SET_INSERT] >> 
      `Gm (BAG_INSERT A (BAG_OF_SET Γ)) A'` by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gm_lw] >>
      `Gm (BAG_INSERT B (BAG_OF_SET Γ)) A'` by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gm_lw] >>
      `Gm (BAG_INSERT (A Or B) (BAG_OF_SET Γ)) A'` by metis_tac[Gm_lor] >>
      `Gm ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ)) A'` by metis_tac[Gm_cut] >>
      (* Needs Lemma *)
 )


Theorem Nm_lw `∀D A. Nm D A ==> ∀B. Nm (B INSERT D) A` (
  Induct_on `Nm` >> rw[] 
    >- (`Nm {B} B` by metis_tac[Nm_ax] >>
        `Nm {A} A` by metis_tac[Nm_ax] >>
        `Nm {B;A} (B And A)` by metis_tac[Nm_andi,INSERT_SING_UNION] >>
        metis_tac[Nm_ander])
    >- (simp[Once INSERT_SING_UNION] >> simp[UNION_ASSOC] >> irule Nm_andi >>
        `Nm (B' INSERT D) A` by metis_tac[] >> fs[Once INSERT_SING_UNION])
    >- (fs[Once INSERT_SING_UNION] >> metis_tac[Nm_andel])
    >- (fs[Once INSERT_SING_UNION] >> metis_tac[Nm_ander])
    >- (fs[Once INSERT_SING_UNION] >> irule Nm_impi >>
        `Nm ({B} ∪ (A INSERT D)) A'` by metis_tac[] >>
        `Nm ({A} ∪ ({B} ∪ D)) A'`
          by metis_tac[INSERT_SING_UNION,UNION_COMM,UNION_ASSOC] >>
        simp[Once INSERT_SING_UNION])
    >- (fs[Once INSERT_SING_UNION] >>
        `Nm ({B} ∪ D) (A Imp A')` by metis_tac[] >>
        `Nm ({B} ∪ D') A` by metis_tac[] >>
        `Nm (({B} ∪ D) ∪ ({B} ∪ D')) A'` by metis_tac[Nm_impe] >>
        metis_tac[UNION_ASSOC,UNION_COMM,UNION_IDEMPOT])
    >- (fs[Once INSERT_SING_UNION] >>
        irule Nm_orir >> metis_tac[])
    >- (fs[Once INSERT_SING_UNION] >>
        irule Nm_oril >> metis_tac[])
    >- (fs[Once INSERT_SING_UNION] >>
        `Nm ({B'} ∪ (A INSERT D)) A'` by metis_tac[] >>
        `Nm ((A INSERT D) ∪ {B'}) A'` by metis_tac[UNION_COMM] >>
        `Nm (A INSERT (D ∪ {B'})) A'` by metis_tac[INSERT_UNION_EQ] >>
        `Nm (A INSERT ({B'} ∪ D)) A'` by metis_tac[UNION_COMM] >>
        `Nm ({B'} ∪ (B INSERT D)) A'` by metis_tac[] >>
        `Nm ((B INSERT D) ∪ {B'}) A'` by metis_tac[UNION_COMM] >>
        `Nm (B INSERT (D ∪ {B'})) A'` by metis_tac[INSERT_UNION_EQ] >>
        `Nm (B INSERT ({B'} ∪ D)) A'` by metis_tac[UNION_COMM] >>
        `Nm ({B'} ∪ D) (A Or B)` by metis_tac[] >>
        metis_tac[Nm_ore]));

(* Theorem Nm_lw_UNION `∀D A. Nm D A ==> ∀D'. Nm (D' ∪ D) A` ( *)
(*   Induct_on `Nm` >> rw[] *)
(*             >-   *)
(*  Theorem Nm_lw_SUBSET `∀D A. Nm D A ==> ∀D'. D ⊆ D' ==> Nm D' A` ( *)
(*   Induct_on `Nm` >> rw[]  *)
(*     >- (Cases_on `D'` >- fs[] >-  *)

  
(* IN PROGRESS *)
(* Apparently Nm takes a subset here!? *)
Theorem Gm_Nm `∀Γ A. Gm Γ A ==> ?Γ'. Γ' ⊆ (SET_OF_BAG Γ) /\ Nm Γ' A` (
  Induct_on `Gm` >> rw[]
    >- (Q.EXISTS_TAC `{A}` >> simp[SUBSET_DEF,SET_OF_BAG] >> metis_tac[Nm_ax])
    >- (Q.EXISTS_TAC `Γ'` >> fs[SET_OF_BAG,BAG_UNION,BAG_INSERT]) 
    >- (rename [`Nm _ C`] >>
        `∀D A. Nm D A ==> ∀D'. D ⊆ D' ==> Nm D' A` by cheat >>
        `Nm {A And B} (A And B)` by metis_tac[Nm_ax] >>
        `Nm {A And B} A` by metis_tac[Nm_andel] >>
        `Nm ((SET_OF_BAG (BAG_INSERT A Γ))) C` by metis_tac[] >>
        `Nm (A INSERT (SET_OF_BAG Γ)) C` by metis_tac[SET_OF_BAG_INSERT] >>
        `Nm (SET_OF_BAG Γ) (A Imp C)` by metis_tac[Nm_impi] >>
        `Nm ((SET_OF_BAG Γ) ∪ {A And B}) C` by metis_tac[Nm_impe] >>
        `Nm ((A And B) INSERT (SET_OF_BAG Γ)) C` 
          by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(SET_OF_BAG (BAG_INSERT (A And B) Γ))` >>
        simp[SET_OF_BAG_INSERT])
    >- (rename [`Nm _ C`] >>
        `∀D A. Nm D A ==> ∀D'. D ⊆ D' ==> Nm D' A` by cheat >>
        `Nm {A And B} (A And B)` by metis_tac[Nm_ax] >>
        `Nm {A And B} B` by metis_tac[Nm_ander] >>
        `Nm ((SET_OF_BAG (BAG_INSERT B Γ))) C` by metis_tac[] >>
        `Nm (B INSERT (SET_OF_BAG Γ)) C` by metis_tac[SET_OF_BAG_INSERT] >>
        `Nm (SET_OF_BAG Γ) (B Imp C)` by metis_tac[Nm_impi] >>
        `Nm ((SET_OF_BAG Γ) ∪ {A And B}) C` by metis_tac[Nm_impe] >>
        `Nm ((A And B) INSERT (SET_OF_BAG Γ)) C` 
          by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(SET_OF_BAG (BAG_INSERT (A And B) Γ))` >>
        simp[SET_OF_BAG_INSERT])
    >- (qexists_tac `Γ' ∪ Γ''` >> simp[] >>
        metis_tac[Nm_andi])
    >- (rename [`Nm _ C`] >>
        `∀D A. Nm D A ==> ∀D'. D ⊆ D' ==> Nm D' A` by cheat >>
        fs[SET_OF_BAG_INSERT] >>
        `Nm (A INSERT ((A Or B) INSERT (SET_OF_BAG Γ))) C`
          by (first_assum irule >> qexists_tac `Γ'` >> simp[] >> metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >> 
        `Nm (B INSERT ((A Or B) INSERT (SET_OF_BAG Γ))) C`
          by (first_assum irule >> qexists_tac `Γ''` >> simp[] >>
            metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        qexists_tac `(A Or B) INSERT (SET_OF_BAG Γ)` >>
        simp[SUBSET_INSERT_RIGHT] >>
        `Nm {(A Or B)} (A Or B)` by metis_tac[Nm_ax] >>
        `Nm ({A Or B} ∪ (SET_OF_BAG Γ)) (A Or B)`
          by metis_tac[SUBSET_UNION] >>
        `Nm ((A Or B) INSERT (SET_OF_BAG Γ)) (A Or B)`
          by metis_tac[INSERT_SING_UNION] >>
        metis_tac[Nm_ore])
    >- (qexists_tac `Γ'` >> simp[Nm_orir])
    >- (qexists_tac `Γ'` >> simp[Nm_oril])
    >- ( (*skipped*))
    >- ( (*skipped, same prob*))
    >- (simp[SET_OF_BAG_UNION] >> (*skipped, similar problem*)
        `∀D A. Nm D A ==> ∀D'. D ⊆ D' ==> Nm D' A` by cheat >>
        `Nm (SET_OF_BAG (BAG_INSERT A Γ')) A'` by metis_tac[] >>
        `Nm (SET_OF_BAG Γ) A` by metis_tac[] >>
        `Nm (A INSERT (SET_OF_BAG Γ')) A'` by metis_tac[SET_OF_BAG_INSERT] >>
        `Nm (SET_OF_BAG Γ') (A Imp A')` by metis_tac[Nm_impi] >>
        `Nm ((SET_OF_BAG Γ') ∪ (SET_OF_BAG Γ)) A'` by metis_tac[Nm_impe] >>
        qexists_tac `(SET_OF_BAG Γ') ∪ (SET_OF_BAG Γ)` >> simp[])
)

val _ = export_theory()
