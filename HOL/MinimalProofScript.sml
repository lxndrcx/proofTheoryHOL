
(* ========================================================================== *)
(* Equivalence of Sequent Calculus and Natural Deduction                      *)
(* Working from Troelstra and Schwichtenburg - Basic Proof Theory 2nd Edition *)
(*                                                                            *)
(* ========================================================================== *)

open HolKernel boolLib Parse bossLib;
open bagTheory;
open pred_setTheory;

open FormulaSyntaxTheory;

val _ = new_theory "MinimalProof";

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
val NmThm = Define `NmThm A = Nm EMPTY A`;
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


(** Sequent Calculus (Gentzen System) for minimal logic **)
(* Gm is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* S is used to represent the multiset of the Antecedent Context *)
(* The consequent is always a single formula in the minimal logic *)

val (Gm_rules, Gm_ind, Gm_cases) = Hol_reln `
(!(A:'a formula) Γ. (A <: Γ) /\ FINITE_BAG Γ ==> Gm Γ A) (* Ax *)
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

(* ========================================================================== *)
(* Proofs of equivalence of N and G Systems                                   *)
(*                                                                            *)
(*                                                                            *)
(* ========================================================================== *)
Theorem BAG_OF_SET_UNION `∀Γ Γ'. BAG_OF_SET (Γ ∪ Γ') = (BAG_MERGE (BAG_OF_SET Γ) (BAG_OF_SET Γ'))` (
 rpt strip_tac >> simp[UNION_DEF] >> simp[BAG_OF_SET] >> simp[BAG_MERGE] >>
 simp[FUN_EQ_THM] >> rw[] >> fs[]);

Theorem BAG_OF_SET_DIFF `BAG_OF_SET (Γ DIFF Γ') 
                         = BAG_FILTER (COMPL Γ') (BAG_OF_SET Γ)` (
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

Theorem BAG_MERGE_EMPTY 
`∀b. ((BAG_MERGE {||} b) = b) /\ ((BAG_MERGE b {||}) = b)` (
  rw[] >> 
  simp[BAG_MERGE,FUN_EQ_THM,EMPTY_BAG]);

Theorem Nm_FINITE `!D A. Nm D A ==> FINITE D` (Induct_on `Nm` >> rw[])
Theorem Gm_FINITE `!D A. Gm D A ==> FINITE_BAG D` (Induct_on `Gm` >> rw[])

Theorem BAG_INSERT_FILTER_COMP_OF_SET 
`∀s a. (BAG_INSERT a (BAG_FILTER (COMPL {a}) (BAG_OF_SET s))) 
        = (BAG_OF_SET (a INSERT s))` (
  simp[BAG_OF_SET,BAG_INSERT,BAG_FILTER_DEF,COMPL_DEF,INSERT_DEF] >>
  rw[FUN_EQ_THM] >> metis_tac[]); (* Probably don't need this anymore *)

Theorem BAG_MERGE_ELBAG_SUB_BAG_INSERT 
`∀A b. (BAG_MERGE {|A|} b) ≤ (BAG_INSERT A b)` (
  rw[] >> simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG] >>
    simp[SUB_BAG,BAG_INN] >> rw[]);

(* Thanks for this theorem Michael *)
Theorem Gm_lw `∀Γ A. Gm Γ A ⇒ ∀Γ'. Γ ≤ Γ' /\ FINITE_BAG Γ' ⇒ Gm Γ' A`
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

Theorem BAG_MERGE_CARD
`∀a b. FINITE_BAG a /\ FINITE_BAG b ==>
                       BAG_CARD (BAG_MERGE a b) ≤ (BAG_CARD a + BAG_CARD b)` (
  rw[] >>
  `(BAG_MERGE a b) ≤ (a ⊎ b)`
    by metis_tac[BAG_MERGE_SUB_BAG_UNION] >>
  `FINITE_BAG (a ⊎ b)` by metis_tac[FINITE_BAG_UNION] >>
  `BAG_CARD (BAG_MERGE a b) ≤ BAG_CARD (a ⊎ b)`
    by metis_tac[SUB_BAG_CARD] >>
  metis_tac[BAG_CARD_UNION]);

Theorem BAG_MERGE_EQ_EMPTY[simp] 
`∀a b. (BAG_MERGE a b = {||}) = (a = {||}) ∧ (b = {||})` (
  rw[BAG_MERGE,EMPTY_BAG,FUN_EQ_THM] >>
  EQ_TAC >>
  rw[] >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[] );

Theorem FINITE_BAG_INSERT[simp] `∀e b. FINITE_BAG b 
                                   <=> FINITE_BAG (BAG_INSERT e b)` (
  rw[]);

Theorem BAG_MERGE_BAG_INSERT
`∀e a b.
((a e ≤ b e) ==> ((BAG_MERGE a (BAG_INSERT e b))
                   = (BAG_INSERT e (BAG_MERGE a b)))) ∧
((b e < a e) ==> ((BAG_MERGE a (BAG_INSERT e b)) 
                   = (BAG_MERGE a b))) ∧
((a e < b e) ==> ((BAG_MERGE (BAG_INSERT e a) b)
                   = ((BAG_MERGE a b)))) ∧
((b e ≤ a e) ==> ((BAG_MERGE (BAG_INSERT e a) b) 
                   = (BAG_INSERT e (BAG_MERGE a b)))) ∧
((a e = b e) ==> ((BAG_MERGE (BAG_INSERT e a) (BAG_INSERT e b))
                   = (BAG_INSERT e (BAG_MERGE a b))))` (
  rw[]
    >- (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
        rw[] >- (Cases_on `x=e` >> fs[]) >> fs[])
    >- (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
        reverse (rw[]) >- (Cases_on `x=e` >> fs[]) >> fs[])
    >- (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
        rw[] >- (Cases_on `x=e` >> fs[]) >> fs[])
    >> (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
        rw[] >> fs[]));

Theorem BAG_INSERT_EQ_MERGE_DELETE
`∀a b c e Σ Δ. (BAG_INSERT e a = BAG_MERGE b c)
                ∧ (BAG_DELETE b e Σ) ∧ (BAG_DELETE c e Δ)
            ==> ((BAG_MERGE b c = BAG_INSERT e (BAG_MERGE Σ Δ)))` (
  rw[BAG_DELETE] >>
  fs[BAG_INSERT,BAG_MERGE,EMPTY_BAG,FUN_EQ_THM] >>
  rw[] >> fs[]);

Theorem BAG_INSERT_EQ_MERGE_DIFF
`∀a b c e. (BAG_INSERT e a = BAG_MERGE b c) 
      ==> ((BAG_MERGE b c = BAG_INSERT e (BAG_MERGE (b - {|e|}) (c - {|e|}))))`
(rw[BAG_DIFF] >>
    fs[BAG_INSERT,BAG_MERGE,EMPTY_BAG,FUN_EQ_THM] >>
    reverse(rw[])
    >- (`b e - 1 + 1 = b e` suffices_by simp[EQ_SYM_EQ] >>
        irule arithmeticTheory.SUB_ADD >>
        `c e ≤ b e` by simp[] >>
        first_x_assum (qspec_then `e` mp_tac) >>
        rw[]) >> fs[]);

Theorem FINITE_BAG_MERGE[simp]
`∀a b. FINITE_BAG (BAG_MERGE a b) <=> FINITE_BAG a /\ FINITE_BAG b ` (
  rw[] >>
  reverse(EQ_TAC)
    >- (`BAG_MERGE a b ≤ a ⊎ b` by metis_tac[BAG_MERGE_SUB_BAG_UNION] >>
        rw[] >>
        `FINITE_BAG (a ⊎ b)` by metis_tac[FINITE_BAG_UNION] >>
        metis_tac[FINITE_SUB_BAG])
    >- (`∀c:'a bag. FINITE_BAG c ==> ∀a b. (c = BAG_MERGE a b)
             ==> FINITE_BAG a /\ FINITE_BAG b` suffices_by metis_tac[] >>
        Induct_on `c` >>
        rw[] >>
        `BAG_MERGE a b = BAG_INSERT e (BAG_MERGE (a - {|e|}) (b - {|e|}))`
          by metis_tac[BAG_INSERT_EQ_MERGE_DIFF] >>
        fs[] >>
        rw[] >>
        first_x_assum (qspecl_then [`a - {|e|}`,`b - {|e|}`] mp_tac) >>
        rw[] >>
        metis_tac[FINITE_BAG_DIFF_dual,FINITE_BAG]));

Theorem BAG_INSERT_BAG_OF_SET_BAG_DIFF
`∀e s. BAG_INSERT e (BAG_OF_SET s - {|e|}) = BAG_MERGE {|e|} (BAG_OF_SET s)` (
  simp[BAG_OF_SET,BAG_INSERT,BAG_DIFF,FUN_EQ_THM,BAG_MERGE,EMPTY_BAG_alt] >>
  rw[EMPTY_BAG,COND_CLAUSES] >> fs[]);

Theorem BAG_OF_SET_BAG_DIFF_DIFF
`∀b s. (BAG_OF_SET s) - b = (BAG_OF_SET (s DIFF (SET_OF_BAG b)))` (
  simp[BAG_OF_SET,DIFF_DEF,FUN_EQ_THM,BAG_DIFF] >>
  rw[BAG_IN,BAG_INN,IN_DEF] >> fs[]);

Theorem BAG_OF_SET_EQ_INSERT
`∀e b s. (BAG_INSERT e b = BAG_OF_SET s) ==>
         (?s'. s = (e INSERT s'))` (
  rw[] >>
  qexists_tac `s DELETE e` >>
  rw[INSERT_DEF,DELETE_DEF] >>
  simp[FUN_EQ_THM] >>
  rw[IN_DEF] >>
  EQ_TAC
  >- simp[]
  >- (rw[] >>
      `?t. s = (e INSERT t)`
        by metis_tac[DECOMPOSITION, BAG_IN_BAG_OF_SET, BAG_IN_BAG_INSERT] >>
      fs[]));

Theorem SET_OF_EL_BAG
`∀e. SET_OF_BAG {|e|} = {e}` (rw[SET_OF_BAG,FUN_EQ_THM]);

Theorem FINITE_BAG_OF_SET
`∀s. FINITE s <=> FINITE_BAG (BAG_OF_SET s)` (
  rw[] >> EQ_TAC
  >- (rw[] >>
      Induct_on `s` >>
      simp[SET_OF_EMPTY] >>
      rw[] >>
      simp[BAG_OF_SET_INSERT] >>
      simp[FINITE_BAG_MERGE])
  >- (`∀c. FINITE_BAG c ==> ∀s. (c = BAG_OF_SET s) ==> FINITE s`
        suffices_by metis_tac[] >>
      Induct_on `c` >>
      rw[]
        >- (Cases_on `s={}` >- rw[] >>
            `?e. e ∈ s` by metis_tac[MEMBER_NOT_EMPTY] >>
            fs[BAG_OF_SET,EMPTY_BAG_alt,FUN_EQ_THM] >>
            first_x_assum (qspec_then `e` mp_tac) >>
            rw[])
        >- (`e ∈ s`
              by metis_tac[BAG_IN_BAG_OF_SET,BAG_DECOMPOSE,BAG_IN_BAG_INSERT] >>
            `?t. s = (e INSERT t)` by metis_tac[BAG_OF_SET_EQ_INSERT] >>
            fs[] >>
            fs[BAG_OF_SET_INSERT] >>
            `(BAG_MERGE {|e|} (BAG_OF_SET t)) 
                = (BAG_INSERT e 
                  (BAG_MERGE ({|e|}-{|e|}) ((BAG_OF_SET t)-{|e|})))`
              by metis_tac[BAG_INSERT_EQ_MERGE_DIFF] >>
            fs[BAG_MERGE_EMPTY] >>
            `BAG_OF_SET t - {|e|} = BAG_OF_SET (t DIFF {e})`
              by simp[BAG_OF_SET_BAG_DIFF_DIFF,SET_OF_EL_BAG] >>
            first_x_assum (qspec_then `t DIFF {e}` mp_tac) >> DISCH_TAC >>
            metis_tac[FINITE_DIFF_down,FINITE_DEF])));

Theorem Gm_lw_BAG_MERGE
`!Γ₁ A. Gm Γ₁ A ==> !Γ₂. FINITE_BAG Γ₂ ==> Gm (BAG_MERGE Γ₂ Γ₁) A` (
  rw[] >>
  irule Gm_lw >>
  `FINITE_BAG Γ₁` by metis_tac[Gm_FINITE] >>
  simp[FINITE_BAG_MERGE] >>
  qexists_tac `Γ₁` >>
  simp[SUB_BAG,BAG_INN_BAG_MERGE]);

Theorem Gm_lw_BAG_UNION `∀Γ A. Gm Γ A ==> ∀Γ'. FINITE_BAG Γ'
                               ==> Gm (Γ ⊎ Γ') A` (
  rw[] >> 
  irule Gm_lw >>
  `FINITE_BAG Γ` by metis_tac[Gm_FINITE] >>
  simp[FINITE_BAG_UNION] >>
  qexists_tac `Γ` >> 
  simp[]);

Theorem Gm_lw_BAG_INSERT `∀Γ A. Gm Γ A ==> ∀B Γ'. Gm (BAG_INSERT B Γ) A` (
  rw[] >>
  irule Gm_lw >>
  `FINITE_BAG Γ` by metis_tac[Gm_FINITE] >>
  simp[FINITE_BAG_INSERT] >>
  qexists_tac `Γ` >>
  simp[SUB_BAG_INSERT_I]);

val _ = overload_on ("unibag", ``\b. BAG_OF_SET (SET_OF_BAG b)``);

val unibag_thm = CONJ BAG_OF_SET SET_OF_BAG;

Theorem unibag_INSERT `∀a b. (unibag (BAG_INSERT a b))
                       = BAG_MERGE {|a|} (unibag b)` (
    rw[BAG_OF_SET_INSERT,SET_OF_BAG_INSERT]);

Theorem unibag_UNION `∀a b. unibag (a ⊎ b) = BAG_MERGE (unibag a) (unibag b)` (
    rw[SET_OF_BAG_UNION,BAG_OF_SET_UNION]);

Theorem unibag_IN `∀e b. BAG_IN e b ==> BAG_IN e (unibag b)` (
    rw[IN_SET_OF_BAG,BAG_IN_BAG_OF_SET]);

Theorem unibag_EQ_BAG_INSERT 
`∀e b b'. (unibag b = BAG_INSERT e b') ==> ?c. (b' = unibag c)` (
    rw[] >>
    fs[unibag_thm,BAG_INSERT,FUN_EQ_THM,BAG_IN,BAG_INN] >>
    qexists_tac `b'` >>
    rw[] >>
    first_x_assum (qspec_then `x` mp_tac) >>
    rw[] >>
    Induct_on `b' e` >>
    rw[]);

Theorem unibag_FINITE `∀b. FINITE_BAG b = FINITE_BAG (unibag b)`
(rw[] >> EQ_TAC >> metis_tac[FINITE_SET_OF_BAG, FINITE_BAG_OF_SET]);

val Gm_lc_AeA =
    Q.prove(`∀A e Γ'. Gm (BAG_INSERT A (BAG_INSERT e (BAG_INSERT A Γ'))) B
            ==> Gm (BAG_INSERT e (BAG_INSERT A Γ')) B`,
            rw[] >>
            `Gm ({|A;A|} ⊎ ({|e|} ⊎ Γ')) B`
              by (fs[BAG_UNION_INSERT,ASSOC_BAG_UNION,BAG_INSERT_UNION] >>
                  simp[COMM_BAG_UNION] >>
                  fs[EL_BAG,BAG_UNION]) >>
            `Gm ({|A|} ⊎ ({|e|} ⊎ Γ')) B`
              by metis_tac[Gm_lc] >>
            `Gm (({|A|} ⊎ {|e|}) ⊎ Γ') B`
              by fs[ASSOC_BAG_UNION] >>
            `Gm (({|e|} ⊎ {|A|}) ⊎ Γ') B`
              by fs[COMM_BAG_UNION] >>
            fs[BAG_INSERT_UNION] >>
            fs[EL_BAG] >>
            simp[ASSOC_BAG_UNION]);

Theorem Gm_INSERT_TO_MERGE `∀Γ. FINITE_BAG Γ ==> ∀A B. Gm (BAG_INSERT A Γ) B
             ==> Gm (BAG_MERGE {|A|} Γ) B` (
    Induct_on `Γ` >>
    rw[]
    >- simp[BAG_MERGE_EMPTY] 
    >- (Cases_on `A=e`
        >- (fs[] >>
            `BAG_MERGE {|e|} (BAG_INSERT e Γ) = BAG_INSERT e Γ`
              by (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
                  rw[] >> fs[]) >>
            fs[] >>
            `Gm ({|e;e|} ⊎ Γ) B` by fs[BAG_INSERT_UNION,ASSOC_BAG_UNION] >>
            `Gm ({|e|} ⊎ Γ) B` by metis_tac[Gm_lc] >>
            `{|e|} ⊎ Γ = BAG_INSERT e Γ`
              by rw[BAG_INSERT_UNION] >>
            metis_tac[])

        >- (Cases_on `BAG_IN A Γ`
            >- (`?Γ'. Γ = BAG_INSERT A Γ'` by metis_tac[BAG_DECOMPOSE] >>
                fs[] >>
                `Gm (BAG_INSERT e (BAG_INSERT A Γ')) B` 
                  by metis_tac[Gm_lc_AeA] >>
                fs[Gm_lw_BAG_MERGE])
            >- (`BAG_INSERT A (BAG_INSERT e Γ)
                 = BAG_MERGE {|A|} (BAG_INSERT e Γ)`
                  by (`Γ A = 0` by metis_tac[NOT_BAG_IN] >>
                      simp[BAG_INSERT,BAG_MERGE,EMPTY_BAG,FUN_EQ_THM] >>
                      rw[] >>
                      fs[COND_CLAUSES]) >>
                fs[]))));


Theorem unibag_ALL_DISTINCT `∀b. BAG_ALL_DISTINCT (unibag b)` (
  rw[BAG_ALL_DISTINCT]);

Theorem unibag_IN `∀e b. BAG_IN e b ==> BAG_IN e (unibag b)` (
  rw[BAG_IN]);


Theorem unibag_EL_MERGE_cases `∀e b.
((BAG_IN e b) ==> (BAG_MERGE {|e|} (unibag b) = (unibag b)))
∧ (¬(BAG_IN e b) ==> (BAG_MERGE {|e|} (unibag b) = BAG_INSERT e (unibag b)))` (
  rw[]
    >- (`BAG_ALL_DISTINCT (unibag b)` by metis_tac[unibag_ALL_DISTINCT] >>
        `BAG_ALL_DISTINCT {|e|}` by simp[BAG_ALL_DISTINCT_THM] >>
        `BAG_ALL_DISTINCT (BAG_MERGE {|e|} (unibag b))`
          by simp[BAG_ALL_DISTINCT_BAG_MERGE] >>
        qspecl_then [`BAG_MERGE {|e|} (unibag b)`,`unibag b`] mp_tac
          BAG_ALL_DISTINCT_EXTENSION >>
        rw[] >>
        metis_tac[])
    >- (`BAG_ALL_DISTINCT (unibag b)` by metis_tac[unibag_ALL_DISTINCT] >>
        `BAG_ALL_DISTINCT {|e|}` by simp[BAG_ALL_DISTINCT_THM] >>
        `BAG_ALL_DISTINCT (BAG_MERGE {|e|} (unibag b))`
          by simp[BAG_ALL_DISTINCT_BAG_MERGE] >>
        `BAG_ALL_DISTINCT (BAG_INSERT e (unibag b))`
          by simp[BAG_ALL_DISTINCT] >>
        qspecl_then [`BAG_MERGE {|e|} (unibag b)`,`BAG_INSERT e (unibag b)`] 
          mp_tac BAG_ALL_DISTINCT_EXTENSION >>
        rw[]));

Theorem unibag_AA_EQ_A `unibag ({|A;A|} ⊎ Γ) = unibag ({|A|} ⊎ Γ)` (
  simp[unibag_thm]);

Theorem unibag_DECOMPOSE `unibag Γ ≠ Γ ==> ?A Γ0. Γ = {|A;A|} ⊎ Γ0` (
  simp[unibag_thm] >>
  simp[SimpL ``$==>``,FUN_EQ_THM,PULL_EXISTS] >>
  rw[]
    >- (qexists_tac `x` >>
        qexists_tac `Γ (| x |-> Γ x - 2 |)` >>
        fs[BAG_IN,BAG_INN] >>
        simp[FUN_EQ_THM,BAG_UNION,
             BAG_INSERT,EMPTY_BAG,combinTheory.APPLY_UPDATE_THM] >>
        qx_gen_tac `y` >>
        Cases_on `x=y` >> 
        rw[])
    >- fs[BAG_IN,BAG_INN]);

Theorem unibag_SUB_BAG `∀b. unibag b ≤ b` 
(rw[unibag_thm,SUB_BAG,BAG_IN,BAG_INN]);

Theorem Gm_unibag `∀Γ A. Gm Γ A <=> Gm (unibag Γ) A` (
rw[] >> EQ_TAC
  >- (`∀Γ. FINITE_BAG Γ ==> ∀A. Gm Γ A ==> Gm (unibag Γ) A` 
        suffices_by metis_tac[Gm_FINITE] >>
      gen_tac >>
      Induct_on `BAG_CARD Γ` >>
      rw[]
        >- (`Γ = {||}` by metis_tac[BCARD_0] >>
            fs[])
        >- (Cases_on `unibag Γ = Γ` >- fs[] >>
            drule_then strip_assume_tac unibag_DECOMPOSE >>
            rename [`Γ = {|B;B|} ⊎ Γ0`,`SUC n = BAG_CARD Γ`] >>
            `Gm ({|B|} ⊎ Γ0) A` by metis_tac[Gm_lc] >>
            `BAG_CARD ({|B|} ⊎ Γ0) = n` by fs[BAG_CARD_THM] >>
            `FINITE_BAG ({|B|} ⊎ Γ0)` by fs[] >>
            metis_tac[unibag_AA_EQ_A]))
   >- metis_tac[unibag_SUB_BAG,Gm_lw,Gm_FINITE,unibag_FINITE]);

Theorem Nm_Gm `∀Γ A. Nm Γ A ==> Gm (BAG_OF_SET Γ) A` (
 Induct_on `Nm ` >>
 rw[Gm_rules]
 >- (irule Gm_ax >> simp[] >>
     metis_tac[FINITE_BAG_OF_SET,FINITE_DEF])
 >- (irule Gm_rand >> conj_tac
     >- (`Gm (BAG_OF_SET (Γ' ∪ Γ)) A` suffices_by metis_tac[UNION_COMM] >>
         simp[BAG_OF_SET_UNION] >>
         metis_tac[Gm_lw_BAG_MERGE,Gm_FINITE])
     >- (simp[BAG_OF_SET_UNION] >>
             metis_tac[Gm_lw_BAG_MERGE,Gm_FINITE]))
 >- (`Gm {|A|} A` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     `Gm {|A And B|} A` by metis_tac[Gm_landl] >>
     `Gm ((BAG_OF_SET Γ) + {||}) A` by metis_tac[Gm_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (`Gm {|A'|} A'` by metis_tac[Gm_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     `Gm {|A And A'|} A'` by metis_tac[Gm_landr] >>
     `Gm ((BAG_OF_SET Γ) + {||}) A'` by metis_tac[Gm_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (irule Gm_rimp >>
     fs[BAG_OF_SET_INSERT] >>
     irule Gm_lw >>
     simp[] >>
     drule Gm_FINITE >>
     rw[] >>
     qexists_tac `BAG_MERGE {|A|} (BAG_OF_SET Γ)` >>
     simp[BAG_MERGE_ELBAG_SUB_BAG_INSERT])
 >- (simp[BAG_OF_SET_UNION] >>
    `FINITE_BAG (BAG_OF_SET Γ')` by metis_tac[Nm_FINITE,FINITE_BAG_OF_SET] >>
    `Gm (BAG_INSERT A' (BAG_OF_SET Γ')) A'`
      by simp[Gm_ax,BAG_IN_BAG_INSERT] >>
    `Gm (BAG_INSERT (A Imp A') (BAG_OF_SET Γ')) A'`
      by metis_tac[Gm_limp] >>
    `Gm ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ')) A'`
      by metis_tac[Gm_cut] >>
    `Gm (unibag (BAG_OF_SET Γ ⊎ BAG_OF_SET Γ')) A'` by metis_tac[Gm_unibag] >>
    fs[unibag_UNION])
  >- (fs[BAG_OF_SET_INSERT] >>
      `FINITE_BAG (BAG_INSERT A (BAG_OF_SET Γ))` 
        by metis_tac[Nm_FINITE,FINITE_BAG_OF_SET,FINITE_BAG_INSERT] >>
      `Gm (BAG_INSERT A (BAG_OF_SET Γ)) A'`
        by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gm_lw] >>
      `FINITE_BAG (BAG_INSERT B (BAG_OF_SET Γ))` 
        by metis_tac[Nm_FINITE,FINITE_BAG_OF_SET,FINITE_BAG_INSERT] >>
      `Gm (BAG_INSERT B (BAG_OF_SET Γ)) A'`
        by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gm_lw] >>
      `Gm (BAG_INSERT (A Or B) (BAG_OF_SET Γ)) A'` by metis_tac[Gm_lor] >>
      `Gm ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ)) A'` by metis_tac[Gm_cut] >>
      `Gm (unibag (BAG_OF_SET Γ ⊎ BAG_OF_SET Γ)) A'` by metis_tac[Gm_unibag] >>
      fs[unibag_UNION]));

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

Theorem Nm_lw_SUBSET `∀D'. FINITE D' ==> ∀D A. Nm D A  /\ D ⊆ D' ==> Nm D' A` (
 GEN_TAC >>
 Induct_on `CARD D'`
   >- (rw[] >>
       metis_tac[CARD_EQ_0,SUBSET_EMPTY])
   >- (rw[] >>
       Cases_on `D=D'`
         >- metis_tac[]
         >- (`?D₀ e. (D' = e INSERT D₀) /\ D ⊆ D₀ /\ e NOTIN D₀`
               by (`?e. e ∈ D' /\ e NOTIN D`
                   by metis_tac[PSUBSET_DEF,PSUBSET_MEMBER] >>
                   qexists_tac `D' DELETE e` >>
                   qexists_tac `e` >>
                   simp[] >>
                   fs[SUBSET_DEF]) >>
             rw[] >>
             fs[] >>
             metis_tac[Nm_lw])));

Theorem Nm_impi_DELETE `∀D A B. Nm D A ==> Nm (D DELETE B) (B Imp A)` (
  rw[] >>
  `Nm (B INSERT D) A` by metis_tac[Nm_lw] >>
  Cases_on `B ∈ D`
    >- (`?D'. (D = B INSERT D') /\ B NOTIN D'`
          by metis_tac[DECOMPOSITION] >>
        fs[] >>
        `(B INSERT D') DELETE B = D'`
          by (dsimp[EXTENSION] >>
              metis_tac[]) >>
        simp[Nm_impi])
>- (simp[DELETE_NON_ELEMENT_RWT,Nm_impi]));

(* Apparently Nm takes a subset here!? *)
Theorem Gm_Nm `∀Γ A. Gm Γ A ==> ?Γ'. Γ' ⊆ (SET_OF_BAG Γ) /\ Nm Γ' A` (
  Induct_on `Gm` >> rw[]
    >- (qexists_tac `{A}` >> simp[SUBSET_DEF,SET_OF_BAG] >> metis_tac[Nm_ax])
    >- (qexists_tac `Γ'` >> fs[SET_OF_BAG,BAG_UNION,BAG_INSERT])
    >- (rename [`Nm _ C`] >>
        `Nm {A And B} (A And B)` by metis_tac[Nm_ax] >>
        `Nm {A And B} A` by metis_tac[Nm_andel] >>
        `Nm (Γ' DELETE A) (A Imp C)`
          by metis_tac[Nm_impi_DELETE] >>
        `Nm ((Γ' DELETE A) ∪ {A And B}) C` by metis_tac[Nm_impe] >>
        `Nm ((A And B) INSERT (Γ' DELETE A)) C`
                  by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(A And B) INSERT Γ' DELETE A` >>
        fs[SET_OF_BAG_INSERT] >>
        fs[SUBSET_DEF] >>
        metis_tac[])
    >- (rename [`Nm _ C`] >>
        `Nm {A And B} (A And B)` by metis_tac[Nm_ax] >>
        `Nm {A And B} B` by metis_tac[Nm_ander] >>
        `Nm (B INSERT Γ') C` by metis_tac[Nm_lw] >>
        `Nm (Γ' DELETE B) (B Imp C)`
          by (Cases_on `B ∈ Γ'`
              >- (`?Γ0. (Γ' = B INSERT Γ0) /\ B NOTIN Γ0`
                    by metis_tac[DECOMPOSITION] >>
                  fs[] >>
                  `(B INSERT Γ0) DELETE B = Γ0`
                    by (dsimp[EXTENSION] >>
                        metis_tac[]) >>
                  simp[Nm_impi])
              >- (simp[DELETE_NON_ELEMENT_RWT,Nm_impi])) >>
        `Nm ((Γ' DELETE B) ∪ {A And B}) C` by metis_tac[Nm_impe] >>
        `Nm ((A And B) INSERT (Γ' DELETE B)) C`
          by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(A And B) INSERT Γ' DELETE B` >>
        fs[SET_OF_BAG_INSERT] >>
        fs[SUBSET_DEF] >>
        metis_tac[])
    >- (qexists_tac `Γ' ∪ Γ''` >> simp[] >>
        metis_tac[Nm_andi])
    >- (rename [`Nm _ C`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gm_FINITE,FINITE_BAG_INSERT] >>
        `Nm (A INSERT ((A Or B) INSERT (SET_OF_BAG Γ))) C`
          by (irule Nm_lw_SUBSET >>
              simp[] >>
              qexists_tac `Γ'` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        `Nm (B INSERT ((A Or B) INSERT (SET_OF_BAG Γ))) C`
          by (irule Nm_lw_SUBSET >>
              simp[] >>
              qexists_tac `Γ''` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        qexists_tac `(A Or B) INSERT (SET_OF_BAG Γ)` >>
        simp[SUBSET_INSERT_RIGHT] >>
        `Nm {(A Or B)} (A Or B)` by metis_tac[Nm_ax] >>
        `FINITE ({A Or B} ∪ (SET_OF_BAG Γ))`
          by (`FINITE (SET_OF_BAG Γ)` 
                by metis_tac[FINITE_SET_OF_BAG] >>
              metis_tac[FINITE_UNION,FINITE_DEF]) >>
        `Nm ({A Or B} ∪ (SET_OF_BAG Γ)) (A Or B)`
          by metis_tac[SUBSET_UNION,Nm_lw_SUBSET] >>
        `Nm ((A Or B) INSERT (SET_OF_BAG Γ)) (A Or B)`
          by metis_tac[INSERT_SING_UNION] >>
        metis_tac[Nm_ore])
    >- (qexists_tac `Γ'` >> simp[Nm_orir])
    >- (qexists_tac `Γ'` >> simp[Nm_oril])
    >- (rename [`Nm _ C`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gm_FINITE,FINITE_BAG_INSERT] >>
        `FINITE (SET_OF_BAG Γ)` by metis_tac[FINITE_SET_OF_BAG] >>
        `Nm {A Imp B} (A Imp B)` by metis_tac[Nm_ax] >>
        `Nm (SET_OF_BAG Γ) A` by metis_tac[Nm_lw_SUBSET] >>
        `Nm ({A Imp B} ∪ (SET_OF_BAG Γ)) B` by metis_tac[Nm_impe] >>
        `Nm ((A Imp B) INSERT (SET_OF_BAG Γ)) B`
          by metis_tac[INSERT_SING_UNION] >>
        qexists_tac `(A Imp B) INSERT SET_OF_BAG Γ` >>
        simp[SUBSET_INSERT_RIGHT] >>
        `Nm (B INSERT (SET_OF_BAG Γ)) C` 
          by metis_tac[Nm_lw_SUBSET,FINITE_INSERT] >>
        `Nm (SET_OF_BAG Γ) (B Imp C)` by metis_tac[Nm_impi] >>
        `Nm ((SET_OF_BAG Γ) ∪ ((A Imp B) INSERT SET_OF_BAG Γ)) C` 
          by metis_tac[Nm_impe] >>
        metis_tac[UNION_COMM,UNION_ASSOC,UNION_IDEMPOT,INSERT_SING_UNION])
    >- (rename [`Nm Δ C`,`Nm _ (A Imp C)`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE (A INSERT (SET_OF_BAG Γ))` 
          by (simp[] >> metis_tac[Gm_FINITE,FINITE_BAG_INSERT]) >>
        `Nm (A INSERT (SET_OF_BAG Γ)) C` by metis_tac[Nm_lw_SUBSET] >>
        `Nm (SET_OF_BAG Γ) (A Imp C)` by metis_tac[Nm_impi] >>
        metis_tac[SUBSET_REFL])
    >- (rename [`Gm Γ A`,`Gm (BAG_INSERT A Γ2) B`,`Nm Δ1 A`,`Nm Δ2 B`] >>
        `Nm (A INSERT Δ2) B` by metis_tac[Nm_lw] >>
        `Nm (Δ2 DELETE A) (A Imp B)` by metis_tac[Nm_impi_DELETE] >>
        `Nm ((Δ2 DELETE A) ∪ Δ1) B` by metis_tac[Nm_impe] >>
        qexists_tac `((Δ2 DELETE A) ∪ Δ1)` >>
        rw[]
          >- (irule SUBSET_TRANS >>
              qexists_tac `(SET_OF_BAG Γ2)` >>
              fs[SET_OF_BAG_INSERT,SET_OF_BAG_UNION] >>
              fs[SUBSET_DEF] >>
              metis_tac[])
          >- (fs[SET_OF_BAG_UNION] >>
              metis_tac[SUBSET_DEF,IN_UNION])
));

Theorem Gm_iff_Nm
`∀Γ A. Gm Γ A <=> Nm (SET_OF_BAG Γ) A` (
  rw[] >>
  EQ_TAC 
    >- (rw[] >>
      `?D. D ⊆ (SET_OF_BAG Γ) ∧ Nm D A` by metis_tac[Gm_Nm] >>
      metis_tac[Nm_lw_SUBSET,Gm_FINITE,FINITE_SET_OF_BAG]) >>
  rw[] >>
  `Gm (unibag Γ) A` by metis_tac[Nm_Gm] >>
  metis_tac[Gm_unibag]);

val _ = export_theory()
