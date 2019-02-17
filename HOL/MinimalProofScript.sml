
(* ========================================================================== *)
(* Equivalence of Sequent Calculus and Natural Deduction                      *)
(* Working from Troelstra and Schwichtenburg - Basic Proof Theory 2nd Edition *)
(*                                                                            *)
(* ========================================================================== *)

open HolKernel boolLib Parse bossLib;
open bagTheory;
open pred_setTheory;

open FormulaSyntaxTheory;
open BagLemmataTheory;

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
/\ (!A B C D D1 D2. (Nm D (A Or B)) /\
(Nm (A INSERT D1) C) /\ (Nm (B INSERT D2) C) ==> Nm (D ∪ D1 ∪ D2) C)`; (* Or Elim *)

val [Nm_ax, Nm_andi, Nm_andel, Nm_ander,
     Nm_impi, Nm_impe, Nm_orir, Nm_oril, Nm_ore] = CONJUNCTS Nm_rules;

Theorem Nm_FINITE:
  !D A. Nm D A ==> FINITE D
Proof Induct_on `Nm` >> rw[]
QED

val (Nmd_rules, Nmd_ind, Nmd_cases) = Hol_reln `
(! (A :'a formula). Nmd {A} A) (* Base case *)
/\ (!A B D1 D2. (Nmd D1 A) /\ (Nmd D2 B)
                             ==> (Nmd (D1 UNION D2) (A And B))) (* And Intro *)
/\ (!A B D. (Nmd D (A And B)) ==> Nmd D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Nmd D (A And B)) ==> Nmd D B) (* And Elim Right Conjunct *)
/\ (!A B D. (Nmd D B) ==> Nmd (D DELETE A) (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Nmd D1 (A Imp B)) /\ (Nmd D2 A) ==> 
                 Nmd (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Nmd D A ==> Nmd D (A Or B)) (* Or Intro right *)
/\ (!A B D. Nmd D B ==> Nmd D (A Or B)) (* Or Intro left *)
/\ (!A B C D D1 D2. (Nmd D (A Or B)) /\ (Nmd D1 C) /\ (Nmd D2 C) ==>
    Nmd (D ∪ (D1 DELETE A) ∪ (D2 DELETE B)) C)`; (* Or Elim *)

val [Nmd_ax, Nmd_andi, Nmd_andel, Nmd_ander,
     Nmd_impi, Nmd_impe, Nmd_orir, Nmd_oril, Nmd_ore] = CONJUNCTS Nmd_rules;

Theorem Nm_lw:
  ∀D A. Nm D A ==> ∀B. Nm (B INSERT D) A
Proof
  rw[] >>
  `Nm {B} B` by metis_tac[Nm_ax] >>
  `Nm ({B} ∪ D) (B And A)` by metis_tac[Nm_andi] >>
  `Nm ({B} ∪ D) A` by metis_tac[Nm_ander] >>
  metis_tac[INSERT_SING_UNION]
QED

Theorem Nmd_lw:
  ∀D A. Nmd D A ==> ∀B. Nmd (B INSERT D) A
Proof
  rw[] >>
  `Nmd {B} B` by metis_tac[Nmd_ax] >>
  `Nmd ({B} ∪ D) (B And A)` by metis_tac[Nmd_andi] >>
  `Nmd ({B} ∪ D) A` by metis_tac[Nmd_ander] >>
  metis_tac[INSERT_SING_UNION]
QED

Theorem Nm_lw_SUBSET:
  ∀D'. FINITE D' ==> ∀D A. Nm D A  /\ D ⊆ D' ==> Nm D' A
Proof
  GEN_TAC >>
  Induct_on `CARD D'`
  >- (rw[] >> metis_tac[CARD_EQ_0,SUBSET_EMPTY])
  >- (rw[] >> Cases_on `D=D'` >- metis_tac[] >>
      `?D₀ e. (D' = e INSERT D₀) /\ D ⊆ D₀ /\ e NOTIN D₀`
        by (`?e. e ∈ D' /\ e NOTIN D`
              by metis_tac[PSUBSET_DEF,PSUBSET_MEMBER] >>
              qexists_tac `D' DELETE e` >>
              qexists_tac `e` >>
              simp[] >>
              fs[SUBSET_DEF]) >>
            rw[] >>
            fs[] >>
            metis_tac[Nm_lw])
QED

Theorem Nmd_lw_SUBSET:
  ∀D'. FINITE D' ==> ∀D A. Nmd D A  /\ D ⊆ D' ==> Nmd D' A
Proof
  GEN_TAC >>
  Induct_on `CARD D'`
  >- (rw[] >> metis_tac[CARD_EQ_0,SUBSET_EMPTY])
  >- (rw[] >> Cases_on `D=D'` >- metis_tac[] >>
      `?D₀ e. (D' = e INSERT D₀) /\ D ⊆ D₀ /\ e NOTIN D₀`
        by (`?e. e ∈ D' /\ e NOTIN D`
              by metis_tac[PSUBSET_DEF,PSUBSET_MEMBER] >>
              qexists_tac `D' DELETE e` >>
              qexists_tac `e` >>
              simp[] >>
              fs[SUBSET_DEF]) >>
            rw[] >>
            fs[] >>
            metis_tac[Nmd_lw])
QED

Theorem Nm_impi_DELETE:
  ∀D A B. Nm D A ==> Nm (D DELETE B) (B Imp A)
Proof
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
    >- simp[DELETE_NON_ELEMENT_RWT,Nm_impi]
QED

Theorem Nm_Nmd:
  ∀D A. Nm D A <=> Nmd D A
Proof
 `(∀D A:'a formula. Nm D A ==> Nmd D A) ∧
  (∀D A:'a formula. Nmd D A ==> Nm D A)`
    suffices_by metis_tac[] >>
  conj_tac
  >- (Induct_on `Nm` >>
      rw[Nmd_rules]
        >- metis_tac[Nmd_andel]
        >- metis_tac[Nmd_ander]
        >- (`Nmd ((A INSERT D) DELETE A) (A Imp B)`
              by metis_tac[Nmd_impi] >>
            Cases_on `A ∈ D`
              >- (fs[DELETE_DEF] >>
                  `Nmd (A INSERT (D DIFF {A})) (A Imp B)`
                    by metis_tac[Nmd_lw] >>
                  fs[Once INSERT_SING_UNION] >>
                  `{A} ⊆ D` by simp[SUBSET_DEF] >>
                  metis_tac[UNION_DIFF])
              >- fs[DELETE_DEF,DELETE_NON_ELEMENT])
        >- metis_tac[Nmd_impe]
        >- (`Nmd (D ∪ ((A INSERT D1) DELETE A) ∪ ((B INSERT D2) DELETE B)) C`
              by metis_tac[Nmd_ore] >>
            fs[DELETE_DEF] >>
            irule Nmd_lw_SUBSET >>
            `FINITE (D ∪ D1 ∪ D2)`
              by (simp[FINITE_UNION] >> metis_tac[Nm_FINITE,FINITE_INSERT]) >>
            simp[] >>
            qexists_tac `D ∪ (D1 DIFF {A}) ∪ (D2 DIFF {B})` >>
            rw[SUBSET_DEF]))
  >- (Induct_on `Nmd` >>
      rw[Nm_rules]
        >- metis_tac[Nm_andel]
        >- metis_tac[Nm_ander]
        >- metis_tac[Nm_impi_DELETE]
        >- metis_tac[Nm_impe]
        >- (`Nm (A INSERT (D1 DELETE A)) C`
              by (irule Nm_lw_SUBSET >>
                  rw[] >- metis_tac[Nm_FINITE] >>
                  qexists_tac `D1` >>
                  rw[DELETE_DEF,SUBSET_DEF]) >>
            `Nm (B INSERT (D2 DELETE B)) C`
              by (irule Nm_lw_SUBSET >>
                  rw[] >- metis_tac[Nm_FINITE] >>
                  qexists_tac `D2` >>
                  rw[DELETE_DEF,SUBSET_DEF]) >>
            metis_tac[Nm_ore]))
QED

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
∧  (∀A B Γ Δ. (Gm Γ A) ∧ (Gm (BAG_INSERT A Δ) B) ==> Gm (Γ + Δ) B)` (* Cut *)

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
Theorem Gm_FINITE:
  !D A. Gm D A ==> FINITE_BAG D
Proof Induct_on `Gm` >> rw[]
QED

(* Thanks for this theorem Michael *)
Theorem Gm_lw:
  ∀Γ A. Gm Γ A ⇒ ∀Γ'. Γ ≤ Γ' /\ FINITE_BAG Γ' ⇒ Gm Γ' A
Proof
  Induct_on `Gm` >> rw[]
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
      conj_tac >> first_x_assum irule >> fs[SUB_BAG_INSERT])
QED

Theorem Gm_lw_BAG_MERGE:
  !Γ₁ A. Gm Γ₁ A ==> !Γ₂. FINITE_BAG Γ₂ ==> Gm (BAG_MERGE Γ₂ Γ₁) A
Proof
  rw[] >>
  irule Gm_lw >>
  `FINITE_BAG Γ₁` by metis_tac[Gm_FINITE] >>
  simp[FINITE_BAG_MERGE] >>
  qexists_tac `Γ₁` >>
  simp[SUB_BAG,BAG_INN_BAG_MERGE]
QED

Theorem Gm_lw_BAG_UNION:
  ∀Γ A. Gm Γ A ==> ∀Γ'. FINITE_BAG Γ' ==> Gm (Γ ⊎ Γ') A
Proof
  rw[] >>
  irule Gm_lw >>
  `FINITE_BAG Γ` by metis_tac[Gm_FINITE] >>
  simp[FINITE_BAG_UNION] >>
  qexists_tac `Γ` >>
  simp[]
QED

Theorem Gm_lw_BAG_INSERT:
  ∀Γ A. Gm Γ A ==> ∀B Γ'. Gm (BAG_INSERT B Γ) A
Proof
  rw[] >>
  irule Gm_lw >>
  `FINITE_BAG Γ` by metis_tac[Gm_FINITE] >>
  simp[FINITE_BAG_THM] >>
  qexists_tac `Γ` >>
  simp[SUB_BAG_INSERT_I]
QED

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

Theorem Gm_INSERT_TO_MERGE:
  ∀Γ. FINITE_BAG Γ ==>
  ∀A B. Gm (BAG_INSERT A Γ) B ==> Gm (BAG_MERGE {|A|} Γ) B
Proof
    Induct_on `Γ` >>
    rw[] >>
    Cases_on `A=e`
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
              fs[]))
QED

val unibag_AA_A = Q.prove(`unibag ({|A;A|} ⊎ Γ) = unibag ({|A|} ⊎ Γ)`,
simp[unibag_thm])


Theorem Gm_unibag:
  ∀Γ A. Gm Γ A <=> Gm (unibag Γ) A
Proof
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
              metis_tac[unibag_AA_A]))
    >- metis_tac[unibag_SUB_BAG,Gm_lw,Gm_FINITE,unibag_FINITE]
QED

Theorem Nm_Gm:
  ∀Γ A. Nm Γ A ==> Gm (BAG_OF_SET Γ) A
Proof
 Induct_on `Nm` >>
 rw[Gm_rules]
 (* >- (irule Gm_ax >> simp[] >> *)
 (*     metis_tac[FINITE_BAG_OF_SET,FINITE_DEF]) *)
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
 >- (rename [`Nm (_ INSERT _) C`] >>
     fs[BAG_OF_SET_UNION,BAG_OF_SET_INSERT] >>
     qabbrev_tac `Δ = ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET D1) ⊎ (BAG_OF_SET D2))` >>
     `FINITE_BAG (BAG_INSERT A Δ)`
       by (simp[Abbr`Δ`,FINITE_BAG_THM] >>
           metis_tac[FINITE_BAG_OF_SET,Nm_FINITE,FINITE_INSERT]) >>
      `Gm (BAG_INSERT A Δ) C`
        by (`Gm (BAG_MERGE {|A|} Δ) C`
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gm_lw] >>
            simp[Abbr`Δ`] >>
            irule Gm_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_THM] >>
            qexists_tac `BAG_MERGE {|A|} (BAG_OF_SET D1)` >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      `FINITE_BAG (BAG_INSERT B Δ)`
      by (simp[Abbr`Δ`,FINITE_BAG_THM] >>
              metis_tac[FINITE_BAG_OF_SET,Nm_FINITE,FINITE_INSERT]) >>
      `Gm (BAG_INSERT B Δ) C`
        by (`Gm (BAG_MERGE {|B|} Δ) C`
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gm_lw] >>
            simp[Abbr`Δ`] >>
            irule Gm_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_THM] >>
            qexists_tac `BAG_MERGE {|B|} (BAG_OF_SET D2)` >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      `Gm Δ (A Or B)`
        by (simp[Abbr`Δ`] >>
            irule Gm_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,Nm_FINITE,FINITE_BAG_OF_SET] >>
            irule Gm_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,Nm_FINITE,FINITE_BAG_OF_SET] >>
            metis_tac[]) >>
      `Gm (BAG_INSERT (A Or B) Δ) C` by metis_tac[Gm_lor] >>
      `Gm ((BAG_OF_SET Γ) ⊎ Δ) C` by metis_tac[Gm_cut] >>
      `Gm (unibag (BAG_OF_SET Γ ⊎ Δ)) C` by metis_tac[Gm_unibag] >>
      `(unibag (BAG_OF_SET Γ ⊎ Δ))
        = BAG_MERGE (BAG_MERGE (BAG_OF_SET Γ) (BAG_OF_SET D1)) (BAG_OF_SET D2)`
         suffices_by metis_tac[] >>
      rw[Abbr`Δ`,unibag_UNION,BAG_MERGE,FUN_EQ_THM])
QED

(* Apparently Nm takes a subset here!? *)
Theorem Gm_Nm:
  ∀Γ A. Gm Γ A ==> ?Γ'. Γ' ⊆ (SET_OF_BAG Γ) /\ Nm Γ' A
Proof
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
        qabbrev_tac `Δ = (A Or B) INSERT (SET_OF_BAG Γ)` >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gm_FINITE,FINITE_BAG_THM] >>
        `Nm (A INSERT Δ) C`
          by (irule Nm_lw_SUBSET >>
              simp[Abbr`Δ`] >>
              qexists_tac `Γ'` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        `Nm (B INSERT Δ) C`
          by (irule Nm_lw_SUBSET >>
              simp[Abbr`Δ`] >>
              qexists_tac `Γ''` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        qexists_tac `Δ` >>
        simp[] >>
        `Nm {(A Or B)} (A Or B)` by metis_tac[Nm_ax] >>
        `FINITE ({A Or B} ∪ (SET_OF_BAG Γ))`
          by (`FINITE (SET_OF_BAG Γ)`
                by metis_tac[FINITE_SET_OF_BAG] >>
              metis_tac[FINITE_UNION,FINITE_DEF]) >>
        `Nm ({A Or B} ∪ (SET_OF_BAG Γ)) (A Or B)`
          by metis_tac[SUBSET_UNION,Nm_lw_SUBSET] >>
        `Nm Δ (A Or B)`
          by (simp[Abbr`Δ`] >>metis_tac[INSERT_SING_UNION]) >>
        `Nm (Δ ∪ Δ ∪ Δ) C` by metis_tac[Nm_ore] >>
        metis_tac[UNION_IDEMPOT])
    >- (qexists_tac `Γ'` >> simp[Nm_orir])
    >- (qexists_tac `Γ'` >> simp[Nm_oril])
    >- (rename [`Nm _ C`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gm_FINITE,FINITE_BAG_THM] >>
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
          by (simp[] >> metis_tac[Gm_FINITE,FINITE_BAG_THM]) >>
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
              metis_tac[SUBSET_DEF,IN_UNION]))
QED

Theorem Gm_iff_Nm:
∀Γ A. Gm Γ A <=> Nm (SET_OF_BAG Γ) A
Proof
  rw[] >>
  EQ_TAC
    >- (rw[] >>
      `?D. D ⊆ (SET_OF_BAG Γ) ∧ Nm D A` by metis_tac[Gm_Nm] >>
      metis_tac[Nm_lw_SUBSET,Gm_FINITE,FINITE_SET_OF_BAG]) >>
  rw[] >>
  `Gm (unibag Γ) A` by metis_tac[Nm_Gm] >>
  metis_tac[Gm_unibag]
QED

val _ = set_fixity "Nm" (Infix (NONASSOC, 320));
val _ = set_fixity "Nmd" (Infix (NONASSOC, 320));
val _ = set_fixity "Gm" (Infix (NONASSOC, 320));
val _ = set_fixity "BAG_MERGE" (Infix (NONASSOC, 330));
(* val _ = set_fixity "BAG_INSERT" (Infixl 330); *)

val _ = export_theory()
