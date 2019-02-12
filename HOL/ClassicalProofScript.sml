
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

val _ = new_theory "IntuitionisticProof";

(** Natural Deduction for classical logic **)
(* Nc is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* D, D1, D2, D3 are used to represent the set of open assumptions *)
(* I'm representing the deductions simply with unlabeled sets of
   open assumptions, as in T&S 2.1.8-2.1.9 (p.41--44) *)

val (Nc_rules, Nc_ind, Nc_cases) = Hol_reln `
(! (A :'a formula). Nc {A} A) (* Base case *)
/\ (!A B D1 D2. (Nc D1 A) /\ (Nc D2 B)
   ==> (Nc (D1 UNION D2) (A And B))) (* And Intro *)
/\ (!A B D. (Nc D (A And B)) ==> Nc D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Nc D (A And B)) ==> Nc D B) (* And Elim Right Conjunct *)
/\ (!A B D. (Nc (A INSERT D) B) ==> Nc D (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Nc D1 (A Imp B)) /\ (Nc D2 A)
   ==> Nc (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Nc D A ==> Nc D (A Or B))  (* Or Intro right *)
/\ (!A B D. Nc D B ==> Nc D (A Or B))  (* Or Intro left *)
/\ (!A B C D D1 D2. (Nc D (A Or B)) /\ (* Or Elim *)
(Nc (A INSERT D1) C) /\ (Nc (B INSERT D2) C) ==> Nc (D ∪ D1 ∪ D2) C)
/\ (!A D. (Nc ((Not A) INSERT D) Bot) ==> (Nc D A))`; (* Intuitionistic Absurdity Rule *)

val [Nc_ax, Nc_andi, Nc_andel, Nc_ander,
     Nc_impi, Nc_impe, Nc_orir, Nc_oril, Nc_ore, Nc_bot] = CONJUNCTS Nc_rules;

Theorem Nc_FINITE `!D A. Nc D A ==> FINITE D` (Induct_on `Nc` >> rw[])

Theorem Nc_lw `∀D A. Nc D A ==> ∀B. Nc (B INSERT D) A` (
  rw[] >>
`Nc {B} B` by metis_tac[Nc_ax] >>
`Nc ({B} ∪ D) (B And A)` by metis_tac[Nc_andi] >>
`Nc ({B} ∪ D) A` by metis_tac[Nc_ander] >>
metis_tac[INSERT_SING_UNION]);

Theorem Nc_lw_SUBSET `∀D'. FINITE D' ==> ∀D A. Nc D A  /\ D ⊆ D' ==> Nc D' A` (
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
metis_tac[Nc_lw])));
Theorem Nc_impi_DELETE `∀D A B. Nc D A ==> Nc (D DELETE B) (B Imp A)` (
  rw[] >>
  `Nc (B INSERT D) A` by metis_tac[Nc_lw] >>
  Cases_on `B ∈ D`
    >- (`?D'. (D = B INSERT D') /\ B NOTIN D'`
          by metis_tac[DECOMPOSITION] >>
        fs[] >>
        `(B INSERT D') DELETE B = D'`
          by (dsimp[EXTENSION] >>
              metis_tac[]) >>
        simp[Nc_impi])
    >- simp[DELETE_NON_ELEMENT_RWT,Nc_impi]);

val NcThm = Define `NcThm A = Nc EMPTY A`;

(* Example deductions *)
val Nc_example = Q.prove(`NcThm (A Imp (B Imp A))`,
`Nc {A} A` by rw[Nc_ax] >>
`Nc {B} B` by rw[Nc_ax] >>
`{A} UNION {B} = {A;B}` by simp[UNION_DEF,INSERT_DEF] >>
`Nc {A;B} (A And B)` by metis_tac[Nc_andi] >>
`Nc {A;B} (A)` by metis_tac[Nc_andel] >>
`Nc {A} (B Imp A)` by (irule Nc_impi >> simp[INSERT_COMM]) >>
`Nc {} (A Imp (B Imp A))` by metis_tac[Nc_impi] >>
 rw[NcThm]);

val Nc_example = Q.prove(`NcThm (Bot Imp A)`,
  `Nc {Bot} Bot` by rw[Nc_rules] >>
  `Nc {Bot} A` by rw[Nc_rules] >>
  `{} = ({Bot} DIFF {Bot})` by rw[DIFF_DEF] >>
  `Nc EMPTY (Bot Imp A)` by metis_tac[Nc_rules] >>
  rw[NcThm]);


(** Sequent Calculus (Gentzen System) for classical logic **)
(* Gc is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* S is used to represent the multiset of the Antecedent Context *)
(* The consequent is a multiset of formula in the classical logic *)

val (Gc_rules, Gc_ind, Gc_cases) = Hol_reln `
(!(A:'a formula) Γ. (A <: Γ) /\ FINITE_BAG Γ ==> Gc Γ A) (* Ax *)
/\ (∀ A Γ. (Bot <: Γ) /\ FINITE_BAG Γ ==> Gc Γ A) (* LBot *)
/\ (!A Γ C. (Gc ({|A;A|} + Γ) C)
   ==> Gc ({|A|} + Γ) C) (* Left Contraction *)
/\ (!A B Γ C. (Gc (BAG_INSERT A Γ) C)
   ==> (Gc (BAG_INSERT (A And B) Γ) C)) (* Left And 1 *)
/\ (!A B Γ C. (Gc (BAG_INSERT B Γ) C)
   ==> (Gc (BAG_INSERT (A And B) Γ) C)) (* Left And 2 *)
/\ (!A B Γ. (Gc Γ A) /\ (Gc Γ B)
   ==> (Gc Γ (A And B))) (* Right And *)
/\ (!A B Γ C. (Gc (BAG_INSERT A Γ) C)
    /\ (Gc (BAG_INSERT B Γ) C)
   ==> (Gc (BAG_INSERT (A Or B) Γ) C)) (* Left Or *)
/\ (!A B Γ. (Gc Γ A)
   ==> (Gc Γ (A Or B))) (* Right Or 1 *)
/\ (!A B Γ. (Gc Γ B)
   ==> (Gc Γ (A Or B))) (* Right Or 2 *)
/\ (!A B Γ C. (Gc Γ A) /\ (Gc (BAG_INSERT B Γ) C)
   ==> (Gc (BAG_INSERT (A Imp B) Γ) C)) (* Left Imp *)
/\ (!A B Γ. (Gc (BAG_INSERT A Γ) B)
   ==> (Gc Γ (A Imp B))) (* Right Imp *)
∧  (∀A B Γ Γ'. (Gc Γ A) ∧ (Gc (BAG_INSERT A Γ') B) ==> Gc (Γ + Γ') B)` (* Cut *)

val [Gc_ax, Gc_bot, Gc_lc, Gc_landl, Gc_landr, Gc_rand,
     Gc_lor, Gc_rorl, Gc_rorr, Gc_limp, Gc_rimp, Gc_cut] = CONJUNCTS Gc_rules;

val GcThm = Define `GcThm A = Gc EMPTY_BAG A`;

val Gc_example1 =
    Q.prove(`GcThm ((A And B) Imp (B And A))`, rw[GcThm,Gc_rules]);

val Gc_example2 = Q.prove (`GcThm ((A Imp (A Imp B)) Imp (A Imp B))`,
rw[GcThm] >>
`Gc {|(A Imp A Imp B)|} (A Imp B)` suffices_by metis_tac[Gc_rules] >>
`Gc {|A;(A Imp A Imp B)|} (B)` suffices_by metis_tac[Gc_rules] >>
`Gc {|A|} (A)` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gc {|B;A|} (B)` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
(* `Gc {|A;B|} (B)` by simp[Gc_lw] >> *)
(* `Gc {|B;A|} (B)` by simp[BAG_INSERT_commutes] >> *)
`Gc {|(A Imp B);A|} (B)` by metis_tac[Gc_rules] >>
`Gc {|(A Imp A Imp B);A|} (B)` suffices_by metis_tac[BAG_INSERT_commutes] >>
metis_tac[Gc_rules]);

val Gc_land_commutes =
    Q.prove(`Gc {| A And B |} Δ ==> Gc {| B And A |} Δ`, rw[] >>
`Gc {|B|} B` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gc {|B And A|} B` by metis_tac[Gc_landl] >>
`Gc {|A|} A` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gc {|B And A|} A` by metis_tac[Gc_landr] >>
`Gc {|B And A|} (A And B)` by metis_tac[Gc_rand] >>
`Gc ({|B And A|} + {||}) Δ` by metis_tac[Gc_cut] >>
metis_tac[BAG_UNION_EMPTY]);

Theorem Gc_FINITE `!D A. Gc D A ==> FINITE_BAG D` (Induct_on `Gc` >> rw[]);

(* Thanks for this theorem Michael *)
Theorem Gc_lw `∀Γ A. Gc Γ A ⇒ ∀Γ'. Γ ≤ Γ' /\ FINITE_BAG Γ' ⇒ Gc Γ' A`
(Induct_on `Gc` >> rw[]
>- (irule Gc_ax >> fs[SUB_BAG, BAG_IN])
>- (irule Gc_bot >> fs[SUB_BAG,BAG_IN])
>- (‘∃Γ₂. Γ' = {|A|} ⊎ Γ₂’
       by (qexists_tac ‘Γ' - {|A|}’ >> irule SUB_BAG_DIFF_EQ >>
           metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gc_lc >> first_x_assum irule >> simp[] >> fs[])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A And B) Γ₂’
      by (qexists_tac ‘Γ' - {|A And B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gc_landl >> first_x_assum irule >> fs[SUB_BAG_INSERT])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A And B) Γ₂’
      by (qexists_tac ‘Γ' - {|A And B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gc_landr >> first_x_assum irule >> fs[SUB_BAG_INSERT])
>- (irule Gc_rand >> simp[])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A Or B) Γ₂’
      by (qexists_tac ‘Γ' - {|A Or B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> fs[SUB_BAG_INSERT] >> irule Gc_lor >> conj_tac >>
    first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
>- simp[Gc_rorl]
>- simp[Gc_rorr]
>- (‘∃Γ₂. Γ' = BAG_INSERT (A Imp B) Γ₂’
      by (qexists_tac ‘Γ' - {|A Imp B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gc_limp >> fs[SUB_BAG_INSERT])
>- simp[SUB_BAG_INSERT, Gc_rimp]
>- (rename [‘Γ₁ ⊎ Γ₂ ≤ Γ₃’] >>
    ‘∃Γ₀. Γ₃ = Γ₀ ⊎ Γ₁ ⊎ Γ₂’
      by metis_tac[SUB_BAG_EXISTS, COMM_BAG_UNION, ASSOC_BAG_UNION] >>
    rw[] >> irule Gc_cut >>
    rename [‘Gc (BAG_INSERT A _) B’] >> qexists_tac ‘A’ >>
    conj_tac >> first_x_assum irule >> fs[SUB_BAG_INSERT]));

Theorem Gc_lw_BAG_MERGE
`!Γ₁ A. Gc Γ₁ A ==> !Γ₂. FINITE_BAG Γ₂ ==> Gc (BAG_MERGE Γ₂ Γ₁) A` (
  rw[] >>
  irule Gc_lw >>
  `FINITE_BAG Γ₁` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_MERGE] >>
  qexists_tac `Γ₁` >>
  simp[SUB_BAG,BAG_INN_BAG_MERGE]);

Theorem Gc_lw_BAG_UNION `∀Γ A. Gc Γ A ==> ∀Γ'. FINITE_BAG Γ'
                               ==> Gc (Γ ⊎ Γ') A` (
  rw[] >>
  irule Gc_lw >>
  `FINITE_BAG Γ` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_UNION] >>
  qexists_tac `Γ` >>
  simp[]);

Theorem Gc_lw_BAG_INSERT `∀Γ A. Gc Γ A ==> ∀B Γ'. Gc (BAG_INSERT B Γ) A` (
  rw[] >>
  irule Gc_lw >>
  `FINITE_BAG Γ` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_THM] >>
  qexists_tac `Γ` >>
  simp[SUB_BAG_INSERT_I]);

val Gc_lc_AeA =
    Q.prove(`∀A e Γ'. Gc (BAG_INSERT A (BAG_INSERT e (BAG_INSERT A Γ'))) B
            ==> Gc (BAG_INSERT e (BAG_INSERT A Γ')) B`,
            rw[] >>
            `Gc ({|A;A|} ⊎ ({|e|} ⊎ Γ')) B`
              by (fs[BAG_UNION_INSERT,ASSOC_BAG_UNION,BAG_INSERT_UNION] >>
                  simp[COMM_BAG_UNION] >>
                  fs[EL_BAG,BAG_UNION]) >>
            `Gc ({|A|} ⊎ ({|e|} ⊎ Γ')) B`
              by metis_tac[Gc_lc] >>
            `Gc (({|A|} ⊎ {|e|}) ⊎ Γ') B`
              by fs[ASSOC_BAG_UNION] >>
            `Gc (({|e|} ⊎ {|A|}) ⊎ Γ') B`
              by fs[COMM_BAG_UNION] >>
            fs[BAG_INSERT_UNION] >>
            fs[EL_BAG] >>
            simp[ASSOC_BAG_UNION]);

Theorem Gc_INSERT_TO_MERGE `∀Γ. FINITE_BAG Γ ==> ∀A B. Gc (BAG_INSERT A Γ) B
             ==> Gc (BAG_MERGE {|A|} Γ) B` (
    Induct_on `Γ` >>
    rw[]
    >- simp[BAG_MERGE_EMPTY]
    >- (Cases_on `A=e`
        >- (fs[] >>
            `BAG_MERGE {|e|} (BAG_INSERT e Γ) = BAG_INSERT e Γ`
              by (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
                  rw[] >> fs[]) >>
            fs[] >>
            `Gc ({|e;e|} ⊎ Γ) B` by fs[BAG_INSERT_UNION,ASSOC_BAG_UNION] >>
            `Gc ({|e|} ⊎ Γ) B` by metis_tac[Gc_lc] >>
            `{|e|} ⊎ Γ = BAG_INSERT e Γ`
              by rw[BAG_INSERT_UNION] >>
            metis_tac[])

        >- (Cases_on `BAG_IN A Γ`
            >- (`?Γ'. Γ = BAG_INSERT A Γ'` by metis_tac[BAG_DECOMPOSE] >>
                fs[] >>
                `Gc (BAG_INSERT e (BAG_INSERT A Γ')) B`
                  by metis_tac[Gc_lc_AeA] >>
                fs[Gc_lw_BAG_MERGE])
            >- (`BAG_INSERT A (BAG_INSERT e Γ)
                 = BAG_MERGE {|A|} (BAG_INSERT e Γ)`
                  by (`Γ A = 0` by metis_tac[NOT_BAG_IN] >>
                      simp[BAG_INSERT,BAG_MERGE,EMPTY_BAG,FUN_EQ_THM] >>
                      rw[] >>
                      fs[COND_CLAUSES]) >>
                fs[]))));

val unibag_AA_A = Q.prove(`unibag ({|A;A|} ⊎ Γ) = unibag ({|A|} ⊎ Γ)`,
  simp[unibag_thm]);

Theorem Gc_unibag `∀Γ A. Gc Γ A <=> Gc (unibag Γ) A` (
rw[] >> EQ_TAC
  >- (`∀Γ. FINITE_BAG Γ ==> ∀A. Gc Γ A ==> Gc (unibag Γ) A`
        suffices_by metis_tac[Gc_FINITE] >>
      gen_tac >>
      Induct_on `BAG_CARD Γ` >>
      rw[]
        >- (`Γ = {||}` by metis_tac[BCARD_0] >>
            fs[])
        >- (Cases_on `unibag Γ = Γ` >- fs[] >>
            drule_then strip_assume_tac unibag_DECOMPOSE >>
            rename [`Γ = {|B;B|} ⊎ Γ0`,`SUC n = BAG_CARD Γ`] >>
            `Gc ({|B|} ⊎ Γ0) A` by metis_tac[Gc_lc] >>
            `BAG_CARD ({|B|} ⊎ Γ0) = n` by fs[BAG_CARD_THM] >>
            `FINITE_BAG ({|B|} ⊎ Γ0)` by fs[] >>
            metis_tac[unibag_AA_A]))
   >- metis_tac[unibag_SUB_BAG,Gc_lw,Gc_FINITE,unibag_FINITE]);

Theorem Nc_Gc `∀Γ A. Nc Γ A ==> Gc (BAG_OF_SET Γ) A` (
 Induct_on `Nc ` >>
 rw[Gc_rules]
 >- (irule Gc_ax >> simp[] >>
     metis_tac[FINITE_BAG_OF_SET,FINITE_DEF])
 >- (irule Gc_rand >> conj_tac
     >- (`Gc (BAG_OF_SET (Γ' ∪ Γ)) A` suffices_by metis_tac[UNION_COMM] >>
         simp[BAG_OF_SET_UNION] >>
         metis_tac[Gc_lw_BAG_MERGE,Gc_FINITE])
     >- (simp[BAG_OF_SET_UNION] >>
             metis_tac[Gc_lw_BAG_MERGE,Gc_FINITE]))
 >- (`Gc {|A|} A` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     `Gc {|A And B|} A` by metis_tac[Gc_landl] >>
     `Gc ((BAG_OF_SET Γ) + {||}) A` by metis_tac[Gc_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (`Gc {|A'|} A'` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     `Gc {|A And A'|} A'` by metis_tac[Gc_landr] >>
     `Gc ((BAG_OF_SET Γ) + {||}) A'` by metis_tac[Gc_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (irule Gc_rimp >>
     fs[BAG_OF_SET_INSERT] >>
     irule Gc_lw >>
     simp[] >>
     drule Gc_FINITE >>
     rw[] >>
     qexists_tac `BAG_MERGE {|A|} (BAG_OF_SET Γ)` >>
     simp[BAG_MERGE_ELBAG_SUB_BAG_INSERT])
 >- (simp[BAG_OF_SET_UNION] >>
    `FINITE_BAG (BAG_OF_SET Γ')` by metis_tac[Nc_FINITE,FINITE_BAG_OF_SET] >>
    `Gc (BAG_INSERT A' (BAG_OF_SET Γ')) A'`
      by simp[Gc_ax,BAG_IN_BAG_INSERT] >>
    `Gc (BAG_INSERT (A Imp A') (BAG_OF_SET Γ')) A'`
      by metis_tac[Gc_limp] >>
    `Gc ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ')) A'`
      by metis_tac[Gc_cut] >>
    `Gc (unibag (BAG_OF_SET Γ ⊎ BAG_OF_SET Γ')) A'` by metis_tac[Gc_unibag] >>
    fs[unibag_UNION])
 >- (rename [`Nc (_ INSERT _) C`] >>
     fs[BAG_OF_SET_UNION,BAG_OF_SET_INSERT] >>
     qabbrev_tac `Δ = ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET D1) ⊎ (BAG_OF_SET D2))` >>
     `FINITE_BAG (BAG_INSERT A Δ)`
       by (simp[Abbr`Δ`,FINITE_BAG_THM] >>
           metis_tac[FINITE_BAG_OF_SET,Nc_FINITE,FINITE_INSERT]) >>
      `Gc (BAG_INSERT A Δ) C`
        by (`Gc (BAG_MERGE {|A|} Δ) C`
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gc_lw] >>
            simp[Abbr`Δ`] >>
            irule Gc_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_THM] >>
            qexists_tac `BAG_MERGE {|A|} (BAG_OF_SET D1)` >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      `FINITE_BAG (BAG_INSERT B Δ)`
      by (simp[Abbr`Δ`,FINITE_BAG_THM] >>
              metis_tac[FINITE_BAG_OF_SET,Nc_FINITE,FINITE_INSERT]) >>
      `Gc (BAG_INSERT B Δ) C`
        by (`Gc (BAG_MERGE {|B|} Δ) C`
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gc_lw] >>
            simp[Abbr`Δ`] >>
            irule Gc_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_THM] >>
            qexists_tac `BAG_MERGE {|B|} (BAG_OF_SET D2)` >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      `Gc Δ (A Or B)`
        by (simp[Abbr`Δ`] >>
            irule Gc_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,Nc_FINITE,FINITE_BAG_OF_SET] >>
            irule Gc_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,Nc_FINITE,FINITE_BAG_OF_SET] >>
            metis_tac[]) >>
      `Gc (BAG_INSERT (A Or B) Δ) C` by metis_tac[Gc_lor] >>
      `Gc ((BAG_OF_SET Γ) ⊎ Δ) C` by metis_tac[Gc_cut] >>
      `Gc (unibag (BAG_OF_SET Γ ⊎ Δ)) C` by metis_tac[Gc_unibag] >>
      `(unibag (BAG_OF_SET Γ ⊎ Δ))
        = BAG_MERGE (BAG_MERGE (BAG_OF_SET Γ) (BAG_OF_SET D1)) (BAG_OF_SET D2)`
         suffices_by metis_tac[] >>
      rw[Abbr`Δ`,unibag_UNION,BAG_MERGE,FUN_EQ_THM])
 >- (`Gc {|Bot|} A` by metis_tac[Gc_bot,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     metis_tac[Gc_cut,BAG_UNION_EMPTY])
 );

(* Apparently Nc takes a subset here!? *)
Theorem Gc_Nc `∀Γ A. Gc Γ A ==> ?Γ'. Γ' ⊆ (SET_OF_BAG Γ) /\ Nc Γ' A` (
  Induct_on `Gc` >> rw[]
    >- (qexists_tac `{A}` >> simp[SUBSET_DEF,SET_OF_BAG] >> metis_tac[Nc_ax])
    >- (qexists_tac `{Bot}` >> simp[SUBSET_DEF,SET_OF_BAG] >>
        metis_tac[Nc_bot,Nc_ax])
    >- (qexists_tac `Γ'` >> fs[SET_OF_BAG,BAG_UNION,BAG_INSERT])
    >- (rename [`Nc _ C`] >>
        `Nc {A And B} (A And B)` by metis_tac[Nc_ax] >>
        `Nc {A And B} A` by metis_tac[Nc_andel] >>
        `Nc (Γ' DELETE A) (A Imp C)`
          by metis_tac[Nc_impi_DELETE] >>
        `Nc ((Γ' DELETE A) ∪ {A And B}) C` by metis_tac[Nc_impe] >>
        `Nc ((A And B) INSERT (Γ' DELETE A)) C`
                  by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(A And B) INSERT Γ' DELETE A` >>
        fs[SET_OF_BAG_INSERT] >>
        fs[SUBSET_DEF] >>
        metis_tac[])
    >- (rename [`Nc _ C`] >>
        `Nc {A And B} (A And B)` by metis_tac[Nc_ax] >>
        `Nc {A And B} B` by metis_tac[Nc_ander] >>
        `Nc (B INSERT Γ') C` by metis_tac[Nc_lw] >>
        `Nc (Γ' DELETE B) (B Imp C)`
          by (Cases_on `B ∈ Γ'`
              >- (`?Γ0. (Γ' = B INSERT Γ0) /\ B NOTIN Γ0`
                    by metis_tac[DECOMPOSITION] >>
                  fs[] >>
                  `(B INSERT Γ0) DELETE B = Γ0`
                    by (dsimp[EXTENSION] >>
                        metis_tac[]) >>
                  simp[Nc_impi])
              >- (simp[DELETE_NON_ELEMENT_RWT,Nc_impi])) >>
        `Nc ((Γ' DELETE B) ∪ {A And B}) C` by metis_tac[Nc_impe] >>
        `Nc ((A And B) INSERT (Γ' DELETE B)) C`
          by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(A And B) INSERT Γ' DELETE B` >>
        fs[SET_OF_BAG_INSERT] >>
        fs[SUBSET_DEF] >>
        metis_tac[])
    >- (qexists_tac `Γ' ∪ Γ''` >> simp[] >>
        metis_tac[Nc_andi])
    >- (rename [`Nc _ C`] >>
        qabbrev_tac `Δ = (A Or B) INSERT (SET_OF_BAG Γ)` >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gc_FINITE,FINITE_BAG_THM] >>
        `Nc (A INSERT Δ) C`
          by (irule Nc_lw_SUBSET >>
              simp[Abbr`Δ`] >>
              qexists_tac `Γ'` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        `Nc (B INSERT Δ) C`
          by (irule Nc_lw_SUBSET >>
              simp[Abbr`Δ`] >>
              qexists_tac `Γ''` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        qexists_tac `Δ` >>
        simp[] >>
        `Nc {(A Or B)} (A Or B)` by metis_tac[Nc_ax] >>
        `FINITE ({A Or B} ∪ (SET_OF_BAG Γ))`
          by (`FINITE (SET_OF_BAG Γ)`
                by metis_tac[FINITE_SET_OF_BAG] >>
              metis_tac[FINITE_UNION,FINITE_DEF]) >>
        `Nc ({A Or B} ∪ (SET_OF_BAG Γ)) (A Or B)`
          by metis_tac[SUBSET_UNION,Nc_lw_SUBSET] >>
        `Nc Δ (A Or B)`
          by (simp[Abbr`Δ`] >>metis_tac[INSERT_SING_UNION]) >>
        `Nc (Δ ∪ Δ ∪ Δ) C` by metis_tac[Nc_ore] >>
        metis_tac[UNION_IDEMPOT])
    >- (qexists_tac `Γ'` >> simp[Nc_orir])
    >- (qexists_tac `Γ'` >> simp[Nc_oril])
    >- (rename [`Nc _ C`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gc_FINITE,FINITE_BAG_THM] >>
        `FINITE (SET_OF_BAG Γ)` by metis_tac[FINITE_SET_OF_BAG] >>
        `Nc {A Imp B} (A Imp B)` by metis_tac[Nc_ax] >>
        `Nc (SET_OF_BAG Γ) A` by metis_tac[Nc_lw_SUBSET] >>
        `Nc ({A Imp B} ∪ (SET_OF_BAG Γ)) B` by metis_tac[Nc_impe] >>
        `Nc ((A Imp B) INSERT (SET_OF_BAG Γ)) B`
          by metis_tac[INSERT_SING_UNION] >>
        qexists_tac `(A Imp B) INSERT SET_OF_BAG Γ` >>
        simp[SUBSET_INSERT_RIGHT] >>
        `Nc (B INSERT (SET_OF_BAG Γ)) C`
          by metis_tac[Nc_lw_SUBSET,FINITE_INSERT] >>
        `Nc (SET_OF_BAG Γ) (B Imp C)` by metis_tac[Nc_impi] >>
        `Nc ((SET_OF_BAG Γ) ∪ ((A Imp B) INSERT SET_OF_BAG Γ)) C`
          by metis_tac[Nc_impe] >>
        metis_tac[UNION_COMM,UNION_ASSOC,UNION_IDEMPOT,INSERT_SING_UNION])
    >- (rename [`Nc Δ C`,`Nc _ (A Imp C)`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE (A INSERT (SET_OF_BAG Γ))`
          by (simp[] >> metis_tac[Gc_FINITE,FINITE_BAG_THM]) >>
        `Nc (A INSERT (SET_OF_BAG Γ)) C` by metis_tac[Nc_lw_SUBSET] >>
        `Nc (SET_OF_BAG Γ) (A Imp C)` by metis_tac[Nc_impi] >>
        metis_tac[SUBSET_REFL])
    >- (rename [`Gc Γ A`,`Gc (BAG_INSERT A Γ2) B`,`Nc Δ1 A`,`Nc Δ2 B`] >>
        `Nc (A INSERT Δ2) B` by metis_tac[Nc_lw] >>
        `Nc (Δ2 DELETE A) (A Imp B)` by metis_tac[Nc_impi_DELETE] >>
        `Nc ((Δ2 DELETE A) ∪ Δ1) B` by metis_tac[Nc_impe] >>
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

Theorem Gc_iff_Nc
`∀Γ A. Gc Γ A <=> Nc (SET_OF_BAG Γ) A` (
  rw[] >>
  EQ_TAC
    >- (rw[] >>
      `?D. D ⊆ (SET_OF_BAG Γ) ∧ Nc D A` by metis_tac[Gc_Nc] >>
      metis_tac[Nc_lw_SUBSET,Gc_FINITE,FINITE_SET_OF_BAG]) >>
  rw[] >>
  `Gc (unibag Γ) A` by metis_tac[Nc_Gc] >>
  metis_tac[Gc_unibag]);

val _ = export_theory()
