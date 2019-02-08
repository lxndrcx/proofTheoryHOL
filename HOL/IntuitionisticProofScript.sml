
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
(* Ni is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* D, D1, D2, D3 are used to represent the set of open assumptions *)
(* I'm representing the deductions simply with unlabeled sets of
   open assumptions, as in T&S 2.1.8-2.1.9 (p.41--44) *)

val (Ni_rules, Ni_ind, Ni_cases) = Hol_reln `
(! (A :'a formula). Ni {A} A) (* Base case *)
/\ (!A B D1 D2. (Ni D1 A) /\ (Ni D2 B)
   ==> (Ni (D1 UNION D2) (A And B))) (* And Intro *)
/\ (!A B D. (Ni D (A And B)) ==> Ni D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Ni D (A And B)) ==> Ni D B) (* And Elim Right Conjunct *)
/\ (!A B D. (Ni (A INSERT D) B) ==> Ni D (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Ni D1 (A Imp B)) /\ (Ni D2 A)
   ==> Ni (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Ni D A ==> Ni D (A Or B))  (* Or Intro right *)
/\ (!A B D. Ni D B ==> Ni D (A Or B))  (* Or Intro left *)
/\ (!A B C D D1 D2. (Ni D (A Or B)) /\ (* Or Elim *)
(Ni (A INSERT D1) C) /\ (Ni (B INSERT D2) C) ==> Ni (D ∪ D1 ∪ D2) C) 
/\ (!A D. (Ni D Bot) ==> (Ni D A))`; (* Intuitionistic Absurdity Rule *)

val [Ni_ax, Ni_andi, Ni_andel, Ni_ander,
     Ni_impi, Ni_impe, Ni_orir, Ni_oril, Ni_ore, Ni_bot] = CONJUNCTS Ni_rules;

Theorem Ni_FINITE `!D A. Ni D A ==> FINITE D` (Induct_on `Ni` >> rw[])
Theorem Ni_lw `∀D A. Ni D A ==> ∀B. Ni (B INSERT D) A` (
  rw[] >>
`Ni {B} B` by metis_tac[Ni_ax] >>
`Ni ({B} ∪ D) (B And A)` by metis_tac[Ni_andi] >>
`Ni ({B} ∪ D) A` by metis_tac[Ni_ander] >>
metis_tac[INSERT_SING_UNION]);

Theorem Ni_lw_SUBSET `∀D'. FINITE D' ==> ∀D A. Ni D A  /\ D ⊆ D' ==> Ni D' A` (
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
metis_tac[Ni_lw])));
Theorem Ni_impi_DELETE `∀D A B. Ni D A ==> Ni (D DELETE B) (B Imp A)` (
  rw[] >>
  `Ni (B INSERT D) A` by metis_tac[Ni_lw] >>
  Cases_on `B ∈ D`
    >- (`?D'. (D = B INSERT D') /\ B NOTIN D'`
          by metis_tac[DECOMPOSITION] >>
        fs[] >>
        `(B INSERT D') DELETE B = D'`
          by (dsimp[EXTENSION] >>
              metis_tac[]) >>
        simp[Ni_impi])
    >- simp[DELETE_NON_ELEMENT_RWT,Ni_impi]);
val NiThm = Define `NiThm A = Ni EMPTY A`;
(* Example deductions *)
val Ni_example = Q.prove(`NiThm (A Imp (B Imp A))`,
`Ni {A} A` by rw[Ni_ax] >>
`Ni {B} B` by rw[Ni_ax] >>
`{A} UNION {B} = {A;B}` by simp[UNION_DEF,INSERT_DEF] >>
`Ni {A;B} (A And B)` by metis_tac[Ni_andi] >>
`Ni {A;B} (A)` by metis_tac[Ni_andel] >>
`Ni {A} (B Imp A)` by (irule Ni_impi >> simp[INSERT_COMM]) >>
`Ni {} (A Imp (B Imp A))` by metis_tac[Ni_impi] >>
 rw[NiThm]);

val Ni_example = Q.prove(`NiThm (Bot Imp A)`,
  `Ni {Bot} Bot` by rw[Ni_rules] >>
  `Ni {Bot} A` by rw[Ni_rules] >>
  `{} = ({Bot} DIFF {Bot})` by rw[DIFF_DEF] >>
  `Ni EMPTY (Bot Imp A)` by metis_tac[Ni_rules] >>
  rw[NiThm]);


(** Sequent Calculus (Gentzen System) for minimal logic **)
(* Gi is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* S is used to represent the multiset of the Antecedent Context *)
(* The consequent is always a single formula in the minimal logic *)

val (Gi_rules, Gi_ind, Gi_cases) = Hol_reln `
(!(A:'a formula) Γ. (A <: Γ) /\ FINITE_BAG Γ ==> Gi Γ A) (* Ax *)
/\ (Gi {|Bot|} A) (* LBot *)
/\ (!A Γ C. (Gi ({|A;A|} + Γ) C)
   ==> Gi ({|A|} + Γ) C) (* Left Contraction *)
/\ (!A B Γ C. (Gi (BAG_INSERT A Γ) C)
   ==> (Gi (BAG_INSERT (A And B) Γ) C)) (* Left And 1 *)
/\ (!A B Γ C. (Gi (BAG_INSERT B Γ) C)
   ==> (Gi (BAG_INSERT (A And B) Γ) C)) (* Left And 2 *)
/\ (!A B Γ. (Gi Γ A) /\ (Gi Γ B)
   ==> (Gi Γ (A And B))) (* Right And *)
/\ (!A B Γ C. (Gi (BAG_INSERT A Γ) C)
    /\ (Gi (BAG_INSERT B Γ) C)
   ==> (Gi (BAG_INSERT (A Or B) Γ) C)) (* Left Or *)
/\ (!A B Γ. (Gi Γ A)
   ==> (Gi Γ (A Or B))) (* Right Or 1 *)
/\ (!A B Γ. (Gi Γ B)
   ==> (Gi Γ (A Or B))) (* Right Or 2 *)
/\ (!A B Γ C. (Gi Γ A) /\ (Gi (BAG_INSERT B Γ) C)
   ==> (Gi (BAG_INSERT (A Imp B) Γ) C)) (* Left Imp *)
/\ (!A B Γ. (Gi (BAG_INSERT A Γ) B)
   ==> (Gi Γ (A Imp B))) (* Right Imp *)
∧  (∀A B Γ Γ'. (Gi Γ A) ∧ (Gi (BAG_INSERT A Γ') B) ==> Gi (Γ + Γ') B)` (* Cut *)

val [Gi_ax, Gm_bot, Gi_lc, Gi_landl, Gi_landr, Gi_rand,
     Gi_lor, Gi_rorl, Gi_rorr, Gi_limp, Gi_rimp, Gi_cut] = CONJUNCTS Gi_rules;

val GiThm = Define `GiThm A = Gi EMPTY_BAG A`;

val Gi_example1 =
    Q.prove(`GiThm ((A And B) Imp (B And A))`, rw[GiThm,Gi_rules]);

val Gi_example2 = Q.prove (`GiThm ((A Imp (A Imp B)) Imp (A Imp B))`,
rw[GiThm] >>
`Gi {|(A Imp A Imp B)|} (A Imp B)` suffices_by metis_tac[Gi_rules] >>
`Gi {|A;(A Imp A Imp B)|} (B)` suffices_by metis_tac[Gi_rules] >>
`Gi {|A|} (A)` by metis_tac[Gi_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gi {|B;A|} (B)` by metis_tac[Gi_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
(* `Gi {|A;B|} (B)` by simp[Gi_lw] >> *)
(* `Gi {|B;A|} (B)` by simp[BAG_INSERT_commutes] >> *)
`Gi {|(A Imp B);A|} (B)` by metis_tac[Gi_rules] >>
`Gi {|(A Imp A Imp B);A|} (B)` suffices_by metis_tac[BAG_INSERT_commutes] >>
metis_tac[Gi_rules]);

val Gi_land_commutes =
    Q.prove(`Gi {| A And B |} Δ ==> Gi {| B And A |} Δ`, rw[] >>
`Gi {|B|} B` by metis_tac[Gi_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gi {|B And A|} B` by metis_tac[Gi_landl] >>
`Gi {|A|} A` by metis_tac[Gi_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
`Gi {|B And A|} A` by metis_tac[Gi_landr] >>
`Gi {|B And A|} (A And B)` by metis_tac[Gi_rand] >>
`Gi ({|B And A|} + {||}) Δ` by metis_tac[Gi_cut] >>
metis_tac[BAG_UNION_EMPTY]);

Theorem Gi_FINITE `!D A. Gi D A ==> FINITE_BAG D` (Induct_on `Gi` >> rw[]);

(* Thanks for this theorem Michael *)
Theorem Gi_lw `∀Γ A. Gi Γ A ⇒ ∀Γ'. Γ ≤ Γ' /\ FINITE_BAG Γ' ⇒ Gi Γ' A`
(Induct_on `Gi` >> rw[]
>- (irule Gi_ax >> fs[SUB_BAG, BAG_IN])
>- (‘∃Γ₂. Γ' = {|A|} ⊎ Γ₂’
       by (qexists_tac ‘Γ' - {|A|}’ >> irule SUB_BAG_DIFF_EQ >>
           metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gi_lc >> first_x_assum irule >> simp[] >> fs[])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A And B) Γ₂’
      by (qexists_tac ‘Γ' - {|A And B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gi_landl >> first_x_assum irule >> fs[SUB_BAG_INSERT])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A And B) Γ₂’
      by (qexists_tac ‘Γ' - {|A And B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gi_landr >> first_x_assum irule >> fs[SUB_BAG_INSERT])
>- (irule Gi_rand >> simp[])
>- (‘∃Γ₂. Γ' = BAG_INSERT (A Or B) Γ₂’
      by (qexists_tac ‘Γ' - {|A Or B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> fs[SUB_BAG_INSERT] >> irule Gi_lor >> conj_tac >>
    first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
>- simp[Gi_rorl]
>- simp[Gi_rorr]
>- (‘∃Γ₂. Γ' = BAG_INSERT (A Imp B) Γ₂’
      by (qexists_tac ‘Γ' - {|A Imp B|}’ >> fs[BAG_INSERT_UNION] >>
          irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
    rw[] >> irule Gi_limp >> fs[SUB_BAG_INSERT])
>- simp[SUB_BAG_INSERT, Gi_rimp]
>- (rename [‘Γ₁ ⊎ Γ₂ ≤ Γ₃’] >>
    ‘∃Γ₀. Γ₃ = Γ₀ ⊎ Γ₁ ⊎ Γ₂’
      by metis_tac[SUB_BAG_EXISTS, COMM_BAG_UNION, ASSOC_BAG_UNION] >>
    rw[] >> irule Gi_cut >>
    rename [‘Gi (BAG_INSERT A _) B’] >> qexists_tac ‘A’ >>
    conj_tac >> first_x_assum irule >> fs[SUB_BAG_INSERT]));

Theorem Gi_lw_BAG_MERGE
`!Γ₁ A. Gi Γ₁ A ==> !Γ₂. FINITE_BAG Γ₂ ==> Gi (BAG_MERGE Γ₂ Γ₁) A` (
  rw[] >>
  irule Gi_lw >>
  `FINITE_BAG Γ₁` by metis_tac[Gi_FINITE] >>
  simp[FINITE_BAG_MERGE] >>
  qexists_tac `Γ₁` >>
  simp[SUB_BAG,BAG_INN_BAG_MERGE]);

Theorem Gi_lw_BAG_UNION `∀Γ A. Gi Γ A ==> ∀Γ'. FINITE_BAG Γ'
                               ==> Gi (Γ ⊎ Γ') A` (
  rw[] >> 
  irule Gi_lw >>
  `FINITE_BAG Γ` by metis_tac[Gi_FINITE] >>
  simp[FINITE_BAG_UNION] >>
  qexists_tac `Γ` >> 
  simp[]);

Theorem Gi_lw_BAG_INSERT `∀Γ A. Gi Γ A ==> ∀B Γ'. Gi (BAG_INSERT B Γ) A` (
  rw[] >>
  irule Gi_lw >>
  `FINITE_BAG Γ` by metis_tac[Gi_FINITE] >>
  simp[FINITE_BAG_INSERT] >>
  qexists_tac `Γ` >>
  simp[SUB_BAG_INSERT_I]);

val Gi_lc_AeA =
    Q.prove(`∀A e Γ'. Gi (BAG_INSERT A (BAG_INSERT e (BAG_INSERT A Γ'))) B
            ==> Gi (BAG_INSERT e (BAG_INSERT A Γ')) B`,
            rw[] >>
            `Gi ({|A;A|} ⊎ ({|e|} ⊎ Γ')) B`
              by (fs[BAG_UNION_INSERT,ASSOC_BAG_UNION,BAG_INSERT_UNION] >>
                  simp[COMM_BAG_UNION] >>
                  fs[EL_BAG,BAG_UNION]) >>
            `Gi ({|A|} ⊎ ({|e|} ⊎ Γ')) B`
              by metis_tac[Gi_lc] >>
            `Gi (({|A|} ⊎ {|e|}) ⊎ Γ') B`
              by fs[ASSOC_BAG_UNION] >>
            `Gi (({|e|} ⊎ {|A|}) ⊎ Γ') B`
              by fs[COMM_BAG_UNION] >>
            fs[BAG_INSERT_UNION] >>
            fs[EL_BAG] >>
            simp[ASSOC_BAG_UNION]);

Theorem Gi_INSERT_TO_MERGE `∀Γ. FINITE_BAG Γ ==> ∀A B. Gi (BAG_INSERT A Γ) B
             ==> Gi (BAG_MERGE {|A|} Γ) B` (
    Induct_on `Γ` >>
    rw[]
    >- simp[BAG_MERGE_EMPTY] 
    >- (Cases_on `A=e`
        >- (fs[] >>
            `BAG_MERGE {|e|} (BAG_INSERT e Γ) = BAG_INSERT e Γ`
              by (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
                  rw[] >> fs[]) >>
            fs[] >>
            `Gi ({|e;e|} ⊎ Γ) B` by fs[BAG_INSERT_UNION,ASSOC_BAG_UNION] >>
            `Gi ({|e|} ⊎ Γ) B` by metis_tac[Gi_lc] >>
            `{|e|} ⊎ Γ = BAG_INSERT e Γ`
              by rw[BAG_INSERT_UNION] >>
            metis_tac[])

        >- (Cases_on `BAG_IN A Γ`
            >- (`?Γ'. Γ = BAG_INSERT A Γ'` by metis_tac[BAG_DECOMPOSE] >>
                fs[] >>
                `Gi (BAG_INSERT e (BAG_INSERT A Γ')) B` 
                  by metis_tac[Gi_lc_AeA] >>
                fs[Gi_lw_BAG_MERGE])
            >- (`BAG_INSERT A (BAG_INSERT e Γ)
                 = BAG_MERGE {|A|} (BAG_INSERT e Γ)`
                  by (`Γ A = 0` by metis_tac[NOT_BAG_IN] >>
                      simp[BAG_INSERT,BAG_MERGE,EMPTY_BAG,FUN_EQ_THM] >>
                      rw[] >>
                      fs[COND_CLAUSES]) >>
                fs[]))));

val unibag_AA_A = Q.prove(`unibag ({|A;A|} ⊎ Γ) = unibag ({|A|} ⊎ Γ)`,
  simp[unibag_thm]);

Theorem Gi_unibag `∀Γ A. Gi Γ A <=> Gi (unibag Γ) A` (
rw[] >> EQ_TAC
  >- (`∀Γ. FINITE_BAG Γ ==> ∀A. Gi Γ A ==> Gi (unibag Γ) A`
        suffices_by metis_tac[Gi_FINITE] >>
      gen_tac >>
      Induct_on `BAG_CARD Γ` >>
      rw[]
        >- (`Γ = {||}` by metis_tac[BCARD_0] >>
            fs[])
        >- (Cases_on `unibag Γ = Γ` >- fs[] >>
            drule_then strip_assume_tac unibag_DECOMPOSE >>
            rename [`Γ = {|B;B|} ⊎ Γ0`,`SUC n = BAG_CARD Γ`] >>
            `Gi ({|B|} ⊎ Γ0) A` by metis_tac[Gi_lc] >>
            `BAG_CARD ({|B|} ⊎ Γ0) = n` by fs[BAG_CARD_THM] >>
            `FINITE_BAG ({|B|} ⊎ Γ0)` by fs[] >>
            metis_tac[unibag_AA_A]))
   >- metis_tac[unibag_SUB_BAG,Gi_lw,Gi_FINITE,unibag_FINITE]);

Theorem Ni_Gi `∀Γ A. Ni Γ A ==> Gi (BAG_OF_SET Γ) A` (
 Induct_on `Ni ` >>
 rw[Gi_rules]
 >- (irule Gi_ax >> simp[] >>
     metis_tac[FINITE_BAG_OF_SET,FINITE_DEF])
 >- (irule Gi_rand >> conj_tac
     >- (`Gi (BAG_OF_SET (Γ' ∪ Γ)) A` suffices_by metis_tac[UNION_COMM] >>
         simp[BAG_OF_SET_UNION] >>
         metis_tac[Gi_lw_BAG_MERGE,Gi_FINITE])
     >- (simp[BAG_OF_SET_UNION] >>
             metis_tac[Gi_lw_BAG_MERGE,Gi_FINITE]))
 >- (`Gi {|A|} A` by metis_tac[Gi_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     `Gi {|A And B|} A` by metis_tac[Gi_landl] >>
     `Gi ((BAG_OF_SET Γ) + {||}) A` by metis_tac[Gi_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (`Gi {|A'|} A'` by metis_tac[Gi_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     `Gi {|A And A'|} A'` by metis_tac[Gi_landr] >>
     `Gi ((BAG_OF_SET Γ) + {||}) A'` by metis_tac[Gi_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (irule Gi_rimp >>
     fs[BAG_OF_SET_INSERT] >>
     irule Gi_lw >>
     simp[] >>
     drule Gi_FINITE >>
     rw[] >>
     qexists_tac `BAG_MERGE {|A|} (BAG_OF_SET Γ)` >>
     simp[BAG_MERGE_ELBAG_SUB_BAG_INSERT])
 >- (simp[BAG_OF_SET_UNION] >>
    `FINITE_BAG (BAG_OF_SET Γ')` by metis_tac[Ni_FINITE,FINITE_BAG_OF_SET] >>
    `Gi (BAG_INSERT A' (BAG_OF_SET Γ')) A'`
      by simp[Gi_ax,BAG_IN_BAG_INSERT] >>
    `Gi (BAG_INSERT (A Imp A') (BAG_OF_SET Γ')) A'`
      by metis_tac[Gi_limp] >>
    `Gi ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ')) A'`
      by metis_tac[Gi_cut] >>
    `Gi (unibag (BAG_OF_SET Γ ⊎ BAG_OF_SET Γ')) A'` by metis_tac[Gi_unibag] >>
    fs[unibag_UNION])
 >- (rename [`Ni (_ INSERT _) C`] >>
     fs[BAG_OF_SET_UNION,BAG_OF_SET_INSERT] >>
     qabbrev_tac `Δ = ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET D1) ⊎ (BAG_OF_SET D2))` >>
     `FINITE_BAG (BAG_INSERT A Δ)`
       by (simp[Abbr`Δ`,FINITE_BAG_INSERT] >>
           metis_tac[FINITE_BAG_OF_SET,Ni_FINITE,FINITE_INSERT]) >>
      `Gi (BAG_INSERT A Δ) C`
        by (`Gi (BAG_MERGE {|A|} Δ) C`
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gi_lw] >>
            simp[Abbr`Δ`] >>
            irule Gi_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_INSERT] >>
            qexists_tac `BAG_MERGE {|A|} (BAG_OF_SET D1)` >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      `FINITE_BAG (BAG_INSERT B Δ)`
      by (simp[Abbr`Δ`,FINITE_BAG_INSERT] >>
              metis_tac[FINITE_BAG_OF_SET,Ni_FINITE,FINITE_INSERT]) >>
      `Gi (BAG_INSERT B Δ) C`
        by (`Gi (BAG_MERGE {|B|} Δ) C`
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,Gi_lw] >>
            simp[Abbr`Δ`] >>
            irule Gi_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_INSERT] >>
            qexists_tac `BAG_MERGE {|B|} (BAG_OF_SET D2)` >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      `Gi Δ (A Or B)`
        by (simp[Abbr`Δ`] >>
            irule Gi_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,Ni_FINITE,FINITE_BAG_OF_SET] >>
            irule Gi_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,Ni_FINITE,FINITE_BAG_OF_SET] >>
            metis_tac[]) >>
      `Gi (BAG_INSERT (A Or B) Δ) C` by metis_tac[Gi_lor] >>
      `Gi ((BAG_OF_SET Γ) ⊎ Δ) C` by metis_tac[Gi_cut] >>
      `Gi (unibag (BAG_OF_SET Γ ⊎ Δ)) C` by metis_tac[Gi_unibag] >>
      `(unibag (BAG_OF_SET Γ ⊎ Δ))
        = BAG_MERGE (BAG_MERGE (BAG_OF_SET Γ) (BAG_OF_SET D1)) (BAG_OF_SET D2)`
         suffices_by metis_tac[] >>
      rw[Abbr`Δ`,unibag_UNION,BAG_MERGE,FUN_EQ_THM]));

(* Apparently Ni takes a subset here!? *)
Theorem Gi_Ni `∀Γ A. Gi Γ A ==> ?Γ'. Γ' ⊆ (SET_OF_BAG Γ) /\ Ni Γ' A` (
  Induct_on `Gi` >> rw[]
    >- (qexists_tac `{A}` >> simp[SUBSET_DEF,SET_OF_BAG] >> metis_tac[Ni_ax])
    >- (qexists_tac `Γ'` >> fs[SET_OF_BAG,BAG_UNION,BAG_INSERT])
    >- (rename [`Ni _ C`] >>
        `Ni {A And B} (A And B)` by metis_tac[Ni_ax] >>
        `Ni {A And B} A` by metis_tac[Ni_andel] >>
        `Ni (Γ' DELETE A) (A Imp C)`
          by metis_tac[Ni_impi_DELETE] >>
        `Ni ((Γ' DELETE A) ∪ {A And B}) C` by metis_tac[Ni_impe] >>
        `Ni ((A And B) INSERT (Γ' DELETE A)) C`
                  by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(A And B) INSERT Γ' DELETE A` >>
        fs[SET_OF_BAG_INSERT] >>
        fs[SUBSET_DEF] >>
        metis_tac[])
    >- (rename [`Ni _ C`] >>
        `Ni {A And B} (A And B)` by metis_tac[Ni_ax] >>
        `Ni {A And B} B` by metis_tac[Ni_ander] >>
        `Ni (B INSERT Γ') C` by metis_tac[Ni_lw] >>
        `Ni (Γ' DELETE B) (B Imp C)`
          by (Cases_on `B ∈ Γ'`
              >- (`?Γ0. (Γ' = B INSERT Γ0) /\ B NOTIN Γ0`
                    by metis_tac[DECOMPOSITION] >>
                  fs[] >>
                  `(B INSERT Γ0) DELETE B = Γ0`
                    by (dsimp[EXTENSION] >>
                        metis_tac[]) >>
                  simp[Ni_impi])
              >- (simp[DELETE_NON_ELEMENT_RWT,Ni_impi])) >>
        `Ni ((Γ' DELETE B) ∪ {A And B}) C` by metis_tac[Ni_impe] >>
        `Ni ((A And B) INSERT (Γ' DELETE B)) C`
          by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        qexists_tac `(A And B) INSERT Γ' DELETE B` >>
        fs[SET_OF_BAG_INSERT] >>
        fs[SUBSET_DEF] >>
        metis_tac[])
    >- (qexists_tac `Γ' ∪ Γ''` >> simp[] >>
        metis_tac[Ni_andi])
    >- (rename [`Ni _ C`] >>
        qabbrev_tac `Δ = (A Or B) INSERT (SET_OF_BAG Γ)` >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gi_FINITE,FINITE_BAG_INSERT] >>
        `Ni (A INSERT Δ) C`
          by (irule Ni_lw_SUBSET >>
              simp[Abbr`Δ`] >>
              qexists_tac `Γ'` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        `Ni (B INSERT Δ) C`
          by (irule Ni_lw_SUBSET >>
              simp[Abbr`Δ`] >>
              qexists_tac `Γ''` >>
              simp[] >>
              metis_tac[INSERT_COMM,SUBSET_INSERT_RIGHT]) >>
        qexists_tac `Δ` >>
        simp[] >>
        `Ni {(A Or B)} (A Or B)` by metis_tac[Ni_ax] >>
        `FINITE ({A Or B} ∪ (SET_OF_BAG Γ))`
          by (`FINITE (SET_OF_BAG Γ)`
                by metis_tac[FINITE_SET_OF_BAG] >>
              metis_tac[FINITE_UNION,FINITE_DEF]) >>
        `Ni ({A Or B} ∪ (SET_OF_BAG Γ)) (A Or B)`
          by metis_tac[SUBSET_UNION,Ni_lw_SUBSET] >>
        `Ni Δ (A Or B)`
          by (simp[Abbr`Δ`] >>metis_tac[INSERT_SING_UNION]) >>
        `Ni (Δ ∪ Δ ∪ Δ) C` by metis_tac[Ni_ore] >>
        metis_tac[UNION_IDEMPOT])
    >- (qexists_tac `Γ'` >> simp[Ni_orir])
    >- (qexists_tac `Γ'` >> simp[Ni_oril])
    >- (rename [`Ni _ C`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE_BAG Γ` by metis_tac[Gi_FINITE,FINITE_BAG_INSERT] >>
        `FINITE (SET_OF_BAG Γ)` by metis_tac[FINITE_SET_OF_BAG] >>
        `Ni {A Imp B} (A Imp B)` by metis_tac[Ni_ax] >>
        `Ni (SET_OF_BAG Γ) A` by metis_tac[Ni_lw_SUBSET] >>
        `Ni ({A Imp B} ∪ (SET_OF_BAG Γ)) B` by metis_tac[Ni_impe] >>
        `Ni ((A Imp B) INSERT (SET_OF_BAG Γ)) B`
          by metis_tac[INSERT_SING_UNION] >>
        qexists_tac `(A Imp B) INSERT SET_OF_BAG Γ` >>
        simp[SUBSET_INSERT_RIGHT] >>
        `Ni (B INSERT (SET_OF_BAG Γ)) C` 
          by metis_tac[Ni_lw_SUBSET,FINITE_INSERT] >>
        `Ni (SET_OF_BAG Γ) (B Imp C)` by metis_tac[Ni_impi] >>
        `Ni ((SET_OF_BAG Γ) ∪ ((A Imp B) INSERT SET_OF_BAG Γ)) C` 
          by metis_tac[Ni_impe] >>
        metis_tac[UNION_COMM,UNION_ASSOC,UNION_IDEMPOT,INSERT_SING_UNION])
    >- (rename [`Ni Δ C`,`Ni _ (A Imp C)`] >>
        fs[SET_OF_BAG_INSERT] >>
        `FINITE (A INSERT (SET_OF_BAG Γ))` 
          by (simp[] >> metis_tac[Gi_FINITE,FINITE_BAG_INSERT]) >>
        `Ni (A INSERT (SET_OF_BAG Γ)) C` by metis_tac[Ni_lw_SUBSET] >>
        `Ni (SET_OF_BAG Γ) (A Imp C)` by metis_tac[Ni_impi] >>
        metis_tac[SUBSET_REFL])
    >- (rename [`Gi Γ A`,`Gi (BAG_INSERT A Γ2) B`,`Ni Δ1 A`,`Ni Δ2 B`] >>
        `Ni (A INSERT Δ2) B` by metis_tac[Ni_lw] >>
        `Ni (Δ2 DELETE A) (A Imp B)` by metis_tac[Ni_impi_DELETE] >>
        `Ni ((Δ2 DELETE A) ∪ Δ1) B` by metis_tac[Ni_impe] >>
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

Theorem Gi_iff_Ni
`∀Γ A. Gi Γ A <=> Ni (SET_OF_BAG Γ) A` (
  rw[] >>
  EQ_TAC 
    >- (rw[] >>
      `?D. D ⊆ (SET_OF_BAG Γ) ∧ Ni D A` by metis_tac[Gi_Ni] >>
      metis_tac[Ni_lw_SUBSET,Gi_FINITE,FINITE_SET_OF_BAG]) >>
  rw[] >>
  `Gi (unibag Γ) A` by metis_tac[Ni_Gi] >>
  metis_tac[Gi_unibag]);

val _ = export_theory()
