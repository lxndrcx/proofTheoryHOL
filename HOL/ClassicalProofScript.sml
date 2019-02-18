
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

val _ = new_theory "ClassicalProof";

(** Natural Deduction for classical logic **)
(* Nc is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* D, D1, D2, D3 are used to represent the set of open assumptions *)
(* I'm representing the deductions simply with unlabeled sets of
   open assumptions, as in T&S 2.1.8-2.1.9 (p.41--44) *)

val _ = set_fixity "Nc" (Infix(NONASSOC,320));
val _ = set_fixity "Gc" (Infix(NONASSOC,320));

val (Nc_rules, Nc_ind, Nc_cases) = Hol_reln `
(! (A :'a formula). {A} Nc A) (* Base case *)
/\ (!A B D1 D2 D. (D1 Nc A) /\ (D2 Nc B)
   /\ (D = (D1 UNION D2)) ==> D Nc (A And B)) (* And Intro *)
/\ (!A B D. (D Nc (A And B)) ==> D Nc A) (* And Elimination Left Conjunct *)
/\ (!A B D. (D Nc (A And B)) ==> D Nc B) (* And Elim Right Conjunct *)
/\ (!A B D. ((A INSERT D) Nc B) ==> D Nc (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2 D. (D1 Nc (A Imp B)) /\ (D2 Nc A) /\ (D = (D1 UNION D2))
    ==> D Nc B) (* Imp Elim *)
/\ (!A B D. D Nc A ==> D Nc (A Or B))  (* Or Intro right *)
/\ (!A B D. D Nc B ==> D Nc (A Or B))  (* Or Intro left *)
/\ (!A B C D D1 D2 D0. (D Nc (A Or B)) /\ (* Or Elim *)
    ((A INSERT D1) Nc C) /\ ((B INSERT D2) Nc C) /\ (D0 = (D ∪ D1 ∪ D2))
    ==> D0 Nc C)
/\ (!A D. (((Not A) INSERT D) Nc Bot) (* Classical Absurdity Rule *)
==> (D Nc A))`; 

val [Nc_ax, Nc_andi, Nc_andel, Nc_ander,
     Nc_impi, Nc_impe, Nc_orir, Nc_oril, Nc_ore, Nc_bot] = CONJUNCTS Nc_rules;

Theorem Nc_FINITE:
  !D A. D Nc A ==> FINITE D
Proof
  Induct_on `D Nc A` >> 
  rw[]
QED

Theorem Nc_lw:
  ∀D A. D Nc A ==> ∀B. (B INSERT D) Nc A
Proof
  rw[] >>
  `{B} Nc B` by metis_tac[Nc_ax] >>
  `({B} ∪ D) Nc (B And A)` by metis_tac[Nc_andi] >>
  `({B} ∪ D) Nc A` by metis_tac[Nc_ander] >>
  metis_tac[INSERT_SING_UNION]
QED

Theorem Nc_lw_SUBSET:
  ∀D'. FINITE D' ==> ∀D A. (D Nc A) /\ D ⊆ D' ==> D' Nc A
Proof
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
          metis_tac[Nc_lw]))
QED

Theorem Nc_impi_DELETE:
  ∀D A B. D Nc A ==> (D DELETE B) Nc (B Imp A)
Proof
  rw[] >>
  `(B INSERT D) Nc A` by metis_tac[Nc_lw] >>
  Cases_on `B ∈ D`
    >- (`?D'. (D = B INSERT D') /\ B NOTIN D'`
          by metis_tac[DECOMPOSITION] >>
        fs[] >>
        `(B INSERT D') DELETE B = D'`
          by (dsimp[EXTENSION] >>
              metis_tac[]) >>
        simp[Nc_impi])
    >- simp[DELETE_NON_ELEMENT_RWT,Nc_impi]
QED

val NcThm = Define `NcThm A = EMPTY Nc A`;

(* Example deductions *)
val Nc_example = Q.prove(`NcThm (A Imp (B Imp A))`,
`{A} Nc A` by rw[Nc_ax] >>
`{B} Nc B` by rw[Nc_ax] >>
`{A} UNION {B} = {A;B}` by simp[UNION_DEF,INSERT_DEF] >>
`{A;B} Nc (A And B)` by metis_tac[Nc_andi] >>
`{A;B} Nc (A)` by metis_tac[Nc_andel] >>
`{A} Nc (B Imp A)` by (irule Nc_impi >> simp[INSERT_COMM]) >>
`{} Nc (A Imp (B Imp A))` by metis_tac[Nc_impi] >>
 rw[NcThm]);

val Nc_example = Q.prove(`NcThm (Bot Imp A)`,
  `{Bot} Nc Bot` by rw[Nc_ax] >>
  `{Not A;Bot} Nc Bot` by metis_tac[Nc_lw] >>
  `{Bot} Nc A` by rw[Nc_bot] >>
  `EMPTY Nc (Bot Imp A)` by metis_tac[Nc_rules,DIFF_DEF] >>
  rw[NcThm]);


(** Sequent Calculus (Gentzen System) for classical logic **)
(* Gc is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* S is used to represent the multiset of the Antecedent Context *)
(* The consequent is a multiset of formula in the classical logic *)

val (Gc_rules, Gc_ind, Gc_cases) = Hol_reln `
(!(A:'a formula) Γ Δ.
                   (A <: Γ) /\ FINITE_BAG Γ /\
                   (A <: Δ) /\ FINITE_BAG Δ
                   ==> Γ Gc Δ) (* Ax *)
/\ (∀ Γ Δ. (Bot <: Γ) /\ FINITE_BAG Γ /\ FINITE_BAG Δ ==> Γ Gc Δ) (* LBot *)
/\ (!A Γ Δ Σ. (({|A;A|} + Γ) Gc Δ) /\ (Σ = ({|A|} + Γ))
                     ==> Σ Gc Δ) (* Left Contraction *)
/\ (!A Γ Δ Σ. (Γ Gc ({|A;A|} + Δ)) /\ (Σ = ({|A|} + Δ))
                     ==> Γ Gc Σ) (* Right Contraction *)
/\ (!A B Γ Δ Σ. ((BAG_INSERT A Γ) Gc Δ)
   /\ (Σ = (BAG_INSERT (A And B) Γ)) ==> Σ Gc Δ) (* Left And 1 *)
/\ (!A B Γ Δ Σ. ((BAG_INSERT B Γ) Gc Δ)
    /\ (Σ = (BAG_INSERT (A And B) Γ)) ==> Σ Gc Δ) (* Left And 1 *)
/\ (!A B Γ Δ Σ. (Γ Gc (BAG_INSERT A Δ)) /\ (Γ Gc (BAG_INSERT B Δ))
              /\ (Σ = BAG_INSERT (A And B) Δ)
              ==> Γ Gc Σ) (* Right And *)
/\ (!A B Γ Δ. ((BAG_INSERT A Γ) Gc Δ)
    /\ ((BAG_INSERT B Γ) Gc Δ)
    /\ (Σ = (BAG_INSERT (A Or B) Γ)) ==> Σ Gc Δ) (* Left Or *)
/\ (!A B Γ Δ Δ'. (Γ Gc (BAG_INSERT A Δ)) /\ (Δ' = (BAG_INSERT (A Or B) Δ))
   ==> Γ Gc Δ') (* Right Or 1 *)
/\ (!A B Γ Δ Δ'. (Γ Gc (BAG_INSERT B Δ)) /\ (Δ' = (BAG_INSERT (A Or B) Δ))
   ==> Γ Gc Δ') (* Right Or 2 *)
/\ (!A B Γ Δ Σ. (Γ Gc (BAG_INSERT A Δ)) /\ ((BAG_INSERT B Γ) Gc Δ)
              /\ (Σ = (BAG_INSERT (A Imp B) Γ)) ==> Σ Gc Δ) (* Left Imp *)
/\ (!A B Γ Δ Δ'. ((BAG_INSERT A Γ) Gc (BAG_INSERT B Δ))
                 /\ (Δ' = BAG_INSERT (A Imp B) Δ)
                 ==> (Γ Gc Δ)) (* Right Imp *)
/\ (∀A Γ Γ' Δ Δ'. (Γ Gc (BAG_INSERT A Δ)) ∧ ((BAG_INSERT A Γ') Gc Δ') 
                       ==> Γ ⊎ Γ' Gc Δ ⊎ Δ')` (* Cut_cs *)

val [Gc_ax, Gc_bot, Gc_lc, Gc_rc, Gc_landl, Gc_landr, Gc_rand,
     Gc_lor, Gc_rorl, Gc_rorr, Gc_limp, Gc_rimp, Gc_cut] = CONJUNCTS Gc_rules;
   
(* val GcThm = Define `GcThm A = EMPTY_BAG Gc A`; *)

(* val Gc_example1 = *)
(*     Q.prove(`GcThm ((A And B) Imp (B And A))`, rw[GcThm,Gc_rules]); *)

(* val Gc_example2 = Q.prove (`GcThm ((A Imp (A Imp B)) Imp (A Imp B))`, *)
(* rw[GcThm] >> *)
(* `Gc {|(A Imp A Imp B)|} (A Imp B)` suffices_by metis_tac[Gc_rules] >> *)
(* `Gc {|A;(A Imp A Imp B)|} (B)` suffices_by metis_tac[Gc_rules] >> *)
(* `Gc {|A|} (A)` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >> *)
(* `Gc {|B;A|} (B)` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >> *)
(* (* `Gc {|A;B|} (B)` by simp[Gc_lw] >> *) *)
(* (* `Gc {|B;A|} (B)` by simp[BAG_INSERT_commutes] >> *) *)
(* `Gc {|(A Imp B);A|} (B)` by metis_tac[Gc_rules] >> *)
(* `Gc {|(A Imp A Imp B);A|} (B)` suffices_by metis_tac[BAG_INSERT_commutes] >> *)
(* metis_tac[Gc_rules]); *)

(* val Gc_land_commutes = *)
(*     Q.prove(`Gc {| A And B |} Δ ==> Gc {| B And A |} Δ`, rw[] >> *)
(* `Gc {|B|} B` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >> *)
(* `Gc {|B And A|} B` by metis_tac[Gc_landl] >> *)
(* `Gc {|A|} A` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >> *)
(* `Gc {|B And A|} A` by metis_tac[Gc_landr] >> *)
(* `Gc {|B And A|} (A And B)` by metis_tac[Gc_rand] >> *)
(* `Gc ({|B And A|} + {||}) Δ` by metis_tac[Gc_cut] >> *)
(* metis_tac[BAG_UNION_EMPTY]); *)

Theorem Gc_FINITE:
  !h c. h Gc c ==> FINITE_BAG h /\ FINITE_BAG c
Proof
  Induct_on `h Gc c` >> rw[]
QED

Theorem BAG_INSERT_SUB_BAG_DECOMPOSE:
   !e b b'. BAG_INSERT e b <= b' ==> ?c. b' = BAG_INSERT e c
Proof
  rw[] >>
  irule BAG_DECOMPOSE >>
  metis_tac[SUB_BAG_BAG_IN]
QED

Theorem EL_BAG_UNION_SUB_BAG_DECOMPOSE:
  !e b b'. {|e|} + b <= b' ==> ?c. b' = BAG_INSERT e c
Proof
  rw[] >>
  irule BAG_INSERT_SUB_BAG_DECOMPOSE >>
  qexists_tac `b` >>
  fs[BAG_INSERT_UNION]
QED

Theorem Gc_lw:
  ∀Γ Δ. Γ Gc Δ ==> ∀Γ'. Γ ≤ Γ' /\ FINITE_BAG Γ' ==> Γ' Gc Δ
Proof
  Induct_on `Γ Gc Δ` >>
  rw[]
  >- (irule Gc_ax >> 
      fs[] >> 
      qexists_tac `A` >>
      fs[SUB_BAG,BAG_IN])
  >- (irule Gc_bot >> fs[SUB_BAG,BAG_IN])
  >- (irule Gc_lc >>
      qexists_tac `A` >>
      `?b. Γ'' = BAG_INSERT A b`
        by metis_tac[EL_BAG_UNION_SUB_BAG_DECOMPOSE] >>
      fs[] >>
      rw[] >>
      qexists_tac `b` >>
      simp[Once BAG_INSERT_UNION,EL_BAG] >>
      first_x_assum (qspec_then `{|A;A|} ⊎ b` mp_tac) >>
      fs[BAG_INSERT_UNION])
  >- (irule Gc_rc >>
      qexists_tac `A` >>
      qexists_tac `Δ` >>
      fs[])
  >- (irule Gc_landl >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      `?b. Γ'' = BAG_INSERT (A And B) b`
        by metis_tac[BAG_INSERT_SUB_BAG_DECOMPOSE] >>
      fs[] >> rw[] >>
      first_x_assum (qspec_then `BAG_INSERT A b` mp_tac) >>
      fs[] >>
      rw[SUB_BAG_INSERT] >>
      `Γ ≤ b` suffices_by metis_tac[] >>
      fs[SUB_BAG_INSERT])
  >- (irule Gc_landr >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      `?b. Γ'' = BAG_INSERT (A And B) b`
        by metis_tac[BAG_INSERT_SUB_BAG_DECOMPOSE] >>
      fs[] >> rw[] >>
      first_x_assum (qspec_then `BAG_INSERT B b` mp_tac) >>
      fs[] >>
      rw[SUB_BAG_INSERT] >>
      `Γ ≤ b` suffices_by metis_tac[] >>
      fs[SUB_BAG_INSERT])
  >- (irule Gc_rand >> 
      qexists_tac `A` >>
      qexists_tac `B` >>
      simp[])
  >- (irule Gc_lor >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      `?b. Γ'' = BAG_INSERT (A Or B) b`
        by metis_tac[BAG_INSERT_SUB_BAG_DECOMPOSE] >>
      fs[] >> rw[] >>
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (irule Gc_rorl >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      qexists_tac `Δ` >>
      simp[])
  >- (irule Gc_rorr >>
            qexists_tac `A` >>
            qexists_tac `B` >>
            qexists_tac `Δ` >>
            simp[])
  >- (irule Gc_limp >> 
      qexists_tac `A` >>
      qexists_tac `B` >>
      `?b. Γ'' = BAG_INSERT (A Imp B) b`
        by metis_tac[BAG_INSERT_SUB_BAG_DECOMPOSE] >>
        fs[] >> rw[] >>
        first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (irule Gc_rimp >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      qexists_tac `BAG_INSERT (A Imp B) Δ` >>
      simp[] >>
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (
      irule Gc_cut >>
           
      first_x_assum (qspec_then `BAG_INSERT A Γ'` mp_tac) >>
      rw[] >>
      fs[SUB_BAG_INSERT])
QED

Theorem Gc_rw:
  ∀Γ Δ. Γ Gc Δ ==> ∀Δ'. Δ ≤ Δ' /\ FINITE_BAG Δ' ==> Γ Gc Δ'
Proof
  Induct_on `Γ Gc Δ` >>
  rw[]
  >- (irule Gc_ax >> 
      fs[] >> 
      qexists_tac `A` >>
      fs[SUB_BAG,BAG_IN])
  >- (irule Gc_bot >> fs[SUB_BAG,BAG_IN])
  >- (irule Gc_lc >>
      qexists_tac `A` >>
      qexists_tac `Γ` >>
      fs[])
  >- (irule Gc_rc >>
      qexists_tac `A` >>
      `?b. Δ'' = BAG_INSERT A b`
        by metis_tac[EL_BAG_UNION_SUB_BAG_DECOMPOSE] >>
      fs[] >>
      rw[] >>
      qexists_tac `b` >>
      simp[Once BAG_INSERT_UNION,EL_BAG] >>
      first_x_assum (qspec_then `{|A;A|} ⊎ b` mp_tac) >>
      fs[BAG_INSERT_UNION])
  >- (irule Gc_landl >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      fs[])
  >- (irule Gc_landr >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      fs[])
  >- (irule Gc_rand >> 
      qexists_tac `A` >>
      qexists_tac `B` >>
      `?b. Δ'' = BAG_INSERT (A And B) b`
        by metis_tac[BAG_INSERT_SUB_BAG_DECOMPOSE] >>
      fs[] >> rw[] >> 
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (irule Gc_lor >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      qexists_tac `Γ'` >>
      fs[])
  >- (irule Gc_rorl >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      `?b. Δ'' = BAG_INSERT (A Or B) b`
        by metis_tac[BAG_INSERT_SUB_BAG_DECOMPOSE] >>
      fs[] >> rw[] >>
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (irule Gc_rorr >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      `?b. Δ'' = BAG_INSERT (A Or B) b`
        by metis_tac[BAG_INSERT_SUB_BAG_DECOMPOSE] >>
      fs[] >> rw[] >>
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (irule Gc_limp >> 
      qexists_tac `A` >>
      qexists_tac `B` >>
      qexists_tac `Γ` >>
      fs[] >>
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (irule Gc_rimp >>
      qexists_tac `A` >>
      qexists_tac `B` >>
      qexists_tac `BAG_INSERT (A Imp B) Δ''` >>
      simp[] >>
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- (irule Gc_cut >>
      qexists_tac `A` >>
      first_x_assum (qspec_then `Δ'` mp_tac) >>
      rw[] >>
      first_x_assum (qspec_then `BAG_INSERT A Δ'` mp_tac) >>
      rw[] >>
      fs[SUB_BAG_INSERT])
QED

Theorem Gc_lw_BAG_MERGE:
  !Γ₁ A. Γ₁ Gc A ==> !Γ₂. FINITE_BAG Γ₂ ==> (BAG_MERGE Γ₂ Γ₁) Gc A
Proof
  rw[] >>
  irule Gc_lw >>
  `FINITE_BAG Γ₁` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_MERGE] >>
  qexists_tac `Γ₁` >>
  simp[SUB_BAG,BAG_INN_BAG_MERGE]
QED

Theorem Gc_lw_BAG_UNION:
  ∀Γ A. (Γ Gc A) ==> ∀Γ'. FINITE_BAG Γ' ==> (Γ ⊎ Γ') Gc A
Proof
  rw[] >>
  irule Gc_lw >>
  `FINITE_BAG Γ` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_UNION] >>
  qexists_tac `Γ` >>
  simp[]
QED

Theorem Gc_rw_BAG_UNION:
  ∀Γ Δ. (Γ Gc Δ) ==> !Δ'. FINITE_BAG Δ' ==> Γ Gc (Δ ⊎ Δ')
Proof
  rw[] >>
  irule Gc_rw >>
  `FINITE_BAG Δ` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_UNION] >>
  qexists_tac `Δ` >>
  simp[]
QED

Theorem Gc_lw_BAG_INSERT:
  ∀Γ A. Γ Gc A ==> ∀B. (BAG_INSERT B Γ) Gc A
Proof
  rw[] >>
  irule Gc_lw >>
  `FINITE_BAG Γ` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_THM] >>
  qexists_tac `Γ` >>
  simp[SUB_BAG_INSERT_I]
QED

Theorem Gc_rw_BAG_INSERT:
  ∀Γ Δ. Γ Gc Δ ==> ∀B. Γ Gc (BAG_INSERT B Δ)
Proof
  rw[] >>
  irule Gc_rw >>
  `FINITE_BAG Δ` by metis_tac[Gc_FINITE] >>
  simp[FINITE_BAG_THM] >>
  qexists_tac `Δ` >>
  simp[SUB_BAG_INSERT_I]
QED

val Gc_lc_AeA =
    Q.prove(`∀A e Γ' B. (BAG_INSERT A (BAG_INSERT e (BAG_INSERT A Γ'))) Gc B
            ==> (BAG_INSERT e (BAG_INSERT A Γ')) Gc B`,
            rw[] >>
            `({|A;A|} ⊎ ({|e|} ⊎ Γ')) Gc B`
              by (fs[BAG_UNION_INSERT,ASSOC_BAG_UNION,BAG_INSERT_UNION] >>
                  simp[COMM_BAG_UNION] >>
                  fs[EL_BAG,BAG_UNION]) >>
            `({|A|} ⊎ ({|e|} ⊎ Γ')) Gc B`
              by metis_tac[Gc_lc] >>
            `(({|A|} ⊎ {|e|}) ⊎ Γ') Gc B`
              by fs[ASSOC_BAG_UNION] >>
            `(({|e|} ⊎ {|A|}) ⊎ Γ') Gc B`
              by fs[COMM_BAG_UNION] >>
            fs[BAG_INSERT_UNION] >>
            fs[EL_BAG] >>
            simp[ASSOC_BAG_UNION]);

Theorem Gc_INSERT_TO_MERGE:
  ∀Γ. FINITE_BAG Γ ==> ∀A B. (BAG_INSERT A Γ) Gc B 
      ==> (BAG_MERGE {|A|} Γ) Gc B
Proof
    Induct_on `Γ` >>
    rw[] >>
    Cases_on `A=e`
        >- (fs[] >>
            `BAG_MERGE {|e|} (BAG_INSERT e Γ) = BAG_INSERT e Γ`
              by (simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,FUN_EQ_THM] >>
                  rw[] >> fs[]) >>
            fs[] >>
            `({|e;e|} ⊎ Γ) Gc B` by fs[BAG_INSERT_UNION,ASSOC_BAG_UNION] >>
            `({|e|} ⊎ Γ) Gc B` by metis_tac[Gc_lc] >>
            `{|e|} ⊎ Γ = BAG_INSERT e Γ`
              by rw[BAG_INSERT_UNION] >>
            metis_tac[])
        >- (Cases_on `BAG_IN A Γ`
            >- (`?Γ'. Γ = BAG_INSERT A Γ'` by metis_tac[BAG_DECOMPOSE] >>
                fs[] >>
                `(BAG_INSERT e (BAG_INSERT A Γ')) Gc B`
                  by metis_tac[Gc_lc_AeA] >>
                fs[Gc_lw_BAG_MERGE])
            >- (`BAG_INSERT A (BAG_INSERT e Γ)
                 = BAG_MERGE {|A|} (BAG_INSERT e Γ)`
                  by (`Γ A = 0` by metis_tac[NOT_BAG_IN] >>
                      simp[BAG_INSERT,BAG_MERGE,EMPTY_BAG,FUN_EQ_THM] >>
                      rw[] >>
                      fs[COND_CLAUSES]) >>
                fs[]))
QED

val unibag_AA_A = Q.prove(`unibag ({|A;A|} ⊎ Γ) = unibag ({|A|} ⊎ Γ)`,
  simp[unibag_thm]);

Theorem Gc_unibag:
  ∀Γ A. Γ Gc A <=> (unibag Γ) Gc A
Proof
  rw[] >> EQ_TAC
  >- (`∀Γ. FINITE_BAG Γ ==> ∀A. Γ Gc A ==> (unibag Γ) Gc A`
        suffices_by metis_tac[Gc_FINITE] >>
      gen_tac >>
      Induct_on `BAG_CARD Γ` >>
      rw[]
        >- (`Γ = {||}` by metis_tac[BCARD_0] >>
            fs[])
        >- (Cases_on `unibag Γ = Γ` >- fs[] >>
            drule_then strip_assume_tac unibag_DECOMPOSE >>
            rename [`Γ = {|B;B|} ⊎ Γ0`,`SUC n = BAG_CARD Γ`] >>
            `({|B|} ⊎ Γ0) Gc A` by metis_tac[Gc_lc] >>
            `BAG_CARD ({|B|} ⊎ Γ0) = n` by fs[BAG_CARD_THM] >>
            `FINITE_BAG ({|B|} ⊎ Γ0)` by fs[] >>
            metis_tac[unibag_AA_A]))
   >- metis_tac[unibag_SUB_BAG,Gc_lw,Gc_FINITE,unibag_FINITE]
QED

Theorem Nc_Gc:
  ∀Γ A. (Γ Nc A) ==> ((BAG_OF_SET Γ) Gc {|A|})
Proof
  Induct_on `Γ Nc A` >>
  rw[]
  >- (irule Gc_ax >> simp[] >>
      metis_tac[FINITE_BAG_OF_SET,FINITE_DEF])
  >- (irule Gc_rand >> rw[]
      >- (`(BAG_OF_SET (Γ' ∪ Γ)) Gc {|A|}`
            suffices_by metis_tac[UNION_COMM] >>
          simp[BAG_OF_SET_UNION] >>
          metis_tac[Gc_lw_BAG_MERGE,Gc_FINITE])
      >- (simp[BAG_OF_SET_UNION] >>
              metis_tac[Gc_lw_BAG_MERGE,Gc_FINITE]))
  >- (irule Gc_cut >>
      qexists_tac `A And B` >>
      conj_tac >- metis_tac[Gc_rw_BAG_INSERT,BAG_INSERT_commutes] >>
      `{|A|} Gc {|A|}` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
      `{|A And B|} Gc {|A|}` by metis_tac[Gc_landl] >>
      simp[Once BAG_INSERT_UNION,EL_BAG] >>
      irule Gc_lw_BAG_UNION >>
      simp[] >>
      metis_tac[Nc_FINITE])
  >- (irule Gc_cut >>
      qexists_tac `A And A'` >>
      conj_tac >- metis_tac[Gc_rw_BAG_INSERT,BAG_INSERT_commutes] >>
      `{|A'|} Gc {|A'|}` by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
      `{|A And A'|} Gc {|A'|}` by metis_tac[Gc_landr] >>
      simp[Once BAG_INSERT_UNION,EL_BAG] >>
      irule Gc_lw_BAG_UNION >>
      simp[] >>
      metis_tac[Nc_FINITE])
  >- (irule Gc_rimp >>
      fs[BAG_OF_SET_INSERT] >>
      qexists_tac `A` >>
      qexists_tac `A'` >>
      irule Gc_lw >>
      simp[] >>
      drule Gc_FINITE >>
      rw[] >>
      qexists_tac `BAG_MERGE {|A|} (BAG_OF_SET Γ)` >>
      simp[BAG_MERGE_ELBAG_SUB_BAG_INSERT] >>
      `BAG_MERGE {|A|} (BAG_OF_SET Γ) Gc {|A Imp A';A'|}`
        suffices_by metis_tac[BAG_INSERT_commutes] >>
      metis_tac[Gc_rw_BAG_INSERT])
  >- (rename [`Γ Nc A Imp B`] >>
      simp[BAG_OF_SET_UNION] >>
      (* `?b b'. (Γ = SET_OF_BAG b) ∧ (Γ' = SET_OF_BAG b')`  *)
      (*   by (qexists_tac `BAG_OF_SET Γ` >> *)
      (*       qexists_tac `BAG_OF_SET Γ'` >> *)
      (*       rw[]) >> *)
      (* fs[] >> rw[] > *)>
      (* `unibag (b ⊎ b') Gc {|B|}` suffices_by metis_tac[unibag_UNION] >> *)
      (* `b ⊎ b' Gc {|B|}` suffices_by metis_tac[Gc_unibag] >> *)
      (* irule Gc_lcut >> *)
      (* qexists_tac `A` >> *)
      `FINITE_BAG (BAG_INSERT B (BAG_OF_SET Γ'))` 
        by metis_tac[Nc_FINITE,FINITE_BAG_OF_SET,FINITE_BAG_INSERT] >>
      `(BAG_INSERT B (BAG_OF_SET Γ')) Gc {|B|}` 
        by (irule Gc_ax >> rw[]) >>
      `(BAG_INSERT (A Imp B) (BAG_OF_SET Γ')) Gc {|B|}`
        by metis_tac[Gc_limp,Gc_rw_BAG_INSERT,BAG_INSERT_commutes] >>
      `((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ')) Gc {|B|}`
        by (irule Gc_cut >>
            qexists_tac `A` >>
            rw[]
              >- (`BAG_OF_SET Γ' ⊎ BAG_OF_SET Γ Gc {|B;A|}`
                    suffices_by metis_tac[COMM_BAG_UNION,BAG_INSERT_commutes] >>
                  irule Gc_rw_BAG_INSERT >>
                  irule Gc_lw_BAG_UNION >>
                  conj_tac >- metis_tac[Gc_FINITE] >>
                  simp[])
              >- (
                  qexists_tac `A` >>
                  qexists_tac `B` >>
                  qexists_tac `BAG_OF_SET Γ'` >>
                  simp[]
              

  qabbrev_tac `Δ = ((BAG_OF_SET Γ) ⊎ (BAG_OF_SET Γ'))` >>
      `FINITE_BAG (BAG_INSERT A' Δ)`
        by (simp[Abbr`Δ`] >>
            metis_tac[Nc_FINITE,FINITE_BAG_OF_SET,FINITE_BAG_UNION]) >>
      `(BAG_INSERT A' Δ) Gc {|A'|}`
        by metis_tac[Gc_ax,BAG_IN_BAG_INSERT,FINITE_BAG_THM] >>
      `(BAG_INSERT A' Δ) Gc {|A;A'|}`
        by metis_tac[Gc_rw_BAG_INSERT] >>
      `Δ Gc {|A;A'|}`
        by (simp[Abbr`Δ`] >>
            `BAG_OF_SET Γ' ⊎ BAG_OF_SET Γ Gc {|A';A|}`
             suffices_by metis_tac[COMM_BAG_UNION,BAG_INSERT_commutes]
            irule Gc_lw_BAG_UNION >>
            simp[] >>
            conj_tac >- metis_tac[Nc_FINITE] >>
            metis_tac[Gc_rw_BAG_INSERT]) >>
      `(BAG_INSERT (A Imp A') Δ) Gc {|A'|}`
        by metis_tac[Gc_limp] >>
      `Δ Gc {|A Imp A'|}`
        by (simp[Abbr`Δ`] >>
            metis_tac[Gc_lw_BAG_UNION,Gc_FINITE]) >>
      
      `Δ Gc {|A'|}`
        by metis_tac[Gc_cut] >>
      `(unibag (BAG_OF_SET Γ ⊎ BAG_OF_SET Γ')) Gc {|A'|}` by metis_tac[Gc_unibag] >>
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
