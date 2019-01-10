(* ========================================================================== *)
(* Equivalence of Sequent Calculus and Natural Deduction                      *)
(* Working from Troelstra and Schwichtenburg - Basic Proof Theory 2nd Edition *)
(*                                                                            *)
(* ========================================================================== *)

open HolKernel boolLib Parse bossLib;
open bagLib bagTheory;
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
(* D, D1, D2, D3 are used to represent the set of open assumptions *)
(* I'm representing the deductions simply with unlabeled sets of
   open assumptions, as in T&S 2.1.8-2.1.9 (p.41--44) *)

val (Nm_rules, Nm_ind, Nm_cases) = Hol_reln `
(! (A :'a formula) (D :'a formula set). Nm {A} A) (* Base case *)
/\ (!A B D1 D2. (Nm D1 A) /\ (Nm D2 B)
   ==> (Nm (D1 UNION D2) (A And B))) (* And Intro *)
/\ (!A B D. (Nm D (A And B)) ==> Nm D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Nm D (A And B)) ==> Nm D B) (* And Elim Right Conjunct *)
/\ (!A B D1 D2. (Nm D1 B) /\ (D2 = (D1 DIFF {A}))
   ==> Nm D2 (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Nm D1 (A Imp B)) /\ (Nm D2 A)
   ==> Nm (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Nm D A ==> Nm D (A Or B)) (* Or Intro right *)
/\ (!A B D. Nm D B ==> Nm D (A Or B)) (* Or Intro left *)
/\ (!A B C D1 D2 D3 D4. (Nm D1 (A Or B)) /\
(Nm D2 C) /\ (Nm D3 C) /\
(D4 = ((D1 UNION D2 UNION D3) DIFF {A;B})) ==> Nm D4 C)`; (* Or Elim *)

val [Nm_ax, Nm_andi, Nm_andel, Nm_ander,
     Nm_impi, Nm_impe, Nm_orir, Nm_oril, Nm_ore] = CONJUNCTS Nm_rules;

(** Natural Deduction for intuitionistic logic **)
(* Ni is the 'deduciblility' relation for this system *)
val (Ni_rules, Ni_ind, Ni_cases) = Hol_reln `
(! (A :'a formula) (D :'a formula set). Ni {A} A) (* Base case *)
/\ (!A B D1 D2. (Ni D1 A) /\ (Ni D2 B)
   ==> (Ni (D1 UNION D2) (A And B))) (* And Intro *)
/\ (!A B D. (Ni D (A And B)) ==> Ni D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Ni D (A And B)) ==> Ni D B) (* And Elim Right Conjunct *)
/\ (!A B D1 D2. (Ni D1 B) /\ (D2 = (D1 DIFF {A}))
   ==> Ni D2 (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Ni D1 (A Imp B)) /\ (Ni D2 A)
   ==> Ni (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Ni D A ==> Ni D (A Or B)) (* Or Intro right *)
/\ (!A B D. Ni D B ==> Ni D (A Or B)) (* Or Intro left *)
/\ (!A B C D1 D2 D3 D4. (Ni D1 (A Or B)) /\
(Ni D2 C) /\ (Ni D3 C) /\
(D4 = ((D1 UNION D2 UNION D3) DIFF {A;B})) ==> Ni D4 C) (* Or Elim *)
/\ (!A D. (Ni D Bot) ==> (Ni D A))`; (* Intuitionistic Absurdity Rule *)

val [Ni_ax, Ni_andi, Ni_andel, Ni_ander, Ni_impi, Ni_impe,
     Ni_orir, Ni_oril, Ni_ore, Ni_absurd] = CONJUNCTS Ni_rules;

(** Natural Deduction for classical logic **)
(* Nc is the 'deduciblility' relation for this system *)
val (Nc_rules, Nc_ind, Nc_cases) = Hol_reln `
(! (A :'a formula) (D :'a formula set). Nc {A} A) (* Base case *)
/\ (!A B D1 D2. (Nc D1 A) /\ (Nc D2 B)
   ==> (Nc (D1 UNION D2) (A And B))) (* And Intro *)
/\ (!A B D. (Nc D (A And B)) ==> Nc D A) (* And Elimination Left Conjunct *)
/\ (!A B D. (Nc D (A And B)) ==> Nc D B) (* And Elim Right Conjunct *)
/\ (!A B D1 D2. (Nc D1 B) /\ (D2 = (D1 DIFF {A}))
   ==> Nc D2 (A Imp B)) (* Imp Intro *)
/\ (!A B D1 D2. (Nc D1 (A Imp B)) /\ (Nc D2 A)
   ==> Nc (D1 UNION D2) B) (* Imp Elim *)
/\ (!A B D. Nc D A ==> Nc D (A Or B)) (* Or Intro right *)
/\ (!A B D. Nc D B ==> Nc D (A Or B)) (* Or Intro left *)
/\ (!A B C D1 D2 D3 D4. (Nc D1 (A Or B)) /\
(Nc D2 C) /\ (Nc D3 C) /\
(D4 = ((D1 UNION D2 UNION D3) DIFF {A;B})) ==> Nc D4 C) (* Or Elim *)
/\ (!A D. (Nc D (Bot))
   ==> Nc (D DIFF {Not A}) A)`; (* Classical absurdidty rule *)

val [Nc_ax, Nc_andi, Nc_andel, Nc_ander, Nc_impi, Nc_impe,
     Nc_orir, Nc_oril, Nc_ore, Nc_absurd] = CONJUNCTS Nc_rules;

val NmThm = Define `NmThm A = Nm EMPTY A`;
val NiThm = Define `NiThm A = Ni EMPTY A`;
val NcThm = Define `NcThm A = Nc EMPTY A`;

(* Example deductions *)
val Nm_example = Q.prove(`NmThm (A Imp (B Imp A))`,
`Nm {A} A` by rw[Nm_rules] >>
`Nm {B} B` by rw[Nm_rules] >>
`{A} UNION {B} = {A;B}` by simp[UNION_DEF,INSERT_DEF] >>
`Nm {A;B} (A And B)` by metis_tac[Nm_rules] >>
`Nm {A;B} (A)` by metis_tac[Nm_rules] >>
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

(** Sequent Calculus (Gentzen System) for minimal logic **)
(* Gm is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* S is used to represent the multiset of the Antecedent Context *)
(* The consequent is always a single formula in the minimal logic *)

val (Gm_rules, Gm_ind, Gm_cases) = Hol_reln `
(!A:'a formula. Gm {|A|} A) (* Ax *)
/\ (!A S C. Gm S D ==> Gm (BAG_INSERT A S) C) (* Left Weakening *)
/\ (!A S C. (Gm ({|A;A|} + S) C)
   ==> Gm ({|A|} + S) C) (* Left Contraction *)
/\ (!A B S C. (Gm (BAG_INSERT A S) C)
   ==> (Gm (BAG_INSERT (A And B) S) C)) (* Left And 1 *)
/\ (!A B S C. (Gm (BAG_INSERT B S) C)
   ==> (Gm (BAG_INSERT (A And B) S) C)) (* Left And 2 *)
/\ (!A B S. (Gm S A) /\ (Gm S B)
   ==> (Gm S (A And B))) (* Right And *)
/\ (!A B S C. (Gm (BAG_INSERT A S) C)
    /\ (Gm (BAG_INSERT B S) C)
   ==> (Gm (BAG_INSERT (A Or B) S) C)) (* Left Or *)
/\ (!A B S. (Gm S A)
   ==> (Gm S (A Or B))) (* Right Or 1 *)
/\ (!A B S. (Gm S B)
   ==> (Gm S (A Or B))) (* Right Or 2 *)
/\ (!A B S C. (Gm S A) /\ (Gm (BAG_INSERT B S) C)
   ==> (Gm (BAG_INSERT (A Imp B) S) C)) (* Left Imp *)
/\ (!A B S. (Gm (BAG_INSERT A S) B)
   ==> (Gm S (A Imp B))) (* Right Imp *)
∧  (∀A B Γ Γ'. (Gm Γ A) ∧ (Gm (BAG_INSERT A Γ') B) ==> Gm (Γ + Γ') B)` (* Cut *)

val [Gm_ax, Gm_lw, Gm_lc, Gm_landl, Gm_landr, Gm_rand,
     Gm_lor, Gm_rorl, Gm_rorr, Gm_limp, Gm_rimp, Gm_cut] = CONJUNCTS Gm_rules;

val GmThm = Define `GmThm A = Gm EMPTY_BAG A`;

val Gm_example1 =
    Q.prove(`GmThm ((A And B) Imp (B And A))`, rw[GmThm,Gm_rules]);

val Gm_example2 =
    Q.prove (`GmThm ((A Imp (A Imp B)) Imp (A Imp B))`,
             rw[GmThm] >> metis_tac[Gm_rules]);

(** Sequent Calculus (Gentzen System) for intuitionistic logic **)
(* Gi is the 'deduciblility' relation for this system *)
(* S and D are used to represent the bag Antecedent and Consequent Contexts *)
(* The Consequent has at most one formula for intuitionistic logic *)

(* Maybe I should change the consequent to option type rather than
   EMPTY or SINGLETON? *)
val (Gi_rules, Gi_ind, Gi_cases) = Hol_reln `
(!A:'a formula. Gi {|A|} {|A|}) (* Ax *)
/\ (Gi {|Bot|} {||}) (* LBot *)
/\ (!A S D. Gi S D ==> Gi (BAG_INSERT A S) D) (* Left Weakening *)
/\ (!A S. Gi S EMPTY_BAG ==> Gi S {|A|}) (* Right Weakening *)
/\ (!A S D. (Gi ({|A;A|} + S) D)
    ==> Gi ({|A|} + S) D) (* Left Contraction *)
/\ (!A B S D. (Gi (BAG_INSERT A S) D)
   ==> (Gi (BAG_INSERT (A And B) S) D)) (* Left And 1 *)
/\ (!A B S D. (Gi (BAG_INSERT B S) D)
   ==> (Gi (BAG_INSERT (A And B) S) D)) (* Left And 2 *)
/\ (!A B S. (Gi S {|A|}) /\ (Gi S {|B|})
   ==> (Gi S {|A And B|})) (* Right And *)
/\ (!A B S D. (Gi (BAG_INSERT A S) D)
    /\ (Gi (BAG_INSERT B S) D)
   ==> (Gi (BAG_INSERT (A Or B) S) D)) (* Left Or *)
/\ (!A B S. (Gi S {|A|})
   ==> (Gi S {|A Or B|})) (* Right Or 1 *)
/\ (!A B S. (Gi S {|B|})
   ==> (Gi S {|A Or B|})) (* Right Or 2 *)
/\ (!A B S D. (Gi S {|A|}) /\ (Gi (BAG_INSERT B S) D)
   ==> (Gi (BAG_INSERT (A Imp B) S) D)) (* Left Imp *)
/\ (!A B S. (Gi (BAG_INSERT A S) {|B|})
   ==> (Gi S {|A Imp B|})) (* Right Imp *)
∧  (∀A Γ Δ. (Gi Γ {|A|}) ∧ (Gi {|A|} Δ) ==> Gi Γ Δ)` (* Cut *)

val [Gi_ax, Gi_bot, Gi_lw, Gi_rw, Gi_lc, Gi_landl, Gi_landr, Gi_rand, Gi_lor,
     Gi_rorl, Gi_rorr, Gi_limp, Gi_rimp, Gi_cut] = CONJUNCTS Gi_rules;

val GiThm = Define `GiThm A = Gi EMPTY_BAG {|A|}`

val Gi_example1 = Q.prove(`Gi {|P And (Not P)|} {|Bot|}`,
`Gi {|P And Not P|} EMPTY_BAG` suffices_by metis_tac[Gi_rules] >>
`Gi {|Bot|} EMPTY_BAG` by metis_tac[Gi_rules] >>
`Gi {|P;Bot|} EMPTY_BAG` by metis_tac[Gi_rules] >>
`{|P;Bot|} = {|Bot;P|}` by metis_tac[BAG_INSERT_commutes] >>
`Gi ({|Bot;P|}) EMPTY_BAG` by metis_tac[Gi_rules] >>
`Gi {|P|} {|P|}` by metis_tac[Gi_rules] >>
`Gi {|P Imp Bot;P|} {||}` by metis_tac[Gi_rules,BAG_INSERT] >>
`Gi {|Not P;P|} {||}` by metis_tac[Not_def] >>
`Gi {|P And Not P;P|} {||}` by metis_tac[Gi_rules] >>
`Gi {|P And Not P;P And Not P|} {||}`
  by metis_tac[Gi_rules,BAG_INSERT_commutes] >>
`{|A;A|} = {|A;A|} + {||}` by simp[] >>
`{|A|} = {|A|} + {||}` by simp[] >>
qspecl_then [`P And Not P`,`{||}`,`{||}`] mp_tac (Gi_lc) >>
simp[]
);

(** Sequent Calculus (Gentzen System) for classical logic **)
(* Gc is the 'deduciblility' relation for this system *)
(* Both contexts are arbitrary size finite bags *)
val (Gc_rules, Gc_ind, Gc_cases) = Hol_reln `
(!A:'a formula. Gc {|A|} {|A|}) (* Ax *)
/\ (Gc {|Bot|} {||}) (* LBot *)
/\ (!A S D. Gc S D ==> Gc (BAG_INSERT A S) D) (* Left Weakening *)
/\ (!A S D. Gc S D ==> Gc S (BAG_INSERT A D)) (* Right Weakening *)
/\ (!A S D. (Gc ({|A;A|} + S) D) 
   ==> Gc ({|A|} + S) D) (* Left Contraction *)
/\ (!A S D. (Gc S ({|A;A|} + D))
   ==> Gc S ({|A|} + D)) (* Right Contraction *)
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
∧  (∀A Γ Γ' Δ Δ'. (Gc Γ (BAG_INSERT A Δ))
     ∧ (Gc (BAG_INSERT A Γ') Δ')
     ==> Gc (Γ + Γ') (Δ + Δ'))` (* Cut *)

val [Gc_ax, Gc_bot, Gc_lw, Gc_rw, Gc_lc, Gc_rc, Gc_landl, Gc_landr, Gc_rand,
     Gc_lor, Gc_rorl, Gc_rorr, Gc_limp, Gc_rimp, Gc_cut] = CONJUNCTS Gc_rules;

val GcThm = Define `GcThm A = Gc EMPTY_BAG {|A|}`

val Gc_example1 = Q.prove(`GcThm (((P Imp Q) Imp P) Imp P)`,rw[GcThm] >>
`Gc {|P|} {|P|}` by metis_tac[Gc_rules] >>
`Gc {|P|} {|Q;P|}` by metis_tac[Gc_rules] >>
`Gc {||} {|P Imp Q;P|}` by metis_tac[Gc_rules] >>
`Gc {|(P Imp Q) Imp P|} {|P|}` by metis_tac[Gc_rules] >>
`Gc {||} {|((P Imp Q) Imp P) Imp P|}` by metis_tac[Gc_rules]);




(* ========================================================================== *)
(* Proofs of equivalence of N and G Systems                                   *)
(*                                                                            *)
(*                                                                            *)
(* ========================================================================== *)

Theorem Nm_Gm `∀Γ A. Nm Γ A ==> Gm (BAG_OF_SET Γ) A` (
 Induct_on `Nm ` >>
 reverse ( rw[Nm_rules,Gm_rules] ) >> 
 >- ()
)

(* Theorem Gm_Nm `∀Γ A.Gm Γ A ==> Nm (SET_OF_BAG Γ) A` () *)

val _ = export_theory()
