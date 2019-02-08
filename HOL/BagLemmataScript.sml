open HolKernel Parse boolLib bossLib;
open bagTheory;
open pred_setTheory;

val _ = new_theory "BagLemmata";

Theorem BAG_OF_SET_UNION `∀Γ Γ'. BAG_OF_SET (Γ ∪ Γ')
                          = (BAG_MERGE (BAG_OF_SET Γ) (BAG_OF_SET Γ'))` (
rw[UNION_DEF,BAG_OF_SET,BAG_MERGE,FUN_EQ_THM] >> rw[] >> fs[]);

Theorem BAG_OF_SET_DIFF `BAG_OF_SET (Γ DIFF Γ')
                         = BAG_FILTER (COMPL Γ') (BAG_OF_SET Γ)` (
simp[DIFF_DEF,BAG_OF_SET,BAG_FILTER_DEF] >> metis_tac[]);

Theorem BAG_OF_SET_INSERT
`!e s. BAG_OF_SET (e INSERT s) = BAG_MERGE {|e|} (BAG_OF_SET s)` (
rw[BAG_OF_SET,INSERT_DEF,BAG_MERGE,EMPTY_BAG,FUN_EQ_THM,BAG_INSERT] >> 
rw[IN_DEF]
 >- (fs[] >>
     `s e = F` by metis_tac[] >>
     fs[COND_CLAUSES])
 >- (`(x = e) = F` by metis_tac[] >>
     fs[COND_CLAUSES])
 >- (`(x = e) = F` by metis_tac[] >>
     `(s x) = T` by metis_tac[] >>
     fs[COND_CLAUSES]));

Theorem BAG_MERGE_SUB_BAG_UNION `∀s t. ((BAG_MERGE s t) ≤ (s ⊎ t))` (
  simp[SUB_BAG,BAG_MERGE,BAG_UNION,BAG_INN]);

Theorem BAG_MERGE_EMPTY
`∀b. ((BAG_MERGE {||} b) = b) /\ ((BAG_MERGE b {||}) = b)` (
  rw[BAG_MERGE,FUN_EQ_THM,EMPTY_BAG]);

Theorem BAG_INSERT_FILTER_COMP_OF_SET 
        `∀s a. (BAG_INSERT a (BAG_FILTER (COMPL {a}) (BAG_OF_SET s)))
          = (BAG_OF_SET (a INSERT s))` (
  rw[BAG_OF_SET,BAG_INSERT,BAG_FILTER_DEF,COMPL_DEF,INSERT_DEF,FUN_EQ_THM] >>
  metis_tac[]); 

Theorem BAG_MERGE_ELBAG_SUB_BAG_INSERT 
        `∀A b. (BAG_MERGE {|A|} b) ≤ (BAG_INSERT A b)` (
  rw[] >> simp[BAG_MERGE,BAG_INSERT,EMPTY_BAG,SUB_BAG,BAG_INN] >> rw[]);


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

val _ = overload_on ("unibag", ``\b. BAG_OF_SET (SET_OF_BAG b)``);

val unibag_thm = save_thm("unibag_thm", CONJ BAG_OF_SET SET_OF_BAG);

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

val _ = export_theory();
