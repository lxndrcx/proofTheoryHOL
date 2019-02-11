open HolKernel Parse boolLib bossLib;
open bagTheory;
open pred_setTheory;

val _ = new_theory "BagLemmata";

Theorem BAG_INSERT_FILTER_COMP_OF_SET
        `!s a. (BAG_INSERT a (BAG_FILTER (COMPL {a}) (BAG_OF_SET s)))
          = (BAG_OF_SET (a INSERT s))` (
  rw[BAG_OF_SET,BAG_INSERT,BAG_FILTER_DEF,COMPL_DEF,INSERT_DEF,FUN_EQ_THM] >>
  metis_tac[]);

Theorem BAG_INSERT_BAG_OF_SET_BAG_DIFF
`!e s. BAG_INSERT e (BAG_OF_SET s - {|e|}) = BAG_MERGE {|e|} (BAG_OF_SET s)` (
  simp[BAG_OF_SET,BAG_INSERT,BAG_DIFF,FUN_EQ_THM,BAG_MERGE,EMPTY_BAG_alt] >>
  rw[EMPTY_BAG,COND_CLAUSES] >> fs[]);

val _ = export_theory();
