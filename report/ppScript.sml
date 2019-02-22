open HolKernel boolLib Parse bossLib
open FormulaSyntaxTheory IntuitionisticProofTheory bagTheory pred_setTheory
val _ = new_theory "pp"

val foo = save_thm("foo", TRUTH);

val _ = set_fixity "G" (Infix (NONASSOC, 450));
val _ = set_fixity "N" (Infix (NONASSOC, 450));
val _ = set_fixity "Nd" (Infix (NONASSOC, 450));
val _ = set_fixity "BAG_MERGE" (Infixl 500);

val makecons = Q.prove(
`BAG_INSERT x {||} + BAG_INSERT y {||} = BAG_INSERT x (BAG_INSERT y {||})`,
rw[BAG_INSERT,EMPTY_BAG,FUN_EQ_THM,BAG_UNION] >> rw[]);

val noins = ONCE_REWRITE_RULE[INSERT_SING_UNION];
val noemp = REWRITE_RULE[UNION_EMPTY];
val nobins = REWRITE_RULE[BAG_INSERT_UNION];
val nobemp = REWRITE_RULE[EL_BAG,BAG_UNION_EMPTY,makecons];

val N_rules' =
  save_thm("N_rules'",N_rules|>noins|>noemp);

val Nd_rules' = save_thm("Nd_rules'",Nd_rules|>REWRITE_RULE[DELETE_DEF]);

val G_rules' =
  save_thm("G_rules'",G_rules|> nobins |> nobemp);

val N_lw' =
  save_thm("N_lw'",N_lw|>noins|>noemp);
val Nd_lw' =
  save_thm("Nd_lw'",Nd_lw|>noins|>noemp);

val BAG_MERGE_ELBAG_SUB_BAG_INSERT' =
  save_thm("BAG_MERGE_ELBAG_SUB_BAG_INSERT'", BAG_MERGE_ELBAG_SUB_BAG_INSERT |>
  nobins |> nobemp);

val BAG_INSERT_EQ_MERGE_DIFF' = save_thm("BAG_INSERT_EQ_MERGE_DIFF'",
BAG_INSERT_EQ_MERGE_DIFF |> nobins |> nobemp);

val BAG_MERGE_BAG_INSERT' = save_thm("BAG_MERGE_BAG_INSERT'",
BAG_MERGE_BAG_INSERT |> nobins |> nobemp);

val BAG_OF_SET_INSERT' = save_thm("BAG_OF_SET_INSERT'", BAG_OF_SET_INSERT |>
noins |> noemp);

val SET_OF_EL_BAG' = save_thm("SET_OF_EL_BAG'", SET_OF_EL_BAG |> nobemp);

val BAG_OF_SET_EQ_INSERT' = save_thm("BAG_OF_SET_EQ_INSERT'",
BAG_OF_SET_EQ_INSERT |> noins |> noemp |> nobins |> nobemp);

val unibag_INSERT' = save_thm("unibag_INSERT'", unibag_INSERT |> nobins |>
nobemp);

val unibag_EQ_BAG_INSERT' = save_thm("unibag_EQ_BAG_INSERT'",
unibag_EQ_BAG_INSERT |> nobins |> nobemp);


val unibag_EL_MERGE_cases' = save_thm("unibag_EL_MERGE_cases'",
unibag_EL_MERGE_cases |> nobins |> nobemp);

val N_impi_DELETE' = save_thm("N_impi_DELETE'", N_impi_DELETE |>
REWRITE_RULE[DELETE_DEF]);

val G_lw_BAG_INSERT' = save_thm("G_lw_BAG_INSERT'", G_lw_BAG_INSERT |> nobins |>
nobemp);

val _ = export_theory()

