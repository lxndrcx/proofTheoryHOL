open HolKernel boolLib Parse bossLib
open FormulaSyntaxTheory IntuitionisticProofTheory
val _ = new_theory "pp"

val foo = save_thm("foo", TRUTH);

val _ = export_theory()

