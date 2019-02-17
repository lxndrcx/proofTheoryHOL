open HolKernel Parse boolLib bossLib;

val _ = new_theory "FormulaSyntax";

val _ = set_fixity "Imp" (Infixr 460);
val _ = set_fixity "BiImp" (Infix (NONASSOC, 450) );
val _ = set_fixity "And" (Infixr 490);
val _ = set_fixity "Or" (Infixr 490);
val _ = set_fixity "Not" (Prefix 510);

val _ = Datatype `formula =
  Var 'a
  | Or formula formula
  | And formula formula
  | Imp formula formula
  | Bot`;


val Not_def = Define `Not A = A Imp Bot`;
val BiImp_def = Define `A BiImp B = (A Imp B) And (B Imp A)`;
val Top_def = Define `Top = Bot Imp Bot`;

val _ = export_theory();

