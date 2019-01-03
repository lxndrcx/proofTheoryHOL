(* Equivalence of Sequent Calculus and Natural Deduction
   Starting with intuitionistic propositional case
 *)

open HolKernel boolLib Parse bossLib;
open pred_setTheory bagTheory;

val _ = new_theory "ProofTheory";

val _ = Datatype `formula =
Var 'a
| Or formula formula
| And formula formula
| Imp formula formula
| Bot`;

val _ = set_mapped_fixity {tok = "-->", fixity = Infixr(460), term_name = "Imp"};
val _ = set_mapped_fixity {tok = "<-->", fixity = Infix(NONASSOC, 450), term_name = "BiImp"};
val _ = set_mapped_fixity {tok = "&&", fixity = Infixr(490), term_name = "And"};
val _ = set_mapped_fixity {tok = "%%", fixity = Infixr(490), term_name = "Or"};
val _ = set_mapped_fixity {tok = "~~", fixity = Prefix(510), term_name = "Not"};

val Not_def = Define `Not f = f --> Bot`;
val BiImp_def = Define `f <--> f' = (f --> f') && (f' --> f)`;
val Top_def = Define `Top = Bot --> Bot`;


(** Natural Deduction for intuitionistic logic **)
(* NDi is the 'deduciblility' relation for this system *)
(* A, B and C are used to represent formulae *)
(* D, D1, D2, D3 are used to represent the set of open/not-discharged assumptions in the deduction *)
(* In Troelstra & Schwichtenberg the deductions are trees, but to represent them this was here val *)
(*     would have complicated things a lot, and is unnessesary to represent the deductions in HOL *)

val (NDi_rules, NDi_induct, NDi_cases) = Hol_reln `
(!A D. A IN D ==> NDi D A) (* Base case: A formula `A` is deducible from any set `D` containing `A` *)
                            /\ (!A B D1 D2. (NDi D1 A /\ (NDi D2 B) ==> (NDi (D1 UNION D2) (A && B)) (* And Introduction *)
`; 


(* val _ = set_mapped_fixity {tok = "N|-", fixity = Infix(NONASSOC,400), term_name = "NiDerives"}; *)
(* val (NiDerives_rules, NiDerives_induct, NiDerives_cases) = Hol_reln `` *)
