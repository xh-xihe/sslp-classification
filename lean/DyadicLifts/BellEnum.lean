import DyadicLifts.Bell
import DyadicLifts.PauliHerm

/-!
# Reducing an arbitrary two-qubit Pauli to the Bell table

The KL propagation case-splits on a two-qubit bare Pauli `B : Fin 2 → SQ`.
`mel_bflag_pauli` rewrites `mel (bflag p) B (bflag q)` to its `![B 0, B 1]` form so
the concrete table lemmas `Bell.mel_II … mel_ZX` apply after a `rcases` on `B 0, B 1`.
-/

open scoped BigOperators

namespace DyadicLifts

open SS

/-- A two-qubit Pauli equals the explicit vector of its two entries. -/
lemma pauli2_eta (B : Fin 2 → SQ) : B = ![B 0, B 1] := by
  funext i; fin_cases i <;> rfl

/-- Rewrite a Bell matrix element of an arbitrary `B` to its tabulated `![B 0, B 1]` form. -/
lemma mel_bflag_pauli (p q : Bool) (B : Fin 2 → SQ) :
    mel (bflag p) B (bflag q) = mel (bflag p) ![B 0, B 1] (bflag q) := by
  conv_lhs => rw [pauli2_eta B]

/-! ## Weights of the special Paulis -/

lemma pauliWt_IX : pauliWt ![SQ.I, SQ.X] = 1 := by decide
lemma pauliWt_XI : pauliWt ![SQ.X, SQ.I] = 1 := by decide
lemma pauliWt_YZ : pauliWt ![SQ.Y, SQ.Z] = 2 := by decide
lemma pauliWt_ZY : pauliWt ![SQ.Z, SQ.Y] = 2 := by decide
lemma pauliWt_YY : pauliWt ![SQ.Y, SQ.Y] = 2 := by decide
lemma pauliWt_ZZ : pauliWt ![SQ.Z, SQ.Z] = 2 := by decide
lemma pauliWt_XX : pauliWt ![SQ.X, SQ.X] = 2 := by decide
lemma pauliWt_II : pauliWt ![SQ.I, SQ.I] = 0 := by decide

end DyadicLifts
