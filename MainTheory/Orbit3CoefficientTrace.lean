import MainTheory.Orbit3CoefficientCollection

/-! # Soundness of coefficient accumulation with checked intermediate states

Each step is a full kernel equality. Telescoping evaluations joins all steps
and therefore covers every input term. Intermediate states are candidate
integer data, not externally trusted computation results.
-/

namespace MainTheory.Orbit3CoefficientTrace

open MainTheory.DyadicCoefficientTree MainTheory.Orbit3CoefficientCollection
open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3CoordinateRealization
open SixQubit.Generated
open scoped BigOperators

theorem telescoping (n : ℕ) (v : ℕ → ℝ) :
    (∑ a : Fin n, (v (a.val + 1) - v a.val)) = v n - v 0 := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    rw [ih (fun k => v (k + 1))]
    ring

theorem trace_evaluation {h n : ℕ} (states : ℕ → Tree h)
    (terms : Fin n → List (Fin (2 ^ h) × ℤ))
    (steps : ∀ a : Fin n, accumulate (states a.val) (terms a) = states (a.val + 1))
    (y : Fin (2 ^ h) → ℝ) :
    evaluate (states n) y = evaluate (states 0) y +
      ∑ a : Fin n, ((terms a).map fun e => (e.2 : ℝ) * y e.1).sum := by
  have he (a : Fin n) : ((terms a).map fun e => (e.2 : ℝ) * y e.1).sum =
      evaluate (states (a.val + 1)) y - evaluate (states a.val) y := by
    have ht := evaluate_accumulate (states a.val) (terms a) y
    rw [steps a] at ht
    linarith
  simp_rw [he]
  rw [telescoping n (fun k => evaluate (states k) y)]
  ring

def rowTerms (P : Fin 3 → SS.PauliString 6) (a : Fin 64) : List (Fin (2 ^ 9) × ℤ) :=
  (List.finRange 64).flatMap fun b => termList P a b

theorem rowTerms_evaluation (P : Fin 3 → SS.PauliString 6) (a : Fin 64) (y : Fin 269 → ℝ) :
    ((rowTerms P a).map fun e => (e.2 : ℝ) * padded y e.1).sum =
      ∑ b : Fin 64, (coefficient P a b : ℝ) *
        tableMatrix y (Orbit3CubicTriples.pairIndex a b) (rightIndex P a b) := by
  unfold rowTerms
  simp only [List.map_flatMap, sum_flatMap_real, termList_evaluation,
    List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem pauli_trace_evaluation (P : Fin 3 → SS.PauliString 6) (states : ℕ → Tree 9)
    (initial : states 0 = zero 9)
    (steps : ∀ a : Fin 64, accumulate (states a.val) (rowTerms P a) = states (a.val + 1))
    (y : Fin 269 → ℝ) : evaluate (states 64) (padded y) = rawEvaluation P y := by
  rw [trace_evaluation states (rowTerms P) steps, initial, evaluate_zero, zero_add]
  simp_rw [rowTerms_evaluation]
  rfl

end MainTheory.Orbit3CoefficientTrace
