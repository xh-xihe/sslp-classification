import MainTheory.DyadicCoefficientTree
import MainTheory.Orbit3PauliMomentInterpretation

/-! # Collecting physical Pauli moment coefficients inside the kernel

The list is computed from all 4096 ordered bit pairs and the checked actual
coordinate table. Collecting repeated terms is justified by a general fold
theorem, rather than by importing an external symbolic evaluation.
-/

namespace MainTheory.Orbit3CoefficientCollection

open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3CoordinateRealization
open MainTheory.DyadicCoefficientTree SixQubit.Generated
open scoped BigOperators

def embed (c : Fin 269) : Fin (2 ^ 9) := ⟨c.val, by have hc := c.isLt; norm_num; omega⟩

noncomputable def padded (y : Fin 269 → ℝ) (j : Fin (2 ^ 9)) : ℝ :=
  if h : j.val < 269 then y ⟨j.val, h⟩ else 0

theorem padded_embed (y : Fin 269 → ℝ) (c : Fin 269) : padded y (embed c) = y c := by
  simp only [padded, embed, c.isLt, ↓reduceDIte]

def termList (P : Fin 3 → SS.PauliString 6) (a b : Fin 64) : List (Fin (2 ^ 9) × ℤ) :=
  match Orbit3Coordinates.Data.entry (Orbit3CubicTriples.pairIndex a b) (rightIndex P a b) with
  | none => []
  | some e => [(embed e.1, coefficient P a b)]

def terms (P : Fin 3 → SS.PauliString 6) : List (Fin (2 ^ 9) × ℤ) :=
  (List.finRange 64).flatMap fun a => (List.finRange 64).flatMap fun b => termList P a b

def coefficients (P : Fin 3 → SS.PauliString 6) : Tree 9 := accumulate (zero 9) (terms P)

theorem termList_evaluation (P : Fin 3 → SS.PauliString 6) (a b : Fin 64) (y : Fin 269 → ℝ) :
    ((termList P a b).map fun e => (e.2 : ℝ) * padded y e.1).sum =
      (coefficient P a b : ℝ) * tableMatrix y (Orbit3CubicTriples.pairIndex a b) (rightIndex P a b) := by
  unfold termList tableMatrix
  cases Orbit3Coordinates.Data.entry (Orbit3CubicTriples.pairIndex a b) (rightIndex P a b) <;>
    simp [padded_embed]

theorem sum_flatMap_real {A : Type*} (l : List A) (f : A → List ℝ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem coefficients_evaluation (P : Fin 3 → SS.PauliString 6) (y : Fin 269 → ℝ) :
    evaluate (coefficients P) (padded y) = rawEvaluation P y := by
  rw [coefficients, evaluate_accumulate, evaluate_zero, zero_add]
  unfold terms rawEvaluation
  simp only [List.map_flatMap, sum_flatMap_real, termList_evaluation,
    List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]

end MainTheory.Orbit3CoefficientCollection
