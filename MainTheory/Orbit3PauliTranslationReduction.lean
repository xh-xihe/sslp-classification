import MainTheory.Orbit3PauliCubicExpansion
import MainTheory.Orbit3SamplingSpectatorX
import MainTheory.Orbit3CubicBasis

/-! # Translation reduction of physical Pauli products to XOR-zero cubics

An explicit equivalence partitions all ordered triples into 64 translated
XOR-zero triples. The actual sampler's translation identity removes that
translation. The factor 64 is a sum, not an average normalization.
-/

namespace MainTheory.Orbit3PauliTranslationReduction

open MainTheory.Orbit3PauliCubicExpansion MainTheory.Orbit3CubicPhaseStability
open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3SamplingSpectatorX MainTheory.Orbit3CliffordAverage
open MainTheory.Orbit3CubicBasis MainTheory.FiniteCubicMoments
open SixQubit.CodeEquiv SS.MacWilliams
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 4000000

def pair (a b : SS.BitString 6) : Triple := (a, b, SS.bxor a b)

def translated (t : Triple) (f : SS.BitString 6) : Triple :=
  (SS.bxor t.1 f, SS.bxor t.2.1 f, SS.bxor t.2.2 f)

def tripleEquiv : Triple ≃ Triple where
  toFun t := translated (pair t.1 t.2.1) t.2.2
  invFun t := (SS.bxor t.2.1 t.2.2, SS.bxor t.1 t.2.2,
    SS.bxor (SS.bxor t.1 t.2.1) t.2.2)
  left_inv t := by
    rcases t with ⟨a, b, c⟩
    apply Prod.ext
    · funext j
      dsimp only [translated, pair, SS.bxor]
      cases a j <;> cases b j <;> cases c j <;> rfl
    · apply Prod.ext <;> funext j <;>
        dsimp only [translated, pair, SS.bxor] <;>
        cases a j <;> cases b j <;> cases c j <;> rfl
  right_inv t := by
    rcases t with ⟨a, b, c⟩
    apply Prod.ext
    · funext j
      dsimp only [translated, pair, SS.bxor]
      cases a j <;> cases b j <;> cases c j <;> rfl
    · apply Prod.ext <;> funext j <;>
        dsimp only [translated, pair, SS.bxor] <;>
        cases a j <;> cases b j <;> cases c j <;> rfl

theorem chi_square (a b : SS.BitString 6) : chi a b * chi a b = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  have he (j : Fin 6) :
      (if a j && b j then (-1 : ℝ) else 1) *
        (if a j && b j then (-1 : ℝ) else 1) = 1 := by
    cases a j <;> cases b j <;> norm_num
  simp only [he, Finset.prod_const_one]

theorem character_translated (P : Fin 3 → SS.PauliString 6)
    (hz : SS.bxor (P 0).z (P 1).z = (P 2).z) (t : Triple) (f : SS.BitString 6) :
    character P (translated t f) = character P t := by
  unfold character translated
  simp only [chi_bxor_right]
  simp_rw [← hz, chi_bxor_left]
  calc
    _ = (chi (P 0).z t.1 * chi (P 1).z t.2.1 *
        (chi (P 0).z t.2.2 * chi (P 1).z t.2.2)) *
        (chi (P 0).z f * chi (P 0).z f) * (chi (P 1).z f * chi (P 1).z f) := by
      ring
    _ = _ := by rw [chi_square, chi_square, mul_one, mul_one]

theorem shifted_translated (P : Fin 3 → SS.PauliString 6) (t : Triple) (f : SS.BitString 6) :
    shifted P (translated t f) = translated (shifted P t) f := by
  apply Prod.ext
  · funext j
    dsimp only [shifted, translated, SS.bxor]
    cases t.1 j <;> cases f j <;> cases (P 0).x j <;> rfl
  · apply Prod.ext
    · funext j
      dsimp only [shifted, translated, SS.bxor]
      cases t.2.1 j <;> cases f j <;> cases (P 1).x j <;> rfl
    · funext j
      dsimp only [shifted, translated, SS.bxor]
      cases t.2.2 j <;> cases f j <;> cases (P 2).x j <;> rfl

theorem entry_translated (t u : Triple) (f : SS.BitString 6) (w : SS.State 6 ℂ) :
    entry (translated t f) (translated u f) w = entry t u (flipAct f w) := rfl

theorem sampled_entry_translated (W : Encoder) (P : Fin 3 → SS.PauliString 6)
    (t : Triple) (f : SS.BitString 6) :
    (∑ g : Index, entry (shifted P (translated t f)) (translated t f) (wave W g)) =
      ∑ g : Index, entry (shifted P t) t (wave W g) := by
  simp_rw [shifted_translated, entry_translated]
  exact sampling_translation_identity f _ (entry_phase_stable _ _) W

theorem sum_triple_equiv (F : Triple → ℝ) :
    (∑ a : SS.BitString 6, ∑ b : SS.BitString 6, ∑ c : SS.BitString 6,
      F (tripleEquiv (a, b, c))) =
      ∑ a : SS.BitString 6, ∑ b : SS.BitString 6, ∑ c : SS.BitString 6, F (a, b, c) := by
  simpa only [Fintype.sum_prod_type] using tripleEquiv.sum_comp F

theorem triple_sum_reduction (W : Encoder) (P : Fin 3 → SS.PauliString 6)
    (hz : SS.bxor (P 0).z (P 1).z = (P 2).z) :
    (∑ a : SS.BitString 6, ∑ b : SS.BitString 6, ∑ c : SS.BitString 6,
      character P (a, b, c) * ∑ g : Index,
        entry (shifted P (a, b, c)) (a, b, c) (wave W g)) =
      64 * ∑ a : SS.BitString 6, ∑ b : SS.BitString 6,
        character P (pair a b) * ∑ g : Index,
          entry (shifted P (pair a b)) (pair a b) (wave W g) := by
  have he := sum_triple_equiv (fun t => character P t *
    ∑ g : Index, entry (shifted P t) t (wave W g))
  rw [← he]
  change (∑ a : SS.BitString 6, ∑ b : SS.BitString 6, ∑ f : SS.BitString 6,
    character P (translated (pair a b) f) * ∑ g : Index,
      entry (shifted P (translated (pair a b) f)) (translated (pair a b) f) (wave W g)) = _
  simp_rw [character_translated P hz, sampled_entry_translated]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num only [Nat.reducePow, Nat.cast_ofNat]
  simp only [← Finset.mul_sum]

theorem sampled_product_reduction (W : Encoder) (P : Fin 3 → SS.PauliString 6)
    (hz : SS.bxor (P 0).z (P 1).z = (P 2).z) (hy : totalY P % 2 = 0) :
    (∑ g : Index, product P (wave W g)) =
      phase P * (64 * ∑ a : SS.BitString 6, ∑ b : SS.BitString 6,
        character P (pair a b) * ∑ g : Index,
          entry (shifted P (pair a b)) (pair a b) (wave W g)) := by
  simp_rw [product_expansion P _ hy]
  rw [← Finset.mul_sum]
  congr 1
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext a
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  exact triple_sum_reduction W P hz

end
end MainTheory.Orbit3PauliTranslationReduction
