import MainTheory.Orbit3CoefficientCollection
import MainTheory.Orbit3SpinForm

/-! # The spin multiplier has the stated integer moment coefficients

The full Y tensor carries a minus sign in the physical Pauli convention.
Consequently the raw coordinate row is 64 times the sampled spin multiplier.
-/

namespace MainTheory.Orbit3SpinMomentInterpretation

open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3CoefficientCollection
open MainTheory.Orbit3PauliCubicExpansion MainTheory.Orbit3PauliTranslationReduction
open MainTheory.Orbit3CubicPhaseStability MainTheory.Orbit3CubicBasis
open MainTheory.Orbit3CoordinateRealization MainTheory.Orbit3SpinForm
open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.CubicTripleCanonical MainTheory.FiniteCubicMoments
open SixQubit.Generated SS.Shadow SS.MacWilliams
open scoped BigOperators

noncomputable section

def complementIndex (a : Fin 64) : Fin 715 := Orbit3CubicTriples.pairIndex a (xor64 a 63)

theorem nbit_63 : SixQubit.Realize.nbit 63 = SS.ones 6 := by decide +kernel

theorem complement_monomial (w : SS.State 6 ℂ) (a : Fin 64) :
    MainTheory.CubicTripleCanonical.monomial w (Orbit3CubicTriples.physical (complementIndex a)) =
      w (SixQubit.Realize.nbit a.val) * w (SS.complement (SixQubit.Realize.nbit a.val)) *
        w (SixQubit.Realize.nbit 63) := by
  rw [complementIndex, Orbit3CubicTriples.actual_cubic_pair, nbit_xor64]
  simp only [show (63 : Fin 64).val = 63 from rfl, nbit_63]
  rw [← SS.complement_eq_bxor_ones]
  have he (s : SS.BitString 6) : SS.bxor s (SS.complement s) = SS.ones 6 := by
    funext j
    dsimp only [SS.bxor, SS.complement, SS.ones]
    cases s j <;> rfl
  rw [he]

def multiplier (t : Fin 715) (w : SS.State 6 ℂ) : ℝ :=
  (star (MainTheory.CubicTripleCanonical.monomial w (Orbit3CubicTriples.physical t)) *
    spin w * w (SixQubit.Realize.nbit 63)).re

theorem multiplier_expansion (t : Fin 715) (w : SS.State 6 ℂ) :
    multiplier t w = ∑ a : Fin 64, -psign (SixQubit.Realize.nbit a.val) *
      entry (Orbit3CubicTriples.physical t) (Orbit3CubicTriples.physical (complementIndex a)) w := by
  unfold multiplier
  rw [spin_eq, ← bitEquiv.sum_comp (fun s => (psign s : ℂ) * w s * w (SS.complement s))]
  simp only [bitEquiv, Equiv.coe_fn_mk, mul_neg, neg_mul, Finset.mul_sum,
    Finset.sum_mul, Complex.neg_re, Complex.re_sum, Finset.sum_neg_distrib]
  apply congrArg (fun x : ℝ => -x)
  apply Finset.sum_congr rfl
  intro a _
  change (star (MainTheory.CubicTripleCanonical.monomial w (Orbit3CubicTriples.physical t)) *
    ((psign (SixQubit.Realize.nbit a.val) : ℂ) * w (SixQubit.Realize.nbit a.val) *
      w (SS.complement (SixQubit.Realize.nbit a.val))) * w (SixQubit.Realize.nbit 63)).re = _
  change _ = psign (SixQubit.Realize.nbit a.val) *
    (star (MainTheory.CubicTripleCanonical.monomial w (Orbit3CubicTriples.physical t)) *
      MainTheory.CubicTripleCanonical.monomial w (Orbit3CubicTriples.physical (complementIndex a))).re
  rw [complement_monomial]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

def spinCoefficient (a : Fin 64) : ℤ := -sign (SS.bdot (SS.ones 6) (SixQubit.Realize.nbit a.val))

def rawEvaluation (t : Fin 715) (y : Fin 269 → ℝ) : ℝ :=
  ∑ a : Fin 64, (spinCoefficient a : ℝ) * tableMatrix y t (complementIndex a)

theorem sampled_spin_coordinates (W : Encoder) (t : Fin 715) :
    64 * (∑ g : Index, multiplier t (wave W g)) = rawEvaluation t (coordinates W) := by
  simp_rw [multiplier_expansion]
  rw [Finset.sum_comm]
  unfold rawEvaluation spinCoefficient
  simp only [tableMatrix_eq_scaled_moment, Matrix.smul_apply, smul_eq_mul, Int.cast_neg,
    ← chi_sign]
  simp only [← Finset.mul_sum, psign]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold moment
  rw [cubicMoment_apply]
  rw [chi_comm (SS.ones 6)]
  simp only [← Finset.mul_sum]
  change 64 * (-chi (SixQubit.Realize.nbit a.val) (SS.ones 6) *
    ∑ g : Index, entry (Orbit3CubicTriples.physical t)
      (Orbit3CubicTriples.physical (complementIndex a)) (wave W g)) =
    -chi (SixQubit.Realize.nbit a.val) (SS.ones 6) *
      (64 * ∑ g : Index, entry (Orbit3CubicTriples.physical t)
        (Orbit3CubicTriples.physical (complementIndex a)) (wave W g))
  ring

def termList (t : Fin 715) (a : Fin 64) : List (Fin (2 ^ 9) × ℤ) :=
  match Orbit3Coordinates.Data.entry t (complementIndex a) with
  | none => []
  | some e => [(embed e.1, spinCoefficient a)]

def terms (t : Fin 715) : List (Fin (2 ^ 9) × ℤ) :=
  (List.finRange 64).flatMap fun a => termList t a

def coefficients (t : Fin 715) : MainTheory.DyadicCoefficientTree.Tree 9 :=
  MainTheory.DyadicCoefficientTree.accumulate (MainTheory.DyadicCoefficientTree.zero 9) (terms t)

theorem termList_evaluation (t : Fin 715) (a : Fin 64) (y : Fin 269 → ℝ) :
    ((termList t a).map fun e => (e.2 : ℝ) * padded y e.1).sum =
      (spinCoefficient a : ℝ) * tableMatrix y t (complementIndex a) := by
  unfold termList tableMatrix
  cases Orbit3Coordinates.Data.entry t (complementIndex a) <;> simp [padded_embed]

theorem coefficients_evaluation (t : Fin 715) (y : Fin 269 → ℝ) :
    MainTheory.DyadicCoefficientTree.evaluate (coefficients t) (padded y) = rawEvaluation t y := by
  rw [coefficients, MainTheory.DyadicCoefficientTree.evaluate_accumulate,
    MainTheory.DyadicCoefficientTree.evaluate_zero, zero_add]
  unfold terms rawEvaluation
  simp only [List.map_flatMap, sum_flatMap_real, termList_evaluation,
    List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]

end
end MainTheory.Orbit3SpinMomentInterpretation
