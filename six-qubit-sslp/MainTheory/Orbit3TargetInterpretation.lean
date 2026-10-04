import SixQubit.Generated.Orbit3TargetData
import MainTheory.Orbit3CoefficientCollection
import MainTheory.Orbit3SamplingTarget
import MainTheory.CompletionCodeBridge

/-! The exhaustive physical target and its collected coordinate evaluations. -/
namespace MainTheory.Orbit3TargetInterpretation

open MainTheory.Orbit3PauliMomentInterpretation MainTheory.Orbit3CoordinateRealization
open MainTheory.Orbit3CoefficientCollection MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.Orbit3ActualSampling MainTheory.Orbit3CliffordAverage
open MainTheory.Orbit3SamplingTarget MainTheory.PhysicalPauliCategories
open MainTheory.Orbit3Target MainTheory.PauliExpectationReal
open SixQubit.Generated
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

theorem product_pair (P : SS.PauliString 6) (w : SS.State 6 ℂ) :
    product ![P, P, MainTheory.CompletionCodeBridge.identity] w =
      (∑ s, Complex.normSq (w s)) * (SS.innerC w (SS.pauliAct P w)).re ^ 2 := by
  have hn : SS.innerC w w = ((∑ s, Complex.normSq (w s) : ℝ) : ℂ) := by
    simp only [SS.innerC, SixQubit.CodeEquiv.star_mul_self, Complex.ofReal_sum]
  unfold product
  rw [Fin.prod_univ_three]
  change (SS.innerC w (SS.pauliAct P w) * SS.innerC w (SS.pauliAct P w) *
    SS.innerC w (SS.pauliAct MainTheory.CompletionCodeBridge.identity w)).re = _
  rw [MainTheory.CompletionCodeBridge.identity_act, hn]
  simp only [Complex.mul_re,
    expectation_im_zero, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem term_eq_sum (w : SS.State 6 ℂ) :
    term w = ∑ i : Fin 120, product (Orbit3TargetData.triple i) w := by
  unfold term
  rw [Finset.mul_sum]
  have he (P : SS.PauliString 6) :
      (∑ s, Complex.normSq (w s)) *
        (if category P = targetCategory then (SS.innerC w (SS.pauliAct P w)).re ^ 2 else 0) =
      if category P = targetCategory then product ![P, P, MainTheory.CompletionCodeBridge.identity] w else 0 := by
    split_ifs <;> simp [product_pair]
  simp_rw [he]
  rw [← Finset.sum_filter, ← Orbit3TargetData.coverage, Finset.sum_image]
  · rfl
  · intro a _ b _ h
    exact Orbit3TargetData.injective h

theorem target_eq_raw (W : Encoder) :
    target W = ∑ i : Fin 120, rawEvaluation (Orbit3TargetData.triple i) (coordinates W) := by
  unfold target
  simp_rw [term_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact sampled_product_coordinates W _ (Orbit3TargetData.xor_x i)
    (Orbit3TargetData.xor_z i) (Orbit3TargetData.even_y i)

theorem padded_tree_evaluation (t : MainTheory.DyadicCoefficientTree.Tree 9) (y : Fin 269 → ℝ) :
    MainTheory.DyadicCoefficientTree.evaluate t (padded y) =
      ∑ j : Fin 269, (MainTheory.DyadicCoefficientTree.lookup t j.val : ℝ) * y j := by
  unfold MainTheory.DyadicCoefficientTree.evaluate
  change (∑ j : Fin (269 + 243), (MainTheory.DyadicCoefficientTree.lookup t j.val : ℝ) * padded y j) = _
  rw [Fin.sum_univ_add]
  have hl (j : Fin 269) : padded y (Fin.castAdd 243 j) = y j := by
    simp only [padded, Fin.val_castAdd, j.isLt, ↓reduceDIte]
  have hh (j : Fin 243) : padded y (Fin.natAdd 269 j) = 0 := by
    have hn : ¬(Fin.natAdd 269 j).val < 269 := by simp only [Fin.val_natAdd]; omega
    simp only [padded, hn, ↓reduceDIte]
  simp only [hl, hh, mul_zero, Finset.sum_const_zero, add_zero, Fin.val_castAdd]

theorem collected_sum (y : Fin 269 → ℝ) :
    (∑ i : Fin 120, MainTheory.DyadicCoefficientTree.evaluate (Orbit3TargetData.finalRow i) (padded y)) =
      Orbit3SexticIdentity.evaluate Orbit3SexticIdentity.target y := by
  have hc (j : Fin 269) : (∑ i : Fin 120,
      (MainTheory.DyadicCoefficientTree.lookup (Orbit3TargetData.finalRow i) j.val : ℝ)) =
        (Orbit3SexticIdentity.target j : ℝ) := by
    exact_mod_cast Orbit3TargetData.target_coefficients j
  simp_rw [padded_tree_evaluation]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hc]
  rfl

end
end MainTheory.Orbit3TargetInterpretation
