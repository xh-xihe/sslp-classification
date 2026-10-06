import Orbit2.CExpansion

namespace Orbit2.Quartic
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem weightedCorrelation_congr (t : Fin 32 → ℂ) (p : Label 4)
    (m n : Label 4 → Fin 32 → Fin 32 → ℤ) (h : ∀ v y, m p v y=n p v y) :
    weightedCorrelation t m p=weightedCorrelation t n p := by
  unfold weightedCorrelation
  simp_rw [h]

theorem weightedCorrelation_const (t : Fin 32 → ℂ) (p : Label 4) (a : ℤ) :
    weightedCorrelation t (fun _ _ _ => a) p =
      (a : ℂ) * Defects.correlation (expansion basis t) (operator p) := by
  rw [correlation_expansion]
  simp only [weightedCorrelation,pairKernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem transverse_zero_longitudinal : ∀ p : Label 4,
    transverseCount p=0 → ∀ i, p i=0 ∨ p i=3 := by decide +kernel

theorem correlation_real (T : Defects.ActiveMatrix) (p : Label 4) :
    star (Defects.correlation T (operator p))=Defects.correlation T (operator p) := by
  unfold Defects.correlation tau
  change (starRingEnd ℂ) (_ / _) = _
  rw [map_div₀]
  simp only [starRingEnd_apply]
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,operator_hermitian]
  have ht : Matrix.trace (T * (T.conjTranspose * operator p)) =
      Matrix.trace (operator p * T * T.conjTranspose) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [ht]
  norm_num

theorem physical_correlation_forbidden (V : Encoder) (p : Label 4)
    (h : pauliWeight p=4 ∨ (transverseCount p=0 ∧ (pauliWeight p=3 ∨ pauliWeight p=2))) :
    Defects.correlation (expansion basis V.physicalT_coordinates) (operator p)=0 := by
  rw [← V.physicalT_expansion]
  unfold Defects.correlation
  rw [Matrix.mul_assoc]
  unfold Encoder.physicalT
  rw [Frames.t_left V.magicFrames V.magicFrames_isometry activeSpin
    activeSpin_hermitian activeSpin_square]
  rcases h with h|⟨hf,hw⟩
  · exact V.activeProjector_weight_four_zero p h
  · apply V.activeProjector_longitudinal_zero p (transverse_zero_longitudinal p hf)
    change 2 ≤ pauliWeight p
    omega

theorem physical_c_term (V : Encoder) (p : Label 4) :
    Defects.correlation (expansion basis V.physicalT_coordinates) (operator p) *
      weightedCorrelation V.physicalT_coordinates cMultiplier p =
    if pauliWeight p=3 ∧ transverseCount p=2 then
      -24 * (Defects.correlation (expansion basis V.physicalT_coordinates) (operator p))^2 else 0 := by
  by_cases hf : pauliWeight p=4 ∨ (transverseCount p=0 ∧ (pauliWeight p=3 ∨ pauliWeight p=2))
  · rw [physical_correlation_forbidden V p hf]
    split_ifs <;> simp
  · have hm : ∀ v y, cMultiplier p v y =
        if pauliWeight p=3 ∧ transverseCount p=2 then -24 else 0 := by
      intro v y
      unfold cMultiplier
      have h4 : ¬ (pauliWeight p=4 ∧ transverseCount p=2) := by tauto
      have h3 : ¬ (pauliWeight p=3 ∧ transverseCount p=0) := by tauto
      have h2 : ¬ (pauliWeight p=2 ∧ transverseCount p=0) := by tauto
      have h3' : ¬ (pauliWeight p=3 ∧ transverseCount p=0 ∧ (isThree y != isThree v)) := by tauto
      have h2' : ¬ (pauliWeight p=2 ∧ transverseCount p=0 ∧ (isThree y && isThree v)) := by tauto
      simp only [h4,h3',h2',if_false,add_zero]
    rw [weightedCorrelation_congr _ p _ (fun _ _ _ => if pauliWeight p=3 ∧ transverseCount p=2 then -24 else 0) hm,weightedCorrelation_const]
    split_ifs <;> push_cast <;> ring

theorem physical_c_nonpositive (V : Encoder) :
    (orderedPolynomial cCoeff V.physicalT_coordinates).re ≤ 0 := by
  rw [← c_contraction_expansion,Complex.re_sum]
  apply Finset.sum_nonpos
  intro p _
  rw [physical_c_term]
  split_ifs
  · have hr := correlation_real (expansion basis V.physicalT_coordinates) p
    have hi := Complex.conj_eq_iff_im.mp hr
    norm_num [pow_two,Complex.mul_re,Complex.mul_im,hi]
    nlinarith [sq_nonneg (Defects.correlation (expansion basis V.physicalT_coordinates) (operator p)).re]
  · simp

theorem physical_g_zero (V : Encoder) : orderedPolynomial gCoeff V.physicalT_coordinates=0 := by
  rw [← projection_contraction_expansion,← V.physicalT_expansion,V.physicalT_equations.2.1]
  simp [tau]

theorem physical_j_zero (V : Encoder) : orderedPolynomial jCoeff V.physicalT_coordinates=0 := by
  rw [← J_contraction_expansion,← V.physicalT_expansion]
  apply Finset.sum_eq_zero
  intro site _
  apply Finset.sum_eq_zero
  intro ax _
  apply Finset.sum_eq_zero
  intro u _
  by_cases h : ax=0
  · simp [jWeight,h]
  · rw [V.physicalT_equations.2.2 site ax h]
    simp [tau]


theorem orderedPolynomial_add (a b : Fin 32 → Fin 32 → Fin 32 → Fin 32 → ℤ)
    (t : Fin 32 → ℂ) :
    orderedPolynomial (fun u v x y => a u v x y + b u v x y) t =
      orderedPolynomial a t + orderedPolynomial b t := by
  simp only [orderedPolynomial,Int.cast_add,mul_add,Finset.sum_add_distrib]

theorem orderedPolynomial_scale (a : ℤ) (k : Fin 32 → Fin 32 → Fin 32 → Fin 32 → ℤ)
    (t : Fin 32 → ℂ) :
    orderedPolynomial (fun u v x y => a * k u v x y) t = (a : ℂ) * orderedPolynomial k t := by
  simp only [orderedPolynomial,Int.cast_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem orderedPolynomial_swap (k : Fin 32 → Fin 32 → Fin 32 → Fin 32 → ℤ)
    (t : Fin 32 → ℂ) :
    orderedPolynomial (fun u v x y => k x y u v) t = star (orderedPolynomial k t) := by
  unfold orderedPolynomial
  simp only [star_sum,star_mul,star_star,star_intCast]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem physical_raw_nonpositive (V : Encoder) :
    (orderedPolynomial rawCoefficient V.physicalT_coordinates).re ≤ 0 := by
  unfold rawCoefficient
  rw [orderedPolynomial_add,orderedPolynomial_add,orderedPolynomial_add,orderedPolynomial_add,
    orderedPolynomial_scale,orderedPolynomial_scale,orderedPolynomial_swap jCoeff,orderedPolynomial_swap gCoeff,
    physical_j_zero,physical_g_zero]
  simpa using physical_c_nonpositive V
end Orbit2.Quartic
