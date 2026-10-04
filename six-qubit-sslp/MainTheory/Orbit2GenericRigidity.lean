import Orbit2.Complete

/-! The homogeneous rigidity proposition for arbitrary complex Pauli coefficients. -/

namespace MainTheory.Orbit2GenericRigidity

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic
open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def Forbidden (p : Label 4) : Prop :=
  (pauliWeight p=4 ∧ transverseCount p=2) ∨
    (transverseCount p=0 ∧ (pauliWeight p=3 ∨ pauliWeight p=2))

theorem c_term (t : Fin 32 → ℂ)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0)
    (p : Label 4) :
    Defects.correlation (expansion basis t) (operator p)*weightedCorrelation t cMultiplier p=
      if pauliWeight p=3 ∧ transverseCount p=2 then
        -24*(Defects.correlation (expansion basis t) (operator p))^2 else 0 := by
  by_cases hp : Forbidden p
  · rw [hf p hp]
    split_ifs <;> simp
  · have hm : ∀ v y,cMultiplier p v y=
        if pauliWeight p=3 ∧ transverseCount p=2 then -24 else 0 := by
      intro v y
      unfold Forbidden at hp
      unfold cMultiplier
      have h4 : ¬(pauliWeight p=4 ∧ transverseCount p=2) := by tauto
      have h3 : ¬(pauliWeight p=3 ∧ transverseCount p=0 ∧ (isThree y != isThree v)) := by tauto
      have h2 : ¬(pauliWeight p=2 ∧ transverseCount p=0 ∧ (isThree y && isThree v)) := by tauto
      simp only [h4,h3,h2,if_false,add_zero]
    rw [weightedCorrelation_congr _ p _
      (fun _ _ _ => if pauliWeight p=3 ∧ transverseCount p=2 then -24 else 0) hm,
      weightedCorrelation_const]
    split_ifs <;> push_cast <;> ring

theorem c_nonpositive (t : Fin 32 → ℂ)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0) :
    (orderedPolynomial cCoeff t).re≤0 := by
  rw [← c_contraction_expansion,Complex.re_sum]
  apply Finset.sum_nonpos
  intro p _
  rw [c_term t hf]
  split_ifs
  · have hi := Complex.conj_eq_iff_im.mp (correlation_real (expansion basis t) p)
    norm_num [pow_two,Complex.mul_re,Complex.mul_im,hi]
    nlinarith [sq_nonneg (Defects.correlation (expansion basis t) (operator p)).re]
  · simp

theorem raw_nonpositive (t : Fin 32 → ℂ)
    (hF : Defects.projectionDefect (expansion basis t)=0)
    (hR : ∀ site ax,ax≠0 →
      Defects.compressionDefect (expansion basis t) (operator (single site ax))=0)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0) :
    (orderedPolynomial rawCoefficient t).re≤0 := by
  have hg : orderedPolynomial gCoeff t=0 := by
    rw [← projection_contraction_expansion,hF]
    simp [tau]
  have hj : orderedPolynomial jCoeff t=0 := by
    rw [← J_contraction_expansion]
    apply Finset.sum_eq_zero
    intro site _
    apply Finset.sum_eq_zero
    intro ax _
    apply Finset.sum_eq_zero
    intro u _
    by_cases ha : ax=0
    · simp [jWeight,ha]
    · rw [hR site ax ha]
      simp [tau]
  unfold rawCoefficient
  rw [orderedPolynomial_add,orderedPolynomial_add,orderedPolynomial_add,orderedPolynomial_add,
    orderedPolynomial_scale,orderedPolynomial_scale,orderedPolynomial_swap jCoeff,
    orderedPolynomial_swap gCoeff,hj,hg]
  simpa using c_nonpositive t hf

theorem weight_three_correlation (t : Fin 32 → ℂ)
    (ht : ∀ i : Fin 24,t (weightThreeLabels i)=0)
    (p : Label 4) (hp : pauliWeight p=3) :
    Defects.correlation (expansion basis t) (operator p)=0 := by
  have hz (u : Fin 32) (hu : pauliWeight (pauliBasis u)=3) : t u=0 := by
    obtain ⟨i,hi⟩ := weightThreeLabels_complete u hu
    rw [← hi]
    exact ht i
  unfold Defects.correlation
  rw [tau_expansion_correlation]
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro u _
  rcases (pauliBasis_support u).2 with hu | hu
  · rcases (pauliBasis_support v).2 with hv | hv
    · rw [weight_three_pair_trace_zero p hp u v hu hv,mul_zero]
    · rw [hz v hv,star_zero,mul_zero,zero_mul]
  · rw [hz u hu,zero_mul,zero_mul]

theorem rigidity (t : Fin 32 → ℂ)
    (hF : Defects.projectionDefect (expansion basis t)=0)
    (hR : ∀ site ax,ax≠0 →
      Defects.compressionDefect (expansion basis t) (operator (single site ax))=0)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0) :
    (∀ i : Fin 24,t (weightThreeLabels i)=0) ∧
      (∀ p : Label 4,pauliWeight p=3 → Defects.correlation (expansion basis t) (operator p)=0) := by
  have he : familyEnergy checkedBlocks (quadraticMonomials t)≤0 := by
    rw [← fullCoefficientEnergy_eq_certificate,← orderedPolynomial_eq_fullEnergy]
    exact div_nonpos_of_nonpos_of_nonneg (raw_nonpositive t hF hR hf) (by norm_num)
  have hc := family_coercivity checkedBlocks (quadraticMonomials t)
  have hm := familyMass_nonneg checkedBlocks (quadraticMonomials t)
  have he0 : familyEnergy checkedBlocks (quadraticMonomials t)=0 := by linarith
  have hi : familyEnergy checkedBlocks (quadraticMonomials t)=
      -(∑ _ : Fin 48,(0 : ℝ)^2) := by simpa using he0
  have ht := (checked_polynomial_rigidity t (fun _ => 0) hi).2
  exact ⟨ht,fun p hp => weight_three_correlation t ht p hp⟩

theorem pauli_set_counts :
    (Finset.univ.filter fun p : Label 4 => pauliWeight p=3 ∧ transverseCount p=2).card=48 ∧
    (Finset.univ.filter fun p : Label 4 => pauliWeight p=2 ∧ transverseCount p=0).card=6 ∧
    (Finset.univ.filter fun p : Label 4 => pauliWeight p=3 ∧ transverseCount p=0).card=4 ∧
    (Finset.univ.filter fun p : Label 4 => pauliWeight p=4 ∧ transverseCount p=2).card=24 := by
  decide +kernel

end

end MainTheory.Orbit2GenericRigidity
