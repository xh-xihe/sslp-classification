import Orbit2.TraceReality

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem weight_one_pair_bound : ∀ u v : Fin 32,
    pauliWeight (pauliBasis u)=1 → pauliWeight (pauliBasis v)=1 →
      pauliWeight (product (pauliBasis u) (pauliBasis v))≤2 := by decide +kernel

theorem weight_three_pair_trace_zero (p : Label 4) (hp : pauliWeight p=3)
    (u v : Fin 32) (hu : pauliWeight (pauliBasis u)=1) (hv : pauliWeight (pauliBasis v)=1) :
    tau (operator p * operator (pauliBasis u) * operator (pauliBasis v))=0 := by
  have hn : p≠product (pauliBasis u) (pauliBasis v) := by
    intro h
    have hb := weight_one_pair_bound u v hu hv
    rw [← h,hp] at hb
    omega
  rw [Matrix.mul_assoc,operator_mul,Matrix.mul_smul,tau_smul,tau_operator_pair]
  simp [hn]

theorem tau_expansion_correlation (E : Defects.ActiveMatrix) (t : Fin 32 → ℂ) :
    tau (E * expansion pauliBasis t * (expansion pauliBasis t).conjTranspose) =
      ∑ v : Fin 32, ∑ u : Fin 32, t u * star (t v) *
        tau (E * operator (pauliBasis u) * operator (pauliBasis v)) := by
  rw [expansion_conjTranspose]
  unfold expansion
  simp only [Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    tau_sum,tau_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Killing the certificate's weight-three T coordinates kills the actual A3.
The projector and enumerator normalization are derived, not assumed. -/
theorem Encoder.A3_zero_of_T_rigidity (V : Encoder)
    (h : ∀ i : Fin 24, V.physicalT_coordinates (weightThreeLabels i)=0) : V.A 3=0 := by
  have ht (u : Fin 32) (hu : pauliWeight (pauliBasis u)=3) : V.physicalT_coordinates u=0 := by
    obtain ⟨i,hi⟩ := weightThreeLabels_complete u hu
    rw [← hi]
    exact h i
  have hp : V.activeProjector=V.physicalT * V.physicalT.conjTranspose :=
    (Frames.t_left V.magicFrames V.magicFrames_isometry activeSpin activeSpin_hermitian activeSpin_square).symm
  have hz (p : Label 4) (hw : pauliWeight p=3) : tau (operator p * V.activeProjector)=0 := by
    rw [hp,← Matrix.mul_assoc,V.physicalT_expansion,tau_expansion_correlation]
    apply Finset.sum_eq_zero
    intro v _
    apply Finset.sum_eq_zero
    intro u _
    rcases (pauliBasis_support u).2 with hu|hu
    · rcases (pauliBasis_support v).2 with hv|hv
      · rw [weight_three_pair_trace_zero p hw u v hu hv,mul_zero]
      · rw [ht v hv,star_zero,mul_zero,zero_mul]
    · rw [ht u hu,zero_mul,zero_mul]
  rw [V.A3_projector]
  have hs : (∑ p : Label 4, if PhysicalFlatness.activeWeight p=3 then
      Complex.normSq (tau (operator p * V.activeProjector)) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro p _
    by_cases hw : PhysicalFlatness.activeWeight p=3
    · have hwp : pauliWeight p=3 := hw
      simp [hw,hz p hwp]
    · simp [hw]
  rw [hs,mul_zero]

theorem Encoder.enumerator_of_certificate_nonpositive (V : Encoder)
    (h : familyEnergy checkedBlocks (quadraticMonomials V.physicalT_coordinates)≤0) :
    0≤V.A 1 ∧ V.A 1≤1 ∧ (fun w : Fin 7 => V.A w.val)=enumeratorLine (V.A 1) := by
  have hc := family_coercivity checkedBlocks (quadraticMonomials V.physicalT_coordinates)
  have hm := familyMass_nonneg checkedBlocks (quadraticMonomials V.physicalT_coordinates)
  have he : familyEnergy checkedBlocks (quadraticMonomials V.physicalT_coordinates)=0 := by linarith
  have hi : familyEnergy checkedBlocks (quadraticMonomials V.physicalT_coordinates) =
      -(∑ _ : Fin 48, (0 : ℝ)^2) := by simpa using he
  have hr := (checked_polynomial_rigidity V.physicalT_coordinates (fun _ => 0) hi).2
  exact V.enumerator_of_rigidity (V.A3_zero_of_T_rigidity hr)

end Orbit2
