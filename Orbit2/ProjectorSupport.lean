import Orbit2.EnumeratorTransport

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unusedSimpArgs false

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic Orbit2.PurityReduction
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def complementBits (x : ActiveBits) : ActiveBits := fun i => FiveQubit.flipSite 1 (x i)

theorem local_diagonal_transverse : ∀ (a : Fin 4) (x : Fin 2), a=1 ∨ a=2 → localG a x x=0 := by
  decide +kernel
theorem local_complement_longitudinal : ∀ (a : Fin 4) (x : Fin 2), a=0 ∨ a=3 →
    localG a x (FiveQubit.flipSite 1 x)=0 := by decide +kernel

theorem operator_diagonal_zero {n : ℕ} (p : Label n) (x : Fin n → Fin 2)
    (h : ∃ i, p i=1 ∨ p i=2) : operator p x x=0 := by
  obtain ⟨i,hi⟩ := h
  unfold operator tensor
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [localC,Matrix.map_apply,local_diagonal_transverse _ _ hi]

theorem operator_complement_zero (p : Label 4) (x : ActiveBits)
    (h : ¬ ∀ i, p i=1 ∨ p i=2) : operator p x (complementBits x)=0 := by
  obtain ⟨i,hi⟩ : ∃ i, p i=0 ∨ p i=3 := by
    push_neg at h
    obtain ⟨i,hi⟩ := h
    refine ⟨i,?_⟩
    generalize hp : p i = a at hi ⊢
    fin_cases a <;> simp_all
  unfold operator tensor
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [localC,Matrix.map_apply,complementBits,local_complement_longitudinal _ _ hi]

theorem longitudinal_zero_reason : ∀ p : Label 4,
    (∀ i, p i=0 ∨ p i=3) → PhysicalFlatness.activeWeight p≥2 →
    forbidden (partner (PhysicalFlatness.activeEmbedding p)) := by decide +kernel

theorem Encoder.activeProjector_longitudinal_zero (V : Encoder) (p : Label 4)
    (hp : ∀ i, p i=0 ∨ p i=3) (hw : PhysicalFlatness.activeWeight p≥2) :
    tau (operator p * V.activeProjector)=0 := by
  apply V.activeProjector_trace_zero
  rw [← V.labelMass_pairing]
  exact V.labelMass_forbidden_zero _ (longitudinal_zero_reason p hp hw)

theorem transverse_four_weight : ∀ p : Label 4, (∀ i, p i=1 ∨ p i=2) →
    PhysicalFlatness.activeWeight p=4 := by decide +kernel

/-- The rank-eight active projector has no opposite-corner entries. This
is derived from the physical four-transverse zero, using actual Pauli spanning. -/
theorem Encoder.activeProjector_complement_zero (V : Encoder) (x : ActiveBits) :
    V.activeProjector x (complementBits x)=0 := by
  have h := congrFun (congrFun (matrix_reconstruction V.activeProjector) x) (complementBits x)
  rw [h]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : ∀ i, p i=1 ∨ p i=2
  · rw [V.activeProjector_weight_four_zero p (transverse_four_weight p hp),zero_mul]
  · rw [operator_complement_zero p x hp,mul_zero]

theorem singleZ_nonzero : ∀ i : Fin 4, single i 3 ≠ (fun _ => 0) := by decide +kernel
theorem singleZ_eq_iff : ∀ i j : Fin 4, single i 3 = single j 3 ↔ i=j := by decide +kernel
theorem longitudinal_small : ∀ p : Label 4,
    (∀ i, p i=0 ∨ p i=3) → PhysicalFlatness.activeWeight p≤1 →
      p=(fun _ => 0) ∨ ∃ i, p=single i 3 := by decide +kernel

theorem Encoder.activeProjector_identity_trace (V : Encoder) :
    tau (operator (fun _ : Fin 4 => 0) * V.activeProjector)=1/2 := by
  rw [operator_zero,Matrix.one_mul]
  unfold tau Encoder.activeProjector
  rw [Frames.pi_trace V.magicFrames V.magicFrames_isometry]
  norm_num

/-- Only the identity and the four single-Z coefficients contribute to the
diagonal of the actual projector. -/
theorem Encoder.activeProjector_diagonal (V : Encoder) (x : ActiveBits) :
    V.activeProjector x x = 1/2 + ∑ i : Fin 4,
      tau (operator (single i 3) * V.activeProjector) * operator (single i 3) x x := by
  have ht (p : Label 4) : tau (operator p * V.activeProjector) * operator p x x =
      (if p=(fun _ => 0) then (1/2 : ℂ) else 0) + ∑ i : Fin 4,
      if p=single i 3 then tau (operator (single i 3) * V.activeProjector) * operator (single i 3) x x else 0 := by
    by_cases hp : p=(fun _ => 0)
    · subst p
      have hn (i : Fin 4) : (fun _ => (0 : Fin 4)) ≠ single i 3 := Ne.symm (singleZ_nonzero i)
      rw [V.activeProjector_identity_trace]
      simp [operator_zero,Matrix.one_apply,hn]
    · by_cases hi : ∃ i, p=single i 3
      · obtain ⟨i,rfl⟩ := hi
        simp [singleZ_nonzero,singleZ_eq_iff]
      · have hn (i : Fin 4) : p≠single i 3 := by intro h; exact hi ⟨i,h⟩
        simp only [hp,hn,if_false,Finset.sum_const_zero,add_zero]
        by_cases hz : ∀ i, p i=0 ∨ p i=3
        · have hw : PhysicalFlatness.activeWeight p≥2 := by
            by_contra hw
            have hl := longitudinal_small p hz (by omega)
            exact hl.elim hp hi
          rw [V.activeProjector_longitudinal_zero p hz hw,zero_mul]
        · have hx : ∃ i, p i=1 ∨ p i=2 := by
            push_neg at hz
            obtain ⟨i,hi⟩ := hz
            refine ⟨i,?_⟩
            generalize p i = a at hi ⊢
            fin_cases a <;> simp_all
          rw [operator_diagonal_zero p x hx,mul_zero]
  have h := congrFun (congrFun (matrix_reconstruction V.activeProjector) x) x
  rw [h]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _ = ∑ p : Label 4, ((if p=(fun _ => 0) then (1/2 : ℂ) else 0) + ∑ i : Fin 4,
      if p=single i 3 then tau (operator (single i 3) * V.activeProjector) * operator (single i 3) x x else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      exact ht p
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp

end Orbit2
