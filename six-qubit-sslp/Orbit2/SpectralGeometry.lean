import Orbit2.FrameParity

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unusedTactic false

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def zSign (i : Fin 4) (x : ActiveBits) : ℤ := if x i=0 then 1 else -1
def hamming (x y : ActiveBits) : ℕ := ∑ i, if x i=y i then 0 else 1
def rowField (x y : ActiveBits) : ℤ := ∑ i, zSign i x * zSign i y

theorem rowField_self : ∀ x : ActiveBits, rowField x x=4 := by decide +kernel
theorem rowField_middle : ∀ x y : ActiveBits,
    (evenBits x ↔ evenBits y) → y≠x → y≠complementBits x → rowField x y=0 := by decide +kernel
theorem rowField_opposite : ∀ x y : ActiveBits,
    ¬ (evenBits x ↔ evenBits y) → rowField x y+2=if hamming x y=1 then 4 else 0 := by decide +kernel

theorem single_Z_phase_G : ∀ (i : Fin 4) (x : ActiveBits),
    (∏ j, localG (single i 3 j) (x j) (x j)) = (zSign i x : GaussianInt) := by decide +kernel

theorem single_Z_diagonal (i : Fin 4) :
    operator (single i 3) = Matrix.diagonal (fun x : ActiveBits => (zSign i x : ℂ)) := by
  ext x y
  have hf : HilbertBridge.flip (single i 3) x=x := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [HilbertBridge.flip,single,if_true]
      change FiveQubit.flipSite 3 (x i)=x i
      generalize x i = a
      fin_cases a <;> rfl
    · change FiveQubit.flipSite (single i 3 j) (x j)=x j
      simp only [single,hj,if_false]
      generalize x j = a
      fin_cases a <;> rfl
  rw [HilbertBridge.operator_row,hf]
  by_cases hxy : x=y
  · subst y
    simp only [if_true,Matrix.diagonal_apply_eq]
    have h := congrArg GaussianInt.toComplex (single_Z_phase_G i x)
    have hcast : ((zSign i x : GaussianInt) : ℂ) = (zSign i x : ℂ) := by
      unfold zSign
      split_ifs <;> simp [GaussianInt.toComplex_neg]
    simpa only [localC,Matrix.map_apply,map_prod,hcast] using h
  · simp [hxy,Ne.symm hxy]

theorem diagonal_norm_compression {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℂ) (v : α → ℂ) (x : α) :
    (M * Matrix.diagonal v * M.conjTranspose) x x =
      ∑ y, v y * (Complex.normSq (M x y) : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro y _
  rw [Complex.star_def,← Complex.mul_conj]
  ring

theorem Encoder.activeProjector_diagonal_mu (V : Encoder) (x : ActiveBits) :
    V.activeProjector x x = (1 + ∑ i : Fin 4, V.activeMu (single i 3) * (zSign i x : ℂ))/2 := by
  have ht (i : Fin 4) : tau (operator (single i 3) * V.activeProjector)=V.activeMu (single i 3)/2 := by
    unfold tau Encoder.activeProjector
    rw [Frames.pi_sigma_trace V.magicFrames V.magicFrames_isometry _ _ (V.physical_commonJ i 3 (by decide))]
    norm_num
    ring
  rw [V.activeProjector_diagonal]
  simp_rw [ht,single_Z_diagonal,Matrix.diagonal_apply_eq]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  ring

end Orbit2
