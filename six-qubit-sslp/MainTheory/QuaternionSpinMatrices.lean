import MainTheory.UnitaryAdjointRepresentation
import Mathlib.Algebra.Quaternion

/-! The faithful spin matrices of real quaternions and their projective kernel. -/

namespace MainTheory.QuaternionSpinMatrices

noncomputable section

open Quaternion
open scoped ComplexConjugate

def spin (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
     -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I]

theorem spin_one : spin 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spin]

theorem spin_mul (q r : ℍ[ℝ]) : spin (q * r) = spin q * spin r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [spin, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem spin_star (q : ℍ[ℝ]) : spin (star q) = (spin q).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [spin, Matrix.conjTranspose_apply]

def spinHom : ℍ[ℝ] →⋆* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := spin
  map_one' := spin_one
  map_mul' := spin_mul
  map_star' := spin_star

theorem spin_injective : Function.Injective spin := by
  intro q r h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  apply Quaternion.ext
  · simpa [spin] using congrArg Complex.re h00
  · simpa [spin] using congrArg Complex.im h00
  · simpa [spin] using congrArg Complex.re h01
  · simpa [spin] using congrArg Complex.im h01

def unitarySpin : unitary ℍ[ℝ] →* Matrix.unitaryGroup (Fin 2) ℂ :=
  (Unitary.map spinHom).toMonoidHom

theorem normSq_unitary (q : unitary ℍ[ℝ]) : Quaternion.normSq q.val = 1 := by
  have h := congrArg (fun r : ℍ[ℝ] => r.re) q.property.2
  simpa only [Quaternion.self_mul_star, Quaternion.re_coe, Quaternion.re_one] using h

theorem scalar_spin_iff (q : ℍ[ℝ]) :
    (∃ c : ℂ, spin q = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ↔
      q.imI = 0 ∧ q.imJ = 0 ∧ q.imK = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).im) hc
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).im) hc
    have h01r := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) hc
    have h01i := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) hc
    simp [spin, Matrix.smul_apply] at h00 h11 h01r h01i
    exact ⟨by linarith, h01r, h01i⟩
  · rintro ⟨hI, hJ, hK⟩
    refine ⟨q.re, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spin, hI, hJ, hK, Matrix.smul_apply]

theorem projective_kernel (q : unitary ℍ[ℝ]) :
    UnitaryAdjointRepresentation.adjoint (unitarySpin q) = 1 ↔
      q.val = 1 ∨ q.val = -1 := by
  rw [UnitaryAdjointRepresentation.adjoint_eq_one_iff]
  change (∃ c : ℂ, spin q.val = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ↔ _
  rw [scalar_spin_iff]
  constructor
  · rintro ⟨hI, hJ, hK⟩
    have hnorm := normSq_unitary q
    rw [Quaternion.normSq_def', hI, hJ, hK] at hnorm
    have hr : q.val.re = 1 ∨ q.val.re = -1 := by
      have : (q.val.re - 1) * (q.val.re + 1) = 0 := by nlinarith [hnorm]
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hr with h | h
    · left; apply Quaternion.ext <;> simp [h, hI, hJ, hK]
    · right; apply Quaternion.ext <;> simp [h, hI, hJ, hK]
  · rintro (h | h) <;> simp [h]

theorem projective_pow (q : unitary ℍ[ℝ]) (m : ℕ) :
    UnitaryAdjointRepresentation.adjoint (unitarySpin q) ^ m = 1 ↔
      q.val ^ m = 1 ∨ q.val ^ m = -1 := by
  rw [← map_pow, ← map_pow, projective_kernel]
  rfl

end

end MainTheory.QuaternionSpinMatrices
