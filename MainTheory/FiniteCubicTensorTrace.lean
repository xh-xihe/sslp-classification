import MainTheory.FiniteCubicMoments

/-! Positive, symmetric three-copy moments and their exact trace normalization. -/

namespace MainTheory.FiniteCubicTensorTrace

noncomputable section

open MainTheory.FiniteCubicMoments
open scoped BigOperators

variable {G B : Type*} [Fintype G] [Fintype B] [Nonempty G]

def tensor (w : G → B → ℂ) : G → (B × B × B) → ℂ := cubic id w

def moment (w : G → B → ℂ) : Matrix (B × B × B) (B × B × B) ℝ :=
  (Fintype.card G : ℝ)⁻¹ • realGram (tensor w)

theorem positive (w : G → B → ℂ) : (moment w).PosSemidef :=
  (realGram_posSemidef _).smul (inv_nonneg.mpr (by positivity))

theorem norm_sum (w : B → ℂ) :
    (∑ t : B × B × B,Complex.normSq (w t.1*w t.2.1*w t.2.2))=
      (∑ b,Complex.normSq (w b))^3 := by
  simp only [Fintype.sum_prod_type,Complex.normSq_mul]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  have h : (∑ x, ∑ y, Complex.normSq (w x)*Complex.normSq (w y))=
      (∑ x, Complex.normSq (w x))*(∑ y, Complex.normSq (w y)) := by
    simp only [Finset.mul_sum, mul_comm]
  rw [h]
  ring

theorem trace (w : G → B → ℂ) (N : ℝ) (hw : ∀ g,∑ b,Complex.normSq (w g b)=N) :
    Matrix.trace (moment w)=N^3 := by
  classical
  rw [moment,Matrix.trace_smul]
  have ht : Matrix.trace (realGram (tensor w))=∑ g : G,
      ∑ t : B × B × B,Complex.normSq (w g t.1*w g t.2.1*w g t.2.2) := by
    simp only [Matrix.trace,Matrix.diag,realGram_apply,tensor,cubic,id_eq]
    simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re]
    rw [Finset.sum_comm]
  rw [ht]
  simp_rw [norm_sum,hw]
  have hcard : (Fintype.card G : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

omit [Fintype G] [Fintype B] [Nonempty G] in
theorem symmetric_swap12 (w : G → B → ℂ) (a b c : B) :
    (fun g => tensor w g (a,b,c))=(fun g => tensor w g (b,a,c)) := by
  funext g
  simp only [tensor,cubic,id_eq]
  ring

omit [Fintype G] [Fintype B] [Nonempty G] in
theorem symmetric_swap23 (w : G → B → ℂ) (a b c : B) :
    (fun g => tensor w g (a,b,c))=(fun g => tensor w g (a,c,b)) := by
  funext g
  simp only [tensor,cubic,id_eq]
  ring

end

end MainTheory.FiniteCubicTensorTrace
