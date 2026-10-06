import MainTheory.RecoveryPartialIsometries
import MainTheory.ErrorGramDiagonalization

/-! # Normalizing orthogonal KL error images, including zero eigenvalues -/

namespace MainTheory.RecoveryNormalization

open FiniteKrausChannel RecoveryPartialIsometries
open scoped ComplexOrder

noncomputable section

variable {I H L : Type*} [Fintype I] [Fintype H] [Fintype L]
  [DecidableEq I] [DecidableEq H] [DecidableEq L]

set_option linter.unusedSectionVars false

def root (w : I → ℝ) (i : I) : ℂ := Real.sqrt (w i)

def normalized (F : I → Matrix H L ℂ) (w : I → ℝ) (i : I) : Matrix H L ℂ :=
  (root w i)⁻¹ • F i

theorem root_star (w : I → ℝ) (i : I) : star (root w i) = root w i := by
  simp [root]

theorem root_conj (w : I → ℝ) (i : I) : (starRingEnd ℂ) (root w i) = root w i := by
  simp [root]

theorem root_sq (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (i : I) :
    root w i * root w i = (w i : ℂ) := by
  unfold root
  exact_mod_cast Real.mul_self_sqrt (hw i)

theorem root_ne_zero (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (i : I) (hi : w i ≠ 0) :
    root w i ≠ 0 := by
  intro h
  have hs := root_sq w hw i
  rw [h, zero_mul] at hs
  exact hi (by exact_mod_cast hs.symm)

theorem root_normSq (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (i : I) :
    Complex.normSq (root w i) = w i := by
  simp only [root, Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (hw i)]

theorem error_zero_of_weight_zero (F : I → Matrix H L ℂ) (w : I → ℝ)
    (hF : ∀ i j, (F i).conjTranspose * F j = if i = j then (w i : ℂ) • 1 else 0)
    (i : I) (hi : w i = 0) : F i = 0 := by
  apply Matrix.conjTranspose_mul_self_eq_zero.1
  simpa [hi] using hF i i

theorem normalized_gram (F : I → Matrix H L ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ i j, (F i).conjTranspose * F j = if i = j then (w i : ℂ) • 1 else 0)
    (i j : I) :
    (normalized F w i).conjTranspose * normalized F w j =
      if i = j then (if w i = 0 then (0 : ℂ) else 1) • 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [normalized, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, hF, if_true, smul_smul]
    change ((root w i)⁻¹ * (star ((root w i)⁻¹) * (w i : ℂ))) • (1 : Matrix L L ℂ) = _
    have hconj : star ((root w i)⁻¹) = (root w i)⁻¹ := by simp [root]
    rw [hconj]
    by_cases hi : w i = 0
    · simp [hi]
    · rw [if_neg hi, ← root_sq w hw i]
      have hr := root_ne_zero w hw i hi
      have heq : (root w i)⁻¹ * (root w i)⁻¹ * (root w i * root w i) = 1 := by
        field_simp
      simpa only [← mul_assoc] using congrArg (fun z : ℂ => z • (1 : Matrix L L ℂ)) heq
  · simp [normalized, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, hF, hij]

theorem normalized_active (F : I → Matrix H L ℂ) (w : I → ℝ) (i : I) :
    (if w i = 0 then (0 : ℂ) else 1) • normalized F w i = normalized F w i := by
  by_cases hi : w i = 0
  · simp [normalized, root, hi]
  · simp [hi]

theorem normalized_mul_error (F : I → Matrix H L ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ i j, (F i).conjTranspose * F j = if i = j then (w i : ℂ) • 1 else 0)
    (i j : I) :
    (normalized F w i).conjTranspose * F j = if i = j then root w j • 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [normalized, Matrix.conjTranspose_smul, Matrix.smul_mul,
      hF, if_true, smul_smul]
    change (star ((root w i)⁻¹) * (w i : ℂ)) • (1 : Matrix L L ℂ) = _
    have hconj : star ((root w i)⁻¹) = (root w i)⁻¹ := by simp [root]
    rw [hconj]
    rw [← root_sq w hw i]
    by_cases hi : root w i = 0
    · simp [hi]
    · simp [hi]
  · simp [normalized, Matrix.conjTranspose_smul, Matrix.smul_mul, hF, hij]

theorem root_smul_normalized (F : I → Matrix H L ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ i j, (F i).conjTranspose * F j = if i = j then (w i : ℂ) • 1 else 0)
    (i : I) : root w i • normalized F w i = F i := by
  by_cases hi : w i = 0
  · simp [normalized, root, hi, error_zero_of_weight_zero F w hF i hi]
  · have hr := root_ne_zero w hw i hi
    simp [normalized, smul_smul, hr]

theorem syndromeProjector_mul_error (F : I → Matrix H L ℂ) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ i j, (F i).conjTranspose * F j = if i = j then (w i : ℂ) • 1 else 0)
    (j : I) : syndromeProjector (normalized F w) * F j = F j := by
  simp only [syndromeProjector, Matrix.sum_mul, Matrix.mul_assoc,
    normalized_mul_error F w hw hF]
  rw [Finset.sum_eq_single j]
  · simpa [Matrix.mul_smul] using root_smul_normalized F w hw hF j
  · intro i _ hij
    simp [hij]
  · simp

/-- A concrete trace-preserving finite Kraus recovery, valid also when the
KL Gram matrix is singular. -/
theorem exists_recovery_of_diagonal (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (F : I → Matrix H L ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ i j, (F i).conjTranspose * F j = if i = j then (w i : ℂ) • 1 else 0) :
    ∃ R : Option I → Matrix H H ℂ, TracePreserving R ∧
      ∀ i j (X : Matrix L L ℂ), action R (F i * X * (F j).conjTranspose) =
        if i = j then (w i : ℂ) • (V * X * V.conjTranspose) else 0 := by
  let W := normalized F w
  have hP := syndromeProjector_idempotent W (fun i => if w i = 0 then (0 : ℂ) else 1)
    (normalized_gram F w hw hF) (normalized_active F w)
  refine ⟨recoveryKraus V W, recovery_tracePreserving V hV W hP, ?_⟩
  intro i j X
  simpa only [root_normSq w hw] using recovery_error_product V W F (root w)
    (normalized_mul_error F w hw hF) (syndromeProjector_mul_error F w hw hF) i j X

end

end MainTheory.RecoveryNormalization
