import MainTheory.FiniteKrausChannel

/-! # A finite Kraus recovery from orthogonal error isometries -/

namespace MainTheory.RecoveryPartialIsometries

open FiniteKrausChannel

noncomputable section

variable {I H L : Type*} [Fintype I] [Fintype H] [Fintype L]
  [DecidableEq I] [DecidableEq H] [DecidableEq L]

set_option linter.unusedSectionVars false

def syndromeProjector (W : I → Matrix H L ℂ) : Matrix H H ℂ :=
  ∑ i, W i * (W i).conjTranspose

theorem syndromeProjector_hermitian (W : I → Matrix H L ℂ) :
    (syndromeProjector W).conjTranspose = syndromeProjector W := by
  simp [syndromeProjector, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]

theorem syndromeProjector_idempotent (W : I → Matrix H L ℂ)
    (p : I → ℂ)
    (hW : ∀ i j, (W i).conjTranspose * W j = if i = j then p i • 1 else 0)
    (hp : ∀ i, p i • W i = W i) :
    syndromeProjector W * syndromeProjector W = syndromeProjector W := by
  classical
  simp only [syndromeProjector, Matrix.sum_mul, Matrix.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, W i * (W i).conjTranspose * (W j * (W j).conjTranspose)) =
        ∑ j, W i * ((W i).conjTranspose * W j) * (W j).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = W i * (W i).conjTranspose := by
      rw [Finset.sum_eq_single i]
      · simp [hW, Matrix.mul_smul, hp]
      · intro j _ hji
        simp [hW, Ne.symm hji]
      · simp

def recoveryKraus (V : Matrix H L ℂ) (W : I → Matrix H L ℂ) :
    Option I → Matrix H H ℂ
  | some i => V * (W i).conjTranspose
  | none => 1 - syndromeProjector W

theorem recovery_tracePreserving (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (W : I → Matrix H L ℂ)
    (hP : syndromeProjector W * syndromeProjector W = syndromeProjector W) :
    TracePreserving (recoveryKraus V W) := by
  classical
  unfold TracePreserving
  rw [Fintype.sum_option]
  simp only [recoveryKraus, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    syndromeProjector_hermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hsome (i : I) : W i * V.conjTranspose * (V * (W i).conjTranspose) =
      W i * (W i).conjTranspose := by
    calc
      _ = W i * (V.conjTranspose * V) * (W i).conjTranspose := by simp [Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp
  simp only [hsome]
  change (1 - syndromeProjector W) * (1 - syndromeProjector W) + syndromeProjector W = 1
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, hP]
  abel

theorem recoveryKraus_mul (V : Matrix H L ℂ) (W F : I → Matrix H L ℂ)
    (z : I → ℂ)
    (hWF : ∀ i j, (W i).conjTranspose * F j = if i = j then z j • 1 else 0)
    (hPF : ∀ j, syndromeProjector W * F j = F j) (r : Option I) (j : I) :
    recoveryKraus V W r * F j = if r = some j then z j • V else 0 := by
  classical
  cases r with
  | none => simp [recoveryKraus, Matrix.sub_mul, hPF]
  | some i =>
    by_cases hij : i = j
    · simp [recoveryKraus, Matrix.mul_assoc, hWF, hij, Matrix.mul_smul]
    · simp [recoveryKraus, Matrix.mul_assoc, hWF, hij]

theorem recovery_error_product (V : Matrix H L ℂ) (W F : I → Matrix H L ℂ)
    (z : I → ℂ)
    (hWF : ∀ i j, (W i).conjTranspose * F j = if i = j then z j • 1 else 0)
    (hPF : ∀ j, syndromeProjector W * F j = F j)
    (i j : I) (X : Matrix L L ℂ) :
    action (recoveryKraus V W) (F i * X * (F j).conjTranspose) =
      if i = j then (Complex.normSq (z i) : ℂ) • (V * X * V.conjTranspose) else 0 := by
  classical
  unfold action
  have hterm (r : Option I) :
      recoveryKraus V W r * (F i * X * (F j).conjTranspose) *
        (recoveryKraus V W r).conjTranspose =
      (recoveryKraus V W r * F i) * X *
        (recoveryKraus V W r * F j).conjTranspose := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp_rw [hterm, recoveryKraus_mul V W F z hWF hPF]
  rw [Finset.sum_eq_single (some i)]
  · by_cases hij : i = j
    · subst j
      simp only [if_true, Matrix.conjTranspose_smul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
      congr 1
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    · simp [hij]
  · intro r _ hr
    simp [hr]
  · simp

end

end MainTheory.RecoveryPartialIsometries
