import Mathlib

/-!
# Elementary purity identities for the quantum Singleton bound

These are finite matrix identities and Cauchy--Schwarz inequalities.  They do
not assume an entropy formalism or a strong-subadditivity axiom.
-/

namespace MainTheory.SingletonPurity

noncomputable section

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

def frobSq (M : Matrix A B ℂ) : ℝ := ∑ a, ∑ b, Complex.normSq (M a b)

theorem frobSq_nonneg (M : Matrix A B ℂ) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem frobSq_eq_zero_iff (M : Matrix A B ℂ) : frobSq M = 0 ↔ M = 0 := by
  constructor
  · intro h
    have ha : ∀ a, (∑ b, Complex.normSq (M a b)) = 0 := by
      exact fun a => (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg (M a b))).1 h a (Finset.mem_univ a)
    ext a b
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg (fun b _ => Complex.normSq_nonneg (M a b))).1
        (ha a) b (Finset.mem_univ b))
  · rintro rfl
    simp [frobSq]

theorem frobSq_pos (M : Matrix A B ℂ) (h : M ≠ 0) : 0 < frobSq M :=
  lt_of_le_of_ne (frobSq_nonneg M) (Ne.symm (mt (frobSq_eq_zero_iff M).1 h))

theorem trace_mul_star (M : Matrix A B ℂ) :
    Matrix.trace (M * M.conjTranspose) = (frobSq M : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    frobSq, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- The two reduced Gram matrices of a pure coefficient tensor have equal purity. -/
theorem gram_purity_eq (M : Matrix A B ℂ) :
    frobSq (M * M.conjTranspose) = frobSq (M.conjTranspose * M) := by
  apply Complex.ofReal_injective
  rw [← trace_mul_star, ← trace_mul_star]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Matrix.trace ((M * M.conjTranspose) * (M * M.conjTranspose))
      = Matrix.trace ((M * M.conjTranspose * M) * M.conjTranspose) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace (M.conjTranspose * (M * M.conjTranspose) * M) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((M.conjTranspose * M) * (M.conjTranspose * M)) := by simp [Matrix.mul_assoc]

theorem normSq_sum_le_card (v : C → ℂ) :
    Complex.normSq (∑ c, v c) ≤ (Fintype.card C : ℝ) * ∑ c, Complex.normSq (v c) := by
  have hre := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c => (v c).re)
  have him := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c => (v c).im)
  simp only [Finset.card_univ] at hre him
  simp only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib,
    ← pow_two]
  nlinarith

/-- Trace out the second finite tensor factor. -/
def partialTrace (M : Matrix (B × C) (B × C) ℂ) : Matrix B B ℂ :=
  fun b b' => ∑ c, M (b, c) (b', c)

/-- Purity cannot drop by more than the dimension under a partial trace. -/
theorem partialTrace_frobSq_le (M : Matrix (B × C) (B × C) ℂ) :
    frobSq (partialTrace M) ≤ (Fintype.card C : ℝ) * frobSq M := by
  have hdiag : (∑ b : B, ∑ b' : B, ∑ c : C, Complex.normSq (M (b, c) (b', c))) ≤
      ∑ b : B, ∑ b' : B, ∑ c : C, ∑ c' : C, Complex.normSq (M (b, c) (b', c')) := by
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro b' _
    apply Finset.sum_le_sum
    intro c _
    exact Finset.single_le_sum (fun c' _ => Complex.normSq_nonneg (M (b, c) (b', c')))
      (Finset.mem_univ c)
  have hsum : (∑ b : B, ∑ b' : B, ∑ c : C, ∑ c' : C, Complex.normSq (M (b, c) (b', c')))
      = frobSq M := by
    simp only [frobSq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
  calc frobSq (partialTrace M)
      ≤ ∑ b : B, ∑ b' : B, (Fintype.card C : ℝ) * ∑ c : C, Complex.normSq (M (b, c) (b', c)) := by
        apply Finset.sum_le_sum
        intro b _
        exact Finset.sum_le_sum fun b' _ => normSq_sum_le_card (fun c => M (b, c) (b', c))
    _ = (Fintype.card C : ℝ) * ∑ b : B, ∑ b' : B, ∑ c : C, Complex.normSq (M (b, c) (b', c)) := by
      simp only [Finset.mul_sum]
    _ ≤ (Fintype.card C : ℝ) * frobSq M := by
      rw [← hsum]
      exact mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _)

theorem frobSq_transpose (M : Matrix A B ℂ) : frobSq M.transpose = frobSq M :=
  Finset.sum_comm

theorem frobSq_nat_smul (k : ℕ) (M : Matrix A B ℂ) :
    frobSq ((k : ℂ) • M) = (k : ℝ) ^ 2 * frobSq M := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_natCast, Finset.mul_sum, pow_two]

/-- The Gram matrix forced by decoupling from a rank-`K` logical reference. -/
def logicalBlock (K : ℕ) (R : Matrix A A ℂ) : Matrix (Fin K × A) (Fin K × A) ℂ :=
  fun ka la' => if ka.1 = la'.1 then R ka.2 la'.2 else 0

theorem frobSq_logicalBlock (K : ℕ) (R : Matrix A A ℂ) :
    frobSq (logicalBlock K R) = (K : ℝ) * frobSq R := by
  classical
  simp only [frobSq, logicalBlock, Fintype.sum_prod_type]
  simp only [apply_ite, Complex.normSq_zero]
  have hsum (k : Fin K) (a : A) :
      (∑ l : Fin K, ∑ a' : A, if k = l then Complex.normSq (R a a') else 0)
        = ∑ a' : A, Complex.normSq (R a a') := by simp
  simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The core Singleton estimate from two complementary decoupled Gram matrices. -/
theorem singleton_of_gram_data {K : ℕ}
    (M : Matrix (Fin K × A) (B × C) ℂ)
    (N : Matrix (Fin K × B) (A × C) ℂ)
    (RA : Matrix A A ℂ) (RB : Matrix B B ℂ)
    (hA : RA ≠ 0) (hB : RB ≠ 0)
    (hMA : M * M.conjTranspose = logicalBlock K RA)
    (hNB : N * N.conjTranspose = logicalBlock K RB)
    (hMB : partialTrace (M.conjTranspose * M) = (K : ℂ) • RB.transpose)
    (hNA : partialTrace (N.conjTranspose * N) = (K : ℂ) • RA.transpose) :
    K ≤ Fintype.card C := by
  have hM := partialTrace_frobSq_le (M.conjTranspose * M)
  have hN := partialTrace_frobSq_le (N.conjTranspose * N)
  rw [hMB, frobSq_nat_smul, frobSq_transpose, ← gram_purity_eq M,
    hMA, frobSq_logicalBlock] at hM
  rw [hNA, frobSq_nat_smul, frobSq_transpose, ← gram_purity_eq N,
    hNB, frobSq_logicalBlock] at hN
  by_cases hK : K = 0
  · omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hApos := frobSq_pos RA hA
  have hBpos := frobSq_pos RB hB
  have hc : (0 : ℝ) ≤ Fintype.card C := Nat.cast_nonneg _
  have h1 : (K : ℝ) * frobSq RB ≤ (Fintype.card C : ℝ) * frobSq RA := by nlinarith
  have h2 : (K : ℝ) * frobSq RA ≤ (Fintype.card C : ℝ) * frobSq RB := by nlinarith
  have hprod := mul_le_mul h1 h2 (by positivity : 0 ≤ (K : ℝ) * frobSq RA)
    (by positivity : 0 ≤ (Fintype.card C : ℝ) * frobSq RA)
  have hsq : (K : ℝ) ^ 2 ≤ (Fintype.card C : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hApos hBpos)).1
    nlinarith [hprod]
  have hle : (K : ℝ) ≤ Fintype.card C := by nlinarith
  exact_mod_cast hle

end

end MainTheory.SingletonPurity
