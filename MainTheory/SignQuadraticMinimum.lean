import Mathlib

namespace MainTheory.SignQuadraticMinimum

open scoped BigOperators

def quadratic {n : ℕ} (c : ℤ) (b : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : ℤ :=
  c + (∑ i, b i * v i) + ∑ i, ∑ j, A i j * v i * v j

def tailMatrix {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => A i.succ j.succ

def branchLinear {n : ℕ} (b : Fin (n+1) → ℤ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (s : ℤ) : Fin n → ℤ :=
  fun i => b i.succ + s * (A 0 i.succ + A i.succ 0)

/-- Exhaustive signed quadratic minimum, sharing the restricted polynomial
at every branch. This is ordinary kernel-reducible integer recursion. -/
def minimum : (n : ℕ) → ℤ → (Fin n → ℤ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, c, _, _ => c
  | n+1, c, b, A =>
    min (minimum n (c + b 0 + A 0 0) (branchLinear b A 1) (tailMatrix A))
      (minimum n (c - b 0 + A 0 0) (branchLinear b A (-1)) (tailMatrix A))

theorem quadratic_cons {n : ℕ} (c : ℤ) (b : Fin (n+1) → ℤ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (s : ℤ) (hs : s * s = 1)
    (v : Fin n → ℤ) :
    quadratic c b A (Fin.cons s v) =
      quadratic (c + b 0 * s + A 0 0) (branchLinear b A s) (tailMatrix A) v := by
  simp only [quadratic, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    branchLinear, tailMatrix, add_mul, mul_add, Finset.sum_add_distrib]
  have hdiag : A 0 0 * s * s = A 0 0 := by rw [mul_assoc, hs, mul_one]
  rw [hdiag]
  have hleft : (∑ i : Fin n, A 0 i.succ * s * v i) =
      ∑ i : Fin n, s * A 0 i.succ * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i : Fin n, A i.succ 0 * v i * s) =
      ∑ i : Fin n, s * A i.succ 0 * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, hright]
  ring

theorem minimum_le : ∀ n (c : ℤ) (b : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ), (∀ i, v i = 1 ∨ v i = -1) → minimum n c b A ≤ quadratic c b A v := by
  intro n
  induction n with
  | zero => intro c b A v _; simp [minimum, quadratic]
  | succ n ih =>
    intro c b A v hv
    have ht : ∀ i : Fin n, v i.succ = 1 ∨ v i.succ = -1 := fun i => hv i.succ
    have he : Fin.cons (v 0) (fun i : Fin n => v i.succ) = v := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rcases hv 0 with hp | hm
    · have hs : v 0 * v 0 = 1 := by rw [hp]; norm_num
      rw [← he, quadratic_cons c b A (v 0) hs, hp]
      simpa only [mul_one] using le_trans (min_le_left _ _)
        (ih (c + b 0 + A 0 0) (branchLinear b A 1) (tailMatrix A) _ ht)
    · have hs : v 0 * v 0 = 1 := by rw [hm]; norm_num
      rw [← he, quadratic_cons c b A (v 0) hs, hm]
      simpa only [mul_neg_one, sub_eq_add_neg] using le_trans (min_le_right _ _)
        (ih (c - b 0 + A 0 0) (branchLinear b A (-1)) (tailMatrix A) _ ht)

end MainTheory.SignQuadraticMinimum
