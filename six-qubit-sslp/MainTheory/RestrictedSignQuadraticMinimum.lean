import MainTheory.SignQuadraticMinimum

namespace MainTheory.SignQuadraticMinimum

def Matches {n : ℕ} (fixed : Fin n → Option ℤ) (v : Fin n → ℤ) : Prop :=
  ∀ i s, fixed i = some s → v i = s

instance {n : ℕ} (fixed : Fin n → Option ℤ) (v : Fin n → ℤ) : Decidable (Matches fixed v) :=
  inferInstanceAs (Decidable (∀ i, ∀ s ∈ fixed i, v i = s))

def restrictedMinimum : (n : ℕ) → ℤ → (Fin n → ℤ) → Matrix (Fin n) (Fin n) ℤ →
    (Fin n → Option ℤ) → ℤ
  | 0, c, _, _, _ => c
  | n+1, c, b, A, fixed =>
    match fixed 0 with
    | none =>
      min (restrictedMinimum n (c + b 0 + A 0 0) (branchLinear b A 1)
        (tailMatrix A) (fun i => fixed i.succ))
        (restrictedMinimum n (c - b 0 + A 0 0) (branchLinear b A (-1))
          (tailMatrix A) (fun i => fixed i.succ))
    | some s => restrictedMinimum n (c + b 0 * s + A 0 0 * s * s) (branchLinear b A s)
        (tailMatrix A) (fun i => fixed i.succ)

theorem restrictedMinimum_le : ∀ n (c : ℤ) (b : Fin n → ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) (fixed : Fin n → Option ℤ)
    (v : Fin n → ℤ), (∀ i, v i = 1 ∨ v i = -1) → Matches fixed v →
      restrictedMinimum n c b A fixed ≤ quadratic c b A v := by
  intro n
  induction n with
  | zero => intro c b A fixed v _ _; simp [restrictedMinimum, quadratic]
  | succ n ih =>
    intro c b A fixed v hv hf
    have ht : ∀ i : Fin n, v i.succ = 1 ∨ v i.succ = -1 := fun i => hv i.succ
    have hft : Matches (fun i : Fin n => fixed i.succ) (fun i => v i.succ) :=
      fun i s hs => hf i.succ s hs
    have he : Fin.cons (v 0) (fun i : Fin n => v i.succ) = v := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hs : v 0 * v 0 = 1 := by
      rcases hv 0 with hp | hm
      · rw [hp]; norm_num
      · rw [hm]; norm_num
    rw [← he, quadratic_cons c b A (v 0) hs]
    cases hfixed : fixed 0 with
    | none =>
      rcases hv 0 with hp | hm
      · simp only [restrictedMinimum, hfixed, hp, mul_one]
        exact le_trans (min_le_left _ _) (ih _ _ _ _ _ ht hft)
      · simp only [restrictedMinimum, hfixed, hm, mul_neg_one, ← sub_eq_add_neg]
        exact le_trans (min_le_right _ _) (ih _ _ _ _ _ ht hft)
    | some s =>
      have hvs := hf 0 s hfixed
      have hs' : s * s = 1 := by rwa [hvs] at hs
      simp only [restrictedMinimum, hfixed, hvs]
      rw [mul_assoc (A 0 0), hs', mul_one]
      exact ih _ _ _ _ _ ht hft

end MainTheory.SignQuadraticMinimum
