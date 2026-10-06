import MainTheory.BinaryBeta

/-!
# The binary denominator constant exists at every size

`BinaryBeta.BetaBound N B` says every nonsingular zero--one matrix of size at
most `N` has inverse denominator at most `B`.  The repository proves
`BetaBound 6 9` by a 1716-case certificate, and that computation is specific
to `N = 6`.

But the mere ∃STENCE of a bound is free: for each size there are only
finitely many zero--one matrices, so the denominators attain a maximum.  This
file records that, so that statements needing "some" bound are not blocked on
computing one.

Nothing here computes a value; `betaOf N` is a supremum over an explicit
finite type, not a certified constant.
-/

namespace MainTheory.BetaExists

open MainTheory.BinaryBeta

/-- The zero--one matrix named by a Boolean matrix. -/
def ofBool {s : ℕ} (M : Matrix (Fin s) (Fin s) Bool) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if M i j then 1 else 0

theorem isZeroOne_ofBool {s : ℕ} (M : Matrix (Fin s) (Fin s) Bool) :
    IsZeroOne (ofBool M) := by
  intro i j
  by_cases h : M i j
  · exact Or.inr (by simp [ofBool, h])
  · exact Or.inl (by simp [ofBool, h])

/-- Every zero--one matrix is `ofBool` of something. -/
theorem exists_ofBool {s : ℕ} {C : Matrix (Fin s) (Fin s) ℤ}
    (hC : IsZeroOne C) : ∃ M, ofBool M = C := by
  refine ⟨fun i j => decide (C i j = 1), ?_⟩
  funext i j
  rcases hC i j with h | h
  · simp [ofBool, h]
  · simp [ofBool, h]

/-- The largest inverse denominator among zero--one matrices of one size. -/
noncomputable def betaAt (s : ℕ) : ℕ :=
  (Finset.univ : Finset (Matrix (Fin s) (Fin s) Bool)).sup fun M =>
    SharpClearing.inverseDenominator (ofBool M)

theorem le_betaAt {s : ℕ} {C : Matrix (Fin s) (Fin s) ℤ} (hC : IsZeroOne C) :
    SharpClearing.inverseDenominator C ≤ betaAt s := by
  obtain ⟨M, rfl⟩ := exists_ofBool hC
  exact Finset.le_sup
    (f := fun M : Matrix (Fin s) (Fin s) Bool =>
      SharpClearing.inverseDenominator (ofBool M)) (Finset.mem_univ M)

/-- A bound valid for every size up to `N`. -/
noncomputable def betaOf (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sup betaAt

/-- **A binary denominator bound exists at every size.**

Not a computation: this is the pigeonhole fact that finitely many matrices
have finitely many denominators.  The sharp value at `N = 6` is the separate
certified result `BetaExact 6 9`. -/
theorem betaBound_betaOf (N : ℕ) : BetaBound N (betaOf N) := by
  intro s hs hsN C hC _
  refine le_trans (le_betaAt hC) ?_
  exact Finset.le_sup (f := betaAt) (Finset.mem_range.2 (by omega))

theorem exists_betaBound (N : ℕ) : ∃ B, BetaBound N B :=
  ⟨betaOf N, betaBound_betaOf N⟩

/-- The bound is positive: inverse denominators are. -/
theorem betaOf_pos (N : ℕ) : 0 < betaOf N := by
  have h1 : (1 : ℕ) ≤ betaAt 0 := by
    have hle : SharpClearing.inverseDenominator
        (ofBool (fun _ _ => true : Matrix (Fin 0) (Fin 0) Bool))
        ≤ betaAt 0 :=
      le_betaAt (isZeroOne_ofBool _)
    exact le_trans (SharpClearing.inverseDenominator_pos _) hle
  have h2 : betaAt 0 ≤ betaOf N :=
    Finset.le_sup (f := betaAt) (Finset.mem_range.2 (by omega))
  omega

end MainTheory.BetaExists
