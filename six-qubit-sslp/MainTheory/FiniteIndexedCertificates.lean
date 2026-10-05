import MainTheory.BalancedFiniteTable

/-! Checked witnesses selected by a balanced, exhaustively indexed table. -/
namespace MainTheory.FiniteIndexedCertificates

open MainTheory.BalancedFiniteTable

theorem all {n : ℕ} {P : Fin n → Prop}
    (table : MainTheory.BalancedFiniteTable.Tree {i : Fin n // P i})
    (index : ∀ i : Fin n, (lookup table i.val).val = i) (i : Fin n) : P i := by
  have h := (lookup table i.val).property
  rwa [index i] at h

end MainTheory.FiniteIndexedCertificates
