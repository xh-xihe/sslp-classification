import MainTheory.SharpClearing

/-!
# The semantic binary denominator constant

This file deliberately separates the *meaning* of the binary constant from
any finite computation used to establish its value.  In particular, no table
of proposed values is used in the definitions below.

`BetaBound N B` says that every nonsingular zero--one integer matrix of every
positive size at most `N` has sharp inverse denominator at most `B`.
`BetaExact N B` additionally contains an explicit matrix attaining `B`.

The determinant bridge is intentionally one-way: determinant clearing gives
an upper bound on the sharp denominator.  Attainment still has to be proved
from an inverse computation or from a genuine `SmithWitness`; determinant
attainment alone is not enough.
-/

namespace MainTheory.BinaryBeta

open MainTheory.SharpClearing

/-- Entrywise zero--one matrices, stated over the integers so that determinant
and Smith-form results apply without a coercion layer. -/
def IsZeroOne {m n : Type*} (C : Matrix m n ℤ) : Prop :=
  ∀ i j, C i j = 0 ∨ C i j = 1

/-- The universal upper-bound half of the binary denominator constant. -/
def BetaBound (N B : ℕ) : Prop :=
  ∀ (s : ℕ), 1 ≤ s → s ≤ N →
    ∀ C : Matrix (Fin s) (Fin s) ℤ,
      IsZeroOne C → C.det ≠ 0 → inverseDenominator C ≤ B

/-- The lower-bound half: a positive size at most `N` actually attains `B`. -/
def BetaAttained (N B : ℕ) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ s ≤ N ∧
    ∃ C : Matrix (Fin s) (Fin s) ℤ,
      IsZeroOne C ∧ C.det ≠ 0 ∧ inverseDenominator C = B

/-- Exact semantic certification of the binary denominator constant through
size `N`.  A value cannot enter through a private lookup table: both a
universal theorem and an attaining matrix are fields of the certificate. -/
structure BetaExact (N B : ℕ) : Prop where
  upper : BetaBound N B
  attained : BetaAttained N B

/-- The sharp inverse denominator is no larger than the absolute determinant.

This is the bridge that turns a fully checked maximum-determinant theorem into
the upper half of a beta theorem.  It uses divisibility from `SharpClearing`,
not a numerical coincidence. -/
theorem inverseDenominator_le_detNatAbs
    {s : Type*} [Fintype s] [DecidableEq s]
    (C : Matrix s s ℤ) (hdet : C.det ≠ 0) :
    inverseDenominator C ≤ C.det.natAbs := by
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hdet)
    (inverseDenominator_dvd_detNatAbs C hdet)

/-- A uniform absolute-determinant bound supplies the universal beta bound. -/
theorem betaBound_of_detNatAbs_bound {N B : ℕ}
    (hbound :
      ∀ (s : ℕ), 1 ≤ s → s ≤ N →
        ∀ C : Matrix (Fin s) (Fin s) ℤ,
          IsZeroOne C → C.det ≠ 0 → C.det.natAbs ≤ B) :
    BetaBound N B := by
  intro s hs hsn C hbinary hdet
  exact (inverseDenominator_le_detNatAbs C hdet).trans
    (hbound s hs hsn C hbinary hdet)

/-! ## Reducing all smaller sizes to the top size -/

/-- The canonical equivalence used to pad an `s x s` matrix to size `N`. -/
def padEquiv {s N : ℕ} (h : s ≤ N) :
    Fin s ⊕ Fin (N - s) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

/-- Pad by an identity block, then reindex the sum type as `Fin N`. -/
def padMatrix {s N : ℕ} (h : s ≤ N)
    (C : Matrix (Fin s) (Fin s) ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.reindex (padEquiv h) (padEquiv h)
    (Matrix.fromBlocks C 0 0 1)

/-- Identity padding preserves the determinant exactly. -/
theorem padMatrix_det {s N : ℕ} (h : s ≤ N)
    (C : Matrix (Fin s) (Fin s) ℤ) :
    (padMatrix h C).det = C.det := by
  unfold padMatrix
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Identity padding preserves the zero--one property. -/
theorem padMatrix_isZeroOne {s N : ℕ} (h : s ≤ N)
    (C : Matrix (Fin s) (Fin s) ℤ) (hC : IsZeroOne C) :
    IsZeroOne (padMatrix h C) := by
  intro i j
  change
    (Matrix.fromBlocks C 0 0 1)
        ((padEquiv h).symm i) ((padEquiv h).symm j) = 0 ∨
      (Matrix.fromBlocks C 0 0 1)
        ((padEquiv h).symm i) ((padEquiv h).symm j) = 1
  generalize (padEquiv h).symm i = i'
  generalize (padEquiv h).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using hC i' j'
  · simp
  · simp
  · by_cases hij : i' = j'
    · subst j'
      simp
    · simp [hij]

/-- It is enough to bound determinants in the single top size `N`: every
smaller positive binary matrix embeds as `diag(C, I)`, with the same
determinant.  For beta-six this removes the need for five additional finite
enumerations. -/
theorem betaBound_of_fixedSize_detNatAbs_bound {N B : ℕ}
    (hbound : ∀ C : Matrix (Fin N) (Fin N) ℤ,
      IsZeroOne C → C.det ≠ 0 → C.det.natAbs ≤ B) :
    BetaBound N B := by
  apply betaBound_of_detNatAbs_bound
  intro s _hs hsN C hbinary hdet
  have hpaddedDet : (padMatrix hsN C).det ≠ 0 := by
    simpa [padMatrix_det] using hdet
  have hpadded := hbound (padMatrix hsN C)
    (padMatrix_isZeroOne hsN C hbinary) hpaddedDet
  simpa [padMatrix_det] using hpadded

/-- On a genuine normalized Smith certificate, the determinant bridge bounds
the displayed final Smith factor as well. -/
theorem SmithWitness.lastFactor_le_detNatAbs
    {s : Type*} [Fintype s] [DecidableEq s] [LinearOrder s] [Nonempty s]
    {C : Matrix s s ℤ} (w : SmithWitness C) :
    w.lastFactor ≤ C.det.natAbs := by
  rw [← inverseDenominator_eq_smithLastFactor w]
  exact inverseDenominator_le_detNatAbs C w.det_ne_zero

/-- An explicit Smith witness turns equality of its last factor into a sharp
attainment statement.  This is the appropriate lower-bound bridge for a
future `BetaExact 6 9` certificate. -/
theorem betaAttained_of_smithWitness
    {N B s : ℕ} [Nonempty (Fin s)]
    (hs : 1 ≤ s) (hsN : s ≤ N)
    (C : Matrix (Fin s) (Fin s) ℤ) (hbinary : IsZeroOne C)
    (w : SmithWitness C) (hlast : w.lastFactor = B) :
    BetaAttained N B := by
  refine ⟨s, hs, hsN, C, hbinary, w.det_ne_zero, ?_⟩
  rw [inverseDenominator_eq_smithLastFactor w, hlast]

/-- Exact beta values, when certified semantically, are unique. -/
theorem BetaExact.bound_eq {N B D : ℕ}
    (hB : BetaExact N B) (hD : BetaExact N D) : B = D := by
  rcases hB.attained with ⟨s, hs, hsN, C, hbinary, hdet, hvalue⟩
  have hBD : B ≤ D := by
    rw [← hvalue]
    exact hD.upper s hs hsN C hbinary hdet
  rcases hD.attained with ⟨t, ht, htN, A, hAbinary, hAdet, hAvalue⟩
  have hDB : D ≤ B := by
    rw [← hAvalue]
    exact hB.upper t ht htN A hAbinary hAdet
  exact Nat.le_antisymm hBD hDB

end MainTheory.BinaryBeta
