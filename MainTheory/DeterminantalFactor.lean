import MainTheory.SharpClearing

/-!
# The sharp denominator is the last determinantal factor

`thm:d3-bound` and `lem:denominator-clearing` state the divisibility
`q | d_r(C)`, with `d_r(C)` the last invariant factor of the pivot matrix.
This repository proves `q | inverseDenominator C` outright, and
`SharpClearing` proves `inverseDenominator C = w.lastFactor` for a
`SmithWitness w` -- but at the time this file was written nothing built a
`SmithWitness`, so the *identification* of that number with the paper's
`d_r(C)`, not the bound, was what was missing.

Building a `SmithWitness` means unimodular `U` and `V` over the integers with
`U C V` diagonal *and* the divisibility chain, which Mathlib does not provide:
`Submodule.smithNormalForm` returns bases rather than matrices and does not
expose the chain.

`SmithExistence.exists_normalized_smith` has since built one anyway, by
minimising a measure over genuine positive diagonal reductions, and
`PivotSmithNormalForm` uses it to state `q | d_r(C)` against an actual normal
form of each pivot.  So the two routes now agree, and this one remains the
cheaper: the identification does not need any of that.  The last invariant factor of a
nonsingular integer matrix has a second classical description, as the ratio of
the last two *determinantal divisors*

  `d_s(C) = D_s(C) / D_{s-1}(C)`,

`D_k` being the gcd of all `k x k` minors.  For a square nonsingular matrix
`D_s = |det C|`, and the `(s-1)`-minors are exactly the cofactors, so
`D_{s-1}` is the gcd of the entries of the adjugate.  This file proves

  `inverseDenominator C = |det C| / gcd(adjugate C)`,

which is `d_s(C)` on the nose, with no Smith normal form anywhere.

The proof is entrywise.  `C * adjugate C = det C` makes the adjugate over the
determinant *be* the rational inverse, so an entry's denominator divides `q`
exactly when `det C | q * adjugate C i j`; asking that of every entry is
asking `det | q * gcd(adjugate)`, which pins the least such `q` to
`|det| / gcd(adjugate)`.
-/

namespace MainTheory.DeterminantalFactor

open MainTheory.SharpClearing

variable {s : Type*} [Fintype s] [DecidableEq s]

omit [DecidableEq s] in
/-- Casting a matrix product to the rationals is the product of the casts. -/
theorem ratMatrix_mul (A B : Matrix s s ℤ) :
    ratMatrix (A * B) = ratMatrix A * ratMatrix B :=
  Matrix.map_mul

theorem ratMatrix_det_smul_one (C : Matrix s s ℤ) :
    ratMatrix (C.det • (1 : Matrix s s ℤ)) = (C.det : ℚ) • (1 : Matrix s s ℚ) := by
  ext i j
  simp only [ratMatrix, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, eq_intCast]
  by_cases h : i = j <;> simp [h]

/-- **The rational inverse is the adjugate over the determinant.**

Proved from `Matrix.mul_adjugate` by exhibiting a right inverse, so it needs
no lemma about how `adjugate` interacts with a ring hom. -/
theorem inv_eq_smul_adjugate (C : Matrix s s ℤ) (h : C.det ≠ 0) :
    (ratMatrix C)⁻¹ = ((C.det : ℚ))⁻¹ • ratMatrix C.adjugate := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, ← ratMatrix_mul, Matrix.mul_adjugate,
    ratMatrix_det_smul_one, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h),
    one_smul]

theorem inv_entry (C : Matrix s s ℤ) (h : C.det ≠ 0) (i j : s) :
    (ratMatrix C)⁻¹ i j = (C.adjugate i j : ℚ) / (C.det : ℚ) := by
  rw [inv_eq_smul_adjugate C h]
  simp only [Matrix.smul_apply, smul_eq_mul, ratMatrix, Matrix.map_apply,
    eq_intCast]
  ring

/-! ## The two determinantal divisors -/

/-- `D_{s-1}(C)`: the gcd of the cofactors, that is of the entries of the
adjugate.  For a square matrix the `(s-1)`-minors are exactly the cofactors, so
this is the second-to-last determinantal divisor. -/
noncomputable def cofactorGcd (C : Matrix s s ℤ) : ℕ :=
  Finset.univ.gcd fun p : s × s => (C.adjugate p.1 p.2).natAbs

theorem cofactorGcd_dvd (C : Matrix s s ℤ) (i j : s) :
    cofactorGcd C ∣ (C.adjugate i j).natAbs :=
  Finset.gcd_dvd (Finset.mem_univ (i, j))

theorem cofactorGcd_dvd_int (C : Matrix s s ℤ) (i j : s) :
    ((cofactorGcd C : ℕ) : ℤ) ∣ C.adjugate i j := by
  have h : ((cofactorGcd C : ℕ) : ℤ) ∣ ((C.adjugate i j).natAbs : ℤ) :=
    Int.natCast_dvd_natCast.2 (cofactorGcd_dvd C i j)
  exact h.trans (Int.natAbs_dvd.2 dvd_rfl)

/-- The Laplace expansion makes the gcd of the cofactors divide the
determinant, so `D_{s-1} | D_s` as the classical theory requires. -/
theorem cofactorGcd_dvd_det (C : Matrix s s ℤ) [Nonempty s] :
    cofactorGcd C ∣ C.det.natAbs := by
  classical
  obtain ⟨i⟩ := ‹Nonempty s›
  have hrow : (C * C.adjugate) i i = C.det := by
    rw [Matrix.mul_adjugate]
    simp
  have hsum : (∑ j, C i j * C.adjugate j i) = C.det := by
    rw [← hrow, Matrix.mul_apply]
  have hdvd : ((cofactorGcd C : ℕ) : ℤ) ∣ C.det := by
    rw [← hsum]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (cofactorGcd_dvd_int C j i) _
  simpa using Int.natAbs_dvd_natAbs.2 hdvd

/-! ## The entrywise clearing criterion -/

theorem den_dvd_iff (C : Matrix s s ℤ) (hdet : C.det ≠ 0) (q : ℕ) (hq : 0 < q)
    (i j : s) :
    ((ratMatrix C)⁻¹ i j).den ∣ q ↔ C.det ∣ (q : ℤ) * C.adjugate i j := by
  have hdq : ((C.det : ℚ)) ≠ 0 := by exact_mod_cast hdet
  rw [Denominator.clears_iff q hq, inv_entry C hdet i j]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have : (q : ℚ) * (C.adjugate i j : ℚ) = (C.det : ℚ) * (a : ℚ) := by
      field_simp at ha
      linarith [ha]
    exact_mod_cast this
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hb' : ((q : ℚ)) * (C.adjugate i j : ℚ) = (C.det : ℚ) * (b : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hb
    field_simp
    linarith [hb']

theorem inverseDenominator_dvd_iff (C : Matrix s s ℤ) (hdet : C.det ≠ 0)
    (q : ℕ) (hq : 0 < q) :
    inverseDenominator C ∣ q ↔ ∀ i j, C.det ∣ (q : ℤ) * C.adjugate i j := by
  constructor
  · intro hd i j
    exact (den_dvd_iff C hdet q hq i j).1
      ((inverse_entry_den_dvd C i j).trans hd)
  · intro h
    refine Denominator.lcmDen_dvd_of_clears (inverseEntries C) q fun p => ?_
    exact (den_dvd_iff C hdet q hq p.1 p.2).2 (h p.1 p.2)

/-! ## The identification -/

/-- **The sharp denominator is the last determinantal factor.**

`inverseDenominator C = D_s(C) / D_{s-1}(C)`, which is the classical last
invariant factor `d_s(C)` of `eq:snf`. -/
theorem inverseDenominator_eq_det_div_cofactorGcd (C : Matrix s s ℤ)
    [Nonempty s] (hdet : C.det ≠ 0) :
    inverseDenominator C = C.det.natAbs / cofactorGcd C := by
  classical
  have hgd : cofactorGcd C ∣ C.det.natAbs := cofactorGcd_dvd_det C
  have hgpos : 0 < cofactorGcd C := by
    rcases Nat.eq_zero_or_pos (cofactorGcd C) with h | h
    · exact absurd (Int.natAbs_eq_zero.1 (Nat.eq_zero_of_zero_dvd (h ▸ hgd))) hdet
    · exact h
  set Q := C.det.natAbs / cofactorGcd C with hQ
  have hQg : Q * cofactorGcd C = C.det.natAbs := Nat.div_mul_cancel hgd
  have hQpos : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, zero_mul] at hQg
      exact absurd (Int.natAbs_eq_zero.1 hQg.symm) hdet
    · exact h
  refine Nat.dvd_antisymm ?_ ?_
  · refine (inverseDenominator_dvd_iff C hdet Q hQpos).2 fun i j => ?_
    obtain ⟨b, hb⟩ := cofactorGcd_dvd C i j
    have hnat : C.det.natAbs ∣ Q * (C.adjugate i j).natAbs := by
      rw [hb, ← mul_assoc, hQg]
      exact Dvd.intro b rfl
    have habs : C.det.natAbs ∣ ((Q : ℤ) * C.adjugate i j).natAbs := by
      rw [Int.natAbs_mul]
      simpa using hnat
    exact Int.natAbs_dvd_natAbs.1 habs
  · have hall := (inverseDenominator_dvd_iff C hdet _ (inverseDenominator_pos C)).1
      dvd_rfl
    have hnat : ∀ i j, C.det.natAbs ∣ inverseDenominator C * (C.adjugate i j).natAbs := by
      intro i j
      have h := hall i j
      rw [← Int.natAbs_dvd_natAbs] at h
      simpa [Int.natAbs_mul] using h
    have hgcd : C.det.natAbs ∣ inverseDenominator C * cofactorGcd C := by
      have hg : C.det.natAbs ∣ Finset.univ.gcd
          fun p : s × s => inverseDenominator C * (C.adjugate p.1 p.2).natAbs :=
        Finset.dvd_gcd fun p _ => hnat p.1 p.2
      simpa [cofactorGcd, Finset.gcd_mul_left] using hg
    rw [← hQg] at hgcd
    exact (Nat.mul_dvd_mul_iff_right hgpos).1 hgcd

/-- The paper's `d_r(C)`, defined the classical way. -/
noncomputable def lastInvariantFactor (C : Matrix s s ℤ) : ℕ :=
  C.det.natAbs / cofactorGcd C

/-- **`eq:snf`'s `d_r(C)` is the number this development already bounds.**

Every theorem of the form `q | inverseDenominator C` in this repository is
therefore a theorem of the form `q | d_r(C)` in the paper's notation. -/
theorem dvd_lastInvariantFactor {C : Matrix s s ℤ} [Nonempty s]
    (hdet : C.det ≠ 0) {q : ℕ} (h : q ∣ inverseDenominator C) :
    q ∣ lastInvariantFactor C := by
  rwa [inverseDenominator_eq_det_div_cofactorGcd C hdet] at h

end MainTheory.DeterminantalFactor
