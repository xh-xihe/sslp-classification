import SixQubit.CodeBridge

/-!
# Generic physical flip-character obstructions

The columns enumerate the complete incidence set of two arbitrary support
bounds.  Honest Knill--Laflamme conditions supply every matrix row, including
the nonzero Pauli prefactor.  An invertible restricted character matrix then
annihilates the actual products of endpoint amplitudes.
-/

namespace MainTheory.FlipCharacter

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

variable {n N : ℕ}

def incidenceSet (S₀ S₁ : Finset (SS.BitString n)) (e : SS.BitString n) :=
  S₁.filter (fun y => SS.bxor y e ∈ S₀)

def character (z y : SS.BitString n) : ℂ := if SS.bdot z y then -1 else 1

def incidenceMonomial (c d : SS.State n ℂ) (e y : SS.BitString n) : ℂ :=
  star (c (SS.bxor y e)) * d y

def restrictedCharacterMatrix (z y : Fin N → SS.BitString n) :
    Matrix (Fin N) (Fin N) ℂ := fun a b => character (z a) (y b)

theorem character_zero (y : SS.BitString n) : character (fun _ => false) y = 1 := by
  simp [character, SS.bdot]

theorem character_single (j : Fin n) (y : SS.BitString n) :
    character (SS.stdBasis j) y = if y j then -1 else 1 := by
  rw [character, SixQubit.bdot_stdBasis]

/-- Reindexing does not discard any incidence or require its amplitude nonzero. -/
theorem offSum_eq_indexed (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.State n ℂ) (e z : SS.BitString n) (y : Fin N → SS.BitString n)
    (hy : Function.Injective y)
    (hI : Finset.univ.image y = incidenceSet S₀ S₁ e) :
    SixQubit.offSumOn S₀ S₁ c d e z =
      ∑ r, character z (y r) * incidenceMonomial c d e (y r) := by
  classical
  change (∑ v ∈ incidenceSet S₀ S₁ e,
    SixQubit.signMul (SS.bdot z v) (star (c (SS.bxor v e)) * d v)) = _
  rw [← hI, Finset.sum_image hy.injOn]
  apply Finset.sum_congr rfl
  intro r _
  cases hb : SS.bdot z (y r) <;>
    simp [character, incidenceMonomial, SixQubit.signMul, hb]

/-- Every selected row is derived from the physical cross-KL equation. -/
theorem restricted_matrix_times_monomials (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.State n ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ x, x ∉ S₁ → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3)
    (e : SS.BitString n) (z y : Fin N → SS.BitString n)
    (hy : Function.Injective y)
    (hI : Finset.univ.image y = incidenceSet S₀ S₁ e)
    (hw : ∀ a, (⟨e,z a⟩ : SS.PauliString n).wt ≤ 2) :
    restrictedCharacterMatrix z y *ᵥ (fun r => incidenceMonomial c d e (y r)) = 0 := by
  ext a
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S₀ S₁ c d hc hd hdist e (z a) (hw a)
  rw [offSum_eq_indexed S₀ S₁ c d e (z a) y hy hI] at h
  exact h

/-- The generic nonsingular restricted-character criterion, on arbitrary
numbers of physical qubits and actual amplitude products. -/
theorem monomials_zero_of_det_ne_zero (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.State n ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ x, x ∉ S₁ → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3)
    (e : SS.BitString n) (z y : Fin N → SS.BitString n)
    (hy : Function.Injective y)
    (hI : Finset.univ.image y = incidenceSet S₀ S₁ e)
    (hw : ∀ a, (⟨e,z a⟩ : SS.PauliString n).wt ≤ 2)
    (hdet : (restrictedCharacterMatrix z y).det ≠ 0) :
    ∀ r, incidenceMonomial c d e (y r) = 0 := by
  have hrow := restricted_matrix_times_monomials S₀ S₁ c d hc hd hdist e z y hy hI hw
  have hu : IsUnit (restrictedCharacterMatrix z y) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hz : (fun r => incidenceMonomial c d e (y r)) = 0 :=
    Matrix.mulVec_injective_of_isUnit hu (by simpa using hrow)
  exact fun r => congrFun hz r

theorem normSq_incidenceMonomial (c d : SS.State n ℂ) (e y : SS.BitString n) :
    Complex.normSq (incidenceMonomial c d e y) =
      Complex.normSq (c (SS.bxor y e)) * Complex.normSq (d y) := by
  simp [incidenceMonomial, Complex.normSq_mul]

/-- One incidence with positive product of endpoint probabilities contradicts
the full-rank physical cross-KL system. -/
theorem not_hasDistance_of_positive_incidence (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.State n ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ x, x ∉ S₁ → d x = 0)
    (e : SS.BitString n) (z y : Fin N → SS.BitString n)
    (hy : Function.Injective y)
    (hI : Finset.univ.image y = incidenceSet S₀ S₁ e)
    (hw : ∀ a, (⟨e,z a⟩ : SS.PauliString n).wt ≤ 2)
    (hdet : (restrictedCharacterMatrix z y).det ≠ 0)
    (r : Fin N)
    (hp : 0 < Complex.normSq (c (SS.bxor (y r) e)) * Complex.normSq (d (y r))) :
    ¬ SS.HasDistance ![c,d] 3 := by
  intro hdist
  have hz := monomials_zero_of_det_ne_zero S₀ S₁ c d hc hd hdist e z y hy hI hw hdet r
  have hn := normSq_incidenceMonomial c d e (y r)
  rw [hz, Complex.normSq_zero] at hn
  linarith

/-- Dressing a one-bit flip by one further coordinate is always low-weight. -/
theorem wt_single_flip_single_dressing (i j : Fin n) :
    (⟨SS.stdBasis i, SS.stdBasis j⟩ : SS.PauliString n).wt ≤ 2 := by
  classical
  apply (SixQubit.wt_le_of_support _ ({i,j} : Finset (Fin n)) ?_).trans
    ((Finset.card_insert_le _ _).trans (by simp))
  intro k hk
  rcases hk with hk | hk
  · simpa [SS.stdBasis] using Or.inl (show k = i by simpa [SS.stdBasis] using hk)
  · simpa [SS.stdBasis] using Or.inr (show k = j by simpa [SS.stdBasis] using hk)

/-- The `Y_i Z_j` row is also a genuine weight-at-most-two Pauli. -/
theorem wt_single_flip_pair_dressing (i j : Fin n) :
    (⟨SS.stdBasis i, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩ : SS.PauliString n).wt ≤ 2 := by
  classical
  apply (SixQubit.wt_le_of_support _ ({i,j} : Finset (Fin n)) ?_).trans
    ((Finset.card_insert_le _ _).trans (by simp))
  intro k hk
  by_cases hki : k = i
  · simp [hki]
  by_cases hkj : k = j
  · simp [hkj]
  rcases hk with hk | hk
  · change SS.stdBasis i k = true at hk
    rw [SS.stdBasis_apply_ne hki] at hk
    contradiction
  · change SS.bxor (SS.stdBasis i) (SS.stdBasis j) k = true at hk
    rw [SS.bxor_apply, SS.stdBasis_apply_ne hki, SS.stdBasis_apply_ne hkj] at hk
    contradiction

theorem wt_single_flip_zero_dressing (i : Fin n) :
    (⟨SS.stdBasis i, fun _ => false⟩ : SS.PauliString n).wt ≤ 2 := by
  simpa using wt_single_flip_pair_dressing i i

end
end MainTheory.FlipCharacter
