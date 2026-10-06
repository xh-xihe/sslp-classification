import Mathlib
import SS.HilbertKL
import SixQubit.CodeBridge
import MainTheory.PhaseSector

/-!
# Phase-sector probabilities and their common first moment

`MainTheory.PhaseSector` proves the support/fibre part of Lemma 2.3 of
`documents/20260822/main.tex`, conditional on a logical eigenbasis.  The lemma
also has a genuinely code-theoretic clause which was missing there: when the
code detects every one-qubit `Z`, the probability distributions carried by all
logical eigensectors have the same first moments.

This file proves that clause for an arbitrary finite logical dimension.  It
also records the two facts needed by the coloured rationalisation argument:
the sector weights are nonnegative and normalised, and every logical word has
nonempty support.  No spectral theorem is assumed here; as in
`PhaseSector.lean`, the eigenbasis is supplied as data.  Producing it from a
code-preserving unitary is a separate operator-theoretic obligation.
-/

namespace MainTheory.PhaseSectorMoments

open SS
open SixQubit

noncomputable section

variable {n K : ℕ}

/-- The Born probability of a computational basis string in a logical word. -/
def probability (psi : Fin K → SS.State n ℂ) (k : Fin K)
    (x : SS.BitString n) : ℝ :=
  Complex.normSq (psi k x)

/-- The probability that physical coordinate `j` is occupied in logical word
`k`.  This is the `j`-th component of the sector mean in Lemma 2.3. -/
def mean (psi : Fin K → SS.State n ℂ) (k : Fin K) (j : Fin n) : ℝ :=
  occOn Finset.univ (psi k) j

theorem probability_nonneg (psi : Fin K → SS.State n ℂ)
    (k : Fin K) (x : SS.BitString n) :
    0 ≤ probability psi k x :=
  Complex.normSq_nonneg _

/-- A normalised logical word gives a probability distribution on the Boolean
cube. -/
theorem probability_sum_eq_one (psi : Fin K → SS.State n ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1) (k : Fin K) :
    ∑ x, probability psi k x = 1 := by
  have hm := massOn_eq_one (Finset.univ : Finset (SS.BitString n)) (psi k)
    (by simp) (hnorm k)
  simpa [probability, massOn] using hm

/-- Every normalised word has a supported basis string.  This rules out an
empty phase sector without making a classical choice of a base point. -/
theorem exists_mem_support (psi : Fin K → SS.State n ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1) (k : Fin K) :
    ∃ x, psi k x ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : psi k = 0 := by
    funext x
    exact h x
  have := hnorm k
  rw [hz] at this
  simp [SS.innerC] at this

/-- A nonzero amplitude has strictly positive Born weight. -/
theorem probability_pos_of_ne_zero (psi : Fin K → SS.State n ℂ)
    (k : Fin K) (x : SS.BitString n) (hx : psi k x ≠ 0) :
    0 < probability psi k x := by
  exact Complex.normSq_pos.mpr hx

private theorem pureZ_character_eq
    (psi : Fin K → SS.State n ℂ) (hdet : SS.Detects psi 1)
    (k l : Fin K) (j : Fin n) :
    charOn Finset.univ (psi k) (SS.stdBasis j) =
      charOn Finset.univ (psi l) (SS.stdBasis j) := by
  let P : SS.PauliString n :=
    ⟨(fun _ => false), SS.stdBasis j⟩
  have hwt : P.wt ≤ 1 := by
    simpa [P] using (wt_pureZ_single j)
  obtain ⟨c, hc⟩ := hdet P hwt
  have hkk := hc k k
  have hll := hc l l
  rw [if_pos rfl] at hkk hll
  have hkchar := innerC_pureZ_eq_charOn
    (Finset.univ : Finset (SS.BitString n)) (psi k) (by simp)
    (SS.stdBasis j)
  have hlchar := innerC_pureZ_eq_charOn
    (Finset.univ : Finset (SS.BitString n)) (psi l) (by simp)
    (SS.stdBasis j)
  change SS.innerC (psi k) (SS.pauliAct P (psi k)) = c at hkk
  change SS.innerC (psi l) (SS.pauliAct P (psi l)) = c at hll
  change SS.innerC (psi k)
      (SS.pauliAct ⟨(fun _ => false), SS.stdBasis j⟩ (psi k)) =
        ((charOn Finset.univ (psi k) (SS.stdBasis j) : ℝ) : ℂ) at hkchar
  change SS.innerC (psi l)
      (SS.pauliAct ⟨(fun _ => false), SS.stdBasis j⟩ (psi l)) =
        ((charOn Finset.univ (psi l) (SS.stdBasis j) : ℝ) : ℂ) at hlchar
  have hcast :
      ((charOn Finset.univ (psi k) (SS.stdBasis j) : ℝ) : ℂ) =
        ((charOn Finset.univ (psi l) (SS.stdBasis j) : ℝ) : ℂ) := by
    rw [← hkchar, ← hlchar, hkk, hll]
  exact_mod_cast hcast

/-- **The common-first-moment clause of Lemma 2.3.**

Detection of the one-qubit `Z_j` makes its Knill--Laflamme diagonal scalar
independent of the logical eigensector.  Since that character is
`1 - 2 * mean_j` for a normalised word, all sector means agree. -/
theorem mean_eq_of_detects_one
    (psi : Fin K → SS.State n ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hdet : SS.Detects psi 1) (k l : Fin K) (j : Fin n) :
    mean psi k j = mean psi l j := by
  have hmassk := massOn_eq_one (Finset.univ : Finset (SS.BitString n))
    (psi k) (by simp) (hnorm k)
  have hmassl := massOn_eq_one (Finset.univ : Finset (SS.BitString n))
    (psi l) (by simp) (hnorm l)
  have hchar := pureZ_character_eq psi hdet k l j
  rw [charOn_stdBasis, charOn_stdBasis, hmassk, hmassl] at hchar
  simpa [mean] using (show occOn Finset.univ (psi k) j =
      occOn Finset.univ (psi l) j by linarith)

/-- Vector form: there is one mean vector shared by every logical sector. -/
theorem exists_common_mean
    (psi : Fin K → SS.State n ℂ) [Nonempty (Fin K)]
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hdet : SS.Detects psi 1) :
    ∃ mu : Fin n → ℝ, ∀ k j, mean psi k j = mu j := by
  classical
  let k0 : Fin K := Classical.choice inferInstance
  refine ⟨mean psi k0, ?_⟩
  intro k j
  exact mean_eq_of_detects_one psi hnorm hdet k k0 j

/-- The probability/common-mean package used by the coloured augmented system.
It is deliberately stated independently of a particular choice of eigenvalues:
the moment conclusion follows from error detection, while the phase-sector
support conclusion lives in `MainTheory.PhaseSector`. -/
theorem probability_package
    (psi : Fin K → SS.State n ℂ) [Nonempty (Fin K)]
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hdet : SS.Detects psi 1) :
    (∀ k x, 0 ≤ probability psi k x) ∧
    (∀ k, ∑ x, probability psi k x = 1) ∧
    (∀ k, ∃ x, psi k x ≠ 0) ∧
    ∃ mu : Fin n → ℝ, ∀ k j, mean psi k j = mu j := by
  refine ⟨probability_nonneg psi, probability_sum_eq_one psi hnorm,
    exists_mem_support psi hnorm, exists_common_mean psi hnorm hdet⟩

end

end MainTheory.PhaseSectorMoments
