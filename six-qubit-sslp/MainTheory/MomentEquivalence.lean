import SixQubit.CodeBridge

/-!
# `eq:LP-first` and `eq:LP-second` are equivalences, not just consequences

Subsection II.F sets up the exact Knill--Laflamme completion inside a fixed
SSLP sector, and says of the moment system

> Equality of the diagonal compressions of `Z_i` and `Z_i Z_j` **is equivalent
> to** `eq:LP-normalization`--`eq:LP-positive`.

The repository proved one direction: `SixQubit.CodeBridge.occOn_eq_of_hasDistance`
and `occ2On_eq_of_hasDistance` derive equality of the first and second binary
moments from distance three.  That is the direction the no-go arguments need --
an infeasible moment polytope rules a sector out -- and it is all that was
stated.

The converse direction is what makes the linear program a faithful
*reformulation* rather than a necessary condition, and it is what
`thm:sslp-completeness` leans on when it says solving the system exactly
produces no false positives.  It is not deep: `charOn_stdBasis` and
`charOn_stdBasis_pair` are exact changes of basis, so once the masses are one
the character equalities and the moment equalities are the same statements.
This file records that.
-/

namespace MainTheory.MomentEquivalence

open SixQubit

variable {n : ℕ}

/-- **`eq:LP-first` as an equivalence.**

With both masses one, equality of the `Z_i` diagonal compressions and equality
of the first binary moments are the same condition. -/
theorem charOn_stdBasis_eq_iff (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.BitString n → ℂ)
    (hm0 : massOn S₀ c = 1) (hm1 : massOn S₁ d = 1) (i : Fin n) :
    charOn S₀ c (SS.stdBasis i) = charOn S₁ d (SS.stdBasis i)
      ↔ occOn S₀ c i = occOn S₁ d i := by
  rw [charOn_stdBasis, charOn_stdBasis, hm0, hm1]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`eq:LP-second` as an equivalence.**

Given the masses and the first moments, equality of the `Z_i Z_j` diagonal
compressions and equality of the second binary moments are the same
condition. -/
theorem charOn_stdBasis_pair_eq_iff (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.BitString n → ℂ)
    (hm0 : massOn S₀ c = 1) (hm1 : massOn S₁ d = 1) (i j : Fin n)
    (hi : occOn S₀ c i = occOn S₁ d i)
    (hj : occOn S₀ c j = occOn S₁ d j) :
    charOn S₀ c (SS.bxor (SS.stdBasis i) (SS.stdBasis j))
        = charOn S₁ d (SS.bxor (SS.stdBasis i) (SS.stdBasis j))
      ↔ occ2On S₀ c i j = occ2On S₁ d i j := by
  rw [charOn_stdBasis_pair, charOn_stdBasis_pair, hm0, hm1, hi, hj]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`eq:LP-normalization` and `eq:LP-positive`.**

The remaining two clauses of the moment system hold for any normalized
amplitude vector: the weights are a probability distribution on the fibre.
Stated so that the linear program's feasible region is exhibited as containing
exactly the codes, not merely as a relaxation. -/
theorem lp_normalization_and_positivity (S : Finset (SS.BitString n))
    (c : SS.BitString n → ℂ) (hc : ∀ x, x ∉ S → c x = 0)
    (hn : SS.innerC c c = 1) :
    massOn S c = 1 ∧ ∀ x, 0 ≤ Complex.normSq (c x) :=
  ⟨massOn_eq_one S c hc hn, fun x => Complex.normSq_nonneg (c x)⟩

end MainTheory.MomentEquivalence
