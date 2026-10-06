import SixQubit.Orbit7PairRank
import SixQubit.Orbit7Gauge

/-!
# Orbit 7: rank transport back through the fixed gauge

The uniform presentation is obtained from the repository representative by
interchanging the two logical basis vectors and applying physical `X` on
qubits four and five.  The logical interchange does not change the code
projector.  Under partial trace, the `X` operators on traced-out qubits
disappear; on the retained active qubit they only permute its computational
basis.  Qubit zero is not flipped.

This file formalizes the resulting retained-basis permutation and its effect
on `Matrix.rank`.  It deliberately calls the matrix below the
*gauge-transported pair marginal*: the present development has no independent
definition of partial trace against which to prove, entry by entry, that this
matrix is the original-gauge `rho_{As}`.  Thus the theorem here is an exact
kernel statement about transport of the already formalized uniform
`pairMarginal`, without an additional unproved reduced-density assertion.
-/

namespace SixQubit.Orbit7Gauge

open SixQubit.CodeEquiv
open SixQubit.Orbit7Universal

noncomputable section

/-- Whether the fixed gauge flips active coordinate `s` (physical qubit
`s.succ`).  Exactly active coordinates three and four are flipped. -/
def retainedActiveFlip (s : Fin 5) : Bool := flip45 s.succ

theorem retainedActiveFlip_eq_true_iff (s : Fin 5) :
    retainedActiveFlip s = true ↔ s = 3 ∨ s = 4 := by
  fin_cases s <;> decide

/-- The basis permutation on the retained pair `(A,s)`.  The zero-angle
qubit `A` is unchanged, while `s` is toggled precisely when the fixed physical
gauge contains `X_s`. -/
def retainedPairEquiv (s : Fin 5) :
    (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2) :=
  Equiv.prodCongr (Equiv.refl _) (swapEquiv (retainedActiveFlip s))

@[simp] theorem retainedPairEquiv_apply (s : Fin 5) (a b : Fin 2) :
    retainedPairEquiv s (a, b) =
      (a, swapIdx (retainedActiveFlip s) b) := rfl

/-- The uniform pair marginal, explicitly relabelled by the local `X` basis
permutation that remains on the retained subsystem after undoing the fixed
gauge.  This name records the semantic boundary explained in the module
docstring: no separate partial-trace definition is silently identified with
this matrix. -/
def gaugeTransportedPairMarginal
    (c d : SS.State 6 ℂ) (s : Fin 5) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (pairMarginal (bottom d) (top c) s).submatrix
    (retainedPairEquiv s) (retainedPairEquiv s)

@[simp] theorem gaugeTransportedPairMarginal_apply
    (c d : SS.State 6 ℂ) (s : Fin 5) (a b a' b' : Fin 2) :
    gaugeTransportedPairMarginal c d s (a, b) (a', b') =
      pairMarginal (bottom d) (top c) s
        (a, swapIdx (retainedActiveFlip s) b)
        (a', swapIdx (retainedActiveFlip s) b') := rfl

/-- Rank two at `s` for the pair marginal transported back to the original
gauge. -/
def OriginalPairRankTwoAt
    (c d : SS.State 6 ℂ) (s : Fin 5) : Prop :=
  (gaugeTransportedPairMarginal c d s).rank = 2

/-- The original-gauge structural rank assertion, phrased using the exact
gauge-transported marginal above. -/
def OriginalHasPairRankTwo (c d : SS.State 6 ℂ) : Prop :=
  ∃ s : Fin 5, OriginalPairRankTwoAt c d s

/-- Simultaneous row and column relabelling by the retained local `X`
permutation preserves the literal `Matrix.rank`. -/
theorem gaugeTransportedPairMarginal_rank
    (c d : SS.State 6 ℂ) (s : Fin 5) :
    (gaugeTransportedPairMarginal c d s).rank =
      (pairMarginal (bottom d) (top c) s).rank := by
  unfold gaugeTransportedPairMarginal
  exact Matrix.rank_submatrix _ _ _

/-- A rank-two pair in the uniform gauge transports, by an explicit retained
basis equivalence, to a rank-two pair in the original gauge.  Equality of
ranks is proved by `Matrix.rank_submatrix`; it is not an assumed invariance. -/
theorem originalHasPairRankTwo_of_uniform
    (c d : SS.State 6 ℂ)
    (h : HasPairRankTwo (bottom d) (top c)) :
    OriginalHasPairRankTwo c d := by
  rcases h with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  unfold PairRankTwoAt at hs
  unfold OriginalPairRankTwoAt
  rw [gaugeTransportedPairMarginal_rank]
  exact hs

end

end SixQubit.Orbit7Gauge
