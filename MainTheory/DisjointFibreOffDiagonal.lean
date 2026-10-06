import SixQubit.CodeBridge

/-!
# Disjoint fibres kill every diagonal Pauli's off-diagonal element

The sentence that licenses `eq:LP-normalization`--`eq:LP-positive` as the
*complete* diagonal reduction is "The two fibers are disjoint, so off-diagonal
matrix elements of every diagonal Pauli vanish automatically".  Without it the
displayed linear programme would be only the diagonal half of the diagonal
Knill--Laflamme system, and the off-diagonal half would be an extra obligation.

What the package had was the identity Pauli alone:
`SixQubit.innerC_eq_zero_of_disjoint` concludes `innerC c d = 0` from disjoint
supports.  The general statement is one line further out.
`SixQubit.innerC_eq_offSumOn` writes the matrix element as
`i^{#Y} * offSumOn S_0 S_1 c d P.x P.z`, and `offSumOn` sums over
`S_1.filter (fun y => bxor y P.x in S_0)`.  A *diagonal* Pauli is one with no
`X` part, so `P.x = 0`, the shift is the identity, and the index set is
`S_1 cap S_0` -- empty exactly when the fibres are disjoint.

So the vanishing is a property of the *supports*, needing neither the
Knill--Laflamme equations nor the amplitudes, which is what "automatically" in
the paper's sentence means.
-/

namespace MainTheory.DisjointFibreOffDiagonal

open SixQubit

variable {n : ℕ}

/-- With no `X` part the off-diagonal support sum runs over the intersection of
the two fibres, hence vanishes when they are disjoint. -/
theorem offSumOn_zero_of_disjoint (S₀ S₁ : Finset (SS.BitString n))
    (hdisj : Disjoint S₀ S₁) (c d : SS.BitString n → ℂ)
    (z : SS.BitString n) :
    offSumOn S₀ S₁ c d (fun _ => false) z = 0 := by
  classical
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Finset.mem_filter, SS.bxor_zero] at hy
  exact absurd hy.2 (Finset.disjoint_right.1 hdisj hy.1)

/-- **"The two fibers are disjoint, so off-diagonal matrix elements of every
diagonal Pauli vanish automatically."**

A diagonal Pauli is one whose `X` part is trivial.  No hypothesis about
distance, orthonormality or the amplitudes is used. -/
theorem innerC_pauliAct_eq_zero_of_disjoint
    (S₀ S₁ : Finset (SS.BitString n)) (hdisj : Disjoint S₀ S₁)
    (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0)
    (P : SS.PauliString n) (hP : P.x = fun _ => false) :
    SS.innerC c (SS.pauliAct P d) = 0 := by
  rw [innerC_eq_offSumOn S₀ S₁ c d hc hd P, hP,
    offSumOn_zero_of_disjoint S₀ S₁ hdisj c d P.z, mul_zero]

end MainTheory.DisjointFibreOffDiagonal
