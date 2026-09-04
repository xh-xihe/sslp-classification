import MainTheory.D3BoundedNormalForm

/-!
# The `beta_n` route does not change the projective logical order

`D3BoundedNormalForm.boundedGenerator` replaces a code's finite generator by a
sparse one whose modulus meets the sharp six-qubit cutoff.  The file says in
prose that "the two generate the same group and have the same order", and
nothing states it.  That sentence is what
`thm:d3-sslp-classification`'s generator clause rests on: the normal form the
bounded route produces is only the paper's `C_m` if `m` survives the route.

It does, and the analytic content was already proved and unused.
`FlipSemanticTransport.flip_ratio` says the local `X` string contributes only a
common scalar, so it leaves the logical eigenvalue ratio alone -- and that
ratio is exactly what pins the order, through
`TwoFiberCertificate.ratio_order` on one side and
`normalizedProjectiveOrder` on the other.  `flip_ratio` had no call site
anywhere in the repository.
-/

namespace MainTheory.BoundedGeneratorOrder

open MainTheory
open MainTheory.D3BoundedNormalForm
open MainTheory.D3AutomaticBoundedGenerator

variable {n q : ℕ}

/-- **The bounded generator has the same projective logical order.**

Any two-fibre certificate of the bounded generator carries the same
`logicalOrder` as the certificate it was built from. -/
theorem logicalOrder_boundedGenerator [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G)
    [NeZero (frameFreshSparsePhase T).data.order]
    (Tb : RankTwoGlobal.TwoFiberCertificate (boundedGenerator T)) :
    Tb.logicalOrder = T.logicalOrder := by
  have hratio :
      (boundedGenerator T).eigenvalue 1 / (boundedGenerator T).eigenvalue 0
        = (automaticFreshGenerator T).eigenvalue 1
            / (automaticFreshGenerator T).eigenvalue 0 :=
    MainTheory.FlipSemanticTransport.flip_ratio (C' := C)
      (automaticFreshGenerator T) T.x0
      (codeSpan_shift_of_span T _ (automaticFreshGenerator T).span_eq)
  have hchi :
      (boundedGenerator T).eigenvalue 1 / (boundedGenerator T).eigenvalue 0
        = Cyclic.chi G.zeta (((q / T.logicalOrder : ℕ) : ZMod q)) := by
    rw [hratio]
    show (normalizedEigenvalue T) 1 / (normalizedEigenvalue T) 0 = _
    simp [normalizedEigenvalue]
  have hiff : ∀ k : ℕ, Tb.logicalOrder ∣ k ↔ T.logicalOrder ∣ k := by
    intro k
    rw [Tb.logicalOrder_eq, ← Tb.ratio_order k, hchi,
      T.normalizedProjectiveOrder k]
  exact Nat.dvd_antisymm ((hiff _).2 dvd_rfl) ((hiff _).1 dvd_rfl)

end MainTheory.BoundedGeneratorOrder
