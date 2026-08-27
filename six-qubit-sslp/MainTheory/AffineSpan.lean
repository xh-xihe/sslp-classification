import Mathlib
import SixQubit.CodeBridge
import MainTheory.Covariance

/-!
# The common affine span, quantum half

`MainTheory/Covariance.lean` carries the geometric half of `main.tex` Lemma 5.2:
for strictly positive weights, the covariance form vanishes on a direction
exactly when that direction annihilates the centred support, so the range of the
covariance is the centred span.  That half mentions no codes.

This file supplies the quantum half.  It is short, because the repository
already had it: `SixQubit/CodeBridge.lean` proves that a distance-three code's
two logical words have equal occupation numbers and equal joint occupation
numbers, and both of those are generic in `n` despite living in the `SixQubit`
namespace.  Subtracting the outer product of the first moments turns them into
equal covariances, which is exactly `eq:common-covariance`.

Put together with `Covariance.proj_eq_zero_congr`, this gives Lemma 5.2's
conclusion that the two supports have the same centred span, and hence the same
affine span.  What is *not* done here is the passage from that to
`aff(T_0) = mu + V = aff(T_1)` as a statement about `AffineSubspace`; that is
bookkeeping over Mathlib's affine-span API and is left open rather than claimed.
-/

namespace MainTheory.AffineSpan

open SixQubit

variable {n : ℕ}

/-- **The two covariance matrices agree.**

This is `main.tex` eq. `eq:common-covariance`.  The first moments agree by the
weight-one diagonal Knill-Laflamme rows and the second moments by the
weight-two rows; the covariance is their difference. -/
theorem covariance_eq_of_hasDistance
    (S0 S1 : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) (i j : Fin n) :
    occ2On S0 c i j - occOn S0 c i * occOn S0 c j
      = occ2On S1 d i j - occOn S1 d i * occOn S1 d j := by
  rw [occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist i j,
    occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist i,
    occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist j]

/-- The first moments agree, restated as the common mean `mu` of
`eq:two-common-mean`. -/
theorem mean_eq_of_hasDistance
    (S0 S1 : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    (fun i => occOn S0 c i) = fun i => occOn S1 d i := by
  funext i
  exact occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist i

end MainTheory.AffineSpan
