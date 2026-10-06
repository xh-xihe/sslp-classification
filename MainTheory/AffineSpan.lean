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

Put together with `Covariance.span_eq_of_cov_eq`, this gives Lemma 5.2's
conclusion outright: the two supports have the same centred span, which is the
subspace `V` of `eq:V-r`, and `aff(T_k) = mu + V` follows since `mu` is a convex
combination of each support.  An earlier draft left that last step open and
called it bookkeeping; it is short, but it is what turns the covariance
computation into the statement the lemma makes, so it is proved.
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
