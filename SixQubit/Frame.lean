import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Orthogonal frames in `ℂ²`

Several orbits carry a free qubit -- a zero-angle qubit, or an effective
repetition qubit -- so the amplitudes group into vectors in `ℂ²`.  When the
Knill--Laflamme rows isolate a complete set of inner products between a bottom
block and the matching top block, the two block frame operators

```
C = Σ cᵢ cᵢ† ,      D = Σ dⱼ dⱼ†
```

satisfy `C D = 0`, because every `cᵢ† dⱼ` vanishes.  The diagonal conditions on
the free qubit make the two frames equal, so `C² = 0`, and a positive
semidefinite matrix with `C² = 0` is zero.  That contradicts a positive block
mass.

The proof never builds a matrix.  It works with the entries

```
α = Σ ‖aᵢ‖² ,   β = Σ aᵢ conj bᵢ
```

of `C` directly, and the whole argument is the single identity

```
α α' + β conj β' = Σᵢⱼ aᵢ conj pⱼ (conj aᵢ pⱼ + conj bᵢ qⱼ) ,
```

which is `(C D)₀₀` written out.  With `C = D` the left side becomes
`α² + ‖β‖²`, a sum of two nonnegative reals, so both vanish.

`native_decide` is not used.
-/

namespace SixQubit.Frame

open scoped ComplexConjugate

noncomputable section

/-- `z * conj z` is the squared modulus. -/
theorem self_mul_star (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm]; exact SixQubit.star_mul_self z

/-- `(C D)₀₀ = 0` for a two-element bottom block and a two-element top block,
written out in coordinates. -/
theorem cd_entry {a1 a2 b1 b2 p1 p2 q1 q2 : ℂ}
    (o11 : star a1 * p1 + star b1 * q1 = 0)
    (o12 : star a1 * p2 + star b1 * q2 = 0)
    (o21 : star a2 * p1 + star b2 * q1 = 0)
    (o22 : star a2 * p2 + star b2 * q2 = 0) :
    (a1 * star a1 + a2 * star a2) * (p1 * star p1 + p2 * star p2)
      + (a1 * star b1 + a2 * star b2) * (q1 * star p1 + q2 * star p2) = 0 := by
  linear_combination (a1 * star p1) * o11 + (a1 * star p2) * o12
    + (a2 * star p1) * o21 + (a2 * star p2) * o22

/-- **The block frame vanishes.**  Four orthogonalities plus equality of the
two block frames force the whole bottom block to be zero. -/
theorem block_zero {a1 a2 b1 b2 p1 p2 q1 q2 : ℂ}
    (o11 : star a1 * p1 + star b1 * q1 = 0)
    (o12 : star a1 * p2 + star b1 * q2 = 0)
    (o21 : star a2 * p1 + star b2 * q1 = 0)
    (o22 : star a2 * p2 + star b2 * q2 = 0)
    (fA : Complex.normSq a1 + Complex.normSq a2
            = Complex.normSq p1 + Complex.normSq p2)
    (fC : a1 * star b1 + a2 * star b2 = p1 * star q1 + p2 * star q2) :
    Complex.normSq a1 + Complex.normSq a2 = 0 := by
  have key := cd_entry o11 o12 o21 o22
  have hstar : q1 * star p1 + q2 * star p2
      = star (a1 * star b1 + a2 * star b2) := by
    have hc := congrArg star fC
    simp only [star_add, star_mul', star_star] at hc
    simp only [star_add, star_mul', star_star]
    linear_combination -hc
  rw [hstar, self_mul_star a1, self_mul_star a2, self_mul_star p1,
    self_mul_star p2, self_mul_star (a1 * star b1 + a2 * star b2)] at key
  have hcast := congrArg (fun x : Real => (x : ℂ)) fA
  push_cast at hcast
  have hreal : (Complex.normSq a1 + Complex.normSq a2)
        * (Complex.normSq a1 + Complex.normSq a2)
      + Complex.normSq (a1 * star b1 + a2 * star b2) = 0 := by
    have hc : (((Complex.normSq a1 + Complex.normSq a2)
          * (Complex.normSq a1 + Complex.normSq a2)
        + Complex.normSq (a1 * star b1 + a2 * star b2) : Real) : ℂ) = 0 := by
      push_cast
      linear_combination key
        + ((Complex.normSq a1 : ℂ) + (Complex.normSq a2 : ℂ)) * hcast
    exact_mod_cast hc
  nlinarith [Complex.normSq_nonneg (a1 * star b1 + a2 * star b2),
    Complex.normSq_nonneg a1, Complex.normSq_nonneg a2]

end

end SixQubit.Frame
