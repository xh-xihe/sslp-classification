import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# The odd triangle of reciprocal flip relations

Several no-go orbits reduce to the following configuration.  Three indices
`a, b, c` carry bottom amplitudes `u` and top amplitudes `v`, and each of the
three pairs satisfies a *reciprocal* flip relation

```
u_a * v_b + u_b * v_a = 0 ,
u_a * v_c + u_c * v_a = 0 ,
u_b * v_c + u_c * v_b = 0 .
```

Written with the phase ratios `rho_i = v_i / conj(u_i)` this says
`rho_i + rho_j = 0` for all three pairs, whose coefficient matrix has
determinant `-2`; the three unit-modulus numbers would all have to vanish.

The formalization below avoids introducing `rho` at all, and therefore needs
no division and no nonvanishing side conditions on the way in.  Eliminating
between the three relations gives, identically,

```
v_c * (1) - v_a * (3) - v_b * (2)  =  -2 * u_c * v_a * v_b ,
```

so `u_c * v_a * v_b = 0` outright.  Since the moment system makes each of the
three probabilities positive, all six amplitudes are nonzero and this is a
contradiction.

Everything here is ordinary commutative algebra over `ℂ`; the module mentions
no bit strings.  `native_decide` is not used.
-/

namespace SixQubit.Triangle

open scoped ComplexConjugate

noncomputable section

/-- The elimination identity behind the odd triangle: the three reciprocal
relations force the single product `u_c * v_a * v_b` to vanish. -/
theorem prod_eq_zero {ua ub uc va vb vc : ℂ}
    (h1 : ua * vb + ub * va = 0)
    (h2 : ua * vc + uc * va = 0)
    (h3 : ub * vc + uc * vb = 0) :
    uc * va * vb = 0 := by
  linear_combination (-vc / 2) * h1 + (vb / 2) * h2 + (va / 2) * h3

/-- **The odd triangle is contradictory.**  Three reciprocal relations on
three indices whose amplitudes are all nonzero cannot hold simultaneously. -/
theorem contradiction {ua ub uc va vb vc : ℂ}
    (h1 : ua * vb + ub * va = 0)
    (h2 : ua * vc + uc * va = 0)
    (h3 : ub * vc + uc * vb = 0)
    (hc : uc ≠ 0) (ha : va ≠ 0) (hb : vb ≠ 0) : False := by
  have key := prod_eq_zero h1 h2 h3
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hc h'
    · exact ha h'
  · exact hb h

/-- The form in which the orbits actually meet it: the six amplitudes are
given as `star (c x)` and `d y`, and nonvanishing comes from positive
probabilities. -/
theorem contradiction_of_normSq {ca cb cc da db dc : ℂ}
    (h1 : star ca * db + star cb * da = 0)
    (h2 : star ca * dc + star cc * da = 0)
    (h3 : star cb * dc + star cc * db = 0)
    (hcc : 0 < Complex.normSq cc)
    (hda : 0 < Complex.normSq da)
    (hdb : 0 < Complex.normSq db) : False := by
  refine contradiction h1 h2 h3 ?_ ?_ ?_
  · intro h
    have : cc = 0 := by simpa using congrArg star h
    rw [this] at hcc; simp at hcc
  · intro h; rw [h] at hda; simp at hda
  · intro h; rw [h] at hdb; simp at hdb

/-! ## The mixed pair triangle

A second, genuinely different configuration, met by orbits 49 and 51.  Three
vectors of `C^2`

```
x = (a, b) ,    y = (c, d) ,    w = (e, f)
```

are pairwise orthogonal for the symmetric bilinear form `B(x,y) = x0*y1 + x1*y0`
whose matrix is the exchange matrix, i.e.

```
B(x,w) = a*f + b*e = 0 ,
B(y,w) = c*f + d*e = 0 ,
B(x,y) = a*d + b*c = 0 .
```

`B` is nondegenerate on `C^2`, so the three orthogonality conditions force the
three vectors into a single isotropic line; concretely, eliminating between the
three relations gives, identically,

```
(c/2)*(1) - (a/2)*(2) + (e/2)*(3)  =  e*b*c ,
```

so `e*b*c = 0` outright.  As before this is a division-free elimination: no
phase ratio is introduced, and no nonvanishing side condition is needed on the
way in.
-/

/-- The elimination identity behind the mixed pair triangle: the three
orthogonality relations force the single product `e*b*c` to vanish. -/
theorem pair_prod_eq_zero {a b c d e f : ℂ}
    (h1 : a * f + b * e = 0)
    (h2 : c * f + d * e = 0)
    (h3 : a * d + b * c = 0) :
    e * b * c = 0 := by
  linear_combination (c / 2) * h1 - (a / 2) * h2 + (e / 2) * h3

/-- **The mixed pair triangle is contradictory** when the three coordinates
`e`, `b`, `c` are nonzero. -/
theorem pair_contradiction {a b c d e f : ℂ}
    (h1 : a * f + b * e = 0)
    (h2 : c * f + d * e = 0)
    (h3 : a * d + b * c = 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) : False := by
  have key := pair_prod_eq_zero h1 h2 h3
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact he h'
    · exact hb h'
  · exact hc h

/-- The form in which orbits 49 and 51 meet it: nonvanishing comes from
positive probabilities. -/
theorem pair_contradiction_of_normSq {a b c d e f : ℂ}
    (h1 : a * f + b * e = 0)
    (h2 : c * f + d * e = 0)
    (h3 : a * d + b * c = 0)
    (hb : 0 < Complex.normSq b)
    (hc : 0 < Complex.normSq c)
    (he : 0 < Complex.normSq e) : False :=
  pair_contradiction h1 h2 h3 (Complex.normSq_pos.mp hb) (Complex.normSq_pos.mp hc)
    (Complex.normSq_pos.mp he)

end

end SixQubit.Triangle
