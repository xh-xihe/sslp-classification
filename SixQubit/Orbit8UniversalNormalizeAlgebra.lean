import SixQubit.Orbit8UniversalHafnianSymmetry

/-! Division-safe algebra used to normalize a nonzero five-star graph. -/

namespace SixQubit.Orbit8Universal

noncomputable section

lemma normalize_triangle
    (sa sb sc eab eac ebc : ℂ)
    (hsa : sa ≠ 0) (hsb : sb ≠ 0) (hsc : sc ≠ 0)
    (h : sa * ebc + sb * eac + sc * eab = 0) :
    eab / (sa*sb) + eac / (sa*sc) + ebc / (sb*sc) = 0 := by
  field_simp [hsa, hsb, hsc]
  linear_combination h

lemma normalize_quad
    (sa sb sc sd eab eac ead ebc ebd ecd : ℂ)
    (hsa : sa ≠ 0) (hsb : sb ≠ 0) (hsc : sc ≠ 0) (hsd : sd ≠ 0)
    (h : eab*ecd + eac*ebd + ead*ebc = 0) :
    (eab/(sa*sb))*(ecd/(sc*sd)) +
      (eac/(sa*sc))*(ebd/(sb*sd)) +
      (ead/(sa*sd))*(ebc/(sb*sc)) = 0 := by
  field_simp [hsa, hsb, hsc, hsd]
  linear_combination h

/-- Raw hafnian equations around a nonzero star contradict three active
vertices.  The ordering of the five non-anchor vertices is arbitrary. -/
theorem raw_support3_impossible
    (s1 s2 s3 s4 s5 : ℂ)
    (e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 : ℂ)
    (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0) (hs3 : s3 ≠ 0)
    (hs4 : s4 ≠ 0) (hs5 : s5 ≠ 0)
    (he13 : e13 ≠ 0) (he14 : e14 ≠ 0)
    (t134 : s1*e34 + s3*e14 + s4*e13 = 0)
    (t135 : s1*e35 + s3*e15 + s5*e13 = 0)
    (t145 : s1*e45 + s4*e15 + s5*e14 = 0)
    (t234 : s2*e34 + s3*e24 + s4*e23 = 0)
    (t235 : s2*e35 + s3*e25 + s5*e23 = 0)
    (t245 : s2*e45 + s4*e25 + s5*e24 = 0)
    (t345 : s3*e45 + s4*e35 + s5*e34 = 0)
    (q1345 : e13*e45 + e14*e35 + e15*e34 = 0)
    (q1235 : e12*e35 + e13*e25 + e15*e23 = 0)
    (q1245 : e12*e45 + e14*e25 + e15*e24 = 0) : False := by
  let x12 := e12/(s1*s2)
  let x13 := e13/(s1*s3)
  let x14 := e14/(s1*s4)
  let x15 := e15/(s1*s5)
  let x23 := e23/(s2*s3)
  let x24 := e24/(s2*s4)
  let x25 := e25/(s2*s5)
  let x34 := e34/(s3*s4)
  let x35 := e35/(s3*s5)
  let x45 := e45/(s4*s5)
  apply normalized_support3_impossible x12 x13 x14 x15 x23 x24 x25 x34 x35 x45
  · exact div_ne_zero he13 (mul_ne_zero hs1 hs3)
  · exact div_ne_zero he14 (mul_ne_zero hs1 hs4)
  · exact normalize_triangle s1 s3 s4 e13 e14 e34 hs1 hs3 hs4 t134
  · exact normalize_triangle s1 s3 s5 e13 e15 e35 hs1 hs3 hs5 t135
  · exact normalize_triangle s1 s4 s5 e14 e15 e45 hs1 hs4 hs5 t145
  · exact normalize_triangle s2 s3 s4 e23 e24 e34 hs2 hs3 hs4 t234
  · exact normalize_triangle s2 s3 s5 e23 e25 e35 hs2 hs3 hs5 t235
  · exact normalize_triangle s2 s4 s5 e24 e25 e45 hs2 hs4 hs5 t245
  · exact normalize_triangle s3 s4 s5 e34 e35 e45 hs3 hs4 hs5 t345
  · exact normalize_quad s1 s3 s4 s5 e13 e14 e15 e34 e35 e45
      hs1 hs3 hs4 hs5 q1345
  · exact normalize_quad s1 s2 s3 s5 e12 e13 e15 e23 e25 e35
      hs1 hs2 hs3 hs5 q1235
  · exact normalize_quad s1 s2 s4 s5 e12 e14 e15 e24 e25 e45
      hs1 hs2 hs4 hs5 q1245

end

end SixQubit.Orbit8Universal
