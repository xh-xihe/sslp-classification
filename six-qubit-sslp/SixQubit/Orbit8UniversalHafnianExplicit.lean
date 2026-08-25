import SixQubit.Orbit8UniversalNormalizeAlgebra

/-! The fifteen complementary hafnians in canonical edge coordinates. -/

namespace SixQubit.Orbit8Universal

open SixQubit
noncomputable section

set_option maxRecDepth 20000

macro "expand_haf" : tactic => `(tactic|
  simp [compHaf, hafVia_decode, spare, awayPairs_zero, awayPairs_one,
    awayPairs_two, awayPairs_three, awayPairs_four, awayPairs_five,
    touches, topRecip, edgeDecode, edgeState, pairMask, SS.stdBasis,
    SS.complement, SS.bxor] <;> ring)

@[simp] theorem compHaf_01 (d : SS.BitString 6 → ℂ) :
    compHaf d 0 1 = v d 2 3*v d 4 5 + v d 2 4*v d 3 5 + v d 2 5*v d 3 4 := by
  expand_haf
@[simp] theorem compHaf_02 (d : SS.BitString 6 → ℂ) :
    compHaf d 0 2 = v d 1 3*v d 4 5 + v d 1 4*v d 3 5 + v d 1 5*v d 3 4 := by
  expand_haf
@[simp] theorem compHaf_03 (d : SS.BitString 6 → ℂ) :
    compHaf d 0 3 = v d 1 2*v d 4 5 + v d 1 4*v d 2 5 + v d 1 5*v d 2 4 := by
  expand_haf
@[simp] theorem compHaf_04 (d : SS.BitString 6 → ℂ) :
    compHaf d 0 4 = v d 1 2*v d 3 5 + v d 1 3*v d 2 5 + v d 1 5*v d 2 3 := by
  expand_haf
@[simp] theorem compHaf_05 (d : SS.BitString 6 → ℂ) :
    compHaf d 0 5 = v d 1 2*v d 3 4 + v d 1 3*v d 2 4 + v d 1 4*v d 2 3 := by
  expand_haf

@[simp] theorem compHaf_12 (d : SS.BitString 6 → ℂ) :
    compHaf d 1 2 = v d 0 3*v d 4 5 + v d 0 4*v d 3 5 + v d 0 5*v d 3 4 := by
  expand_haf
@[simp] theorem compHaf_13 (d : SS.BitString 6 → ℂ) :
    compHaf d 1 3 = v d 0 2*v d 4 5 + v d 0 4*v d 2 5 + v d 0 5*v d 2 4 := by
  expand_haf
@[simp] theorem compHaf_14 (d : SS.BitString 6 → ℂ) :
    compHaf d 1 4 = v d 0 2*v d 3 5 + v d 0 3*v d 2 5 + v d 0 5*v d 2 3 := by
  expand_haf
@[simp] theorem compHaf_15 (d : SS.BitString 6 → ℂ) :
    compHaf d 1 5 = v d 0 2*v d 3 4 + v d 0 3*v d 2 4 + v d 0 4*v d 2 3 := by
  expand_haf

@[simp] theorem compHaf_23 (d : SS.BitString 6 → ℂ) :
    compHaf d 2 3 = v d 0 1*v d 4 5 + v d 0 4*v d 1 5 + v d 0 5*v d 1 4 := by
  expand_haf
@[simp] theorem compHaf_24 (d : SS.BitString 6 → ℂ) :
    compHaf d 2 4 = v d 0 1*v d 3 5 + v d 0 3*v d 1 5 + v d 0 5*v d 1 3 := by
  expand_haf
@[simp] theorem compHaf_25 (d : SS.BitString 6 → ℂ) :
    compHaf d 2 5 = v d 0 1*v d 3 4 + v d 0 3*v d 1 4 + v d 0 4*v d 1 3 := by
  expand_haf

@[simp] theorem compHaf_34 (d : SS.BitString 6 → ℂ) :
    compHaf d 3 4 = v d 0 1*v d 2 5 + v d 0 2*v d 1 5 + v d 0 5*v d 1 2 := by
  expand_haf
@[simp] theorem compHaf_35 (d : SS.BitString 6 → ℂ) :
    compHaf d 3 5 = v d 0 1*v d 2 4 + v d 0 2*v d 1 4 + v d 0 4*v d 1 2 := by
  expand_haf
@[simp] theorem compHaf_45 (d : SS.BitString 6 → ℂ) :
    compHaf d 4 5 = v d 0 1*v d 2 3 + v d 0 2*v d 1 3 + v d 0 3*v d 1 2 := by
  expand_haf

end
end SixQubit.Orbit8Universal
