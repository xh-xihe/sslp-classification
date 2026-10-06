import SixQubit.CodeOrbit32

/-! The complete real moment normal form in the SI table coordinates.
All row combinations are kernel checked, with nonnegative boundaries retained.
No final no-code theorem is used to discharge an intermediate equation. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit32PrintedMomentNormal
noncomputable section
open SixQubit.Orbit32
open scoped BigOperators

def VectorMoments (q r : Fin 16 → ℝ) : Prop := MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) (r ⟨12,by decide⟩) (r ⟨13,by decide⟩) (r ⟨14,by decide⟩) (r ⟨15,by decide⟩)

structure PrintedNormalForm (q r : Fin 16 → ℝ) : Prop where
  reflection0_0 : (q ⟨0,by decide⟩) + (r ⟨12,by decide⟩)/3 - 2*(r ⟨4,by decide⟩)/3 - 2*(r ⟨8,by decide⟩)/3=0
  reflection1_0 : (q ⟨4,by decide⟩) - 2*(r ⟨12,by decide⟩)/3 - 2*(r ⟨4,by decide⟩)/3 + (r ⟨8,by decide⟩)/3=0
  reflection2_0 : (q ⟨8,by decide⟩) - 2*(r ⟨12,by decide⟩)/3 + (r ⟨4,by decide⟩)/3 - 2*(r ⟨8,by decide⟩)/3=0
  oddBottom0 : (q ⟨15,by decide⟩) + (r ⟨12,by decide⟩)/3 + (r ⟨4,by decide⟩)/3 + (r ⟨8,by decide⟩)/3 - 1/8=0
  oddTop0 : (r ⟨12,by decide⟩)/3 + (r ⟨3,by decide⟩) + (r ⟨4,by decide⟩)/3 + (r ⟨8,by decide⟩)/3 - 1/8=0
  reflection0_1 : (q ⟨1,by decide⟩) + (r ⟨13,by decide⟩)/3 - 2*(r ⟨5,by decide⟩)/3 - 2*(r ⟨9,by decide⟩)/3=0
  reflection1_1 : (q ⟨5,by decide⟩) - 2*(r ⟨13,by decide⟩)/3 - 2*(r ⟨5,by decide⟩)/3 + (r ⟨9,by decide⟩)/3=0
  reflection2_1 : (q ⟨9,by decide⟩) - 2*(r ⟨13,by decide⟩)/3 + (r ⟨5,by decide⟩)/3 - 2*(r ⟨9,by decide⟩)/3=0
  oddBottom1 : (q ⟨14,by decide⟩) + (r ⟨13,by decide⟩)/3 + (r ⟨5,by decide⟩)/3 + (r ⟨9,by decide⟩)/3 - 1/8=0
  oddTop1 : (r ⟨13,by decide⟩)/3 + (r ⟨2,by decide⟩) + (r ⟨5,by decide⟩)/3 + (r ⟨9,by decide⟩)/3 - 1/8=0
  reflection0_2 : (q ⟨2,by decide⟩) - 2*(r ⟨10,by decide⟩)/3 + (r ⟨14,by decide⟩)/3 - 2*(r ⟨6,by decide⟩)/3=0
  reflection1_2 : (q ⟨6,by decide⟩) + (r ⟨10,by decide⟩)/3 - 2*(r ⟨14,by decide⟩)/3 - 2*(r ⟨6,by decide⟩)/3=0
  reflection2_2 : (q ⟨10,by decide⟩) - 2*(r ⟨10,by decide⟩)/3 - 2*(r ⟨14,by decide⟩)/3 + (r ⟨6,by decide⟩)/3=0
  oddBottom2 : (q ⟨13,by decide⟩) + (r ⟨10,by decide⟩)/3 + (r ⟨14,by decide⟩)/3 + (r ⟨6,by decide⟩)/3 - 1/8=0
  oddTop2 : (r ⟨1,by decide⟩) + (r ⟨10,by decide⟩)/3 + (r ⟨14,by decide⟩)/3 + (r ⟨6,by decide⟩)/3 - 1/8=0
  reflection0_3 : (q ⟨3,by decide⟩) - 2*(r ⟨11,by decide⟩)/3 + (r ⟨15,by decide⟩)/3 - 2*(r ⟨7,by decide⟩)/3=0
  reflection1_3 : (q ⟨7,by decide⟩) + (r ⟨11,by decide⟩)/3 - 2*(r ⟨15,by decide⟩)/3 - 2*(r ⟨7,by decide⟩)/3=0
  reflection2_3 : (q ⟨11,by decide⟩) - 2*(r ⟨11,by decide⟩)/3 - 2*(r ⟨15,by decide⟩)/3 + (r ⟨7,by decide⟩)/3=0
  oddBottom3 : (q ⟨12,by decide⟩) + (r ⟨11,by decide⟩)/3 + (r ⟨15,by decide⟩)/3 + (r ⟨7,by decide⟩)/3 - 1/8=0
  oddTop3 : (r ⟨0,by decide⟩) + (r ⟨11,by decide⟩)/3 + (r ⟨15,by decide⟩)/3 + (r ⟨7,by decide⟩)/3 - 1/8=0
  row0 : (r ⟨4,by decide⟩) + (r ⟨5,by decide⟩) + (r ⟨6,by decide⟩) + (r ⟨7,by decide⟩) - 1/4=0
  row1 : (r ⟨10,by decide⟩) + (r ⟨11,by decide⟩) + (r ⟨8,by decide⟩) + (r ⟨9,by decide⟩) - 1/4=0
  row2 : (r ⟨12,by decide⟩) + (r ⟨13,by decide⟩) + (r ⟨14,by decide⟩) + (r ⟨15,by decide⟩) - 1/4=0
  nonnegQ : ∀ j, 0 ≤ q j
  nonnegR : ∀ j, 0 ≤ r j

theorem normal_of_moments (q r : Fin 16 → ℝ) (hm : VectorMoments q r) : PrintedNormalForm q r := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) (r ⟨12,by decide⟩) (r ⟨13,by decide⟩) (r ⟨14,by decide⟩) (r ⟨15,by decide⟩) at hm
  constructor
  · linear_combination 1 * hm.n0 + -1 * hm.n1 + (-1/3) * hm.m1 + (-1/3) * hm.m2 + (-7/12) * hm.m3 + (-7/12) * hm.m4 + (-7/12) * hm.m5 + (-3/4) * hm.m6 + (-1/12) * hm.c12 + (1/6) * hm.c13 + (1/6) * hm.c14 + (1/6) * hm.c15 + (1/12) * hm.c16 + (1/6) * hm.c23 + (1/6) * hm.c24 + (1/6) * hm.c25 + (1/12) * hm.c26 + (1/6) * hm.c34 + (1/6) * hm.c35 + (1/3) * hm.c36 + (1/6) * hm.c45 + (1/3) * hm.c46 + (1/3) * hm.c56
  · linear_combination (-1/3) * hm.m1 + (2/3) * hm.m2 + (-1/12) * hm.m3 + (-1/12) * hm.m4 + (-1/12) * hm.m5 + (1/4) * hm.m6 + (-1/12) * hm.c12 + (1/6) * hm.c13 + (1/6) * hm.c14 + (1/6) * hm.c15 + (1/12) * hm.c16 + (-1/3) * hm.c23 + (-1/3) * hm.c24 + (-1/3) * hm.c25 + (1/12) * hm.c26 + (1/6) * hm.c34 + (1/6) * hm.c35 + (-1/6) * hm.c36 + (1/6) * hm.c45 + (-1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (2/3) * hm.m1 + (-1/3) * hm.m2 + (-1/12) * hm.m3 + (-1/12) * hm.m4 + (-1/12) * hm.m5 + (1/4) * hm.m6 + (-1/12) * hm.c12 + (-1/3) * hm.c13 + (-1/3) * hm.c14 + (-1/3) * hm.c15 + (1/12) * hm.c16 + (1/6) * hm.c23 + (1/6) * hm.c24 + (1/6) * hm.c25 + (1/12) * hm.c26 + (1/6) * hm.c34 + (1/6) * hm.c35 + (-1/6) * hm.c36 + (1/6) * hm.c45 + (-1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (-5/24) * hm.m1 + (-5/24) * hm.m2 + (-1/12) * hm.m3 + (-1/12) * hm.m4 + (-1/12) * hm.m5 + (3/8) * hm.m6 + (1/6) * hm.c12 + (1/6) * hm.c13 + (1/6) * hm.c14 + (1/6) * hm.c15 + (-1/6) * hm.c16 + (1/6) * hm.c23 + (1/6) * hm.c24 + (1/6) * hm.c25 + (-1/6) * hm.c26 + (1/6) * hm.c34 + (1/6) * hm.c35 + (-1/6) * hm.c36 + (1/6) * hm.c45 + (-1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (-5/24) * hm.m1 + (-5/24) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/8) * hm.m6 + (-1/12) * hm.c12 + (1/6) * hm.c13 + (1/6) * hm.c14 + (1/6) * hm.c15 + (1/12) * hm.c16 + (1/6) * hm.c23 + (1/6) * hm.c24 + (1/6) * hm.c25 + (1/12) * hm.c26 + (-1/3) * hm.c34 + (-1/3) * hm.c35 + (-1/6) * hm.c36 + (-1/3) * hm.c45 + (-1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (-1/4) * hm.m3 + (5/12) * hm.m4 + (5/12) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (1/6) * hm.c13 + (-1/6) * hm.c14 + (-1/6) * hm.c15 + (1/12) * hm.c16 + (1/6) * hm.c23 + (-1/6) * hm.c24 + (-1/6) * hm.c25 + (1/12) * hm.c26 + (-1/6) * hm.c34 + (-1/6) * hm.c35 + (1/3) * hm.c36 + (1/6) * hm.c45 + (-1/3) * hm.c46 + (-1/3) * hm.c56
  · linear_combination (1/4) * hm.m3 + (-1/12) * hm.m4 + (-1/12) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (1/6) * hm.c13 + (-1/6) * hm.c14 + (-1/6) * hm.c15 + (1/12) * hm.c16 + (-1/3) * hm.c23 + (1/3) * hm.c24 + (1/3) * hm.c25 + (1/12) * hm.c26 + (-1/6) * hm.c34 + (-1/6) * hm.c35 + (-1/6) * hm.c36 + (1/6) * hm.c45 + (1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (1/4) * hm.m3 + (-1/12) * hm.m4 + (-1/12) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (-1/3) * hm.c13 + (1/3) * hm.c14 + (1/3) * hm.c15 + (1/12) * hm.c16 + (1/6) * hm.c23 + (-1/6) * hm.c24 + (-1/6) * hm.c25 + (1/12) * hm.c26 + (-1/6) * hm.c34 + (-1/6) * hm.c35 + (-1/6) * hm.c36 + (1/6) * hm.c45 + (1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (1/8) * hm.m1 + (1/8) * hm.m2 + (1/4) * hm.m3 + (-1/12) * hm.m4 + (-1/12) * hm.m5 + (1/24) * hm.m6 + (1/6) * hm.c12 + (1/6) * hm.c13 + (-1/6) * hm.c14 + (-1/6) * hm.c15 + (-1/6) * hm.c16 + (1/6) * hm.c23 + (-1/6) * hm.c24 + (-1/6) * hm.c25 + (-1/6) * hm.c26 + (-1/6) * hm.c34 + (-1/6) * hm.c35 + (-1/6) * hm.c36 + (1/6) * hm.c45 + (1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (1/8) * hm.m1 + (1/8) * hm.m2 + (-1/2) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (-5/24) * hm.m6 + (-1/12) * hm.c12 + (1/6) * hm.c13 + (-1/6) * hm.c14 + (-1/6) * hm.c15 + (1/12) * hm.c16 + (1/6) * hm.c23 + (-1/6) * hm.c24 + (-1/6) * hm.c25 + (1/12) * hm.c26 + (1/3) * hm.c34 + (1/3) * hm.c35 + (-1/6) * hm.c36 + (-1/3) * hm.c45 + (1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (5/12) * hm.m3 + (-1/4) * hm.m4 + (5/12) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (-1/6) * hm.c13 + (1/6) * hm.c14 + (-1/6) * hm.c15 + (1/12) * hm.c16 + (-1/6) * hm.c23 + (1/6) * hm.c24 + (-1/6) * hm.c25 + (1/12) * hm.c26 + (-1/6) * hm.c34 + (1/6) * hm.c35 + (-1/3) * hm.c36 + (-1/6) * hm.c45 + (1/3) * hm.c46 + (-1/3) * hm.c56
  · linear_combination (-1/12) * hm.m3 + (1/4) * hm.m4 + (-1/12) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (-1/6) * hm.c13 + (1/6) * hm.c14 + (-1/6) * hm.c15 + (1/12) * hm.c16 + (1/3) * hm.c23 + (-1/3) * hm.c24 + (1/3) * hm.c25 + (1/12) * hm.c26 + (-1/6) * hm.c34 + (1/6) * hm.c35 + (1/6) * hm.c36 + (-1/6) * hm.c45 + (-1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (-1/12) * hm.m3 + (1/4) * hm.m4 + (-1/12) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (1/3) * hm.c13 + (-1/3) * hm.c14 + (1/3) * hm.c15 + (1/12) * hm.c16 + (-1/6) * hm.c23 + (1/6) * hm.c24 + (-1/6) * hm.c25 + (1/12) * hm.c26 + (-1/6) * hm.c34 + (1/6) * hm.c35 + (1/6) * hm.c36 + (-1/6) * hm.c45 + (-1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (1/8) * hm.m1 + (1/8) * hm.m2 + (-1/12) * hm.m3 + (1/4) * hm.m4 + (-1/12) * hm.m5 + (1/24) * hm.m6 + (1/6) * hm.c12 + (-1/6) * hm.c13 + (1/6) * hm.c14 + (-1/6) * hm.c15 + (-1/6) * hm.c16 + (-1/6) * hm.c23 + (1/6) * hm.c24 + (-1/6) * hm.c25 + (-1/6) * hm.c26 + (-1/6) * hm.c34 + (1/6) * hm.c35 + (1/6) * hm.c36 + (-1/6) * hm.c45 + (-1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (1/8) * hm.m1 + (1/8) * hm.m2 + (1/6) * hm.m3 + (-1/2) * hm.m4 + (1/6) * hm.m5 + (-5/24) * hm.m6 + (-1/12) * hm.c12 + (-1/6) * hm.c13 + (1/6) * hm.c14 + (-1/6) * hm.c15 + (1/12) * hm.c16 + (-1/6) * hm.c23 + (1/6) * hm.c24 + (-1/6) * hm.c25 + (1/12) * hm.c26 + (1/3) * hm.c34 + (-1/3) * hm.c35 + (1/6) * hm.c36 + (1/3) * hm.c45 + (-1/6) * hm.c46 + (1/6) * hm.c56
  · linear_combination (5/12) * hm.m3 + (5/12) * hm.m4 + (-1/4) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (-1/6) * hm.c13 + (-1/6) * hm.c14 + (1/6) * hm.c15 + (1/12) * hm.c16 + (-1/6) * hm.c23 + (-1/6) * hm.c24 + (1/6) * hm.c25 + (1/12) * hm.c26 + (1/6) * hm.c34 + (-1/6) * hm.c35 + (-1/3) * hm.c36 + (-1/6) * hm.c45 + (-1/3) * hm.c46 + (1/3) * hm.c56
  · linear_combination (-1/12) * hm.m3 + (-1/12) * hm.m4 + (1/4) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (-1/6) * hm.c13 + (-1/6) * hm.c14 + (1/6) * hm.c15 + (1/12) * hm.c16 + (1/3) * hm.c23 + (1/3) * hm.c24 + (-1/3) * hm.c25 + (1/12) * hm.c26 + (1/6) * hm.c34 + (-1/6) * hm.c35 + (1/6) * hm.c36 + (-1/6) * hm.c45 + (1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (-1/12) * hm.m3 + (-1/12) * hm.m4 + (1/4) * hm.m5 + (-1/12) * hm.m6 + (-1/12) * hm.c12 + (1/3) * hm.c13 + (1/3) * hm.c14 + (-1/3) * hm.c15 + (1/12) * hm.c16 + (-1/6) * hm.c23 + (-1/6) * hm.c24 + (1/6) * hm.c25 + (1/12) * hm.c26 + (1/6) * hm.c34 + (-1/6) * hm.c35 + (1/6) * hm.c36 + (-1/6) * hm.c45 + (1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (1/8) * hm.m1 + (1/8) * hm.m2 + (-1/12) * hm.m3 + (-1/12) * hm.m4 + (1/4) * hm.m5 + (1/24) * hm.m6 + (1/6) * hm.c12 + (-1/6) * hm.c13 + (-1/6) * hm.c14 + (1/6) * hm.c15 + (-1/6) * hm.c16 + (-1/6) * hm.c23 + (-1/6) * hm.c24 + (1/6) * hm.c25 + (-1/6) * hm.c26 + (1/6) * hm.c34 + (-1/6) * hm.c35 + (1/6) * hm.c36 + (-1/6) * hm.c45 + (1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (1/8) * hm.n1 + (1/8) * hm.m1 + (1/8) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (-1/2) * hm.m5 + (-5/24) * hm.m6 + (-1/12) * hm.c12 + (-1/6) * hm.c13 + (-1/6) * hm.c14 + (1/6) * hm.c15 + (1/12) * hm.c16 + (-1/6) * hm.c23 + (-1/6) * hm.c24 + (1/6) * hm.c25 + (1/12) * hm.c26 + (-1/3) * hm.c34 + (1/3) * hm.c35 + (1/6) * hm.c36 + (1/3) * hm.c45 + (1/6) * hm.c46 + (-1/6) * hm.c56
  · linear_combination (1/4) * hm.n1 + (1/4) * hm.m1 + (-3/4) * hm.m2 + (1/4) * hm.m6 + (1/2) * hm.c12 + (-1/2) * hm.c16 + (1/2) * hm.c26
  · linear_combination (1/4) * hm.n1 + (-3/4) * hm.m1 + (1/4) * hm.m2 + (1/4) * hm.m6 + (1/2) * hm.c12 + (1/2) * hm.c16 + (-1/2) * hm.c26
  · linear_combination (1/4) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m2 + (1/4) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c16 + (-1/2) * hm.c26
  · intro j
    fin_cases j
    · exact hm.nq0
    · exact hm.nq1
    · exact hm.nq2
    · exact hm.nq3
    · exact hm.nq4
    · exact hm.nq5
    · exact hm.nq6
    · exact hm.nq7
    · exact hm.nq8
    · exact hm.nq9
    · exact hm.nq10
    · exact hm.nq11
    · exact hm.nq12
    · exact hm.nq13
    · exact hm.nq14
    · exact hm.nq15
  · intro j
    fin_cases j
    · exact hm.nr0
    · exact hm.nr1
    · exact hm.nr2
    · exact hm.nr3
    · exact hm.nr4
    · exact hm.nr5
    · exact hm.nr6
    · exact hm.nr7
    · exact hm.nr8
    · exact hm.nr9
    · exact hm.nr10
    · exact hm.nr11
    · exact hm.nr12
    · exact hm.nr13
    · exact hm.nr14
    · exact hm.nr15

theorem moments_of_normal (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) : VectorMoments q r := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) (r ⟨12,by decide⟩) (r ⟨13,by decide⟩) (r ⟨14,by decide⟩) (r ⟨15,by decide⟩)
  constructor
  · linear_combination 1 * hm.reflection0_0 + 1 * hm.reflection1_0 + 1 * hm.reflection2_0 + 1 * hm.oddBottom0 + 1 * hm.reflection0_1 + 1 * hm.reflection1_1 + 1 * hm.reflection2_1 + 1 * hm.oddBottom1 + 1 * hm.reflection0_2 + 1 * hm.reflection1_2 + 1 * hm.reflection2_2 + 1 * hm.oddBottom2 + 1 * hm.reflection0_3 + 1 * hm.reflection1_3 + 1 * hm.reflection2_3 + 1 * hm.oddBottom3 + (2/3) * hm.row0 + (2/3) * hm.row1 + (2/3) * hm.row2
  · linear_combination 1 * hm.oddTop0 + 1 * hm.oddTop1 + 1 * hm.oddTop2 + 1 * hm.oddTop3 + (2/3) * hm.row0 + (2/3) * hm.row1 + (2/3) * hm.row2
  · linear_combination 1 * hm.reflection2_0 + 1 * hm.oddBottom0 + 1 * hm.reflection2_1 + 1 * hm.oddBottom1 + 1 * hm.reflection2_2 + 1 * hm.oddBottom2 + 1 * hm.reflection2_3 + 1 * hm.oddBottom3 + (-2/3) * hm.row0 + (-2/3) * hm.row1 + (-2/3) * hm.row2
  · linear_combination 1 * hm.reflection1_0 + 1 * hm.oddBottom0 + 1 * hm.reflection1_1 + 1 * hm.oddBottom1 + 1 * hm.reflection1_2 + 1 * hm.oddBottom2 + 1 * hm.reflection1_3 + 1 * hm.oddBottom3 + (-2/3) * hm.row0 + (-2/3) * hm.row1 + (-2/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + -1 * hm.oddTop0 + 1 * hm.oddBottom1 + -1 * hm.oddTop1 + 1 * hm.reflection0_2 + 1 * hm.reflection1_2 + 1 * hm.reflection2_2 + 1 * hm.reflection0_3 + 1 * hm.reflection1_3 + 1 * hm.reflection2_3
  · linear_combination 1 * hm.oddBottom0 + -1 * hm.oddTop0 + 1 * hm.reflection0_1 + 1 * hm.reflection1_1 + 1 * hm.reflection2_1 + 1 * hm.oddBottom2 + -1 * hm.oddTop2 + 1 * hm.reflection0_3 + 1 * hm.reflection1_3 + 1 * hm.reflection2_3
  · linear_combination 1 * hm.oddBottom0 + -1 * hm.oddTop0 + 1 * hm.reflection0_1 + 1 * hm.reflection1_1 + 1 * hm.reflection2_1 + 1 * hm.reflection0_2 + 1 * hm.reflection1_2 + 1 * hm.reflection2_2 + 1 * hm.oddBottom3 + -1 * hm.oddTop3
  · linear_combination 1 * hm.reflection1_0 + 1 * hm.reflection2_0 + -1 * hm.oddTop0 + 1 * hm.reflection1_1 + 1 * hm.reflection2_1 + -1 * hm.oddTop1 + 1 * hm.reflection1_2 + 1 * hm.reflection2_2 + -1 * hm.oddTop2 + 1 * hm.reflection1_3 + 1 * hm.reflection2_3 + -1 * hm.oddTop3 + (2/3) * hm.row0 + (2/3) * hm.row1 + (2/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + 1 * hm.oddBottom1 + 1 * hm.oddBottom2 + 1 * hm.oddBottom3 + (-1/3) * hm.row0 + (-1/3) * hm.row1 + (-4/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + 1 * hm.oddBottom1 + 1 * hm.reflection2_2 + 1 * hm.reflection2_3 + (-1/3) * hm.row0 + (-1/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + 1 * hm.reflection2_1 + 1 * hm.oddBottom2 + 1 * hm.reflection2_3 + (-1/3) * hm.row0 + (-1/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + 1 * hm.reflection2_1 + 1 * hm.reflection2_2 + 1 * hm.oddBottom3 + (-1/3) * hm.row0 + (-1/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.reflection2_0 + 1 * hm.reflection2_1 + 1 * hm.reflection2_2 + 1 * hm.reflection2_3 + (-1/3) * hm.row0 + (2/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + 1 * hm.oddBottom1 + 1 * hm.reflection1_2 + 1 * hm.reflection1_3 + (-1/3) * hm.row0 + (-1/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + 1 * hm.reflection1_1 + 1 * hm.oddBottom2 + 1 * hm.reflection1_3 + (-1/3) * hm.row0 + (-1/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + 1 * hm.reflection1_1 + 1 * hm.reflection1_2 + 1 * hm.oddBottom3 + (-1/3) * hm.row0 + (-1/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.reflection1_0 + 1 * hm.reflection1_1 + 1 * hm.reflection1_2 + 1 * hm.reflection1_3 + (2/3) * hm.row0 + (-1/3) * hm.row1 + (-1/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + -1 * hm.oddTop0 + 1 * hm.reflection0_3 + 1 * hm.reflection1_3 + 1 * hm.reflection2_3
  · linear_combination 1 * hm.oddBottom0 + -1 * hm.oddTop0 + 1 * hm.reflection0_2 + 1 * hm.reflection1_2 + 1 * hm.reflection2_2
  · linear_combination -1 * hm.oddTop0 + -1 * hm.oddTop1 + 1 * hm.reflection1_2 + 1 * hm.reflection2_2 + 1 * hm.reflection1_3 + 1 * hm.reflection2_3 + (1/3) * hm.row0 + (1/3) * hm.row1 + (1/3) * hm.row2
  · linear_combination 1 * hm.oddBottom0 + -1 * hm.oddTop0 + 1 * hm.reflection0_1 + 1 * hm.reflection1_1 + 1 * hm.reflection2_1
  · linear_combination -1 * hm.oddTop0 + 1 * hm.reflection1_1 + 1 * hm.reflection2_1 + -1 * hm.oddTop2 + 1 * hm.reflection1_3 + 1 * hm.reflection2_3 + (1/3) * hm.row0 + (1/3) * hm.row1 + (1/3) * hm.row2
  · linear_combination -1 * hm.oddTop0 + 1 * hm.reflection1_1 + 1 * hm.reflection2_1 + 1 * hm.reflection1_2 + 1 * hm.reflection2_2 + -1 * hm.oddTop3 + (1/3) * hm.row0 + (1/3) * hm.row1 + (1/3) * hm.row2
  · exact hm.nonnegQ ⟨0,by decide⟩
  · exact hm.nonnegQ ⟨1,by decide⟩
  · exact hm.nonnegQ ⟨2,by decide⟩
  · exact hm.nonnegQ ⟨3,by decide⟩
  · exact hm.nonnegQ ⟨4,by decide⟩
  · exact hm.nonnegQ ⟨5,by decide⟩
  · exact hm.nonnegQ ⟨6,by decide⟩
  · exact hm.nonnegQ ⟨7,by decide⟩
  · exact hm.nonnegQ ⟨8,by decide⟩
  · exact hm.nonnegQ ⟨9,by decide⟩
  · exact hm.nonnegQ ⟨10,by decide⟩
  · exact hm.nonnegQ ⟨11,by decide⟩
  · exact hm.nonnegQ ⟨12,by decide⟩
  · exact hm.nonnegQ ⟨13,by decide⟩
  · exact hm.nonnegQ ⟨14,by decide⟩
  · exact hm.nonnegQ ⟨15,by decide⟩
  · exact hm.nonnegR ⟨0,by decide⟩
  · exact hm.nonnegR ⟨1,by decide⟩
  · exact hm.nonnegR ⟨2,by decide⟩
  · exact hm.nonnegR ⟨3,by decide⟩
  · exact hm.nonnegR ⟨4,by decide⟩
  · exact hm.nonnegR ⟨5,by decide⟩
  · exact hm.nonnegR ⟨6,by decide⟩
  · exact hm.nonnegR ⟨7,by decide⟩
  · exact hm.nonnegR ⟨8,by decide⟩
  · exact hm.nonnegR ⟨9,by decide⟩
  · exact hm.nonnegR ⟨10,by decide⟩
  · exact hm.nonnegR ⟨11,by decide⟩
  · exact hm.nonnegR ⟨12,by decide⟩
  · exact hm.nonnegR ⟨13,by decide⟩
  · exact hm.nonnegR ⟨14,by decide⟩
  · exact hm.nonnegR ⟨15,by decide⟩

theorem complete_normal_form (q r : Fin 16 → ℝ) :
    VectorMoments q r ↔ PrintedNormalForm q r :=
  ⟨normal_of_moments q r,moments_of_normal q r⟩

def bottom : Fin 16 → SS.BitString 6 :=
  ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def top : Fin 16 → SS.BitString 6 :=
  ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    PrintedNormalForm (fun j => Complex.normSq (c (bottom j)))
      (fun j => Complex.normSq (d (top j))) := by
  apply normal_of_moments
  exact moments c d hc hd hnc hnd hkl

def middle : Fin 4 → Fin 3 → Bool := ![![false,false,false],![false,true,true],![true,false,true],![true,true,false]]
def embed (o u : Fin 3 → Bool) : SS.BitString 6 := ![o 0,o 1,u 0,u 1,u 2,o 2]
def AIndex (e : Fin 4) : Fin 16 := ⟨e.val,by omega⟩
def BIndex (e : Fin 4) : Fin 16 := ⟨4+e.val,by omega⟩
def CIndex (e : Fin 4) : Fin 16 := ⟨8+e.val,by omega⟩
def EIndex (e : Fin 4) : Fin 16 := ⟨4+e.val,by omega⟩
def FIndex (e : Fin 4) : Fin 16 := ⟨8+e.val,by omega⟩
def GIndex (e : Fin 4) : Fin 16 := ⟨12+e.val,by omega⟩
def RIndex (e : Fin 4) : Fin 16 := ⟨15-e.val,by omega⟩
def SIndex (e : Fin 4) : Fin 16 := ⟨3-e.val,by omega⟩
theorem actual_bottom_groups : ∀ e,
    bottom (AIndex e)=embed ![false,false,false] (middle e) ∧
    bottom (BIndex e)=embed ![false,true,true] (middle e) ∧
    bottom (CIndex e)=embed ![true,false,true] (middle e) ∧
    bottom (RIndex e)=embed ![true,true,false] (fun j => !(middle e j)) := by decide +kernel
theorem actual_top_groups : ∀ e,
    top (EIndex e)=embed ![false,true,false] (middle e) ∧
    top (FIndex e)=embed ![true,false,false] (middle e) ∧
    top (GIndex e)=embed ![true,true,true] (middle e) ∧
    top (SIndex e)=embed ![false,false,true] (fun j => !(middle e j)) := by decide +kernel

theorem reflected (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) (e : Fin 4) :
  q (AIndex e)=(2*r (EIndex e)+2*r (FIndex e)-r (GIndex e))/3 ∧
  q (BIndex e)=(2*r (EIndex e)-r (FIndex e)+2*r (GIndex e))/3 ∧
  q (CIndex e)=(-r (EIndex e)+2*r (FIndex e)+2*r (GIndex e))/3 := by
  fin_cases e
  · constructor
    · have he := hm.reflection0_0
      norm_num at he
      norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
      linear_combination he
    · constructor
      · have he := hm.reflection1_0
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he
      · have he := hm.reflection2_0
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he
  · constructor
    · have he := hm.reflection0_1
      norm_num at he
      norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
      linear_combination he
    · constructor
      · have he := hm.reflection1_1
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he
      · have he := hm.reflection2_1
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he
  · constructor
    · have he := hm.reflection0_2
      norm_num at he
      norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
      linear_combination he
    · constructor
      · have he := hm.reflection1_2
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he
      · have he := hm.reflection2_2
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he
  · constructor
    · have he := hm.reflection0_3
      norm_num at he
      norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
      linear_combination he
    · constructor
      · have he := hm.reflection1_3
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he
      · have he := hm.reflection2_3
        norm_num at he
        norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]
        linear_combination he

theorem rowsums (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) :
    (∑ e : Fin 4, r (EIndex e))=1/4 ∧ (∑ e : Fin 4, r (FIndex e))=1/4 ∧
      (∑ e : Fin 4, r (GIndex e))=1/4 := by
  have h0 := hm.row0
  have h1 := hm.row1
  have h2 := hm.row2
  norm_num at h0 h1 h2
  norm_num [Fin.sum_univ_succ,Fin.succ,EIndex,FIndex,GIndex]
  exact ⟨by linear_combination h0,by linear_combination h1,by linear_combination h2⟩
theorem oddweights (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) (e : Fin 4) :
  q (RIndex e)=1/8-(r (EIndex e)+r (FIndex e)+r (GIndex e))/3 ∧
  r (SIndex e)=1/8-(r (EIndex e)+r (FIndex e)+r (GIndex e))/3 := by
  fin_cases e
  · have h0 := hm.oddBottom0
    have h1 := hm.oddTop0
    norm_num at h0 h1
    norm_num [RIndex,SIndex,EIndex,FIndex,GIndex,Fin.succ]
    exact ⟨by linear_combination h0,by linear_combination h1⟩
  · have h0 := hm.oddBottom1
    have h1 := hm.oddTop1
    norm_num at h0 h1
    norm_num [RIndex,SIndex,EIndex,FIndex,GIndex,Fin.succ]
    exact ⟨by linear_combination h0,by linear_combination h1⟩
  · have h0 := hm.oddBottom2
    have h1 := hm.oddTop2
    norm_num at h0 h1
    norm_num [RIndex,SIndex,EIndex,FIndex,GIndex,Fin.succ]
    exact ⟨by linear_combination h0,by linear_combination h1⟩
  · have h0 := hm.oddBottom3
    have h1 := hm.oddTop3
    norm_num at h0 h1
    norm_num [RIndex,SIndex,EIndex,FIndex,GIndex,Fin.succ]
    exact ⟨by linear_combination h0,by linear_combination h1⟩

def parameters (r : Fin 16 → ℝ) : Fin 12 → ℝ := fun j => r ⟨4+j.val,by omega⟩
theorem parameter_injectivity (q r q' r' : Fin 16 → ℝ)
    (hm : PrintedNormalForm q r) (hn : PrintedNormalForm q' r')
    (he : parameters r=parameters r') : q=q' ∧ r=r' := by
  have h0 := congrFun he (⟨0,by decide⟩ : Fin 12)
  change r ⟨4,by decide⟩=r' ⟨4,by decide⟩ at h0
  have h1 := congrFun he (⟨1,by decide⟩ : Fin 12)
  change r ⟨5,by decide⟩=r' ⟨5,by decide⟩ at h1
  have h2 := congrFun he (⟨2,by decide⟩ : Fin 12)
  change r ⟨6,by decide⟩=r' ⟨6,by decide⟩ at h2
  have h3 := congrFun he (⟨3,by decide⟩ : Fin 12)
  change r ⟨7,by decide⟩=r' ⟨7,by decide⟩ at h3
  have h4 := congrFun he (⟨4,by decide⟩ : Fin 12)
  change r ⟨8,by decide⟩=r' ⟨8,by decide⟩ at h4
  have h5 := congrFun he (⟨5,by decide⟩ : Fin 12)
  change r ⟨9,by decide⟩=r' ⟨9,by decide⟩ at h5
  have h6 := congrFun he (⟨6,by decide⟩ : Fin 12)
  change r ⟨10,by decide⟩=r' ⟨10,by decide⟩ at h6
  have h7 := congrFun he (⟨7,by decide⟩ : Fin 12)
  change r ⟨11,by decide⟩=r' ⟨11,by decide⟩ at h7
  have h8 := congrFun he (⟨8,by decide⟩ : Fin 12)
  change r ⟨12,by decide⟩=r' ⟨12,by decide⟩ at h8
  have h9 := congrFun he (⟨9,by decide⟩ : Fin 12)
  change r ⟨13,by decide⟩=r' ⟨13,by decide⟩ at h9
  have h10 := congrFun he (⟨10,by decide⟩ : Fin 12)
  change r ⟨14,by decide⟩=r' ⟨14,by decide⟩ at h10
  have h11 := congrFun he (⟨11,by decide⟩ : Fin 12)
  change r ⟨15,by decide⟩=r' ⟨15,by decide⟩ at h11
  constructor
  · funext j
    fin_cases j
    · change q ⟨0,by decide⟩=q' ⟨0,by decide⟩
      linear_combination 1 * hm.reflection0_0 + -1 * hn.reflection0_0 + (2/3) * h0 + (2/3) * h4 + (-1/3) * h8
    · change q ⟨1,by decide⟩=q' ⟨1,by decide⟩
      linear_combination 1 * hm.reflection0_1 + -1 * hn.reflection0_1 + (2/3) * h1 + (2/3) * h5 + (-1/3) * h9
    · change q ⟨2,by decide⟩=q' ⟨2,by decide⟩
      linear_combination 1 * hm.reflection0_2 + -1 * hn.reflection0_2 + (2/3) * h2 + (2/3) * h6 + (-1/3) * h10
    · change q ⟨3,by decide⟩=q' ⟨3,by decide⟩
      linear_combination 1 * hm.reflection0_3 + -1 * hn.reflection0_3 + (2/3) * hm.row0 + (-2/3) * hn.row0 + (2/3) * hm.row1 + (-2/3) * hn.row1 + (-1/3) * hm.row2 + (1/3) * hn.row2 + (-2/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (-2/3) * h4 + (-2/3) * h5 + (-2/3) * h6 + (1/3) * h8 + (1/3) * h9 + (1/3) * h10
    · change q ⟨4,by decide⟩=q' ⟨4,by decide⟩
      linear_combination 1 * hm.reflection1_0 + -1 * hn.reflection1_0 + (2/3) * h0 + (-1/3) * h4 + (2/3) * h8
    · change q ⟨5,by decide⟩=q' ⟨5,by decide⟩
      linear_combination 1 * hm.reflection1_1 + -1 * hn.reflection1_1 + (2/3) * h1 + (-1/3) * h5 + (2/3) * h9
    · change q ⟨6,by decide⟩=q' ⟨6,by decide⟩
      linear_combination 1 * hm.reflection1_2 + -1 * hn.reflection1_2 + (2/3) * h2 + (-1/3) * h6 + (2/3) * h10
    · change q ⟨7,by decide⟩=q' ⟨7,by decide⟩
      linear_combination 1 * hm.reflection1_3 + -1 * hn.reflection1_3 + (2/3) * hm.row0 + (-2/3) * hn.row0 + (-1/3) * hm.row1 + (1/3) * hn.row1 + (2/3) * hm.row2 + (-2/3) * hn.row2 + (-2/3) * h0 + (-2/3) * h1 + (-2/3) * h2 + (1/3) * h4 + (1/3) * h5 + (1/3) * h6 + (-2/3) * h8 + (-2/3) * h9 + (-2/3) * h10
    · change q ⟨8,by decide⟩=q' ⟨8,by decide⟩
      linear_combination 1 * hm.reflection2_0 + -1 * hn.reflection2_0 + (-1/3) * h0 + (2/3) * h4 + (2/3) * h8
    · change q ⟨9,by decide⟩=q' ⟨9,by decide⟩
      linear_combination 1 * hm.reflection2_1 + -1 * hn.reflection2_1 + (-1/3) * h1 + (2/3) * h5 + (2/3) * h9
    · change q ⟨10,by decide⟩=q' ⟨10,by decide⟩
      linear_combination 1 * hm.reflection2_2 + -1 * hn.reflection2_2 + (-1/3) * h2 + (2/3) * h6 + (2/3) * h10
    · change q ⟨11,by decide⟩=q' ⟨11,by decide⟩
      linear_combination 1 * hm.reflection2_3 + -1 * hn.reflection2_3 + (-1/3) * hm.row0 + (1/3) * hn.row0 + (2/3) * hm.row1 + (-2/3) * hn.row1 + (2/3) * hm.row2 + (-2/3) * hn.row2 + (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (-2/3) * h4 + (-2/3) * h5 + (-2/3) * h6 + (-2/3) * h8 + (-2/3) * h9 + (-2/3) * h10
    · change q ⟨12,by decide⟩=q' ⟨12,by decide⟩
      linear_combination 1 * hm.oddBottom3 + -1 * hn.oddBottom3 + (-1/3) * hm.row0 + (1/3) * hn.row0 + (-1/3) * hm.row1 + (1/3) * hn.row1 + (-1/3) * hm.row2 + (1/3) * hn.row2 + (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (1/3) * h4 + (1/3) * h5 + (1/3) * h6 + (1/3) * h8 + (1/3) * h9 + (1/3) * h10
    · change q ⟨13,by decide⟩=q' ⟨13,by decide⟩
      linear_combination 1 * hm.oddBottom2 + -1 * hn.oddBottom2 + (-1/3) * h2 + (-1/3) * h6 + (-1/3) * h10
    · change q ⟨14,by decide⟩=q' ⟨14,by decide⟩
      linear_combination 1 * hm.oddBottom1 + -1 * hn.oddBottom1 + (-1/3) * h1 + (-1/3) * h5 + (-1/3) * h9
    · change q ⟨15,by decide⟩=q' ⟨15,by decide⟩
      linear_combination 1 * hm.oddBottom0 + -1 * hn.oddBottom0 + (-1/3) * h0 + (-1/3) * h4 + (-1/3) * h8
  · funext j
    fin_cases j
    · change r ⟨0,by decide⟩=r' ⟨0,by decide⟩
      linear_combination 1 * hm.oddTop3 + -1 * hn.oddTop3 + (-1/3) * hm.row0 + (1/3) * hn.row0 + (-1/3) * hm.row1 + (1/3) * hn.row1 + (-1/3) * hm.row2 + (1/3) * hn.row2 + (1/3) * h0 + (1/3) * h1 + (1/3) * h2 + (1/3) * h4 + (1/3) * h5 + (1/3) * h6 + (1/3) * h8 + (1/3) * h9 + (1/3) * h10
    · change r ⟨1,by decide⟩=r' ⟨1,by decide⟩
      linear_combination 1 * hm.oddTop2 + -1 * hn.oddTop2 + (-1/3) * h2 + (-1/3) * h6 + (-1/3) * h10
    · change r ⟨2,by decide⟩=r' ⟨2,by decide⟩
      linear_combination 1 * hm.oddTop1 + -1 * hn.oddTop1 + (-1/3) * h1 + (-1/3) * h5 + (-1/3) * h9
    · change r ⟨3,by decide⟩=r' ⟨3,by decide⟩
      linear_combination 1 * hm.oddTop0 + -1 * hn.oddTop0 + (-1/3) * h0 + (-1/3) * h4 + (-1/3) * h8
    · change r ⟨4,by decide⟩=r' ⟨4,by decide⟩
      linear_combination 1 * h0
    · change r ⟨5,by decide⟩=r' ⟨5,by decide⟩
      linear_combination 1 * h1
    · change r ⟨6,by decide⟩=r' ⟨6,by decide⟩
      linear_combination 1 * h2
    · change r ⟨7,by decide⟩=r' ⟨7,by decide⟩
      linear_combination 1 * hm.row0 + -1 * hn.row0 + -1 * h0 + -1 * h1 + -1 * h2
    · change r ⟨8,by decide⟩=r' ⟨8,by decide⟩
      linear_combination 1 * h4
    · change r ⟨9,by decide⟩=r' ⟨9,by decide⟩
      linear_combination 1 * h5
    · change r ⟨10,by decide⟩=r' ⟨10,by decide⟩
      linear_combination 1 * h6
    · change r ⟨11,by decide⟩=r' ⟨11,by decide⟩
      linear_combination 1 * hm.row1 + -1 * hn.row1 + -1 * h4 + -1 * h5 + -1 * h6
    · change r ⟨12,by decide⟩=r' ⟨12,by decide⟩
      linear_combination 1 * h8
    · change r ⟨13,by decide⟩=r' ⟨13,by decide⟩
      linear_combination 1 * h9
    · change r ⟨14,by decide⟩=r' ⟨14,by decide⟩
      linear_combination 1 * h10
    · change r ⟨15,by decide⟩=r' ⟨15,by decide⟩
      linear_combination 1 * hm.row2 + -1 * hn.row2 + -1 * h8 + -1 * h9 + -1 * h10

end
end MainTheory.Orbit32PrintedMomentNormal
