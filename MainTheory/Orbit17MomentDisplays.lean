import SixQubit.CodeOrbit17
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit17MomentDisplays
open scoped BigOperators
open SixQubit.Orbit17
noncomputable section
def bottom : Fin 16 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def top : Fin 16 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]
def edges : Fin 15 → Fin 6 × Fin 6 := ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
def Moment (p q : Fin 16 → ℝ) := MomentSystem (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) (p 10) (p 11) (p 12) (p 13) (p 14) (p 15) (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (q 6) (q 7) (q 8) (q 9) (q 10) (q 11) (q 12) (q 13) (q 14) (q 15)
theorem actual_words : S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel
theorem edge_coordinates : ∀ e : Fin 15,∀ j : Fin 6,
    bottom ⟨e.val+1,by omega⟩ j=!(j=(edges e).1 ∨ j=(edges e).2) ∧
    top ⟨14-e.val,by omega⟩ j=(j=(edges e).1 ∨ j=(edges e).2) := by decide +kernel
def bottomProb (c : SS.State 6 ℂ) : Fin 16 → ℝ := fun i => Complex.normSq (c (bottom i))
def topProb (d : SS.State 6 ℂ) : Fin 16 → ℝ := fun i => Complex.normSq (d (top i))
theorem physical_moments (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Moment (bottomProb c) (topProb d) := by
  exact moments c d hc hd hnc hnd hkl

theorem bottom_normalization (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 0 + p 1 + p 10 + p 11 + p 12 + p 13 + p 14 + p 15 + p 2 + p 3 + p 4 + p 5 + p 6 + p 7 + p 8 + p 9 = 1 := by
  linear_combination (1) * hm.n0

theorem top_normalization (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 0 + q 1 + q 10 + q 11 + q 12 + q 13 + q 14 + q 15 + q 2 + q 3 + q 4 + q 5 + q 6 + q 7 + q 8 + q 9 = 1 := by
  linear_combination (1) * hm.n1

theorem shell_first (p q : Fin 16 → ℝ) (hm : Moment p q) :
    4*p 1 + 4*p 10 + 4*p 11 + 4*p 12 + 4*p 13 + 4*p 14 + 4*p 15 + 4*p 2 + 4*p 3 + 4*p 4 + 4*p 5 + 4*p 6 + 4*p 7 + 4*p 8 + 4*p 9 = 2*q 0 + 2*q 1 + 2*q 10 + 2*q 11 + 2*q 12 + 2*q 13 + 2*q 14 + 6*q 15 + 2*q 2 + 2*q 3 + 2*q 4 + 2*q 5 + 2*q 6 + 2*q 7 + 2*q 8 + 2*q 9 := by
  linear_combination (1) * hm.m1 + (1) * hm.m2 + (1) * hm.m3 + (1) * hm.m4 + (1) * hm.m5 + (1) * hm.m6

theorem shell_second (p q : Fin 16 → ℝ) (hm : Moment p q) :
    6*p 1 + 6*p 10 + 6*p 11 + 6*p 12 + 6*p 13 + 6*p 14 + 6*p 15 + 6*p 2 + 6*p 3 + 6*p 4 + 6*p 5 + 6*p 6 + 6*p 7 + 6*p 8 + 6*p 9 = q 0 + q 1 + q 10 + q 11 + q 12 + q 13 + q 14 + 15*q 15 + q 2 + q 3 + q 4 + q 5 + q 6 + q 7 + q 8 + q 9 := by
  linear_combination (1) * hm.m12 + (1) * hm.m13 + (1) * hm.m14 + (1) * hm.m15 + (1) * hm.m16 + (1) * hm.m23 + (1) * hm.m24 + (1) * hm.m25 + (1) * hm.m26 + (1) * hm.m34 + (1) * hm.m35 + (1) * hm.m36 + (1) * hm.m45 + (1) * hm.m46 + (1) * hm.m56

theorem bottom_anchor (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 0 = 1/4 := by
  linear_combination (1) * hm.n0 + (-3/4) * hm.n1 + (-7/16) * hm.m1 + (-7/16) * hm.m2 + (-7/16) * hm.m3 + (-7/16) * hm.m4 + (-7/16) * hm.m5 + (-7/16) * hm.m6 + (1/8) * hm.m12 + (1/8) * hm.m13 + (1/8) * hm.m14 + (1/8) * hm.m15 + (1/8) * hm.m16 + (1/8) * hm.m23 + (1/8) * hm.m24 + (1/8) * hm.m25 + (1/8) * hm.m26 + (1/8) * hm.m34 + (1/8) * hm.m35 + (1/8) * hm.m36 + (1/8) * hm.m45 + (1/8) * hm.m46 + (1/8) * hm.m56

theorem top_anchor (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 15 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/16) * hm.m1 + (3/16) * hm.m2 + (3/16) * hm.m3 + (3/16) * hm.m4 + (3/16) * hm.m5 + (3/16) * hm.m6 + (-1/8) * hm.m12 + (-1/8) * hm.m13 + (-1/8) * hm.m14 + (-1/8) * hm.m15 + (-1/8) * hm.m16 + (-1/8) * hm.m23 + (-1/8) * hm.m24 + (-1/8) * hm.m25 + (-1/8) * hm.m26 + (-1/8) * hm.m34 + (-1/8) * hm.m35 + (-1/8) * hm.m36 + (-1/8) * hm.m45 + (-1/8) * hm.m46 + (-1/8) * hm.m56

theorem bottom_edge_mass (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 10 + p 11 + p 12 + p 13 + p 14 + p 15 + p 2 + p 3 + p 4 + p 5 + p 6 + p 7 + p 8 + p 9 = 3/4 := by
  linear_combination (3/4) * hm.n1 + (7/16) * hm.m1 + (7/16) * hm.m2 + (7/16) * hm.m3 + (7/16) * hm.m4 + (7/16) * hm.m5 + (7/16) * hm.m6 + (-1/8) * hm.m12 + (-1/8) * hm.m13 + (-1/8) * hm.m14 + (-1/8) * hm.m15 + (-1/8) * hm.m16 + (-1/8) * hm.m23 + (-1/8) * hm.m24 + (-1/8) * hm.m25 + (-1/8) * hm.m26 + (-1/8) * hm.m34 + (-1/8) * hm.m35 + (-1/8) * hm.m36 + (-1/8) * hm.m45 + (-1/8) * hm.m46 + (-1/8) * hm.m56

theorem top_edge_mass (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 0 + q 1 + q 10 + q 11 + q 12 + q 13 + q 14 + q 2 + q 3 + q 4 + q 5 + q 6 + q 7 + q 8 + q 9 = 3/4 := by
  linear_combination (3/4) * hm.n1 + (-3/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (-3/16) * hm.m4 + (-3/16) * hm.m5 + (-3/16) * hm.m6 + (1/8) * hm.m12 + (1/8) * hm.m13 + (1/8) * hm.m14 + (1/8) * hm.m15 + (1/8) * hm.m16 + (1/8) * hm.m23 + (1/8) * hm.m24 + (1/8) * hm.m25 + (1/8) * hm.m26 + (1/8) * hm.m34 + (1/8) * hm.m35 + (1/8) * hm.m36 + (1/8) * hm.m45 + (1/8) * hm.m46 + (1/8) * hm.m56

theorem degree_sum_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 2 + p 3 + p 4 + p 5 + q 10 + q 11 + q 12 + q 13 + q 14 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (-3/4) * hm.m1 + (1/4) * hm.m2 + (1/4) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6

theorem degree_second_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    3*p 1 + 3*p 2 + 3*p 3 + 3*p 4 + 3*p 5 + q 10 + q 11 + q 12 + q 13 + q 14 = 1 := by
  linear_combination (1) * hm.n1 + (3/8) * hm.m1 + (3/8) * hm.m2 + (3/8) * hm.m3 + (3/8) * hm.m4 + (3/8) * hm.m5 + (3/8) * hm.m6 + (-3/4) * hm.m12 + (-3/4) * hm.m13 + (-3/4) * hm.m14 + (-3/4) * hm.m15 + (-3/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem bottom_degree_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 2 + p 3 + p 4 + p 5 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (9/16) * hm.m1 + (1/16) * hm.m2 + (1/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (-3/8) * hm.m12 + (-3/8) * hm.m13 + (-3/8) * hm.m14 + (-3/8) * hm.m15 + (-3/8) * hm.m16 + (1/8) * hm.m23 + (1/8) * hm.m24 + (1/8) * hm.m25 + (1/8) * hm.m26 + (1/8) * hm.m34 + (1/8) * hm.m35 + (1/8) * hm.m36 + (1/8) * hm.m45 + (1/8) * hm.m46 + (1/8) * hm.m56

theorem top_degree_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 10 + q 11 + q 12 + q 13 + q 14 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (-21/16) * hm.m1 + (3/16) * hm.m2 + (3/16) * hm.m3 + (3/16) * hm.m4 + (3/16) * hm.m5 + (3/16) * hm.m6 + (3/8) * hm.m12 + (3/8) * hm.m13 + (3/8) * hm.m14 + (3/8) * hm.m15 + (3/8) * hm.m16 + (-1/8) * hm.m23 + (-1/8) * hm.m24 + (-1/8) * hm.m25 + (-1/8) * hm.m26 + (-1/8) * hm.m34 + (-1/8) * hm.m35 + (-1/8) * hm.m36 + (-1/8) * hm.m45 + (-1/8) * hm.m46 + (-1/8) * hm.m56

theorem degree_sum_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 6 + p 7 + p 8 + p 9 + q 14 + q 6 + q 7 + q 8 + q 9 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (1/4) * hm.m1 + (-3/4) * hm.m2 + (1/4) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6

theorem degree_second_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    3*p 1 + 3*p 6 + 3*p 7 + 3*p 8 + 3*p 9 + q 14 + q 6 + q 7 + q 8 + q 9 = 1 := by
  linear_combination (1) * hm.n1 + (3/8) * hm.m1 + (3/8) * hm.m2 + (3/8) * hm.m3 + (3/8) * hm.m4 + (3/8) * hm.m5 + (3/8) * hm.m6 + (-3/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (-3/4) * hm.m23 + (-3/4) * hm.m24 + (-3/4) * hm.m25 + (-3/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem bottom_degree_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 6 + p 7 + p 8 + p 9 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/16) * hm.m1 + (9/16) * hm.m2 + (1/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (-3/8) * hm.m12 + (1/8) * hm.m13 + (1/8) * hm.m14 + (1/8) * hm.m15 + (1/8) * hm.m16 + (-3/8) * hm.m23 + (-3/8) * hm.m24 + (-3/8) * hm.m25 + (-3/8) * hm.m26 + (1/8) * hm.m34 + (1/8) * hm.m35 + (1/8) * hm.m36 + (1/8) * hm.m45 + (1/8) * hm.m46 + (1/8) * hm.m56

theorem top_degree_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 14 + q 6 + q 7 + q 8 + q 9 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/16) * hm.m1 + (-21/16) * hm.m2 + (3/16) * hm.m3 + (3/16) * hm.m4 + (3/16) * hm.m5 + (3/16) * hm.m6 + (3/8) * hm.m12 + (-1/8) * hm.m13 + (-1/8) * hm.m14 + (-1/8) * hm.m15 + (-1/8) * hm.m16 + (3/8) * hm.m23 + (3/8) * hm.m24 + (3/8) * hm.m25 + (3/8) * hm.m26 + (-1/8) * hm.m34 + (-1/8) * hm.m35 + (-1/8) * hm.m36 + (-1/8) * hm.m45 + (-1/8) * hm.m46 + (-1/8) * hm.m56

theorem degree_sum_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 10 + p 11 + p 12 + p 2 + p 6 + q 13 + q 3 + q 4 + q 5 + q 9 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m2 + (-3/4) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6

theorem degree_second_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    3*p 10 + 3*p 11 + 3*p 12 + 3*p 2 + 3*p 6 + q 13 + q 3 + q 4 + q 5 + q 9 = 1 := by
  linear_combination (1) * hm.n1 + (3/8) * hm.m1 + (3/8) * hm.m2 + (3/8) * hm.m3 + (3/8) * hm.m4 + (3/8) * hm.m5 + (3/8) * hm.m6 + (1/4) * hm.m12 + (-3/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (-3/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (-3/4) * hm.m34 + (-3/4) * hm.m35 + (-3/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem bottom_degree_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 10 + p 11 + p 12 + p 2 + p 6 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/16) * hm.m1 + (1/16) * hm.m2 + (9/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (1/8) * hm.m12 + (-3/8) * hm.m13 + (1/8) * hm.m14 + (1/8) * hm.m15 + (1/8) * hm.m16 + (-3/8) * hm.m23 + (1/8) * hm.m24 + (1/8) * hm.m25 + (1/8) * hm.m26 + (-3/8) * hm.m34 + (-3/8) * hm.m35 + (-3/8) * hm.m36 + (1/8) * hm.m45 + (1/8) * hm.m46 + (1/8) * hm.m56

theorem top_degree_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 13 + q 3 + q 4 + q 5 + q 9 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/16) * hm.m1 + (3/16) * hm.m2 + (-21/16) * hm.m3 + (3/16) * hm.m4 + (3/16) * hm.m5 + (3/16) * hm.m6 + (-1/8) * hm.m12 + (3/8) * hm.m13 + (-1/8) * hm.m14 + (-1/8) * hm.m15 + (-1/8) * hm.m16 + (3/8) * hm.m23 + (-1/8) * hm.m24 + (-1/8) * hm.m25 + (-1/8) * hm.m26 + (3/8) * hm.m34 + (3/8) * hm.m35 + (3/8) * hm.m36 + (-1/8) * hm.m45 + (-1/8) * hm.m46 + (-1/8) * hm.m56

theorem degree_sum_3 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 10 + p 13 + p 14 + p 3 + p 7 + q 1 + q 12 + q 2 + q 5 + q 8 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m2 + (1/4) * hm.m3 + (-3/4) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6

theorem degree_second_3 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    3*p 10 + 3*p 13 + 3*p 14 + 3*p 3 + 3*p 7 + q 1 + q 12 + q 2 + q 5 + q 8 = 1 := by
  linear_combination (1) * hm.n1 + (3/8) * hm.m1 + (3/8) * hm.m2 + (3/8) * hm.m3 + (3/8) * hm.m4 + (3/8) * hm.m5 + (3/8) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (-3/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m23 + (-3/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (-3/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36 + (-3/4) * hm.m45 + (-3/4) * hm.m46 + (1/4) * hm.m56

theorem bottom_degree_3 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 10 + p 13 + p 14 + p 3 + p 7 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/16) * hm.m1 + (1/16) * hm.m2 + (1/16) * hm.m3 + (9/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (1/8) * hm.m12 + (1/8) * hm.m13 + (-3/8) * hm.m14 + (1/8) * hm.m15 + (1/8) * hm.m16 + (1/8) * hm.m23 + (-3/8) * hm.m24 + (1/8) * hm.m25 + (1/8) * hm.m26 + (-3/8) * hm.m34 + (1/8) * hm.m35 + (1/8) * hm.m36 + (-3/8) * hm.m45 + (-3/8) * hm.m46 + (1/8) * hm.m56

theorem top_degree_3 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 1 + q 12 + q 2 + q 5 + q 8 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/16) * hm.m1 + (3/16) * hm.m2 + (3/16) * hm.m3 + (-21/16) * hm.m4 + (3/16) * hm.m5 + (3/16) * hm.m6 + (-1/8) * hm.m12 + (-1/8) * hm.m13 + (3/8) * hm.m14 + (-1/8) * hm.m15 + (-1/8) * hm.m16 + (-1/8) * hm.m23 + (3/8) * hm.m24 + (-1/8) * hm.m25 + (-1/8) * hm.m26 + (3/8) * hm.m34 + (-1/8) * hm.m35 + (-1/8) * hm.m36 + (3/8) * hm.m45 + (3/8) * hm.m46 + (-1/8) * hm.m56

theorem degree_sum_4 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 11 + p 13 + p 15 + p 4 + p 8 + q 0 + q 11 + q 2 + q 4 + q 7 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m2 + (1/4) * hm.m3 + (1/4) * hm.m4 + (-3/4) * hm.m5 + (1/4) * hm.m6

theorem degree_second_4 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    3*p 11 + 3*p 13 + 3*p 15 + 3*p 4 + 3*p 8 + q 0 + q 11 + q 2 + q 4 + q 7 = 1 := by
  linear_combination (1) * hm.n1 + (3/8) * hm.m1 + (3/8) * hm.m2 + (3/8) * hm.m3 + (3/8) * hm.m4 + (3/8) * hm.m5 + (3/8) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (-3/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (-3/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m34 + (-3/4) * hm.m35 + (1/4) * hm.m36 + (-3/4) * hm.m45 + (1/4) * hm.m46 + (-3/4) * hm.m56

theorem bottom_degree_4 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 11 + p 13 + p 15 + p 4 + p 8 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/16) * hm.m1 + (1/16) * hm.m2 + (1/16) * hm.m3 + (1/16) * hm.m4 + (9/16) * hm.m5 + (1/16) * hm.m6 + (1/8) * hm.m12 + (1/8) * hm.m13 + (1/8) * hm.m14 + (-3/8) * hm.m15 + (1/8) * hm.m16 + (1/8) * hm.m23 + (1/8) * hm.m24 + (-3/8) * hm.m25 + (1/8) * hm.m26 + (1/8) * hm.m34 + (-3/8) * hm.m35 + (1/8) * hm.m36 + (-3/8) * hm.m45 + (1/8) * hm.m46 + (-3/8) * hm.m56

theorem top_degree_4 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 0 + q 11 + q 2 + q 4 + q 7 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/16) * hm.m1 + (3/16) * hm.m2 + (3/16) * hm.m3 + (3/16) * hm.m4 + (-21/16) * hm.m5 + (3/16) * hm.m6 + (-1/8) * hm.m12 + (-1/8) * hm.m13 + (-1/8) * hm.m14 + (3/8) * hm.m15 + (-1/8) * hm.m16 + (-1/8) * hm.m23 + (-1/8) * hm.m24 + (3/8) * hm.m25 + (-1/8) * hm.m26 + (-1/8) * hm.m34 + (3/8) * hm.m35 + (-1/8) * hm.m36 + (3/8) * hm.m45 + (-1/8) * hm.m46 + (3/8) * hm.m56

theorem degree_sum_5 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 12 + p 14 + p 15 + p 5 + p 9 + q 0 + q 1 + q 10 + q 3 + q 6 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m2 + (1/4) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (-3/4) * hm.m6

theorem degree_second_5 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    3*p 12 + 3*p 14 + 3*p 15 + 3*p 5 + 3*p 9 + q 0 + q 1 + q 10 + q 3 + q 6 = 1 := by
  linear_combination (1) * hm.n1 + (3/8) * hm.m1 + (3/8) * hm.m2 + (3/8) * hm.m3 + (3/8) * hm.m4 + (3/8) * hm.m5 + (3/8) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (-3/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (-3/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (-3/4) * hm.m36 + (1/4) * hm.m45 + (-3/4) * hm.m46 + (-3/4) * hm.m56

theorem bottom_degree_5 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 12 + p 14 + p 15 + p 5 + p 9 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/16) * hm.m1 + (1/16) * hm.m2 + (1/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (9/16) * hm.m6 + (1/8) * hm.m12 + (1/8) * hm.m13 + (1/8) * hm.m14 + (1/8) * hm.m15 + (-3/8) * hm.m16 + (1/8) * hm.m23 + (1/8) * hm.m24 + (1/8) * hm.m25 + (-3/8) * hm.m26 + (1/8) * hm.m34 + (1/8) * hm.m35 + (-3/8) * hm.m36 + (1/8) * hm.m45 + (-3/8) * hm.m46 + (-3/8) * hm.m56

theorem top_degree_5 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 0 + q 1 + q 10 + q 3 + q 6 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/16) * hm.m1 + (3/16) * hm.m2 + (3/16) * hm.m3 + (3/16) * hm.m4 + (3/16) * hm.m5 + (-21/16) * hm.m6 + (-1/8) * hm.m12 + (-1/8) * hm.m13 + (-1/8) * hm.m14 + (-1/8) * hm.m15 + (3/8) * hm.m16 + (-1/8) * hm.m23 + (-1/8) * hm.m24 + (-1/8) * hm.m25 + (3/8) * hm.m26 + (-1/8) * hm.m34 + (-1/8) * hm.m35 + (3/8) * hm.m36 + (-1/8) * hm.m45 + (3/8) * hm.m46 + (3/8) * hm.m56

theorem matched_mass_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 = q 14 := by
  linear_combination (3/8) * hm.m1 + (3/8) * hm.m2 + (-1/8) * hm.m3 + (-1/8) * hm.m4 + (-1/8) * hm.m5 + (-1/8) * hm.m6 + (1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem matched_mass_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 2 = q 13 := by
  linear_combination (3/8) * hm.m1 + (-1/8) * hm.m2 + (3/8) * hm.m3 + (-1/8) * hm.m4 + (-1/8) * hm.m5 + (-1/8) * hm.m6 + (-1/4) * hm.m12 + (1/4) * hm.m13 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m16 + (-1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (-1/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem matched_mass_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 3 = q 12 := by
  linear_combination (3/8) * hm.m1 + (-1/8) * hm.m2 + (-1/8) * hm.m3 + (3/8) * hm.m4 + (-1/8) * hm.m5 + (-1/8) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m16 + (1/4) * hm.m23 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36 + (-1/4) * hm.m45 + (-1/4) * hm.m46 + (1/4) * hm.m56

theorem matched_mass_3 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 4 = q 11 := by
  linear_combination (3/8) * hm.m1 + (-1/8) * hm.m2 + (-1/8) * hm.m3 + (-1/8) * hm.m4 + (3/8) * hm.m5 + (-1/8) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (1/4) * hm.m36 + (-1/4) * hm.m45 + (1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_4 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 5 = q 10 := by
  linear_combination (3/8) * hm.m1 + (-1/8) * hm.m2 + (-1/8) * hm.m3 + (-1/8) * hm.m4 + (-1/8) * hm.m5 + (3/8) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (-1/4) * hm.m36 + (1/4) * hm.m45 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_5 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 6 = q 9 := by
  linear_combination (-1/8) * hm.m1 + (3/8) * hm.m2 + (3/8) * hm.m3 + (-1/8) * hm.m4 + (-1/8) * hm.m5 + (-1/8) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (-1/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem matched_mass_6 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 7 = q 8 := by
  linear_combination (-1/8) * hm.m1 + (3/8) * hm.m2 + (-1/8) * hm.m3 + (3/8) * hm.m4 + (-1/8) * hm.m5 + (-1/8) * hm.m6 + (-1/4) * hm.m12 + (1/4) * hm.m13 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m23 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36 + (-1/4) * hm.m45 + (-1/4) * hm.m46 + (1/4) * hm.m56

theorem matched_mass_7 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 8 = q 7 := by
  linear_combination (-1/8) * hm.m1 + (3/8) * hm.m2 + (-1/8) * hm.m3 + (-1/8) * hm.m4 + (3/8) * hm.m5 + (-1/8) * hm.m6 + (-1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m26 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (1/4) * hm.m36 + (-1/4) * hm.m45 + (1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_8 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 9 = q 6 := by
  linear_combination (-1/8) * hm.m1 + (3/8) * hm.m2 + (-1/8) * hm.m3 + (-1/8) * hm.m4 + (-1/8) * hm.m5 + (3/8) * hm.m6 + (-1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (-1/4) * hm.m36 + (1/4) * hm.m45 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_9 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 10 = q 5 := by
  linear_combination (-1/8) * hm.m1 + (-1/8) * hm.m2 + (3/8) * hm.m3 + (3/8) * hm.m4 + (-1/8) * hm.m5 + (-1/8) * hm.m6 + (1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (-1/4) * hm.m36 + (-1/4) * hm.m45 + (-1/4) * hm.m46 + (1/4) * hm.m56

theorem matched_mass_10 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 11 = q 4 := by
  linear_combination (-1/8) * hm.m1 + (-1/8) * hm.m2 + (3/8) * hm.m3 + (-1/8) * hm.m4 + (3/8) * hm.m5 + (-1/8) * hm.m6 + (1/4) * hm.m12 + (-1/4) * hm.m13 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m23 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m26 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (-1/4) * hm.m36 + (-1/4) * hm.m45 + (1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_11 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 12 = q 3 := by
  linear_combination (-1/8) * hm.m1 + (-1/8) * hm.m2 + (3/8) * hm.m3 + (-1/8) * hm.m4 + (-1/8) * hm.m5 + (3/8) * hm.m6 + (1/4) * hm.m12 + (-1/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (-1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (1/4) * hm.m36 + (1/4) * hm.m45 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_12 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 13 = q 2 := by
  linear_combination (-1/8) * hm.m1 + (-1/8) * hm.m2 + (-1/8) * hm.m3 + (3/8) * hm.m4 + (3/8) * hm.m5 + (-1/8) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m26 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (1/4) * hm.m36 + (1/4) * hm.m45 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_13 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 14 = q 1 := by
  linear_combination (-1/8) * hm.m1 + (-1/8) * hm.m2 + (-1/8) * hm.m3 + (3/8) * hm.m4 + (-1/8) * hm.m5 + (3/8) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (1/4) * hm.m23 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (-1/4) * hm.m36 + (-1/4) * hm.m45 + (1/4) * hm.m46 + (-1/4) * hm.m56

theorem matched_mass_14 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 15 = q 0 := by
  linear_combination (-1/8) * hm.m1 + (-1/8) * hm.m2 + (-1/8) * hm.m3 + (-1/8) * hm.m4 + (3/8) * hm.m5 + (3/8) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (-1/4) * hm.m36 + (-1/4) * hm.m45 + (-1/4) * hm.m46 + (1/4) * hm.m56

end
end MainTheory.Orbit17MomentDisplays
