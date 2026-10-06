import SixQubit.CodeOrbit12
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit12MomentDisplays
open scoped BigOperators
open SixQubit.Orbit12
noncomputable section
def bottom : Fin 16 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def top : Fin 16 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]
def edges : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def Moment (p q : Fin 16 → ℝ) := MomentSystem (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) (p 10) (p 11) (p 12) (p 13) (p 14) (p 15) (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (q 6) (q 7) (q 8) (q 9) (q 10) (q 11) (q 12) (q 13) (q 14) (q 15)
theorem actual_words : S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel
theorem edge_coordinates : ∀ e : Fin 6,∀ j : Fin 4,
    bottom ⟨6-e.val,by omega⟩ j.succ.castSucc=(j=(edges e).1 ∨ j=(edges e).2) ∧
    top ⟨6-e.val,by omega⟩ j.succ.castSucc=(j=(edges e).1 ∨ j=(edges e).2) ∧
    bottom ⟨6-e.val,by omega⟩ 5=true ∧ top ⟨6-e.val,by omega⟩ 5=false := by decide +kernel
def bottomProb (c : SS.State 6 ℂ) : Fin 16 → ℝ := fun i => Complex.normSq (c (bottom i))
def topProb (d : SS.State 6 ℂ) : Fin 16 → ℝ := fun i => Complex.normSq (d (top i))
theorem physical_moments (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Moment (bottomProb c) (topProb d) := by
  exact moments c d hc hd hnc hnd hkl

theorem bottom_zero_anchor (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 0 + p 8 = 1/4 := by
  linear_combination (1) * hm.n0 + (-3/4) * hm.n1 + (-5/8) * hm.m2 + (-3/8) * hm.m3 + (-3/8) * hm.m4 + (-3/8) * hm.m5 + (-3/4) * hm.m6 + (1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m36 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem bottom_four_anchor (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 15 + p 7 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (-1/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/4) * hm.m6 + (1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m36 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem top_zero_anchor (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 0 + q 8 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (-3/4) * hm.m6 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m36 + (1/4) * hm.m46 + (1/4) * hm.m56

theorem top_four_anchor (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 15 + q 7 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/4) * hm.m6 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m36 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem zero_anchor_equality (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 0 + p 8 = q 0 + q 8 := by
  linear_combination (1) * hm.n0 + (-1) * hm.n1 + (-1) * hm.m2 + (-1/2) * hm.m3 + (-1/2) * hm.m4 + (-1/2) * hm.m5 + (1/2) * hm.m23 + (1/2) * hm.m24 + (1/2) * hm.m25

theorem four_anchor_equality (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 15 + p 7 = q 15 + q 7 := by
  linear_combination (-1/2) * hm.m2 + (1/2) * hm.m23 + (1/2) * hm.m24 + (1/2) * hm.m25

theorem half_angle_moment (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 10 + p 11 + p 12 + p 13 + p 14 + p 2 + p 3 + p 4 + p 5 + p 6 + p 9 = q 0 + q 15 + q 7 + q 8 := by
  linear_combination (1) * hm.m6

theorem bottom_edge_mass (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 10 + p 11 + p 12 + p 13 + p 14 + p 2 + p 3 + p 4 + p 5 + p 6 + p 9 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (3/4) * hm.m2 + (1/4) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (1/2) * hm.m6 + (-1/2) * hm.m23 + (-1/2) * hm.m24 + (-1/2) * hm.m25

theorem top_edge_mass (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 1 + q 10 + q 11 + q 12 + q 13 + q 14 + q 2 + q 3 + q 4 + q 5 + q 6 + q 9 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (-3/4) * hm.m2 + (-1/4) * hm.m3 + (-1/4) * hm.m4 + (-1/4) * hm.m5 + (1/2) * hm.m6 + (1/2) * hm.m23 + (1/2) * hm.m24 + (1/2) * hm.m25

theorem bottom_anchor_mass (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 0 + p 15 + p 7 + p 8 = 1/2 := by
  linear_combination (1) * hm.n0 + (-1/2) * hm.n1 + (-3/4) * hm.m2 + (-1/4) * hm.m3 + (-1/4) * hm.m4 + (-1/4) * hm.m5 + (-1/2) * hm.m6 + (1/2) * hm.m23 + (1/2) * hm.m24 + (1/2) * hm.m25

theorem top_anchor_mass (p q : Fin 16 → ℝ) (hm : Moment p q) :
    q 0 + q 15 + q 7 + q 8 = 1/2 := by
  linear_combination (1/2) * hm.n1 + (3/4) * hm.m2 + (1/4) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (-1/2) * hm.m6 + (-1/2) * hm.m23 + (-1/2) * hm.m24 + (-1/2) * hm.m25

theorem representative_mass (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 12 + p 13 + p 14 + p 4 + p 5 + p 6 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/4) * hm.m6 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (3/4) * hm.m26 + (-1/4) * hm.m36 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem edge_degree_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 12 + p 13 + p 14 + p 4 + p 5 + p 6 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/4) * hm.m6 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (3/4) * hm.m26 + (-1/4) * hm.m36 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem edge_degree_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 10 + p 11 + p 14 + p 2 + p 3 + p 6 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/4) * hm.m6 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (3/4) * hm.m36 + (-1/4) * hm.m46 + (-1/4) * hm.m56

theorem edge_degree_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 11 + p 13 + p 3 + p 5 + p 9 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/4) * hm.m6 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m36 + (3/4) * hm.m46 + (-1/4) * hm.m56

theorem edge_degree_3 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 10 + p 12 + p 2 + p 4 + p 9 = 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/8) * hm.m2 + (1/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/4) * hm.m6 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m36 + (-1/4) * hm.m46 + (3/4) * hm.m56

theorem matched_mass_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 14 + p 6 = q 14 + q 6 := by
  linear_combination (1/2) * hm.m2 + (1/2) * hm.m23 + (-1/2) * hm.m24 + (-1/2) * hm.m25

theorem matched_mass_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 13 + p 5 = q 13 + q 5 := by
  linear_combination (1/2) * hm.m2 + (-1/2) * hm.m23 + (1/2) * hm.m24 + (-1/2) * hm.m25

theorem matched_mass_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 12 + p 4 = q 12 + q 4 := by
  linear_combination (1/2) * hm.m2 + (-1/2) * hm.m23 + (-1/2) * hm.m24 + (1/2) * hm.m25

theorem matched_mass_3 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 11 + p 3 = q 11 + q 3 := by
  linear_combination (1/2) * hm.m3 + (1/2) * hm.m4 + (-1/2) * hm.m5 + (-1/2) * hm.m23 + (-1/2) * hm.m24 + (1/2) * hm.m25

theorem matched_mass_4 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 10 + p 2 = q 10 + q 2 := by
  linear_combination (1/2) * hm.m3 + (-1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m23 + (1/2) * hm.m24 + (-1/2) * hm.m25

theorem matched_mass_5 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 1 + p 9 = q 1 + q 9 := by
  linear_combination (-1/2) * hm.m3 + (1/2) * hm.m4 + (1/2) * hm.m5 + (1/2) * hm.m23 + (-1/2) * hm.m24 + (-1/2) * hm.m25

theorem complementary_mass_0 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 14 + p 6 = p 1 + p 9 := by
  linear_combination (1/2) * hm.m26 + (1/2) * hm.m36 + (-1/2) * hm.m46 + (-1/2) * hm.m56

theorem complementary_mass_1 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 13 + p 5 = p 10 + p 2 := by
  linear_combination (1/2) * hm.m26 + (-1/2) * hm.m36 + (1/2) * hm.m46 + (-1/2) * hm.m56

theorem complementary_mass_2 (p q : Fin 16 → ℝ) (hm : Moment p q) :
    p 12 + p 4 = p 11 + p 3 := by
  linear_combination (1/2) * hm.m26 + (-1/2) * hm.m36 + (-1/2) * hm.m46 + (1/2) * hm.m56

end
end MainTheory.Orbit12MomentDisplays
