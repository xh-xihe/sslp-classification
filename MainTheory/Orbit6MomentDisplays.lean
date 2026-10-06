import SixQubit.CodeOrbit6
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit6MomentDisplays
open scoped BigOperators
open SixQubit.Orbit6
noncomputable section
def bottom : Fin 22 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19,y20,y21]
def top : Fin 20 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19]
def edges : Fin 10 → Fin 5 × Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def singletonIndex : Fin 5 → Fin 20 := ![5,3,2,1,0]
def complementIndex : Fin 5 → Fin 20 := ![4,6,7,8,9]
def Moment (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) := MomentSystem (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) (p 10) (p 11) (p 12) (p 13) (p 14) (p 15) (p 16) (p 17) (p 18) (p 19) (p 20) (p 21) (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (q 6) (q 7) (q 8) (q 9) (q 10) (q 11) (q 12) (q 13) (q 14) (q 15) (q 16) (q 17) (q 18) (q 19)
theorem actual_words : S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel
theorem edge_coordinates : ∀ e : Fin 10,∀ j : Fin 5,
    bottom ⟨e.val+1,by omega⟩ j.succ=!(j=(edges e).1 ∨ j=(edges e).2) ∧
    bottom ⟨e.val+12,by omega⟩ j.succ=!(j=(edges e).1 ∨ j=(edges e).2) := by decide +kernel
theorem top_coordinates : ∀ i j : Fin 5,
    top (singletonIndex i) j.succ=(i=j) ∧
    top (complementIndex i) j.succ=!(i=j) := by decide +kernel
def bottomProb (c : SS.State 6 ℂ) : Fin 22 → ℝ := fun i => Complex.normSq (c (bottom i))
def topProb (d : SS.State 6 ℂ) : Fin 20 → ℝ := fun i => Complex.normSq (d (top i))
theorem physical_moments (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Moment (bottomProb c) (topProb d) := by
  exact moments c d hc hd hnc hnd hkl

theorem bottom_normalization (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 0 + p 1 + p 10 + p 11 + p 12 + p 13 + p 14 + p 15 + p 16 + p 17 + p 18 + p 19 + p 2 + p 20 + p 21 + p 3 + p 4 + p 5 + p 6 + p 7 + p 8 + p 9 = 1 := by
  linear_combination (1) * hm.n0

theorem top_normalization (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 0 + q 1 + q 10 + q 11 + q 12 + q 13 + q 14 + q 15 + q 16 + q 17 + q 18 + q 19 + q 2 + q 3 + q 4 + q 5 + q 6 + q 7 + q 8 + q 9 = 1 := by
  linear_combination (1) * hm.n1

theorem bottom_anchor (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 0 + p 11 = 1/3 := by
  linear_combination (1) * hm.n0 + (-2/3) * hm.n1 + (-2/3) * hm.m2 + (-2/3) * hm.m3 + (-2/3) * hm.m4 + (-2/3) * hm.m5 + (-2/3) * hm.m6 + (1/3) * hm.m23 + (1/3) * hm.m24 + (1/3) * hm.m25 + (1/3) * hm.m26 + (1/3) * hm.m34 + (1/3) * hm.m35 + (1/3) * hm.m36 + (1/3) * hm.m45 + (1/3) * hm.m46 + (1/3) * hm.m56

theorem bottom_edge_mass (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 1 + p 10 + p 12 + p 13 + p 14 + p 15 + p 16 + p 17 + p 18 + p 19 + p 2 + p 20 + p 21 + p 3 + p 4 + p 5 + p 6 + p 7 + p 8 + p 9 = 2/3 := by
  linear_combination (2/3) * hm.n1 + (2/3) * hm.m2 + (2/3) * hm.m3 + (2/3) * hm.m4 + (2/3) * hm.m5 + (2/3) * hm.m6 + (-1/3) * hm.m23 + (-1/3) * hm.m24 + (-1/3) * hm.m25 + (-1/3) * hm.m26 + (-1/3) * hm.m34 + (-1/3) * hm.m35 + (-1/3) * hm.m36 + (-1/3) * hm.m45 + (-1/3) * hm.m46 + (-1/3) * hm.m56

theorem top_singleton_mass (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 0 + q 1 + q 10 + q 11 + q 12 + q 13 + q 15 + q 2 + q 3 + q 5 = 2/3 := by
  linear_combination (2/3) * hm.n1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m4 + (-1/3) * hm.m5 + (-1/3) * hm.m6 + (1/3) * hm.m23 + (1/3) * hm.m24 + (1/3) * hm.m25 + (1/3) * hm.m26 + (1/3) * hm.m34 + (1/3) * hm.m35 + (1/3) * hm.m36 + (1/3) * hm.m45 + (1/3) * hm.m46 + (1/3) * hm.m56

theorem top_complement_mass (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 14 + q 16 + q 17 + q 18 + q 19 + q 4 + q 6 + q 7 + q 8 + q 9 = 1/3 := by
  linear_combination (1/3) * hm.n1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (1/3) * hm.m4 + (1/3) * hm.m5 + (1/3) * hm.m6 + (-1/3) * hm.m23 + (-1/3) * hm.m24 + (-1/3) * hm.m25 + (-1/3) * hm.m26 + (-1/3) * hm.m34 + (-1/3) * hm.m35 + (-1/3) * hm.m36 + (-1/3) * hm.m45 + (-1/3) * hm.m46 + (-1/3) * hm.m56

theorem singleton_mass_0 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 15 + q 5 = -q 14/2 - q 4/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (-5/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/3) * hm.m23 + (1/3) * hm.m24 + (1/3) * hm.m25 + (1/3) * hm.m26 + (-1/6) * hm.m34 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (-1/6) * hm.m45 + (-1/6) * hm.m46 + (-1/6) * hm.m56

theorem edge_degree_0 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 1 + p 12 + p 13 + p 14 + p 15 + p 2 + p 3 + p 4 = 3*q 14/2 + 3*q 4/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.m23 + (-1/3) * hm.m24 + (-1/3) * hm.m25 + (-1/3) * hm.m26 + (1/6) * hm.m34 + (1/6) * hm.m35 + (1/6) * hm.m36 + (1/6) * hm.m45 + (1/6) * hm.m46 + (1/6) * hm.m56

theorem singleton_mass_1 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 13 + q 3 = -q 16/2 - q 6/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (-5/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/3) * hm.m23 + (-1/6) * hm.m24 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (1/3) * hm.m34 + (1/3) * hm.m35 + (1/3) * hm.m36 + (-1/6) * hm.m45 + (-1/6) * hm.m46 + (-1/6) * hm.m56

theorem edge_degree_1 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 1 + p 12 + p 16 + p 17 + p 18 + p 5 + p 6 + p 7 = 3*q 16/2 + 3*q 6/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.m23 + (1/6) * hm.m24 + (1/6) * hm.m25 + (1/6) * hm.m26 + (-1/3) * hm.m34 + (-1/3) * hm.m35 + (-1/3) * hm.m36 + (1/6) * hm.m45 + (1/6) * hm.m46 + (1/6) * hm.m56

theorem singleton_mass_2 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 12 + q 2 = -q 17/2 - q 7/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (-5/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/6) * hm.m23 + (1/3) * hm.m24 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (1/3) * hm.m34 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (1/3) * hm.m45 + (1/3) * hm.m46 + (-1/6) * hm.m56

theorem edge_degree_2 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 13 + p 16 + p 19 + p 2 + p 20 + p 5 + p 8 + p 9 = 3*q 17/2 + 3*q 7/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/6) * hm.m23 + (-1/3) * hm.m24 + (1/6) * hm.m25 + (1/6) * hm.m26 + (-1/3) * hm.m34 + (1/6) * hm.m35 + (1/6) * hm.m36 + (-1/3) * hm.m45 + (-1/3) * hm.m46 + (1/6) * hm.m56

theorem singleton_mass_3 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 1 + q 11 = -q 18/2 - q 8/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (-5/6) * hm.m5 + (1/6) * hm.m6 + (-1/6) * hm.m23 + (-1/6) * hm.m24 + (1/3) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m34 + (1/3) * hm.m35 + (-1/6) * hm.m36 + (1/3) * hm.m45 + (-1/6) * hm.m46 + (1/3) * hm.m56

theorem edge_degree_3 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 10 + p 14 + p 17 + p 19 + p 21 + p 3 + p 6 + p 8 = 3*q 18/2 + 3*q 8/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/6) * hm.m23 + (1/6) * hm.m24 + (-1/3) * hm.m25 + (1/6) * hm.m26 + (1/6) * hm.m34 + (-1/3) * hm.m35 + (1/6) * hm.m36 + (-1/3) * hm.m45 + (1/6) * hm.m46 + (-1/3) * hm.m56

theorem singleton_mass_4 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    q 0 + q 10 = -q 19/2 - q 9/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (-5/6) * hm.m6 + (-1/6) * hm.m23 + (-1/6) * hm.m24 + (-1/6) * hm.m25 + (1/3) * hm.m26 + (-1/6) * hm.m34 + (-1/6) * hm.m35 + (1/3) * hm.m36 + (-1/6) * hm.m45 + (1/3) * hm.m46 + (1/3) * hm.m56

theorem edge_degree_4 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 10 + p 15 + p 18 + p 20 + p 21 + p 4 + p 7 + p 9 = 3*q 19/2 + 3*q 9/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/6) * hm.m23 + (1/6) * hm.m24 + (1/6) * hm.m25 + (-1/3) * hm.m26 + (1/6) * hm.m34 + (1/6) * hm.m35 + (-1/3) * hm.m36 + (1/6) * hm.m45 + (-1/3) * hm.m46 + (-1/3) * hm.m56

theorem edge_mass_0 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 1 + p 12 = q 14/2 + q 16/2 + q 4/2 + q 6/2 := by
  linear_combination (1/3) * hm.m23 + (-1/6) * hm.m24 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m34 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (1/3) * hm.m45 + (1/3) * hm.m46 + (1/3) * hm.m56

theorem edge_mass_1 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 13 + p 2 = q 14/2 + q 17/2 + q 4/2 + q 7/2 := by
  linear_combination (-1/6) * hm.m23 + (1/3) * hm.m24 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m34 + (1/3) * hm.m35 + (1/3) * hm.m36 + (-1/6) * hm.m45 + (-1/6) * hm.m46 + (1/3) * hm.m56

theorem edge_mass_2 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 14 + p 3 = q 14/2 + q 18/2 + q 4/2 + q 8/2 := by
  linear_combination (-1/6) * hm.m23 + (-1/6) * hm.m24 + (1/3) * hm.m25 + (-1/6) * hm.m26 + (1/3) * hm.m34 + (-1/6) * hm.m35 + (1/3) * hm.m36 + (-1/6) * hm.m45 + (1/3) * hm.m46 + (-1/6) * hm.m56

theorem edge_mass_3 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 15 + p 4 = q 14/2 + q 19/2 + q 4/2 + q 9/2 := by
  linear_combination (-1/6) * hm.m23 + (-1/6) * hm.m24 + (-1/6) * hm.m25 + (1/3) * hm.m26 + (1/3) * hm.m34 + (1/3) * hm.m35 + (-1/6) * hm.m36 + (1/3) * hm.m45 + (-1/6) * hm.m46 + (-1/6) * hm.m56

theorem edge_mass_4 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 16 + p 5 = q 16/2 + q 17/2 + q 6/2 + q 7/2 := by
  linear_combination (-1/6) * hm.m23 + (-1/6) * hm.m24 + (1/3) * hm.m25 + (1/3) * hm.m26 + (1/3) * hm.m34 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (-1/6) * hm.m45 + (-1/6) * hm.m46 + (1/3) * hm.m56

theorem edge_mass_5 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 17 + p 6 = q 16/2 + q 18/2 + q 6/2 + q 8/2 := by
  linear_combination (-1/6) * hm.m23 + (1/3) * hm.m24 + (-1/6) * hm.m25 + (1/3) * hm.m26 + (-1/6) * hm.m34 + (1/3) * hm.m35 + (-1/6) * hm.m36 + (-1/6) * hm.m45 + (1/3) * hm.m46 + (-1/6) * hm.m56

theorem edge_mass_6 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 18 + p 7 = q 16/2 + q 19/2 + q 6/2 + q 9/2 := by
  linear_combination (-1/6) * hm.m23 + (1/3) * hm.m24 + (1/3) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m34 + (-1/6) * hm.m35 + (1/3) * hm.m36 + (1/3) * hm.m45 + (-1/6) * hm.m46 + (-1/6) * hm.m56

theorem edge_mass_7 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 19 + p 8 = q 17/2 + q 18/2 + q 7/2 + q 8/2 := by
  linear_combination (1/3) * hm.m23 + (-1/6) * hm.m24 + (-1/6) * hm.m25 + (1/3) * hm.m26 + (-1/6) * hm.m34 + (-1/6) * hm.m35 + (1/3) * hm.m36 + (1/3) * hm.m45 + (-1/6) * hm.m46 + (-1/6) * hm.m56

theorem edge_mass_8 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 20 + p 9 = q 17/2 + q 19/2 + q 7/2 + q 9/2 := by
  linear_combination (1/3) * hm.m23 + (-1/6) * hm.m24 + (1/3) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m34 + (1/3) * hm.m35 + (-1/6) * hm.m36 + (-1/6) * hm.m45 + (1/3) * hm.m46 + (-1/6) * hm.m56

theorem edge_mass_9 (p : Fin 22 → ℝ) (q : Fin 20 → ℝ) (hm : Moment p q) :
    p 10 + p 21 = q 18/2 + q 19/2 + q 8/2 + q 9/2 := by
  linear_combination (1/3) * hm.m23 + (1/3) * hm.m24 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (1/3) * hm.m34 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (-1/6) * hm.m45 + (-1/6) * hm.m46 + (1/3) * hm.m56

end
end MainTheory.Orbit6MomentDisplays
