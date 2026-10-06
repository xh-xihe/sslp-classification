import SixQubit.CodeOrbit30
set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace MainTheory.Orbit30PrintedMoments
open SixQubit.Orbit30
open scoped BigOperators
noncomputable section
def bottom : Fin 16 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def top : Fin 16 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]
def complementIndex : Fin 16 → Fin 16 := fun i => ⟨15-i.val,by omega⟩
theorem actual_fibers : S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top ∧
    (∀ i,top (complementIndex i)=SS.complement (bottom i)) := by decide +kernel
def Moment (p t : Fin 16 → ℝ) : Prop := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (p ⟨10,by decide⟩) (p ⟨11,by decide⟩) (p ⟨12,by decide⟩) (p ⟨13,by decide⟩) (p ⟨14,by decide⟩) (p ⟨15,by decide⟩) (t ⟨15,by decide⟩) (t ⟨14,by decide⟩) (t ⟨13,by decide⟩) (t ⟨12,by decide⟩) (t ⟨11,by decide⟩) (t ⟨10,by decide⟩) (t ⟨9,by decide⟩) (t ⟨8,by decide⟩) (t ⟨7,by decide⟩) (t ⟨6,by decide⟩) (t ⟨5,by decide⟩) (t ⟨4,by decide⟩) (t ⟨3,by decide⟩) (t ⟨2,by decide⟩) (t ⟨1,by decide⟩) (t ⟨0,by decide⟩)
def coordinateSum (p : Fin 16 → ℝ) : Fin 6 → ℝ :=
  ![p ⟨8,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩,p ⟨4,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩,p ⟨2,by decide⟩ + p ⟨3,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩,p ⟨1,by decide⟩ + p ⟨3,by decide⟩ + p ⟨5,by decide⟩ + p ⟨7,by decide⟩ + p ⟨9,by decide⟩ + p ⟨11,by decide⟩ + p ⟨13,by decide⟩ + p ⟨15,by decide⟩,p ⟨3,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩,p ⟨1,by decide⟩ + p ⟨2,by decide⟩ + p ⟨4,by decide⟩ + p ⟨7,by decide⟩ + p ⟨8,by decide⟩ + p ⟨11,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩]
theorem literal_coordinate_sum (p : Fin 16 → ℝ) (j : Fin 6) :
    coordinateSum p j=∑ i,p i*(if bottom i j then (1 : ℝ) else 0) := by
  fin_cases j <;> norm_num [coordinateSum,bottom,y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,bs,Fin.sum_univ_succ,Fin.succ] <;> ring
def totalSum (p : Fin 16 → ℝ) : ℝ := p ⟨0,by decide⟩ + p ⟨1,by decide⟩ + p ⟨2,by decide⟩ + p ⟨3,by decide⟩ + p ⟨4,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨8,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩
theorem literal_total_sum (p : Fin 16 → ℝ) : totalSum p=∑ i,p i := by
  simp [totalSum,Fin.sum_univ_succ,Fin.succ]
  ring
def Normal (p t : Fin 16 → ℝ) : Prop :=
  t=p ∧ (∀ i,0 ≤ p i) ∧ totalSum p=1 ∧ (∀ j,coordinateSum p j=1/2)
theorem complement0 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨0,by decide⟩=p ⟨0,by decide⟩ := by
  linear_combination (-1 : ℝ)*hm.n0 + (1 : ℝ)*hm.n1 + (1 : ℝ)*hm.m1 + (1 : ℝ)*hm.m2 + (1 : ℝ)*hm.m3 + (1 : ℝ)*hm.m4 + (-1/2 : ℝ)*hm.m5 + (1/2 : ℝ)*hm.m6 + (-1/2 : ℝ)*hm.m12 + (-1/2 : ℝ)*hm.m13 + (-1/2 : ℝ)*hm.m14 + (-1/2 : ℝ)*hm.m16 + (-1/2 : ℝ)*hm.m23 + (-1/2 : ℝ)*hm.m24 + (-1/2 : ℝ)*hm.m26 + (-1/2 : ℝ)*hm.m34 + (-1/2 : ℝ)*hm.m36 + (-1/2 : ℝ)*hm.m46 + (1 : ℝ)*hm.m56
theorem complement1 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨1,by decide⟩=p ⟨1,by decide⟩ := by
  linear_combination (1/2 : ℝ)*hm.m5 + (-1/2 : ℝ)*hm.m6 + (-1/2 : ℝ)*hm.m12 + (-1/2 : ℝ)*hm.m13 + (1/2 : ℝ)*hm.m14 + (1/2 : ℝ)*hm.m16 + (-1/2 : ℝ)*hm.m23 + (1/2 : ℝ)*hm.m24 + (1/2 : ℝ)*hm.m26 + (1/2 : ℝ)*hm.m34 + (1/2 : ℝ)*hm.m36 + (-1 : ℝ)*hm.m45 + (-1/2 : ℝ)*hm.m46
theorem complement2 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨2,by decide⟩=p ⟨2,by decide⟩ := by
  linear_combination (1/2 : ℝ)*hm.m5 + (-1/2 : ℝ)*hm.m6 + (-1/2 : ℝ)*hm.m12 + (1/2 : ℝ)*hm.m13 + (-1/2 : ℝ)*hm.m14 + (1/2 : ℝ)*hm.m16 + (1/2 : ℝ)*hm.m23 + (-1/2 : ℝ)*hm.m24 + (1/2 : ℝ)*hm.m26 + (1/2 : ℝ)*hm.m34 + (-1 : ℝ)*hm.m35 + (-1/2 : ℝ)*hm.m36 + (1/2 : ℝ)*hm.m46
theorem complement3 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨3,by decide⟩=p ⟨3,by decide⟩ := by
  linear_combination (-1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (-5/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (2/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (2/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (-1/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (-1/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (1/3 : ℝ)*hm.m56
theorem complement4 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨4,by decide⟩=p ⟨4,by decide⟩ := by
  linear_combination (1/2 : ℝ)*hm.m5 + (-1/2 : ℝ)*hm.m6 + (1/2 : ℝ)*hm.m12 + (-1/2 : ℝ)*hm.m13 + (-1/2 : ℝ)*hm.m14 + (1/2 : ℝ)*hm.m16 + (1/2 : ℝ)*hm.m23 + (1/2 : ℝ)*hm.m24 + (-1 : ℝ)*hm.m25 + (-1/2 : ℝ)*hm.m26 + (-1/2 : ℝ)*hm.m34 + (1/2 : ℝ)*hm.m36 + (1/2 : ℝ)*hm.m46
theorem complement5 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨5,by decide⟩=p ⟨5,by decide⟩ := by
  linear_combination (-1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (-5/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (2/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (-1/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (2/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (-1/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (1/3 : ℝ)*hm.m56
theorem complement6 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨6,by decide⟩=p ⟨6,by decide⟩ := by
  linear_combination (-1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (-5/6 : ℝ)*hm.m14 + (2/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (-1/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (-1/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (2/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (1/3 : ℝ)*hm.m56
theorem complement7 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨7,by decide⟩=p ⟨7,by decide⟩ := by
  linear_combination (-1 : ℝ)*hm.m1 + (1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (2/3 : ℝ)*hm.m15 + (5/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (-1/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (-1/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (-1/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (-2/3 : ℝ)*hm.m56
theorem complement8 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨8,by decide⟩=p ⟨8,by decide⟩ := by
  linear_combination (1/2 : ℝ)*hm.m5 + (-1/2 : ℝ)*hm.m6 + (1/2 : ℝ)*hm.m12 + (1/2 : ℝ)*hm.m13 + (1/2 : ℝ)*hm.m14 + (-1 : ℝ)*hm.m15 + (-1/2 : ℝ)*hm.m16 + (-1/2 : ℝ)*hm.m23 + (-1/2 : ℝ)*hm.m24 + (1/2 : ℝ)*hm.m26 + (-1/2 : ℝ)*hm.m34 + (1/2 : ℝ)*hm.m36 + (1/2 : ℝ)*hm.m46
theorem complement9 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨9,by decide⟩=p ⟨9,by decide⟩ := by
  linear_combination (-1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (-1/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (-5/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (2/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (2/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (-1/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (1/3 : ℝ)*hm.m56
theorem complement10 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨10,by decide⟩=p ⟨10,by decide⟩ := by
  linear_combination (-1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (-1/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (-5/6 : ℝ)*hm.m24 + (2/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (-1/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (2/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (1/3 : ℝ)*hm.m56
theorem complement11 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨11,by decide⟩=p ⟨11,by decide⟩ := by
  linear_combination (-1 : ℝ)*hm.m2 + (1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (-1/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (2/3 : ℝ)*hm.m25 + (5/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (-1/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (-1/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (-2/3 : ℝ)*hm.m56
theorem complement12 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨12,by decide⟩=p ⟨12,by decide⟩ := by
  linear_combination (-1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (-1/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (-1/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (-5/6 : ℝ)*hm.m34 + (2/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (2/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (1/3 : ℝ)*hm.m56
theorem complement13 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨13,by decide⟩=p ⟨13,by decide⟩ := by
  linear_combination (-1 : ℝ)*hm.m3 + (1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (-1/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (-1/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (2/3 : ℝ)*hm.m35 + (5/6 : ℝ)*hm.m36 + (-1/3 : ℝ)*hm.m45 + (-1/6 : ℝ)*hm.m46 + (-2/3 : ℝ)*hm.m56
theorem complement14 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨14,by decide⟩=p ⟨14,by decide⟩ := by
  linear_combination (-1 : ℝ)*hm.m4 + (1/2 : ℝ)*hm.m5 + (1/6 : ℝ)*hm.m6 + (1/6 : ℝ)*hm.m12 + (1/6 : ℝ)*hm.m13 + (1/6 : ℝ)*hm.m14 + (-1/3 : ℝ)*hm.m15 + (-1/6 : ℝ)*hm.m16 + (1/6 : ℝ)*hm.m23 + (1/6 : ℝ)*hm.m24 + (-1/3 : ℝ)*hm.m25 + (-1/6 : ℝ)*hm.m26 + (1/6 : ℝ)*hm.m34 + (-1/3 : ℝ)*hm.m35 + (-1/6 : ℝ)*hm.m36 + (2/3 : ℝ)*hm.m45 + (5/6 : ℝ)*hm.m46 + (-2/3 : ℝ)*hm.m56
theorem complement15 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    t ⟨15,by decide⟩=p ⟨15,by decide⟩ := by
  linear_combination (-1/2 : ℝ)*hm.m5 + (-1/6 : ℝ)*hm.m6 + (-1/6 : ℝ)*hm.m12 + (-1/6 : ℝ)*hm.m13 + (-1/6 : ℝ)*hm.m14 + (1/3 : ℝ)*hm.m15 + (1/6 : ℝ)*hm.m16 + (-1/6 : ℝ)*hm.m23 + (-1/6 : ℝ)*hm.m24 + (1/3 : ℝ)*hm.m25 + (1/6 : ℝ)*hm.m26 + (-1/6 : ℝ)*hm.m34 + (1/3 : ℝ)*hm.m35 + (1/6 : ℝ)*hm.m36 + (1/3 : ℝ)*hm.m45 + (1/6 : ℝ)*hm.m46 + (-1/3 : ℝ)*hm.m56
theorem balance0 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    coordinateSum p ⟨0,by decide⟩=1/2 := by
  change p ⟨8,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩=1/2
  linear_combination (1/2 : ℝ)*hm.n1 + (1/2 : ℝ)*hm.m1 + (1/2 : ℝ)*hm.m2 + (1/2 : ℝ)*hm.m3 + (1/2 : ℝ)*hm.m4 + (-1/6 : ℝ)*hm.m6 + (-2/3 : ℝ)*hm.m12 + (-2/3 : ℝ)*hm.m13 + (-2/3 : ℝ)*hm.m14 + (4/3 : ℝ)*hm.m15 + (2/3 : ℝ)*hm.m16 + (1/3 : ℝ)*hm.m23 + (1/3 : ℝ)*hm.m24 + (-2/3 : ℝ)*hm.m25 + (-1/3 : ℝ)*hm.m26 + (1/3 : ℝ)*hm.m34 + (-2/3 : ℝ)*hm.m35 + (-1/3 : ℝ)*hm.m36 + (-2/3 : ℝ)*hm.m45 + (-1/3 : ℝ)*hm.m46 + (2/3 : ℝ)*hm.m56
theorem balance1 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    coordinateSum p ⟨1,by decide⟩=1/2 := by
  change p ⟨4,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩=1/2
  linear_combination (1/2 : ℝ)*hm.n1 + (1/2 : ℝ)*hm.m1 + (1/2 : ℝ)*hm.m2 + (1/2 : ℝ)*hm.m3 + (1/2 : ℝ)*hm.m4 + (-1/6 : ℝ)*hm.m6 + (-2/3 : ℝ)*hm.m12 + (1/3 : ℝ)*hm.m13 + (1/3 : ℝ)*hm.m14 + (-2/3 : ℝ)*hm.m15 + (-1/3 : ℝ)*hm.m16 + (-2/3 : ℝ)*hm.m23 + (-2/3 : ℝ)*hm.m24 + (4/3 : ℝ)*hm.m25 + (2/3 : ℝ)*hm.m26 + (1/3 : ℝ)*hm.m34 + (-2/3 : ℝ)*hm.m35 + (-1/3 : ℝ)*hm.m36 + (-2/3 : ℝ)*hm.m45 + (-1/3 : ℝ)*hm.m46 + (2/3 : ℝ)*hm.m56
theorem balance2 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    coordinateSum p ⟨2,by decide⟩=1/2 := by
  change p ⟨2,by decide⟩ + p ⟨3,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩=1/2
  linear_combination (1/2 : ℝ)*hm.n1 + (1/2 : ℝ)*hm.m1 + (1/2 : ℝ)*hm.m2 + (1/2 : ℝ)*hm.m3 + (1/2 : ℝ)*hm.m4 + (-1/6 : ℝ)*hm.m6 + (1/3 : ℝ)*hm.m12 + (-2/3 : ℝ)*hm.m13 + (1/3 : ℝ)*hm.m14 + (-2/3 : ℝ)*hm.m15 + (-1/3 : ℝ)*hm.m16 + (-2/3 : ℝ)*hm.m23 + (1/3 : ℝ)*hm.m24 + (-2/3 : ℝ)*hm.m25 + (-1/3 : ℝ)*hm.m26 + (-2/3 : ℝ)*hm.m34 + (4/3 : ℝ)*hm.m35 + (2/3 : ℝ)*hm.m36 + (-2/3 : ℝ)*hm.m45 + (-1/3 : ℝ)*hm.m46 + (2/3 : ℝ)*hm.m56
theorem balance3 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    coordinateSum p ⟨3,by decide⟩=1/2 := by
  change p ⟨1,by decide⟩ + p ⟨3,by decide⟩ + p ⟨5,by decide⟩ + p ⟨7,by decide⟩ + p ⟨9,by decide⟩ + p ⟨11,by decide⟩ + p ⟨13,by decide⟩ + p ⟨15,by decide⟩=1/2
  linear_combination (1/2 : ℝ)*hm.n1 + (1/2 : ℝ)*hm.m1 + (1/2 : ℝ)*hm.m2 + (1/2 : ℝ)*hm.m3 + (1/2 : ℝ)*hm.m4 + (-1/6 : ℝ)*hm.m6 + (1/3 : ℝ)*hm.m12 + (1/3 : ℝ)*hm.m13 + (-2/3 : ℝ)*hm.m14 + (-2/3 : ℝ)*hm.m15 + (-1/3 : ℝ)*hm.m16 + (1/3 : ℝ)*hm.m23 + (-2/3 : ℝ)*hm.m24 + (-2/3 : ℝ)*hm.m25 + (-1/3 : ℝ)*hm.m26 + (-2/3 : ℝ)*hm.m34 + (-2/3 : ℝ)*hm.m35 + (-1/3 : ℝ)*hm.m36 + (4/3 : ℝ)*hm.m45 + (2/3 : ℝ)*hm.m46 + (2/3 : ℝ)*hm.m56
theorem balance4 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    coordinateSum p ⟨4,by decide⟩=1/2 := by
  change p ⟨3,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩=1/2
  linear_combination (1/2 : ℝ)*hm.n1 + (1/2 : ℝ)*hm.m1 + (1/2 : ℝ)*hm.m2 + (1/2 : ℝ)*hm.m3 + (1/2 : ℝ)*hm.m4 + (1 : ℝ)*hm.m5 + (-5/6 : ℝ)*hm.m6 + (-1/3 : ℝ)*hm.m12 + (-1/3 : ℝ)*hm.m13 + (-1/3 : ℝ)*hm.m14 + (-1/3 : ℝ)*hm.m15 + (1/3 : ℝ)*hm.m16 + (-1/3 : ℝ)*hm.m23 + (-1/3 : ℝ)*hm.m24 + (-1/3 : ℝ)*hm.m25 + (1/3 : ℝ)*hm.m26 + (-1/3 : ℝ)*hm.m34 + (-1/3 : ℝ)*hm.m35 + (1/3 : ℝ)*hm.m36 + (-1/3 : ℝ)*hm.m45 + (1/3 : ℝ)*hm.m46 + (1/3 : ℝ)*hm.m56
theorem balance5 (p t : Fin 16 → ℝ) (hm : Moment p t) :
    coordinateSum p ⟨5,by decide⟩=1/2 := by
  change p ⟨1,by decide⟩ + p ⟨2,by decide⟩ + p ⟨4,by decide⟩ + p ⟨7,by decide⟩ + p ⟨8,by decide⟩ + p ⟨11,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩=1/2
  linear_combination (1/2 : ℝ)*hm.n1 + (1/2 : ℝ)*hm.m1 + (1/2 : ℝ)*hm.m2 + (1/2 : ℝ)*hm.m3 + (1/2 : ℝ)*hm.m4 + (-2 : ℝ)*hm.m5 + (7/6 : ℝ)*hm.m6 + (-1/3 : ℝ)*hm.m12 + (-1/3 : ℝ)*hm.m13 + (-1/3 : ℝ)*hm.m14 + (2/3 : ℝ)*hm.m15 + (-2/3 : ℝ)*hm.m16 + (-1/3 : ℝ)*hm.m23 + (-1/3 : ℝ)*hm.m24 + (2/3 : ℝ)*hm.m25 + (-2/3 : ℝ)*hm.m26 + (-1/3 : ℝ)*hm.m34 + (2/3 : ℝ)*hm.m35 + (-2/3 : ℝ)*hm.m36 + (2/3 : ℝ)*hm.m45 + (-2/3 : ℝ)*hm.m46 + (4/3 : ℝ)*hm.m56
theorem normal_of_moment (p t : Fin 16 → ℝ) (hm : Moment p t) : Normal p t := by
  refine ⟨?_,?_,?_,?_⟩
  · funext i
    fin_cases i
    · exact complement0 p t hm
    · exact complement1 p t hm
    · exact complement2 p t hm
    · exact complement3 p t hm
    · exact complement4 p t hm
    · exact complement5 p t hm
    · exact complement6 p t hm
    · exact complement7 p t hm
    · exact complement8 p t hm
    · exact complement9 p t hm
    · exact complement10 p t hm
    · exact complement11 p t hm
    · exact complement12 p t hm
    · exact complement13 p t hm
    · exact complement14 p t hm
    · exact complement15 p t hm
  · intro i
    fin_cases i
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
  · exact hm.n0
  · intro j
    fin_cases j
    · exact balance0 p t hm
    · exact balance1 p t hm
    · exact balance2 p t hm
    · exact balance3 p t hm
    · exact balance4 p t hm
    · exact balance5 p t hm
theorem moment_of_normal (p t : Fin 16 → ℝ) (h : Normal p t) : Moment p t := by
  rcases h with ⟨ht,hn,hs,hb⟩
  rw [ht]
  have hb0 := hb ⟨0,by decide⟩
  change p ⟨8,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩=1/2 at hb0
  have hb1 := hb ⟨1,by decide⟩
  change p ⟨4,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩=1/2 at hb1
  have hb2 := hb ⟨2,by decide⟩
  change p ⟨2,by decide⟩ + p ⟨3,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩=1/2 at hb2
  have hb3 := hb ⟨3,by decide⟩
  change p ⟨1,by decide⟩ + p ⟨3,by decide⟩ + p ⟨5,by decide⟩ + p ⟨7,by decide⟩ + p ⟨9,by decide⟩ + p ⟨11,by decide⟩ + p ⟨13,by decide⟩ + p ⟨15,by decide⟩=1/2 at hb3
  have hb4 := hb ⟨4,by decide⟩
  change p ⟨3,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩=1/2 at hb4
  have hb5 := hb ⟨5,by decide⟩
  change p ⟨1,by decide⟩ + p ⟨2,by decide⟩ + p ⟨4,by decide⟩ + p ⟨7,by decide⟩ + p ⟨8,by decide⟩ + p ⟨11,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩=1/2 at hb5
  change p ⟨0,by decide⟩ + p ⟨1,by decide⟩ + p ⟨2,by decide⟩ + p ⟨3,by decide⟩ + p ⟨4,by decide⟩ + p ⟨5,by decide⟩ + p ⟨6,by decide⟩ + p ⟨7,by decide⟩ + p ⟨8,by decide⟩ + p ⟨9,by decide⟩ + p ⟨10,by decide⟩ + p ⟨11,by decide⟩ + p ⟨12,by decide⟩ + p ⟨13,by decide⟩ + p ⟨14,by decide⟩ + p ⟨15,by decide⟩=1 at hs
  unfold Moment
  constructor
  · linarith only [hs]
  · linarith only [hs]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · linarith only [hs,hb0,hb1,hb2,hb3,hb4,hb5]
  · exact hn ⟨0,by decide⟩
  · exact hn ⟨1,by decide⟩
  · exact hn ⟨2,by decide⟩
  · exact hn ⟨3,by decide⟩
  · exact hn ⟨4,by decide⟩
  · exact hn ⟨5,by decide⟩
  · exact hn ⟨6,by decide⟩
  · exact hn ⟨7,by decide⟩
  · exact hn ⟨8,by decide⟩
  · exact hn ⟨9,by decide⟩
  · exact hn ⟨10,by decide⟩
  · exact hn ⟨11,by decide⟩
  · exact hn ⟨12,by decide⟩
  · exact hn ⟨13,by decide⟩
  · exact hn ⟨14,by decide⟩
  · exact hn ⟨15,by decide⟩
  · exact hn ⟨15,by decide⟩
  · exact hn ⟨14,by decide⟩
  · exact hn ⟨13,by decide⟩
  · exact hn ⟨12,by decide⟩
  · exact hn ⟨11,by decide⟩
  · exact hn ⟨10,by decide⟩
  · exact hn ⟨9,by decide⟩
  · exact hn ⟨8,by decide⟩
  · exact hn ⟨7,by decide⟩
  · exact hn ⟨6,by decide⟩
  · exact hn ⟨5,by decide⟩
  · exact hn ⟨4,by decide⟩
  · exact hn ⟨3,by decide⟩
  · exact hn ⟨2,by decide⟩
  · exact hn ⟨1,by decide⟩
  · exact hn ⟨0,by decide⟩
theorem complete_normal (p t : Fin 16 → ℝ) : Moment p t ↔ Normal p t :=
  ⟨normal_of_moment p t,moment_of_normal p t⟩
def bottomProbability (c : SS.State 6 ℂ) : Fin 16 → ℝ := fun i => Complex.normSq (c (bottom i))
def topProbability (d : SS.State 6 ℂ) : Fin 16 → ℝ :=
  fun i => Complex.normSq (d (top (complementIndex i)))
theorem physical_moments (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3) :
    Moment (bottomProbability c) (topProbability d) := by
  exact SixQubit.Orbit30.moments c d hc hd hnc hnd hkl
theorem physical_normal (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3) :
    Normal (bottomProbability c) (topProbability d) :=
  normal_of_moment _ _ (physical_moments c d hc hd hnc hnd hkl)
end
end MainTheory.Orbit30PrintedMoments
