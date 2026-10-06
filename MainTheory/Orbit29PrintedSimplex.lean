import MainTheory.Orbit29PhysicalPairReduction
import MainTheory.Orbit29PrintedFaceAudit

/-! Literal per-string probabilities and the exact reduced three-simplex.
Elimination identities are rational linear combinations checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace MainTheory.Orbit29PrintedSimplex
open SixQubit.Orbit29
open scoped BigOperators
noncomputable section

def Moment (q r : Fin 16 → ℝ) : Prop :=
  MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩)
    (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) (r ⟨12,by decide⟩) (r ⟨13,by decide⟩) (r ⟨14,by decide⟩) (r ⟨15,by decide⟩)
def bottomIndex : Fin 6 → Fin 2 → Fin 16 :=
  ![![⟨2,by decide⟩,⟨3,by decide⟩],![⟨4,by decide⟩,⟨5,by decide⟩],![⟨6,by decide⟩,⟨7,by decide⟩],![⟨8,by decide⟩,⟨9,by decide⟩],![⟨10,by decide⟩,⟨11,by decide⟩],![⟨12,by decide⟩,⟨13,by decide⟩]]
def highIndex : Fin 4 → Fin 2 → Fin 16 :=
  ![![⟨6,by decide⟩,⟨7,by decide⟩],![⟨10,by decide⟩,⟨11,by decide⟩],![⟨12,by decide⟩,⟨13,by decide⟩],![⟨14,by decide⟩,⟨15,by decide⟩]]
def normalQ (a b c : ℝ) : Fin 16 → ℝ := ![0,0,b+c,b+c,a+c,a+c,a+b,a+b,1/8-a-b,1/8-a-b,1/8-a-c,1/8-a-c,1/8-b-c,1/8-b-c,1/8,1/8]
def normalR (a b c : ℝ) : Fin 16 → ℝ := ![c,c,b,b,a,a,a+b+c,a+b+c,1/8-a-b-c,1/8-a-b-c,1/8-a,1/8-a,1/8-b,1/8-b,1/8-c,1/8-c]

theorem omitted_zero (q r : Fin 16 → ℝ) (h : Moment q r) :
    q ⟨0,by decide⟩=0 ∧ q ⟨1,by decide⟩=0 := by
  have hs : q ⟨0,by decide⟩+q ⟨1,by decide⟩=0 := by
    linear_combination (1 : ℝ)*h.n0 + (-1 : ℝ)*h.n1 + (-1 : ℝ)*h.m1 + (-1 : ℝ)*h.m2 + (-1 : ℝ)*h.m3 + (-1 : ℝ)*h.m4 + (1/2 : ℝ)*h.m5 + (1/2 : ℝ)*h.m6 + (1/2 : ℝ)*h.c12 + (1/2 : ℝ)*h.c13 + (1/2 : ℝ)*h.c14 + (1/2 : ℝ)*h.c23 + (1/2 : ℝ)*h.c24 + (1/2 : ℝ)*h.c34 + (-1 : ℝ)*h.c56
  constructor <;> linarith [h.nq0,h.nq1]

theorem reduced_normal (q r : Fin 16 → ℝ) (h : Moment q r)
    (hb : ∀ i, q (bottomIndex i 0)=q (bottomIndex i 1))
    (ht : ∀ i, r (highIndex i 0)=r (highIndex i 1)) :
    q=normalQ (r ⟨4,by decide⟩) (r ⟨2,by decide⟩) (r ⟨0,by decide⟩) ∧
    r=normalR (r ⟨4,by decide⟩) (r ⟨2,by decide⟩) (r ⟨0,by decide⟩) := by
  have hz := omitted_zero q r h
  have hb0 := hb ⟨0,by decide⟩
  change q ⟨2,by decide⟩=q ⟨3,by decide⟩ at hb0
  have hb1 := hb ⟨1,by decide⟩
  change q ⟨4,by decide⟩=q ⟨5,by decide⟩ at hb1
  have hb2 := hb ⟨2,by decide⟩
  change q ⟨6,by decide⟩=q ⟨7,by decide⟩ at hb2
  have hb3 := hb ⟨3,by decide⟩
  change q ⟨8,by decide⟩=q ⟨9,by decide⟩ at hb3
  have hb4 := hb ⟨4,by decide⟩
  change q ⟨10,by decide⟩=q ⟨11,by decide⟩ at hb4
  have hb5 := hb ⟨5,by decide⟩
  change q ⟨12,by decide⟩=q ⟨13,by decide⟩ at hb5
  have ht0 := ht ⟨0,by decide⟩
  change r ⟨6,by decide⟩=r ⟨7,by decide⟩ at ht0
  have ht1 := ht ⟨1,by decide⟩
  change r ⟨10,by decide⟩=r ⟨11,by decide⟩ at ht1
  have ht2 := ht ⟨2,by decide⟩
  change r ⟨12,by decide⟩=r ⟨13,by decide⟩ at ht2
  have ht3 := ht ⟨3,by decide⟩
  change r ⟨14,by decide⟩=r ⟨15,by decide⟩ at ht3
  constructor
  · funext i
    fin_cases i
    · change q ⟨0,by decide⟩=0
      linear_combination (1 : ℝ)*hz.1
    · change q ⟨1,by decide⟩=0
      linear_combination (1 : ℝ)*h.n0 + (-1 : ℝ)*h.n1 + (-1 : ℝ)*h.m1 + (-1 : ℝ)*h.m2 + (-1 : ℝ)*h.m3 + (-1 : ℝ)*h.m4 + (1/2 : ℝ)*h.m5 + (1/2 : ℝ)*h.m6 + (1/2 : ℝ)*h.c12 + (1/2 : ℝ)*h.c13 + (1/2 : ℝ)*h.c14 + (1/2 : ℝ)*h.c23 + (1/2 : ℝ)*h.c24 + (1/2 : ℝ)*h.c34 + (-1 : ℝ)*h.c56 + (-1 : ℝ)*hz.1
    · change q ⟨2,by decide⟩=(r ⟨2,by decide⟩)+(r ⟨0,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (-2/3 : ℝ)*h.m2 + (1/3 : ℝ)*h.m3 + (1/3 : ℝ)*h.m4 + (-5/12 : ℝ)*h.m5 + (-5/12 : ℝ)*h.m6 + (5/12 : ℝ)*h.c12 + (-1/12 : ℝ)*h.c13 + (-1/12 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (1/3 : ℝ)*h.c25 + (1/3 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb0 + (-2/3 : ℝ)*hz.1
    · change q ⟨3,by decide⟩=(r ⟨2,by decide⟩)+(r ⟨0,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (-2/3 : ℝ)*h.m2 + (1/3 : ℝ)*h.m3 + (1/3 : ℝ)*h.m4 + (-5/12 : ℝ)*h.m5 + (-5/12 : ℝ)*h.m6 + (5/12 : ℝ)*h.c12 + (-1/12 : ℝ)*h.c13 + (-1/12 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (1/3 : ℝ)*h.c25 + (1/3 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb0 + (-2/3 : ℝ)*hz.1
    · change q ⟨4,by decide⟩=(r ⟨4,by decide⟩)+(r ⟨0,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (1/3 : ℝ)*h.m2 + (-2/3 : ℝ)*h.m3 + (1/3 : ℝ)*h.m4 + (-5/12 : ℝ)*h.m5 + (-5/12 : ℝ)*h.m6 + (-1/12 : ℝ)*h.c12 + (5/12 : ℝ)*h.c13 + (-1/12 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (-1/6 : ℝ)*h.c25 + (-1/6 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (1/3 : ℝ)*h.c35 + (1/3 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb1 + (-2/3 : ℝ)*hz.1
    · change q ⟨5,by decide⟩=(r ⟨4,by decide⟩)+(r ⟨0,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (1/3 : ℝ)*h.m2 + (-2/3 : ℝ)*h.m3 + (1/3 : ℝ)*h.m4 + (-5/12 : ℝ)*h.m5 + (-5/12 : ℝ)*h.m6 + (-1/12 : ℝ)*h.c12 + (5/12 : ℝ)*h.c13 + (-1/12 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (-1/6 : ℝ)*h.c25 + (-1/6 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (1/3 : ℝ)*h.c35 + (1/3 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb1 + (-2/3 : ℝ)*hz.1
    · change q ⟨6,by decide⟩=(r ⟨4,by decide⟩)+(r ⟨2,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (1/3 : ℝ)*h.m2 + (1/3 : ℝ)*h.m3 + (-2/3 : ℝ)*h.m4 + (-5/12 : ℝ)*h.m5 + (-5/12 : ℝ)*h.m6 + (-1/12 : ℝ)*h.c12 + (-1/12 : ℝ)*h.c13 + (5/12 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (-1/6 : ℝ)*h.c25 + (-1/6 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (1/3 : ℝ)*h.c45 + (1/3 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb2 + (-2/3 : ℝ)*hz.1
    · change q ⟨7,by decide⟩=(r ⟨4,by decide⟩)+(r ⟨2,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (1/3 : ℝ)*h.m2 + (1/3 : ℝ)*h.m3 + (-2/3 : ℝ)*h.m4 + (-5/12 : ℝ)*h.m5 + (-5/12 : ℝ)*h.m6 + (-1/12 : ℝ)*h.c12 + (-1/12 : ℝ)*h.c13 + (5/12 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (-1/6 : ℝ)*h.c25 + (-1/6 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (1/3 : ℝ)*h.c45 + (1/3 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb2 + (-2/3 : ℝ)*hz.1
    · change q ⟨8,by decide⟩=1/8-(r ⟨4,by decide⟩)-(r ⟨2,by decide⟩)
      linear_combination (-2/3 : ℝ)*h.n0 + (19/24 : ℝ)*h.n1 + (19/24 : ℝ)*h.m1 + (-5/24 : ℝ)*h.m2 + (-5/24 : ℝ)*h.m3 + (19/24 : ℝ)*h.m4 + (5/12 : ℝ)*h.m5 + (5/12 : ℝ)*h.m6 + (-1/6 : ℝ)*h.c12 + (-1/6 : ℝ)*h.c13 + (-1/6 : ℝ)*h.c14 + (-1/3 : ℝ)*h.c15 + (-1/3 : ℝ)*h.c16 + (1/3 : ℝ)*h.c23 + (-1/6 : ℝ)*h.c24 + (1/6 : ℝ)*h.c25 + (1/6 : ℝ)*h.c26 + (-1/6 : ℝ)*h.c34 + (1/6 : ℝ)*h.c35 + (1/6 : ℝ)*h.c36 + (-1/3 : ℝ)*h.c45 + (-1/3 : ℝ)*h.c46 + (-1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb3 + (2/3 : ℝ)*hz.1
    · change q ⟨9,by decide⟩=1/8-(r ⟨4,by decide⟩)-(r ⟨2,by decide⟩)
      linear_combination (-2/3 : ℝ)*h.n0 + (19/24 : ℝ)*h.n1 + (19/24 : ℝ)*h.m1 + (-5/24 : ℝ)*h.m2 + (-5/24 : ℝ)*h.m3 + (19/24 : ℝ)*h.m4 + (5/12 : ℝ)*h.m5 + (5/12 : ℝ)*h.m6 + (-1/6 : ℝ)*h.c12 + (-1/6 : ℝ)*h.c13 + (-1/6 : ℝ)*h.c14 + (-1/3 : ℝ)*h.c15 + (-1/3 : ℝ)*h.c16 + (1/3 : ℝ)*h.c23 + (-1/6 : ℝ)*h.c24 + (1/6 : ℝ)*h.c25 + (1/6 : ℝ)*h.c26 + (-1/6 : ℝ)*h.c34 + (1/6 : ℝ)*h.c35 + (1/6 : ℝ)*h.c36 + (-1/3 : ℝ)*h.c45 + (-1/3 : ℝ)*h.c46 + (-1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb3 + (2/3 : ℝ)*hz.1
    · change q ⟨10,by decide⟩=1/8-(r ⟨4,by decide⟩)-(r ⟨0,by decide⟩)
      linear_combination (-2/3 : ℝ)*h.n0 + (19/24 : ℝ)*h.n1 + (19/24 : ℝ)*h.m1 + (-5/24 : ℝ)*h.m2 + (19/24 : ℝ)*h.m3 + (-5/24 : ℝ)*h.m4 + (5/12 : ℝ)*h.m5 + (5/12 : ℝ)*h.m6 + (-1/6 : ℝ)*h.c12 + (-1/6 : ℝ)*h.c13 + (-1/6 : ℝ)*h.c14 + (-1/3 : ℝ)*h.c15 + (-1/3 : ℝ)*h.c16 + (-1/6 : ℝ)*h.c23 + (1/3 : ℝ)*h.c24 + (1/6 : ℝ)*h.c25 + (1/6 : ℝ)*h.c26 + (-1/6 : ℝ)*h.c34 + (-1/3 : ℝ)*h.c35 + (-1/3 : ℝ)*h.c36 + (1/6 : ℝ)*h.c45 + (1/6 : ℝ)*h.c46 + (-1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb4 + (2/3 : ℝ)*hz.1
    · change q ⟨11,by decide⟩=1/8-(r ⟨4,by decide⟩)-(r ⟨0,by decide⟩)
      linear_combination (-2/3 : ℝ)*h.n0 + (19/24 : ℝ)*h.n1 + (19/24 : ℝ)*h.m1 + (-5/24 : ℝ)*h.m2 + (19/24 : ℝ)*h.m3 + (-5/24 : ℝ)*h.m4 + (5/12 : ℝ)*h.m5 + (5/12 : ℝ)*h.m6 + (-1/6 : ℝ)*h.c12 + (-1/6 : ℝ)*h.c13 + (-1/6 : ℝ)*h.c14 + (-1/3 : ℝ)*h.c15 + (-1/3 : ℝ)*h.c16 + (-1/6 : ℝ)*h.c23 + (1/3 : ℝ)*h.c24 + (1/6 : ℝ)*h.c25 + (1/6 : ℝ)*h.c26 + (-1/6 : ℝ)*h.c34 + (-1/3 : ℝ)*h.c35 + (-1/3 : ℝ)*h.c36 + (1/6 : ℝ)*h.c45 + (1/6 : ℝ)*h.c46 + (-1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb4 + (2/3 : ℝ)*hz.1
    · change q ⟨12,by decide⟩=1/8-(r ⟨2,by decide⟩)-(r ⟨0,by decide⟩)
      linear_combination (-2/3 : ℝ)*h.n0 + (19/24 : ℝ)*h.n1 + (19/24 : ℝ)*h.m1 + (19/24 : ℝ)*h.m2 + (-5/24 : ℝ)*h.m3 + (-5/24 : ℝ)*h.m4 + (-13/12 : ℝ)*h.m5 + (23/12 : ℝ)*h.m6 + (-1/6 : ℝ)*h.c12 + (-1/6 : ℝ)*h.c13 + (-1/6 : ℝ)*h.c14 + (1/6 : ℝ)*h.c15 + (-5/6 : ℝ)*h.c16 + (-1/6 : ℝ)*h.c23 + (-1/6 : ℝ)*h.c24 + (1/6 : ℝ)*h.c25 + (-5/6 : ℝ)*h.c26 + (1/3 : ℝ)*h.c34 + (2/3 : ℝ)*h.c35 + (-1/3 : ℝ)*h.c36 + (2/3 : ℝ)*h.c45 + (-1/3 : ℝ)*h.c46 + (-1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb0 + (-1/2 : ℝ)*hb1 + (-1/2 : ℝ)*hb2 + (-1/2 : ℝ)*hb3 + (-1/2 : ℝ)*hb4 + (2/3 : ℝ)*hz.1
    · change q ⟨13,by decide⟩=1/8-(r ⟨2,by decide⟩)-(r ⟨0,by decide⟩)
      linear_combination (-2/3 : ℝ)*h.n0 + (19/24 : ℝ)*h.n1 + (19/24 : ℝ)*h.m1 + (19/24 : ℝ)*h.m2 + (-5/24 : ℝ)*h.m3 + (-5/24 : ℝ)*h.m4 + (23/12 : ℝ)*h.m5 + (-13/12 : ℝ)*h.m6 + (-1/6 : ℝ)*h.c12 + (-1/6 : ℝ)*h.c13 + (-1/6 : ℝ)*h.c14 + (-5/6 : ℝ)*h.c15 + (1/6 : ℝ)*h.c16 + (-1/6 : ℝ)*h.c23 + (-1/6 : ℝ)*h.c24 + (-5/6 : ℝ)*h.c25 + (1/6 : ℝ)*h.c26 + (1/3 : ℝ)*h.c34 + (-1/3 : ℝ)*h.c35 + (2/3 : ℝ)*h.c36 + (-1/3 : ℝ)*h.c45 + (2/3 : ℝ)*h.c46 + (-1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb0 + (1/2 : ℝ)*hb1 + (1/2 : ℝ)*hb2 + (1/2 : ℝ)*hb3 + (1/2 : ℝ)*hb4 + (2/3 : ℝ)*hz.1
    · change q ⟨14,by decide⟩=1/8
      linear_combination (-1/3 : ℝ)*h.n0 + (11/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (11/24 : ℝ)*h.m2 + (11/24 : ℝ)*h.m3 + (11/24 : ℝ)*h.m4 + (-1/6 : ℝ)*h.m5 + (-1/6 : ℝ)*h.m6 + (-1/12 : ℝ)*h.c12 + (-1/12 : ℝ)*h.c13 + (-1/12 : ℝ)*h.c14 + (-1/6 : ℝ)*h.c15 + (-1/6 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (-1/6 : ℝ)*h.c25 + (-1/6 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (2/3 : ℝ)*h.c56 + (1/3 : ℝ)*hz.1
    · change q ⟨15,by decide⟩=1/8
      linear_combination (1/3 : ℝ)*h.n0 + (-5/24 : ℝ)*h.n1 + (-5/24 : ℝ)*h.m1 + (-5/24 : ℝ)*h.m2 + (-5/24 : ℝ)*h.m3 + (-5/24 : ℝ)*h.m4 + (-1/3 : ℝ)*h.m5 + (-1/3 : ℝ)*h.m6 + (1/12 : ℝ)*h.c12 + (1/12 : ℝ)*h.c13 + (1/12 : ℝ)*h.c14 + (1/6 : ℝ)*h.c15 + (1/6 : ℝ)*h.c16 + (1/12 : ℝ)*h.c23 + (1/12 : ℝ)*h.c24 + (1/6 : ℝ)*h.c25 + (1/6 : ℝ)*h.c26 + (1/12 : ℝ)*h.c34 + (1/6 : ℝ)*h.c35 + (1/6 : ℝ)*h.c36 + (1/6 : ℝ)*h.c45 + (1/6 : ℝ)*h.c46 + (1/3 : ℝ)*h.c56 + (-1/3 : ℝ)*hz.1
  · funext i
    fin_cases i
    · change r ⟨0,by decide⟩=(r ⟨0,by decide⟩)
      rfl
    · change r ⟨1,by decide⟩=(r ⟨0,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (-2/3 : ℝ)*h.m2 + (-2/3 : ℝ)*h.m3 + (1/3 : ℝ)*h.m4 + (-1/6 : ℝ)*h.m5 + (-1/6 : ℝ)*h.m6 + (1/6 : ℝ)*h.c12 + (1/6 : ℝ)*h.c13 + (1/6 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (1/6 : ℝ)*h.c23 + (1/6 : ℝ)*h.c24 + (1/3 : ℝ)*h.c25 + (1/3 : ℝ)*h.c26 + (1/6 : ℝ)*h.c34 + (1/3 : ℝ)*h.c35 + (1/3 : ℝ)*h.c36 + (-2/3 : ℝ)*h.c45 + (-2/3 : ℝ)*h.c46 + (-1/3 : ℝ)*h.c56 + (-2/3 : ℝ)*hz.1
    · change r ⟨2,by decide⟩=(r ⟨2,by decide⟩)
      rfl
    · change r ⟨3,by decide⟩=(r ⟨2,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (-2/3 : ℝ)*h.m2 + (1/3 : ℝ)*h.m3 + (-2/3 : ℝ)*h.m4 + (-1/6 : ℝ)*h.m5 + (-1/6 : ℝ)*h.m6 + (1/6 : ℝ)*h.c12 + (1/6 : ℝ)*h.c13 + (1/6 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (1/6 : ℝ)*h.c23 + (1/6 : ℝ)*h.c24 + (1/3 : ℝ)*h.c25 + (1/3 : ℝ)*h.c26 + (1/6 : ℝ)*h.c34 + (-2/3 : ℝ)*h.c35 + (-2/3 : ℝ)*h.c36 + (1/3 : ℝ)*h.c45 + (1/3 : ℝ)*h.c46 + (-1/3 : ℝ)*h.c56 + (-2/3 : ℝ)*hz.1
    · change r ⟨4,by decide⟩=(r ⟨4,by decide⟩)
      rfl
    · change r ⟨5,by decide⟩=(r ⟨4,by decide⟩)
      linear_combination (2/3 : ℝ)*h.n0 + (-2/3 : ℝ)*h.n1 + (-2/3 : ℝ)*h.m1 + (1/3 : ℝ)*h.m2 + (-2/3 : ℝ)*h.m3 + (-2/3 : ℝ)*h.m4 + (-1/6 : ℝ)*h.m5 + (-1/6 : ℝ)*h.m6 + (1/6 : ℝ)*h.c12 + (1/6 : ℝ)*h.c13 + (1/6 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (1/6 : ℝ)*h.c23 + (1/6 : ℝ)*h.c24 + (-2/3 : ℝ)*h.c25 + (-2/3 : ℝ)*h.c26 + (1/6 : ℝ)*h.c34 + (1/3 : ℝ)*h.c35 + (1/3 : ℝ)*h.c36 + (1/3 : ℝ)*h.c45 + (1/3 : ℝ)*h.c46 + (-1/3 : ℝ)*h.c56 + (-2/3 : ℝ)*hz.1
    · change r ⟨6,by decide⟩=(r ⟨4,by decide⟩)+(r ⟨2,by decide⟩)+(r ⟨0,by decide⟩)
      linear_combination (1 : ℝ)*h.n0 + (-1 : ℝ)*h.n1 + (-1 : ℝ)*h.m1 + (-1/4 : ℝ)*h.m5 + (-5/4 : ℝ)*h.m6 + (1/4 : ℝ)*h.c12 + (1/4 : ℝ)*h.c13 + (1/4 : ℝ)*h.c14 + (1 : ℝ)*h.c16 + (-1/4 : ℝ)*h.c23 + (-1/4 : ℝ)*h.c24 + (-1/4 : ℝ)*h.c34 + (1/2 : ℝ)*h.c56 + (1/2 : ℝ)*hb0 + (1/2 : ℝ)*hb1 + (1/2 : ℝ)*hb2 + (-1 : ℝ)*hz.1
    · change r ⟨7,by decide⟩=(r ⟨4,by decide⟩)+(r ⟨2,by decide⟩)+(r ⟨0,by decide⟩)
      linear_combination (1 : ℝ)*h.n0 + (-1 : ℝ)*h.n1 + (-1 : ℝ)*h.m1 + (-5/4 : ℝ)*h.m5 + (-1/4 : ℝ)*h.m6 + (1/4 : ℝ)*h.c12 + (1/4 : ℝ)*h.c13 + (1/4 : ℝ)*h.c14 + (1 : ℝ)*h.c15 + (-1/4 : ℝ)*h.c23 + (-1/4 : ℝ)*h.c24 + (-1/4 : ℝ)*h.c34 + (1/2 : ℝ)*h.c56 + (-1/2 : ℝ)*hb0 + (-1/2 : ℝ)*hb1 + (-1/2 : ℝ)*hb2 + (-1 : ℝ)*hz.1
    · change r ⟨8,by decide⟩=1/8-(r ⟨4,by decide⟩)-(r ⟨2,by decide⟩)-(r ⟨0,by decide⟩)
      linear_combination (-4/3 : ℝ)*h.n0 + (35/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (11/24 : ℝ)*h.m2 + (11/24 : ℝ)*h.m3 + (11/24 : ℝ)*h.m4 + (5/6 : ℝ)*h.m5 + (5/6 : ℝ)*h.m6 + (-1/12 : ℝ)*h.c12 + (-1/12 : ℝ)*h.c13 + (-1/12 : ℝ)*h.c14 + (-1/6 : ℝ)*h.c15 + (-1/6 : ℝ)*h.c16 + (-1/12 : ℝ)*h.c23 + (-1/12 : ℝ)*h.c24 + (-1/6 : ℝ)*h.c25 + (-1/6 : ℝ)*h.c26 + (-1/12 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (-1/3 : ℝ)*h.c56 + (4/3 : ℝ)*hz.1
    · change r ⟨9,by decide⟩=1/8-(r ⟨4,by decide⟩)-(r ⟨2,by decide⟩)-(r ⟨0,by decide⟩)
      linear_combination (-2/3 : ℝ)*h.n0 + (19/24 : ℝ)*h.n1 + (19/24 : ℝ)*h.m1 + (-5/24 : ℝ)*h.m2 + (-5/24 : ℝ)*h.m3 + (-5/24 : ℝ)*h.m4 + (2/3 : ℝ)*h.m5 + (2/3 : ℝ)*h.m6 + (1/12 : ℝ)*h.c12 + (1/12 : ℝ)*h.c13 + (1/12 : ℝ)*h.c14 + (-5/6 : ℝ)*h.c15 + (-5/6 : ℝ)*h.c16 + (1/12 : ℝ)*h.c23 + (1/12 : ℝ)*h.c24 + (1/6 : ℝ)*h.c25 + (1/6 : ℝ)*h.c26 + (1/12 : ℝ)*h.c34 + (1/6 : ℝ)*h.c35 + (1/6 : ℝ)*h.c36 + (1/6 : ℝ)*h.c45 + (1/6 : ℝ)*h.c46 + (-2/3 : ℝ)*h.c56 + (2/3 : ℝ)*hz.1
    · change r ⟨10,by decide⟩=1/8-(r ⟨4,by decide⟩)
      linear_combination (-1/3 : ℝ)*h.n0 + (11/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (-13/24 : ℝ)*h.m2 + (11/24 : ℝ)*h.m3 + (11/24 : ℝ)*h.m4 + (7/12 : ℝ)*h.m5 + (-5/12 : ℝ)*h.m6 + (1/6 : ℝ)*h.c12 + (-1/3 : ℝ)*h.c13 + (-1/3 : ℝ)*h.c14 + (-1/6 : ℝ)*h.c15 + (-1/6 : ℝ)*h.c16 + (1/6 : ℝ)*h.c23 + (1/6 : ℝ)*h.c24 + (-1/6 : ℝ)*h.c25 + (5/6 : ℝ)*h.c26 + (-1/3 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb0 + (1/2 : ℝ)*hb3 + (1/2 : ℝ)*hb4 + (1/3 : ℝ)*hz.1
    · change r ⟨11,by decide⟩=1/8-(r ⟨4,by decide⟩)
      linear_combination (-1/3 : ℝ)*h.n0 + (11/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (-13/24 : ℝ)*h.m2 + (11/24 : ℝ)*h.m3 + (11/24 : ℝ)*h.m4 + (-5/12 : ℝ)*h.m5 + (7/12 : ℝ)*h.m6 + (1/6 : ℝ)*h.c12 + (-1/3 : ℝ)*h.c13 + (-1/3 : ℝ)*h.c14 + (-1/6 : ℝ)*h.c15 + (-1/6 : ℝ)*h.c16 + (1/6 : ℝ)*h.c23 + (1/6 : ℝ)*h.c24 + (5/6 : ℝ)*h.c25 + (-1/6 : ℝ)*h.c26 + (-1/3 : ℝ)*h.c34 + (-1/6 : ℝ)*h.c35 + (-1/6 : ℝ)*h.c36 + (-1/6 : ℝ)*h.c45 + (-1/6 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb0 + (-1/2 : ℝ)*hb3 + (-1/2 : ℝ)*hb4 + (1/3 : ℝ)*hz.1
    · change r ⟨12,by decide⟩=1/8-(r ⟨2,by decide⟩)
      linear_combination (-1/3 : ℝ)*h.n0 + (11/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (11/24 : ℝ)*h.m2 + (-13/24 : ℝ)*h.m3 + (11/24 : ℝ)*h.m4 + (-11/12 : ℝ)*h.m5 + (13/12 : ℝ)*h.m6 + (-1/3 : ℝ)*h.c12 + (1/6 : ℝ)*h.c13 + (-1/3 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (-2/3 : ℝ)*h.c16 + (1/6 : ℝ)*h.c23 + (-1/3 : ℝ)*h.c24 + (1/3 : ℝ)*h.c25 + (-2/3 : ℝ)*h.c26 + (1/6 : ℝ)*h.c34 + (1/3 : ℝ)*h.c35 + (1/3 : ℝ)*h.c36 + (1/3 : ℝ)*h.c45 + (-2/3 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb0 + (-1/2 : ℝ)*hb2 + (-1/2 : ℝ)*hb4 + (1/3 : ℝ)*hz.1
    · change r ⟨13,by decide⟩=1/8-(r ⟨2,by decide⟩)
      linear_combination (-1/3 : ℝ)*h.n0 + (11/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (11/24 : ℝ)*h.m2 + (-13/24 : ℝ)*h.m3 + (11/24 : ℝ)*h.m4 + (13/12 : ℝ)*h.m5 + (-11/12 : ℝ)*h.m6 + (-1/3 : ℝ)*h.c12 + (1/6 : ℝ)*h.c13 + (-1/3 : ℝ)*h.c14 + (-2/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (1/6 : ℝ)*h.c23 + (-1/3 : ℝ)*h.c24 + (-2/3 : ℝ)*h.c25 + (1/3 : ℝ)*h.c26 + (1/6 : ℝ)*h.c34 + (1/3 : ℝ)*h.c35 + (1/3 : ℝ)*h.c36 + (-2/3 : ℝ)*h.c45 + (1/3 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb0 + (1/2 : ℝ)*hb2 + (1/2 : ℝ)*hb4 + (1/3 : ℝ)*hz.1
    · change r ⟨14,by decide⟩=1/8-(r ⟨0,by decide⟩)
      linear_combination (-1/3 : ℝ)*h.n0 + (11/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (11/24 : ℝ)*h.m2 + (11/24 : ℝ)*h.m3 + (-13/24 : ℝ)*h.m4 + (-11/12 : ℝ)*h.m5 + (13/12 : ℝ)*h.m6 + (-1/3 : ℝ)*h.c12 + (-1/3 : ℝ)*h.c13 + (1/6 : ℝ)*h.c14 + (1/3 : ℝ)*h.c15 + (-2/3 : ℝ)*h.c16 + (-1/3 : ℝ)*h.c23 + (1/6 : ℝ)*h.c24 + (1/3 : ℝ)*h.c25 + (-2/3 : ℝ)*h.c26 + (1/6 : ℝ)*h.c34 + (1/3 : ℝ)*h.c35 + (-2/3 : ℝ)*h.c36 + (1/3 : ℝ)*h.c45 + (1/3 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (-1/2 : ℝ)*hb0 + (-1/2 : ℝ)*hb1 + (-1/2 : ℝ)*hb3 + (1/3 : ℝ)*hz.1
    · change r ⟨15,by decide⟩=1/8-(r ⟨0,by decide⟩)
      linear_combination (-1/3 : ℝ)*h.n0 + (11/24 : ℝ)*h.n1 + (11/24 : ℝ)*h.m1 + (11/24 : ℝ)*h.m2 + (11/24 : ℝ)*h.m3 + (-13/24 : ℝ)*h.m4 + (13/12 : ℝ)*h.m5 + (-11/12 : ℝ)*h.m6 + (-1/3 : ℝ)*h.c12 + (-1/3 : ℝ)*h.c13 + (1/6 : ℝ)*h.c14 + (-2/3 : ℝ)*h.c15 + (1/3 : ℝ)*h.c16 + (-1/3 : ℝ)*h.c23 + (1/6 : ℝ)*h.c24 + (-2/3 : ℝ)*h.c25 + (1/3 : ℝ)*h.c26 + (1/6 : ℝ)*h.c34 + (-2/3 : ℝ)*h.c35 + (1/3 : ℝ)*h.c36 + (1/3 : ℝ)*h.c45 + (1/3 : ℝ)*h.c46 + (1/6 : ℝ)*h.c56 + (1/2 : ℝ)*hb0 + (1/2 : ℝ)*hb1 + (1/2 : ℝ)*hb3 + (1/3 : ℝ)*hz.1

def xs : Fin 16 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def ys : Fin 16 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]
def probabilities (c : SS.State 6 ℂ) (xs : Fin 16 → SS.BitString 6) : Fin 16 → ℝ :=
  fun i => Complex.normSq (c (xs i))
def printedBottomIndex : Fin 7 → Fin 2 → Fin 16 := ![![⟨14,by decide⟩,⟨15,by decide⟩],![⟨13,by decide⟩,⟨12,by decide⟩],![⟨11,by decide⟩,⟨10,by decide⟩],![⟨7,by decide⟩,⟨6,by decide⟩],![⟨9,by decide⟩,⟨8,by decide⟩],![⟨5,by decide⟩,⟨4,by decide⟩],![⟨3,by decide⟩,⟨2,by decide⟩]]
def printedTopIndex : Fin 8 → Fin 2 → Fin 16 := ![![⟨8,by decide⟩,⟨9,by decide⟩],![⟨4,by decide⟩,⟨5,by decide⟩],![⟨2,by decide⟩,⟨3,by decide⟩],![⟨0,by decide⟩,⟨1,by decide⟩],![⟨15,by decide⟩,⟨14,by decide⟩],![⟨13,by decide⟩,⟨12,by decide⟩],![⟨11,by decide⟩,⟨10,by decide⟩],![⟨7,by decide⟩,⟨6,by decide⟩]]
theorem literal_native_pairs :
    (∀ i j, Orbit29PrintedFaceAudit.bottomPairs i j=xs (printedBottomIndex i j)) ∧
    (∀ i j, Orbit29PrintedFaceAudit.topPairs i j=ys (printedTopIndex i j)) := by decide +kernel
theorem native_bottom_index : ∀ i j, xs (bottomIndex i j)=
    (![![y2,y3],![y4,y5],![y6,y7],![y8,y9],![y10,y11],![y12,y13]] : Fin 6 → Fin 2 → SS.BitString 6) i j := by decide +kernel
theorem native_high_index : ∀ i j, ys (highIndex i j)=
    (![![z6,z7],![z10,z11],![z12,z13],![z14,z15]] : Fin 4 → Fin 2 → SS.BitString 6) i j := by decide +kernel

theorem physical_normal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) :
    probabilities c xs=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ∧
    probabilities d ys=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) := by
  have hm := Orbit29PhysicalPairReduction.physical_moments c d hc hd hnc hnd hdist
  apply reduced_normal (probabilities c xs) (probabilities d ys) hm
  · intro i
    change Complex.normSq (c (xs (bottomIndex i 0)))=Complex.normSq (c (xs (bottomIndex i 1)))
    rw [native_bottom_index,native_bottom_index]
    have hb := Orbit29PhysicalPairReduction.bottom_balanced c d hm hc hd hdist i
    fin_cases i <;> simpa [Orbit29PhysicalPairReduction.bottom] using hb
  · intro i
    change Complex.normSq (d (ys (highIndex i 0)))=Complex.normSq (d (ys (highIndex i 1)))
    rw [native_high_index,native_high_index]
    have ht := Orbit29PhysicalPairReduction.high_balanced c d hm hc hd hdist i
    fin_cases i <;> simpa [Orbit29PhysicalPairReduction.highPairs] using ht

def bottomProbability (a b c : ℝ) : Fin 7 → ℝ :=
  ![1/8,1/8-b-c,1/8-a-c,a+b,1/8-a-b,a+c,b+c]
def topProbability (a b c : ℝ) : Fin 8 → ℝ :=
  ![1/8-a-b-c,a,b,c,1/8-c,1/8-b,1/8-a,a+b+c]

theorem printed_probability_indices (a b c : ℝ) :
    (∀ i j, normalQ a b c (printedBottomIndex i j)=bottomProbability a b c i) ∧
    (∀ i j, normalR a b c (printedTopIndex i j)=topProbability a b c i) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl

theorem physical_printed_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) :
    (∀ i j, Complex.normSq (c (Orbit29PrintedFaceAudit.bottomPairs i j))=
      bottomProbability (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) i) ∧
    (∀ i j, Complex.normSq (d (Orbit29PrintedFaceAudit.topPairs i j))=
      topProbability (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) i) := by
  have hp := physical_normal c d hc hd hnc hnd hdist
  constructor
  · intro i j
    rw [literal_native_pairs.1]
    change probabilities c xs (printedBottomIndex i j)=_
    rw [hp.1]
    exact (printed_probability_indices _ _ _).1 i j
  · intro i j
    rw [literal_native_pairs.2]
    change probabilities d ys (printedTopIndex i j)=_
    rw [hp.2]
    exact (printed_probability_indices _ _ _).2 i j

theorem physical_domain (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) :
    0 ≤ Complex.normSq (d z4) ∧ 0 ≤ Complex.normSq (d z2) ∧
    0 ≤ Complex.normSq (d z0) ∧
      Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)≤1/8 := by
  have hp := physical_normal c d hc hd hnc hnd hdist
  have hr := congrFun hp.2 ⟨8,by decide⟩
  change Complex.normSq (d z8)=1/8-Complex.normSq (d z4)-Complex.normSq (d z2)-Complex.normSq (d z0) at hr
  exact ⟨Complex.normSq_nonneg _,Complex.normSq_nonneg _,Complex.normSq_nonneg _,
    by linarith [Complex.normSq_nonneg (d z8)]⟩

theorem physical_omitted_amplitudes (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) : c y0=0 ∧ c y1=0 := by
  have hm := Orbit29PhysicalPairReduction.physical_moments c d hc hd hnc hnd hdist
  have hz := omitted_zero (probabilities c xs) (probabilities d ys) hm
  exact ⟨Complex.normSq_eq_zero.mp hz.1,Complex.normSq_eq_zero.mp hz.2⟩

end
end MainTheory.Orbit29PrintedSimplex
