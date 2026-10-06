import SixQubit.CodeOrbit29
import MainTheory.Orbit29PairBalance

/-! The pair-balance reduction follows from actual supported physical code
amplitudes, their degree-two moments, and the twelve physical Walsh relations.
No final no-code result is used to prove an intermediate manuscript formula. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.Orbit29PhysicalPairReduction
open SixQubit.Orbit29
open scoped BigOperators
noncomputable section

def Moment (c d : SS.State 6 ℂ) : Prop :=
  MomentSystem (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
  (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15))
def bottom (c : SS.State 6 ℂ) : Fin 6 → Fin 2 → ℂ :=
  ![![c y2,c y3],![c y4,c y5],![c y6,c y7],![c y8,c y9],![c y10,c y11],![c y12,c y13]]
def highPairs (d : SS.State 6 ℂ) : Fin 4 → Fin 2 → ℂ :=
  ![![d z6,d z7],![d z10,d z11],![d z12,d z13],![d z14,d z15]]
def node : Fin 6 → Fin 2 → Fin 4 :=
  ![![⟨0,by decide⟩,⟨1,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨3,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩],![⟨1,by decide⟩,⟨3,by decide⟩],![⟨2,by decide⟩,⟨3,by decide⟩]]
def Q (d : SS.State 6 ℂ) (i : Fin 4) : ℝ :=
  Complex.normSq (highPairs d i 0)+Complex.normSq (highPairs d i 1)

theorem physical_moments (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hdist : SS.HasDistance ![c,d] 3) : Moment c d :=
  moments c d hc hd hnc hnd hdist

theorem native_orth (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ e j,
    star (bottom c e 0)*highPairs d (node e j) 0+
      star (bottom c e 1)*highPairs d (node e j) 1=0 := by
  intro e j
  fin_cases e <;> fin_cases j
  · simpa [bottom,highPairs,node] using orth1_3 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth1_5 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth2_3 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth2_6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth3_3 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w4 (by decide))
  · simpa [bottom,highPairs,node] using orth3_7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef9 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth4_5 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth4_6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth5_5 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w4 (by decide))
  · simpa [bottom,highPairs,node] using orth5_7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef6 w3 (by decide))
  · simpa [bottom,highPairs,node] using orth6_6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef0 w4 (by decide))
  · simpa [bottom,highPairs,node] using orth6_7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w6 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w5 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ef3 w3 (by decide))

theorem bottom_mass (c d : SS.State 6 ℂ) (h : Moment c d) : ∀ e,
    Complex.normSq (bottom c e 0)+Complex.normSq (bottom c e 1)=
      Q d (node e 0)+Q d (node e 1)-1/4 := by
  intro e
  fin_cases e
  · have he := mc1 h
    norm_num [bottom,Q,highPairs,node]
    linarith
  · have he := mc2 h
    norm_num [bottom,Q,highPairs,node]
    linarith
  · have he := mc3 h
    norm_num [bottom,Q,highPairs,node]
    linarith
  · have he := mc4 h
    norm_num [bottom,Q,highPairs,node]
    linarith
  · have he := mc5 h
    norm_num [bottom,Q,highPairs,node]
    linarith
  · have he := mc6 h
    norm_num [bottom,Q,highPairs,node]
    linarith

theorem total_high_mass (c d : SS.State 6 ℂ) (h : Moment c d) :
    (∑ i, Q d i)=3/4 := by
  have he := mq h
  norm_num [Q,highPairs,Fin.sum_univ_succ,Fin.succ]
  linarith

theorem high_mass_bound (c d : SS.State 6 ℂ) (h : Moment c d) : ∀ i, Q d i≤1/4 := by
  intro i
  fin_cases i
  · have he := mp3 h
    norm_num [Q,highPairs]
    linarith [h.nr8,h.nr9]
  · have he := mp5 h
    norm_num [Q,highPairs]
    linarith [h.nr4,h.nr5]
  · have he := mp6 h
    norm_num [Q,highPairs]
    linarith [h.nr2,h.nr3]
  · have he := mp7 h
    norm_num [Q,highPairs]
    linarith [h.nr0,h.nr1]

theorem weighted_determinants (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ i j,
    ((Q d i+Q d j-1/4 : ℝ) : ℂ)*
      (highPairs d i 0*highPairs d j 1-highPairs d j 0*highPairs d i 1)=0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · ring
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨0,by decide⟩ 0) (bottom c ⟨0,by decide⟩ 1)
      (highPairs d (node ⟨0,by decide⟩ 0) 0) (highPairs d (node ⟨0,by decide⟩ 0) 1)
      (highPairs d (node ⟨0,by decide⟩ 1) 0) (highPairs d (node ⟨0,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨0,by decide⟩ 0) (native_orth c d hc hd hdist ⟨0,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨0,by decide⟩] at he
    change ((Q d ⟨0,by decide⟩+Q d ⟨1,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨0,by decide⟩ 0*highPairs d ⟨1,by decide⟩ 1-
        highPairs d ⟨1,by decide⟩ 0*highPairs d ⟨0,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨1,by decide⟩ 0) (bottom c ⟨1,by decide⟩ 1)
      (highPairs d (node ⟨1,by decide⟩ 0) 0) (highPairs d (node ⟨1,by decide⟩ 0) 1)
      (highPairs d (node ⟨1,by decide⟩ 1) 0) (highPairs d (node ⟨1,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨1,by decide⟩ 0) (native_orth c d hc hd hdist ⟨1,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨1,by decide⟩] at he
    change ((Q d ⟨0,by decide⟩+Q d ⟨2,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨0,by decide⟩ 0*highPairs d ⟨2,by decide⟩ 1-
        highPairs d ⟨2,by decide⟩ 0*highPairs d ⟨0,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨2,by decide⟩ 0) (bottom c ⟨2,by decide⟩ 1)
      (highPairs d (node ⟨2,by decide⟩ 0) 0) (highPairs d (node ⟨2,by decide⟩ 0) 1)
      (highPairs d (node ⟨2,by decide⟩ 1) 0) (highPairs d (node ⟨2,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨2,by decide⟩ 0) (native_orth c d hc hd hdist ⟨2,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨2,by decide⟩] at he
    change ((Q d ⟨0,by decide⟩+Q d ⟨3,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨0,by decide⟩ 0*highPairs d ⟨3,by decide⟩ 1-
        highPairs d ⟨3,by decide⟩ 0*highPairs d ⟨0,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨0,by decide⟩ 0) (bottom c ⟨0,by decide⟩ 1)
      (highPairs d (node ⟨0,by decide⟩ 0) 0) (highPairs d (node ⟨0,by decide⟩ 0) 1)
      (highPairs d (node ⟨0,by decide⟩ 1) 0) (highPairs d (node ⟨0,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨0,by decide⟩ 0) (native_orth c d hc hd hdist ⟨0,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨0,by decide⟩] at he
    change ((Q d ⟨0,by decide⟩+Q d ⟨1,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨0,by decide⟩ 0*highPairs d ⟨1,by decide⟩ 1-
        highPairs d ⟨1,by decide⟩ 0*highPairs d ⟨0,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination -he
  · ring
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨3,by decide⟩ 0) (bottom c ⟨3,by decide⟩ 1)
      (highPairs d (node ⟨3,by decide⟩ 0) 0) (highPairs d (node ⟨3,by decide⟩ 0) 1)
      (highPairs d (node ⟨3,by decide⟩ 1) 0) (highPairs d (node ⟨3,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨3,by decide⟩ 0) (native_orth c d hc hd hdist ⟨3,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨3,by decide⟩] at he
    change ((Q d ⟨1,by decide⟩+Q d ⟨2,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨1,by decide⟩ 0*highPairs d ⟨2,by decide⟩ 1-
        highPairs d ⟨2,by decide⟩ 0*highPairs d ⟨1,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨4,by decide⟩ 0) (bottom c ⟨4,by decide⟩ 1)
      (highPairs d (node ⟨4,by decide⟩ 0) 0) (highPairs d (node ⟨4,by decide⟩ 0) 1)
      (highPairs d (node ⟨4,by decide⟩ 1) 0) (highPairs d (node ⟨4,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨4,by decide⟩ 0) (native_orth c d hc hd hdist ⟨4,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨4,by decide⟩] at he
    change ((Q d ⟨1,by decide⟩+Q d ⟨3,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨1,by decide⟩ 0*highPairs d ⟨3,by decide⟩ 1-
        highPairs d ⟨3,by decide⟩ 0*highPairs d ⟨1,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨1,by decide⟩ 0) (bottom c ⟨1,by decide⟩ 1)
      (highPairs d (node ⟨1,by decide⟩ 0) 0) (highPairs d (node ⟨1,by decide⟩ 0) 1)
      (highPairs d (node ⟨1,by decide⟩ 1) 0) (highPairs d (node ⟨1,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨1,by decide⟩ 0) (native_orth c d hc hd hdist ⟨1,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨1,by decide⟩] at he
    change ((Q d ⟨0,by decide⟩+Q d ⟨2,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨0,by decide⟩ 0*highPairs d ⟨2,by decide⟩ 1-
        highPairs d ⟨2,by decide⟩ 0*highPairs d ⟨0,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination -he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨3,by decide⟩ 0) (bottom c ⟨3,by decide⟩ 1)
      (highPairs d (node ⟨3,by decide⟩ 0) 0) (highPairs d (node ⟨3,by decide⟩ 0) 1)
      (highPairs d (node ⟨3,by decide⟩ 1) 0) (highPairs d (node ⟨3,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨3,by decide⟩ 0) (native_orth c d hc hd hdist ⟨3,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨3,by decide⟩] at he
    change ((Q d ⟨1,by decide⟩+Q d ⟨2,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨1,by decide⟩ 0*highPairs d ⟨2,by decide⟩ 1-
        highPairs d ⟨2,by decide⟩ 0*highPairs d ⟨1,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination -he
  · ring
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨5,by decide⟩ 0) (bottom c ⟨5,by decide⟩ 1)
      (highPairs d (node ⟨5,by decide⟩ 0) 0) (highPairs d (node ⟨5,by decide⟩ 0) 1)
      (highPairs d (node ⟨5,by decide⟩ 1) 0) (highPairs d (node ⟨5,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨5,by decide⟩ 0) (native_orth c d hc hd hdist ⟨5,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨5,by decide⟩] at he
    change ((Q d ⟨2,by decide⟩+Q d ⟨3,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨2,by decide⟩ 0*highPairs d ⟨3,by decide⟩ 1-
        highPairs d ⟨3,by decide⟩ 0*highPairs d ⟨2,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨2,by decide⟩ 0) (bottom c ⟨2,by decide⟩ 1)
      (highPairs d (node ⟨2,by decide⟩ 0) 0) (highPairs d (node ⟨2,by decide⟩ 0) 1)
      (highPairs d (node ⟨2,by decide⟩ 1) 0) (highPairs d (node ⟨2,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨2,by decide⟩ 0) (native_orth c d hc hd hdist ⟨2,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨2,by decide⟩] at he
    change ((Q d ⟨0,by decide⟩+Q d ⟨3,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨0,by decide⟩ 0*highPairs d ⟨3,by decide⟩ 1-
        highPairs d ⟨3,by decide⟩ 0*highPairs d ⟨0,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination -he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨4,by decide⟩ 0) (bottom c ⟨4,by decide⟩ 1)
      (highPairs d (node ⟨4,by decide⟩ 0) 0) (highPairs d (node ⟨4,by decide⟩ 0) 1)
      (highPairs d (node ⟨4,by decide⟩ 1) 0) (highPairs d (node ⟨4,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨4,by decide⟩ 0) (native_orth c d hc hd hdist ⟨4,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨4,by decide⟩] at he
    change ((Q d ⟨1,by decide⟩+Q d ⟨3,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨1,by decide⟩ 0*highPairs d ⟨3,by decide⟩ 1-
        highPairs d ⟨3,by decide⟩ 0*highPairs d ⟨1,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination -he
  · have he := SixQubit.Pair29.perp_det
      (bottom c ⟨5,by decide⟩ 0) (bottom c ⟨5,by decide⟩ 1)
      (highPairs d (node ⟨5,by decide⟩ 0) 0) (highPairs d (node ⟨5,by decide⟩ 0) 1)
      (highPairs d (node ⟨5,by decide⟩ 1) 0) (highPairs d (node ⟨5,by decide⟩ 1) 1)
      (native_orth c d hc hd hdist ⟨5,by decide⟩ 0) (native_orth c d hc hd hdist ⟨5,by decide⟩ 1)
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add,
      bottom_mass c d h ⟨5,by decide⟩] at he
    change ((Q d ⟨2,by decide⟩+Q d ⟨3,by decide⟩-1/4 : ℝ) : ℂ)*
      (highPairs d ⟨2,by decide⟩ 0*highPairs d ⟨3,by decide⟩ 1-
        highPairs d ⟨3,by decide⟩ 0*highPairs d ⟨2,by decide⟩ 1)=0 at he
    push_cast at he ⊢
    linear_combination -he
  · ring

theorem high_parallel (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ i j,
    highPairs d i 0*highPairs d j 1-highPairs d j 0*highPairs d i 1=0 := by
  apply Orbit29PairBalance.parallel_all (fun i => highPairs d i 0) (fun i => highPairs d i 1) (Q d)
    (total_high_mass c d h) (high_mass_bound c d h)
  · intro i
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  · intro i
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq,← Complex.ofReal_add]
    rfl
  · exact weighted_determinants c d h hc hd hdist

theorem high_balanced (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ i,
    Complex.normSq (highPairs d i 0)=Complex.normSq (highPairs d i 1) := by
  apply Orbit29PairBalance.balanced_high (fun i => highPairs d i 0) (fun i => highPairs d i 1)
  · have he := total_high_mass c d h
    simpa only [Q,Finset.sum_add_distrib] using he
  · have he := me h
    norm_num [highPairs,Fin.sum_univ_succ,Fin.succ]
    linarith
  · exact high_parallel c d h hc hd hdist

theorem bottom_balanced (c d : SS.State 6 ℂ) (h : Moment c d)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hdist : SS.HasDistance ![c,d] 3) : ∀ e,
    Complex.normSq (bottom c e 0)=Complex.normSq (bottom c e 1) := by
  intro e
  have hw := bottom_mass c d h e
  have hnn0 := Complex.normSq_nonneg (bottom c e 0)
  have hnn1 := Complex.normSq_nonneg (bottom c e 1)
  have hqa : 0 ≤ Q d (node e 0) := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hqb : 0 ≤ Q d (node e 1) := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  by_cases ha : Q d (node e 0)=0
  · have hp : 0 < Q d (node e 1) := by linarith
    exact Orbit29PairBalance.perpendicular_balance _ _ _ _
      (native_orth c d hc hd hdist e 1) (high_balanced c d h hc hd hdist _ ) hp
  · have hp : 0 < Q d (node e 0) := lt_of_le_of_ne hqa (Ne.symm ha)
    exact Orbit29PairBalance.perpendicular_balance _ _ _ _
      (native_orth c d hc hd hdist e 0) (high_balanced c d h hc hd hdist _ ) hp

end
end MainTheory.Orbit29PhysicalPairReduction
