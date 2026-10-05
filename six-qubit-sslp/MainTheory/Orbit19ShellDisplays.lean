import SixQubit.CodeOrbit19
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit19ShellDisplays
open scoped BigOperators
open SixQubit SixQubit.Orbit19
noncomputable section
def bit (x : SS.BitString 6) (j : Fin 6) : ℤ := if x j then 1 else 0
def w (x : SS.BitString 6) : ℤ := ∑ j : Fin 4,bit x (Fin.castAdd 2 j)
def g0 (x : SS.BitString 6) : ℚ := ((w x : ℚ)-2)*((w x : ℚ)-4)/8
def g4 (x : SS.BitString 6) : ℚ := (w x : ℚ)*((w x : ℚ)-2)/8
def h (x : SS.BitString 6) : ℚ := g0 x+g4 x
def u (x : SS.BitString 6) : ℚ := (bit x 4 : ℚ)+(bit x 5 : ℚ)-2*(bit x 4 : ℚ)*(bit x 5 : ℚ)
def chi (j : Fin 6) (x : SS.BitString 6) : ℚ := if x j then -1 else 1
def sign (a : Bool) : ℚ := if a then -1 else 1
def sigma (x : SS.BitString 6) : ℚ := ∑ j : Fin 4,chi (Fin.castAdd 2 j) x
def phi5 (a b : Bool) (x : SS.BitString 6) : ℚ :=
  (1+sign b*chi 4 x)/16*(2+sign a*sigma x-2*sign b*chi 5 x)
def phi6 (a b : Bool) (x : SS.BitString 6) : ℚ :=
  (1+sign b*chi 5 x)/16*(2+sign a*sigma x-2*sign b*chi 4 x)

theorem literal_fibers : ∀ x : SS.BitString 6,
    (x∈S0 ↔ ((w x=0 ∨ w x=4) ∧ x 4=x 5) ∨ (w x=2 ∧ x 4≠x 5)) ∧
    (x∈S1 ↔ ((w x=0 ∨ w x=4) ∧ x 4≠x 5) ∨ (w x=2 ∧ x 4=x 5)) := by decide +kernel
theorem square_weight : ∀ x : SS.BitString 6,
    w x^2=w x+2*(∑ i : Fin 4,∑ j : Fin 4,
      if i<j then bit x (Fin.castAdd 2 i)*bit x (Fin.castAdd 2 j) else 0) := by decide +kernel
theorem shell_projectors : ∀ x : SS.BitString 6,x∈S0 ∪ S1 →
    g0 x=(if w x=0 then 1 else 0) ∧ g4 x=(if w x=4 then 1 else 0) := by decide +kernel
theorem u_restriction : (∀ x : SS.BitString 6,x∈S0 → u x=1-h x) ∧
    (∀ x : SS.BitString 6,x∈S1 → u x=h x) := by decide +kernel
theorem phi5_anchor : ∀ a b x,x∈S1 →
    phi5 a b x=(if x=![a,a,a,a,b,!b] then 1 else 0) := by decide +kernel
theorem phi6_anchor : ∀ a b x,x∈S1 →
    phi6 a b x=(if x=![a,a,a,a,!b,b] then 1 else 0) := by decide +kernel
theorem phi5_expansion : ∀ a b x,
    16*phi5 a b x=2+sign a*sigma x-2*sign b*chi 5 x+2*sign b*chi 4 x+
      sign a*sign b*chi 4 x*sigma x-2*chi 4 x*chi 5 x := by decide +kernel
theorem phi6_expansion : ∀ a b x,
    16*phi6 a b x=2+sign a*sigma x-2*sign b*chi 4 x+2*sign b*chi 5 x+
      sign a*sign b*chi 5 x*sigma x-2*chi 5 x*chi 4 x := by decide +kernel

def AnchorData (c d : SS.State 6 ℂ) : Prop :=
  (star (c y1) * d z0 = 0) ∧
  (star (c y0) * d z1 = 0) ∧
  (star (c y15) * d z14 = 0) ∧
  (star (c y14) * d z15 = 0) ∧
  (star (c y0) * d z0 = 0) ∧
  (star (c y1) * d z1 = 0) ∧
  (star (c y14) * d z14 = 0) ∧
  (star (c y15) * d z15 = 0) ∧
  (Complex.normSq (c y0)+Complex.normSq (c y1)=Complex.normSq (d z0)+Complex.normSq (d z1)) ∧
  (Complex.normSq (c y14)+Complex.normSq (c y15)=Complex.normSq (d z14)+Complex.normSq (d z15)) ∧
  (Complex.normSq (c y0)+Complex.normSq (c y1)+Complex.normSq (c y14)+Complex.normSq (c y15)=1/2) ∧
  ((Complex.normSq (c y0) + Complex.normSq (c y1)) *
      (Complex.normSq (d z0) + Complex.normSq (d z1)) = 0) ∧
  ((Complex.normSq (c y14) + Complex.normSq (c y15)) *
      (Complex.normSq (d z14) + Complex.normSq (d z15)) = 0)

theorem anchor_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (h0 : offSum c d efA w0 = 0)
    (h1 : offSum c d efA w1 = 0)
    (h2 : offSum c d efA w2 = 0)
    (h3 : offSum c d efA w3 = 0)
    (h4 : offSum c d efA w4 = 0)
    (h5 : offSum c d efA w6 = 0)
    (h6 : offSum c d efA w7 = 0)
    (h7 : offSum c d efA w9 = 0)
    (h8 : offSum c d efA w10 = 0)
    (h9 : offSum c d efA w12 = 0)
    (h10 : offSum c d efA w13 = 0)
    (h11 : offSum c d efA w15 = 0)
    (h12 : offSum c d efB w0 = 0)
    (h13 : offSum c d efB w1 = 0)
    (h14 : offSum c d efB w2 = 0)
    (h15 : offSum c d efB w3 = 0)
    (h16 : offSum c d efB w4 = 0)
    (h17 : offSum c d efB w5 = 0)
    (h18 : offSum c d efB w7 = 0)
    (h19 : offSum c d efB w8 = 0)
    (h20 : offSum c d efB w10 = 0)
    (h21 : offSum c d efB w11 = 0)
    (h22 : offSum c d efB w13 = 0)
    (h23 : offSum c d efB w14 = 0)
    : AnchorData c d := by
  rw [exA_w0] at h0
  rw [exA_w1] at h1
  rw [exA_w2] at h2
  rw [exA_w3] at h3
  rw [exA_w4] at h4
  rw [exA_w6] at h5
  rw [exA_w7] at h6
  rw [exA_w9] at h7
  rw [exA_w10] at h8
  rw [exA_w12] at h9
  rw [exA_w13] at h10
  rw [exA_w15] at h11
  rw [exB_w0] at h12
  rw [exB_w1] at h13
  rw [exB_w2] at h14
  rw [exB_w3] at h15
  rw [exB_w4] at h16
  rw [exB_w5] at h17
  rw [exB_w7] at h18
  rw [exB_w8] at h19
  rw [exB_w10] at h20
  rw [exB_w11] at h21
  rw [exB_w13] at h22
  rw [exB_w14] at h23
  have p0 : star (c y1) * d z0 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (1/16 : ℂ) * h4 + (1/16 : ℂ) * h5 + (1/16 : ℂ) * h6 + (1/16 : ℂ) * h7 + (1/16 : ℂ) * h8 + (1/16 : ℂ) * h9 + (1/16 : ℂ) * h10 + (1/16 : ℂ) * h11
  have p1 : star (c y0) * d z1 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (1/16 : ℂ) * h4 + (-1/16 : ℂ) * h5 + (1/16 : ℂ) * h6 + (-1/16 : ℂ) * h7 + (1/16 : ℂ) * h8 + (-1/16 : ℂ) * h9 + (1/16 : ℂ) * h10 + (-1/16 : ℂ) * h11
  have p2 : star (c y15) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (-1/16 : ℂ) * h4 + (-1/16 : ℂ) * h5 + (-1/16 : ℂ) * h6 + (-1/16 : ℂ) * h7 + (-1/16 : ℂ) * h8 + (-1/16 : ℂ) * h9 + (-1/16 : ℂ) * h10 + (-1/16 : ℂ) * h11
  have p3 : star (c y14) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (-1/16 : ℂ) * h4 + (1/16 : ℂ) * h5 + (-1/16 : ℂ) * h6 + (1/16 : ℂ) * h7 + (-1/16 : ℂ) * h8 + (1/16 : ℂ) * h9 + (-1/16 : ℂ) * h10 + (1/16 : ℂ) * h11
  have p4 : star (c y0) * d z0 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (1/16 : ℂ) * h16 + (-1/16 : ℂ) * h17 + (1/16 : ℂ) * h18 + (-1/16 : ℂ) * h19 + (1/16 : ℂ) * h20 + (-1/16 : ℂ) * h21 + (1/16 : ℂ) * h22 + (-1/16 : ℂ) * h23
  have p5 : star (c y1) * d z1 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (1/16 : ℂ) * h16 + (1/16 : ℂ) * h17 + (1/16 : ℂ) * h18 + (1/16 : ℂ) * h19 + (1/16 : ℂ) * h20 + (1/16 : ℂ) * h21 + (1/16 : ℂ) * h22 + (1/16 : ℂ) * h23
  have p6 : star (c y14) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (-1/16 : ℂ) * h16 + (1/16 : ℂ) * h17 + (-1/16 : ℂ) * h18 + (1/16 : ℂ) * h19 + (-1/16 : ℂ) * h20 + (1/16 : ℂ) * h21 + (-1/16 : ℂ) * h22 + (1/16 : ℂ) * h23
  have p7 : star (c y15) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15 + (-1/16 : ℂ) * h16 + (-1/16 : ℂ) * h17 + (-1/16 : ℂ) * h18 + (-1/16 : ℂ) * h19 + (-1/16 : ℂ) * h20 + (-1/16 : ℂ) * h21 + (-1/16 : ℂ) * h22 + (-1/16 : ℂ) * h23
  have n0 : Complex.normSq (c y1) * Complex.normSq (d z0) = 0 := nsqZero p0
  have n1 : Complex.normSq (c y0) * Complex.normSq (d z1) = 0 := nsqZero p1
  have n2 : Complex.normSq (c y15) * Complex.normSq (d z14) = 0 := nsqZero p2
  have n3 : Complex.normSq (c y14) * Complex.normSq (d z15) = 0 := nsqZero p3
  have n4 : Complex.normSq (c y0) * Complex.normSq (d z0) = 0 := nsqZero p4
  have n5 : Complex.normSq (c y1) * Complex.normSq (d z1) = 0 := nsqZero p5
  have n6 : Complex.normSq (c y14) * Complex.normSq (d z14) = 0 := nsqZero p6
  have n7 : Complex.normSq (c y15) * Complex.normSq (d z15) = 0 := nsqZero p7
  obtain ⟨a0, a4, ah⟩ := hm.anchors
  have z0m : (Complex.normSq (c y0) + Complex.normSq (c y1)) *
      (Complex.normSq (d z0) + Complex.normSq (d z1)) = 0 := by
    linear_combination n4 + n1 + n0 + n5
  have z4m : (Complex.normSq (c y14) + Complex.normSq (c y15)) *
      (Complex.normSq (d z14) + Complex.normSq (d z15)) = 0 := by
    linear_combination n6 + n3 + n2 + n7
  exact ⟨p0,p1,p2,p3,p4,p5,p6,p7,a0,a4,ah,z0m,z4m⟩

theorem physical_anchor_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : AnchorData c d :=
  anchor_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w4 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w6 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w7 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w9 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w10 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w12 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w13 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w15 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w4 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w5 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w7 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w8 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w10 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w11 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w13 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w14 (by decide +kernel))

end
end MainTheory.Orbit19ShellDisplays
