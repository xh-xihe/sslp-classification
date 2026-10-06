import SixQubit.CodeOrbit14
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit14ParityFrames
open scoped BigOperators Matrix
open SixQubit SixQubit.Orbit14
noncomputable section
def effective (x : SS.BitString 6) : SS.BitString 4 := ![x 1,x 3,x 4,x 5]
def parity (z : SS.BitString 4) : Bool := (List.ofFn z).count true % 2 = 1
def pack (a : Bool) (z : SS.BitString 4) : SS.BitString 6 := ![a,z 0,z 0,z 1,z 2,z 3]
def spinor (c : SS.State 6 ℂ) (z : SS.BitString 4) : Fin 2 → ℂ :=
  fun a => c (pack (a=1) z)
theorem literal_fibers : ∀ x : SS.BitString 6,
    (x∈S0 ↔ x 1=x 2 ∧ parity (effective x)=false) ∧
    (x∈S1 ↔ x 1=x 2 ∧ parity (effective x)=true) := by decide +kernel
theorem pack_reconstruction : ∀ x : SS.BitString 6,x∈S0 ∪ S1 →
    pack (x 0) (effective x)=x := by decide +kernel
theorem pack_injective : Function.Injective (fun p : Bool × SS.BitString 4 => pack p.1 p.2) := by decide +kernel
theorem bottom_coordinates : (Finset.univ.filter fun p : Bool × SS.BitString 4 => parity p.2=false).image
    (fun p => pack p.1 p.2)=S0 := by decide +kernel
theorem top_coordinates : (Finset.univ.filter fun p : Bool × SS.BitString 4 => parity p.2=true).image
    (fun p => pack p.1 p.2)=S1 := by decide +kernel

def FrameData (c d : SS.State 6 ℂ) : Prop :=
  (star (c y0) * d z2 + star (c y8) * d z10 = 0) ∧
  (star (c y0) * d z1 + star (c y8) * d z9 = 0) ∧
  (star (c y0) * d z0 + star (c y8) * d z8 = 0) ∧
  (star (c y1) * d z3 + star (c y9) * d z11 = 0) ∧
  (star (c y1) * d z1 + star (c y9) * d z9 = 0) ∧
  (star (c y1) * d z0 + star (c y9) * d z8 = 0) ∧
  (star (c y2) * d z3 + star (c y10) * d z11 = 0) ∧
  (star (c y2) * d z2 + star (c y10) * d z10 = 0) ∧
  (star (c y2) * d z0 + star (c y10) * d z8 = 0) ∧
  (star (c y3) * d z3 + star (c y11) * d z11 = 0) ∧
  (star (c y3) * d z2 + star (c y11) * d z10 = 0) ∧
  (star (c y3) * d z1 + star (c y11) * d z9 = 0) ∧
  (c y0 * star (c y8) + c y1 * star (c y9) + c y2 * star (c y10) + c y3 * star (c y11)
      = d z3 * star (d z11) + d z2 * star (d z10) + d z1 * star (d z9) + d z0 * star (d z8)) ∧
  (star (c y4) * d z6 + star (c y12) * d z14 = 0) ∧
  (star (c y4) * d z5 + star (c y12) * d z13 = 0) ∧
  (star (c y4) * d z4 + star (c y12) * d z12 = 0) ∧
  (star (c y5) * d z7 + star (c y13) * d z15 = 0) ∧
  (star (c y5) * d z5 + star (c y13) * d z13 = 0) ∧
  (star (c y5) * d z4 + star (c y13) * d z12 = 0) ∧
  (star (c y6) * d z7 + star (c y14) * d z15 = 0) ∧
  (star (c y6) * d z6 + star (c y14) * d z14 = 0) ∧
  (star (c y6) * d z4 + star (c y14) * d z12 = 0) ∧
  (star (c y7) * d z7 + star (c y15) * d z15 = 0) ∧
  (star (c y7) * d z6 + star (c y15) * d z14 = 0) ∧
  (star (c y7) * d z5 + star (c y15) * d z13 = 0) ∧
  (c y4 * star (c y12) + c y5 * star (c y13) + c y6 * star (c y14) + c y7 * star (c y15)
      = d z7 * star (d z15) + d z6 * star (d z14) + d z5 * star (d z13) + d z4 * star (d z12)) ∧
  (Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) = Complex.normSq (d z3) + Complex.normSq (d z2) + Complex.normSq (d z1) + Complex.normSq (d z0)) ∧
  (Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) = Complex.normSq (d z11) + Complex.normSq (d z10) + Complex.normSq (d z9) + Complex.normSq (d z8)) ∧
  (Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) = Complex.normSq (d z7) + Complex.normSq (d z6) + Complex.normSq (d z5) + Complex.normSq (d z4)) ∧
  (Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) = Complex.normSq (d z15) + Complex.normSq (d z14) + Complex.normSq (d z13) + Complex.normSq (d z12))

theorem frame_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho_ef1_w0 : offSum c d ef1 w0 = 0)
    (ho_ef1_w1 : offSum c d ef1 w1 = 0)
    (ho_ef1_w2 : offSum c d ef1 w2 = 0)
    (ho_ef1_w4 : offSum c d ef1 w4 = 0)
    (ho_ef1_w5 : offSum c d ef1 w5 = 0)
    (ho_ef1_w6 : offSum c d ef1 w6 = 0)
    (ho_ef1_w7 : offSum c d ef1 w7 = 0)
    (ho_ef1_w10 : offSum c d ef1 w10 = 0)
    (ho_ef2_w0 : offSum c d ef2 w0 = 0)
    (ho_ef2_w1 : offSum c d ef2 w1 = 0)
    (ho_ef2_w2 : offSum c d ef2 w2 = 0)
    (ho_ef2_w3 : offSum c d ef2 w3 = 0)
    (ho_ef2_w4 : offSum c d ef2 w4 = 0)
    (ho_ef2_w6 : offSum c d ef2 w6 = 0)
    (ho_ef2_w7 : offSum c d ef2 w7 = 0)
    (ho_ef2_w9 : offSum c d ef2 w9 = 0)
    (ho_ef3_w0 : offSum c d ef3 w0 = 0)
    (ho_ef3_w1 : offSum c d ef3 w1 = 0)
    (ho_ef3_w2 : offSum c d ef3 w2 = 0)
    (ho_ef3_w3 : offSum c d ef3 w3 = 0)
    (ho_ef3_w4 : offSum c d ef3 w4 = 0)
    (ho_ef3_w5 : offSum c d ef3 w5 = 0)
    (ho_ef3_w7 : offSum c d ef3 w7 = 0)
    (ho_ef3_w8 : offSum c d ef3 w8 = 0)
    (hd_w0 : diagBot c efF w0 = diagTop d efF w0)
    (hd_w12 : diagBot c efF w12 = diagTop d efF w12)
    (hd_w11 : diagBot c efF w11 = diagTop d efF w11)
    (hd_w13 : diagBot c efF w13 = diagTop d efF w13)
    : FrameData c d := by
  rw [ex_ef1_w0] at ho_ef1_w0
  rw [ex_ef1_w1] at ho_ef1_w1
  rw [ex_ef1_w2] at ho_ef1_w2
  rw [ex_ef1_w4] at ho_ef1_w4
  rw [ex_ef1_w5] at ho_ef1_w5
  rw [ex_ef1_w6] at ho_ef1_w6
  rw [ex_ef1_w7] at ho_ef1_w7
  rw [ex_ef1_w10] at ho_ef1_w10
  rw [ex_ef2_w0] at ho_ef2_w0
  rw [ex_ef2_w1] at ho_ef2_w1
  rw [ex_ef2_w2] at ho_ef2_w2
  rw [ex_ef2_w3] at ho_ef2_w3
  rw [ex_ef2_w4] at ho_ef2_w4
  rw [ex_ef2_w6] at ho_ef2_w6
  rw [ex_ef2_w7] at ho_ef2_w7
  rw [ex_ef2_w9] at ho_ef2_w9
  rw [ex_ef3_w0] at ho_ef3_w0
  rw [ex_ef3_w1] at ho_ef3_w1
  rw [ex_ef3_w2] at ho_ef3_w2
  rw [ex_ef3_w3] at ho_ef3_w3
  rw [ex_ef3_w4] at ho_ef3_w4
  rw [ex_ef3_w5] at ho_ef3_w5
  rw [ex_ef3_w7] at ho_ef3_w7
  rw [ex_ef3_w8] at ho_ef3_w8
  rw [dexB_w0, dexT_w0] at hd_w0
  rw [dexB_w12, dexT_w12] at hd_w12
  rw [dexB_w11, dexT_w11] at hd_w11
  rw [dexB_w13, dexT_w13] at hd_w13
  obtain ⟨sd0, sd1, sd2, sd3, sd4, sd5, sd6, sd7, sd8, sd9, sd10, sd11⟩ := hm.sliceData
  have s0o12 : star (c y0) * d z2 + star (c y8) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s0o13 : star (c y0) * d z1 + star (c y8) * d z9 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s0o14 : star (c y0) * d z0 + star (c y8) * d z8 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s0o21 : star (c y1) * d z3 + star (c y9) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s0o23 : star (c y1) * d z1 + star (c y9) * d z9 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s0o24 : star (c y1) * d z0 + star (c y9) * d z8 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s0o31 : star (c y2) * d z3 + star (c y10) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s0o32 : star (c y2) * d z2 + star (c y10) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s0o34 : star (c y2) * d z0 + star (c y10) * d z8 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s0o41 : star (c y3) * d z3 + star (c y11) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s0o42 : star (c y3) * d z2 + star (c y11) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s0o43 : star (c y3) * d z1 + star (c y11) * d z9 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s0fB : c y0 * star (c y8) + c y1 * star (c y9) + c y2 * star (c y10) + c y3 * star (c y11)
      = d z3 * star (d z11) + d z2 * star (d z10) + d z1 * star (d z9) + d z0 * star (d z8) := by
    linear_combination (1/4 : ℂ) * hd_w0 + (1/4 : ℂ) * hd_w12 + (1/4 : ℂ) * hd_w11 + (1/4 : ℂ) * hd_w13
  have s1o12 : star (c y4) * d z6 + star (c y12) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s1o13 : star (c y4) * d z5 + star (c y12) * d z13 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s1o14 : star (c y4) * d z4 + star (c y12) * d z12 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s1o21 : star (c y5) * d z7 + star (c y13) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (-1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (1/8 : ℂ) * ho_ef1_w10
  have s1o23 : star (c y5) * d z5 + star (c y13) * d z13 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (1/8 : ℂ) * ho_ef3_w3 + (1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s1o24 : star (c y5) * d z4 + star (c y13) * d z12 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (1/8 : ℂ) * ho_ef2_w3 + (1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s1o31 : star (c y6) * d z7 + star (c y14) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (1/8 : ℂ) * ho_ef2_w1 + (-1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (1/8 : ℂ) * ho_ef2_w9
  have s1o32 : star (c y6) * d z6 + star (c y14) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (-1/8 : ℂ) * ho_ef3_w1 + (1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (1/8 : ℂ) * ho_ef3_w8
  have s1o34 : star (c y6) * d z4 + star (c y14) * d z12 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (1/8 : ℂ) * ho_ef1_w1 + (1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (1/8 : ℂ) * ho_ef1_w5 + (1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s1o41 : star (c y7) * d z7 + star (c y15) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef3_w0 + (1/8 : ℂ) * ho_ef3_w1 + (-1/8 : ℂ) * ho_ef3_w2 + (-1/8 : ℂ) * ho_ef3_w3 + (-1/8 : ℂ) * ho_ef3_w4 + (-1/8 : ℂ) * ho_ef3_w5 + (-1/8 : ℂ) * ho_ef3_w7 + (-1/8 : ℂ) * ho_ef3_w8
  have s1o42 : star (c y7) * d z6 + star (c y15) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef2_w0 + (-1/8 : ℂ) * ho_ef2_w1 + (1/8 : ℂ) * ho_ef2_w2 + (-1/8 : ℂ) * ho_ef2_w3 + (-1/8 : ℂ) * ho_ef2_w4 + (-1/8 : ℂ) * ho_ef2_w6 + (-1/8 : ℂ) * ho_ef2_w7 + (-1/8 : ℂ) * ho_ef2_w9
  have s1o43 : star (c y7) * d z5 + star (c y15) * d z13 = 0 := by
    linear_combination (1/8 : ℂ) * ho_ef1_w0 + (-1/8 : ℂ) * ho_ef1_w1 + (-1/8 : ℂ) * ho_ef1_w2 + (1/8 : ℂ) * ho_ef1_w4 + (-1/8 : ℂ) * ho_ef1_w5 + (-1/8 : ℂ) * ho_ef1_w6 + (-1/8 : ℂ) * ho_ef1_w7 + (-1/8 : ℂ) * ho_ef1_w10
  have s1fB : c y4 * star (c y12) + c y5 * star (c y13) + c y6 * star (c y14) + c y7 * star (c y15)
      = d z7 * star (d z15) + d z6 * star (d z14) + d z5 * star (d z13) + d z4 * star (d z12) := by
    linear_combination (1/4 : ℂ) * hd_w0 + (1/4 : ℂ) * hd_w12 + (-1/4 : ℂ) * hd_w11 + (-1/4 : ℂ) * hd_w13
  exact ⟨s0o12,s0o13,s0o14,s0o21,s0o23,s0o24,s0o31,s0o32,s0o34,s0o41,s0o42,s0o43,s0fB,s1o12,s1o13,s1o14,s1o21,s1o23,s1o24,s1o31,s1o32,s1o34,s1o41,s1o42,s1o43,s1fB,sd0,sd1,sd6,sd7⟩

theorem physical_frame_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : FrameData c d :=
  frame_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w4 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w5 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w6 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w7 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w10 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w4 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w6 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w7 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w9 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w4 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w5 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w7 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w8 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efF w0 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efF w12 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efF w11 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efF w13 (by decide +kernel))


def bottomWords : Fin 8 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7]
def bottomWordsOne : Fin 8 → SS.BitString 6 := ![y8,y9,y10,y11,y12,y13,y14,y15]
def topWords : Fin 8 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7]
def topWordsOne : Fin 8 → SS.BitString 6 := ![z8,z9,z10,z11,z12,z13,z14,z15]
def bottomLabels (i : Fin 8) := effective (bottomWords i)
def topLabels (i : Fin 8) := effective (topWords i)
def bottomSpinor (c : SS.State 6 ℂ) (i : Fin 8) : Fin 2 → ℂ :=
  ![c (bottomWords i),c (bottomWordsOne i)]
def topSpinor (d : SS.State 6 ℂ) (i : Fin 8) : Fin 2 → ℂ :=
  ![d (topWords i),d (topWordsOne i)]
theorem bottom_spinor_words : ∀ (i : Fin 8) (a : Fin 2),pack (a=1) (bottomLabels i)=
    (if a=0 then bottomWords i else bottomWordsOne i) := by decide +kernel
theorem top_spinor_words : ∀ (i : Fin 8) (a : Fin 2),pack (a=1) (topLabels i)=
    (if a=0 then topWords i else topWordsOne i) := by decide +kernel
theorem bottom_labels_exact : Function.Injective bottomLabels ∧
    Finset.univ.image bottomLabels=Finset.univ.filter (fun z => parity z=false) := by decide +kernel
theorem top_labels_exact : Function.Injective topLabels ∧
    Finset.univ.image topLabels=Finset.univ.filter (fun z => parity z=true) := by decide +kernel
theorem actual_bottom_spinor (c : SS.State 6 ℂ) (i : Fin 8) :
    bottomSpinor c i=spinor c (bottomLabels i) := by
  funext a
  rw [spinor,bottom_spinor_words]
  fin_cases a <;> simp [bottomSpinor]
theorem actual_top_spinor (d : SS.State 6 ℂ) (i : Fin 8) :
    topSpinor d i=spinor d (topLabels i) := by
  funext a
  rw [spinor,top_spinor_words]
  fin_cases a <;> simp [topSpinor]
def bottomFrame (c : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i,Matrix.vecMulVec (bottomSpinor c i) (star (bottomSpinor c i))
def topFrame (d : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i,Matrix.vecMulVec (topSpinor d i) (star (topSpinor d i))
theorem frame_of_data (c d : SS.State 6 ℂ) (h : FrameData c d) :
    bottomFrame c=topFrame d := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩ := h
  have c26 := congrArg (fun x : ℝ => (x : ℂ)) h26
  push_cast at c26
  simp only [Complex.normSq_eq_conj_mul_self] at c26
  have c27 := congrArg (fun x : ℝ => (x : ℂ)) h27
  push_cast at c27
  simp only [Complex.normSq_eq_conj_mul_self] at c27
  have c28 := congrArg (fun x : ℝ => (x : ℂ)) h28
  push_cast at c28
  simp only [Complex.normSq_eq_conj_mul_self] at c28
  have c29 := congrArg (fun x : ℝ => (x : ℂ)) h29
  push_cast at c29
  simp only [Complex.normSq_eq_conj_mul_self] at c29
  have s12 := congrArg star h12
  have s25 := congrArg star h25
  ext a b
  fin_cases a <;> fin_cases b
  all_goals norm_num [bottomFrame,topFrame,bottomSpinor,topSpinor,bottomWords,bottomWordsOne,topWords,topWordsOne,Matrix.sum_apply,Matrix.vecMulVec_apply,Pi.star_apply,Fin.sum_univ_succ,Fin.succ] at c26 c27 c28 c29 h12 h25 s12 s25 ⊢
  all_goals simp only [starRingEnd_apply] at c26 c27 c28 c29 h12 h25 s12 s25 ⊢
  · linear_combination c26+c28
  · linear_combination h12+h25
  · linear_combination s12+s25
  · linear_combination c27+c29
theorem physical_frame_equality (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : bottomFrame c=topFrame d := by
  exact frame_of_data c d (physical_frame_data c d hc hd hnc hnd hkl)

end
end MainTheory.Orbit14ParityFrames
