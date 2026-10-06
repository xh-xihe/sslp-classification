import SixQubit.CodeOrbit17
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit17PhaseData
open scoped BigOperators
open SixQubit SixQubit.Orbit17
noncomputable section
def PhaseData (c d : SS.State 6 ℂ) : Prop :=
  (star (c y0) * d z14 + star (c y1) * d z15 = 0) ∧
  (star (c y0) * d z13 + star (c y2) * d z15 = 0) ∧
  (star (c y0) * d z12 + star (c y3) * d z15 = 0) ∧
  (star (c y0) * d z11 + star (c y4) * d z15 = 0) ∧
  (star (c y0) * d z10 + star (c y5) * d z15 = 0) ∧
  (star (c y0) * d z9 + star (c y6) * d z15 = 0) ∧
  (star (c y0) * d z8 + star (c y7) * d z15 = 0) ∧
  (star (c y0) * d z7 + star (c y8) * d z15 = 0) ∧
  (star (c y0) * d z6 + star (c y9) * d z15 = 0) ∧
  (star (c y0) * d z5 + star (c y10) * d z15 = 0) ∧
  (star (c y0) * d z4 + star (c y11) * d z15 = 0) ∧
  (star (c y0) * d z3 + star (c y12) * d z15 = 0) ∧
  (star (c y0) * d z2 + star (c y13) * d z15 = 0) ∧
  (star (c y0) * d z1 + star (c y14) * d z15 = 0) ∧
  (star (c y0) * d z0 + star (c y15) * d z15 = 0) ∧
  (star (c y15) * d z5 + star (c y14) * d z4 + star (c y13) * d z3 + star (c y12) * d z2 + star (c y11) * d z1 + star (c y10) * d z0 = 0) ∧
  (star (c y15) * d z8 + star (c y14) * d z7 + star (c y13) * d z6 + star (c y9) * d z2 + star (c y8) * d z1 + star (c y7) * d z0 = 0) ∧
  (star (c y15) * d z9 + star (c y12) * d z7 + star (c y11) * d z6 + star (c y9) * d z4 + star (c y8) * d z3 + star (c y6) * d z0 = 0) ∧
  (star (c y14) * d z9 + star (c y12) * d z8 + star (c y10) * d z6 + star (c y9) * d z5 + star (c y7) * d z3 + star (c y6) * d z1 = 0) ∧
  (star (c y13) * d z9 + star (c y11) * d z8 + star (c y10) * d z7 + star (c y8) * d z5 + star (c y7) * d z4 + star (c y6) * d z2 = 0) ∧
  (star (c y15) * d z12 + star (c y14) * d z11 + star (c y13) * d z10 + star (c y5) * d z2 + star (c y4) * d z1 + star (c y3) * d z0 = 0) ∧
  (star (c y15) * d z13 + star (c y12) * d z11 + star (c y11) * d z10 + star (c y5) * d z4 + star (c y4) * d z3 + star (c y2) * d z0 = 0) ∧
  (star (c y14) * d z13 + star (c y12) * d z12 + star (c y10) * d z10 + star (c y5) * d z5 + star (c y3) * d z3 + star (c y2) * d z1 = 0) ∧
  (star (c y13) * d z13 + star (c y11) * d z12 + star (c y10) * d z11 + star (c y4) * d z5 + star (c y3) * d z4 + star (c y2) * d z2 = 0) ∧
  (star (c y15) * d z14 + star (c y9) * d z11 + star (c y8) * d z10 + star (c y5) * d z7 + star (c y4) * d z6 + star (c y1) * d z0 = 0) ∧
  (star (c y14) * d z14 + star (c y9) * d z12 + star (c y7) * d z10 + star (c y5) * d z8 + star (c y3) * d z6 + star (c y1) * d z1 = 0) ∧
  (star (c y13) * d z14 + star (c y8) * d z12 + star (c y7) * d z11 + star (c y4) * d z8 + star (c y3) * d z7 + star (c y1) * d z2 = 0) ∧
  (star (c y12) * d z14 + star (c y9) * d z13 + star (c y6) * d z10 + star (c y5) * d z9 + star (c y2) * d z6 + star (c y1) * d z3 = 0) ∧
  (star (c y11) * d z14 + star (c y8) * d z13 + star (c y6) * d z11 + star (c y4) * d z9 + star (c y2) * d z7 + star (c y1) * d z4 = 0) ∧
  (star (c y10) * d z14 + star (c y7) * d z13 + star (c y6) * d z12 + star (c y3) * d z9 + star (c y2) * d z8 + star (c y1) * d z5 = 0) ∧
  (star (c y1) * star (c y10) + star (c y2) * star (c y7) + star (c y3) * star (c y6) = 0) ∧
  (star (c y1) * star (c y11) + star (c y2) * star (c y8) + star (c y4) * star (c y6) = 0) ∧
  (star (c y1) * star (c y12) + star (c y2) * star (c y9) + star (c y5) * star (c y6) = 0) ∧
  (star (c y1) * star (c y13) + star (c y3) * star (c y8) + star (c y4) * star (c y7) = 0) ∧
  (star (c y1) * star (c y14) + star (c y3) * star (c y9) + star (c y5) * star (c y7) = 0) ∧
  (star (c y1) * star (c y15) + star (c y4) * star (c y9) + star (c y5) * star (c y8) = 0) ∧
  (star (c y2) * star (c y13) + star (c y3) * star (c y11) + star (c y4) * star (c y10) = 0) ∧
  (star (c y2) * star (c y14) + star (c y3) * star (c y12) + star (c y5) * star (c y10) = 0) ∧
  (star (c y2) * star (c y15) + star (c y4) * star (c y12) + star (c y5) * star (c y11) = 0) ∧
  (star (c y3) * star (c y15) + star (c y4) * star (c y14) + star (c y5) * star (c y13) = 0) ∧
  (star (c y6) * star (c y13) + star (c y7) * star (c y11) + star (c y8) * star (c y10) = 0) ∧
  (star (c y6) * star (c y14) + star (c y7) * star (c y12) + star (c y9) * star (c y10) = 0) ∧
  (star (c y6) * star (c y15) + star (c y8) * star (c y12) + star (c y9) * star (c y11) = 0) ∧
  (star (c y7) * star (c y15) + star (c y8) * star (c y14) + star (c y9) * star (c y13) = 0) ∧
  (star (c y10) * star (c y15) + star (c y11) * star (c y14) + star (c y12) * star (c y13) = 0) ∧
  (Complex.normSq (star (c y1)) + Complex.normSq (star (c y2)) + Complex.normSq (star (c y3)) + Complex.normSq (star (c y4)) + Complex.normSq (star (c y5)) = 1/4) ∧
  (Complex.normSq (star (c y1)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y7)) + Complex.normSq (star (c y8)) + Complex.normSq (star (c y9)) = 1/4) ∧
  (Complex.normSq (star (c y2)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y12)) = 1/4) ∧
  (Complex.normSq (star (c y3)) + Complex.normSq (star (c y7)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y14)) = 1/4) ∧
  (Complex.normSq (star (c y4)) + Complex.normSq (star (c y8)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y15)) = 1/4) ∧
  (Complex.normSq (star (c y5)) + Complex.normSq (star (c y9)) + Complex.normSq (star (c y12)) + Complex.normSq (star (c y14)) + Complex.normSq (star (c y15)) = 1/4)

theorem phase_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho01a : offSum c d e01 wz = 0)
    (ho01b : offSum c d e01 wp0 = 0)
    (ho02a : offSum c d e02 wz = 0)
    (ho02b : offSum c d e02 wp0 = 0)
    (ho03a : offSum c d e03 wz = 0)
    (ho03b : offSum c d e03 wp0 = 0)
    (ho04a : offSum c d e04 wz = 0)
    (ho04b : offSum c d e04 wp0 = 0)
    (ho05a : offSum c d e05 wz = 0)
    (ho05b : offSum c d e05 wp0 = 0)
    (ho12a : offSum c d e12 wz = 0)
    (ho12b : offSum c d e12 wp1 = 0)
    (ho13a : offSum c d e13 wz = 0)
    (ho13b : offSum c d e13 wp1 = 0)
    (ho14a : offSum c d e14 wz = 0)
    (ho14b : offSum c d e14 wp1 = 0)
    (ho15a : offSum c d e15 wz = 0)
    (ho15b : offSum c d e15 wp1 = 0)
    (ho23a : offSum c d e23 wz = 0)
    (ho23b : offSum c d e23 wp2 = 0)
    (ho24a : offSum c d e24 wz = 0)
    (ho24b : offSum c d e24 wp2 = 0)
    (ho25a : offSum c d e25 wz = 0)
    (ho25b : offSum c d e25 wp2 = 0)
    (ho34a : offSum c d e34 wz = 0)
    (ho34b : offSum c d e34 wp3 = 0)
    (ho35a : offSum c d e35 wz = 0)
    (ho35b : offSum c d e35 wp3 = 0)
    (ho45a : offSum c d e45 wz = 0)
    (ho45b : offSum c d e45 wp4 = 0)
    : PhaseData c d := by
  rw [ex_e01_z] at ho01a
  rw [ex_e01_p] at ho01b
  rw [ex_e02_z] at ho02a
  rw [ex_e02_p] at ho02b
  rw [ex_e03_z] at ho03a
  rw [ex_e03_p] at ho03b
  rw [ex_e04_z] at ho04a
  rw [ex_e04_p] at ho04b
  rw [ex_e05_z] at ho05a
  rw [ex_e05_p] at ho05b
  rw [ex_e12_z] at ho12a
  rw [ex_e12_p] at ho12b
  rw [ex_e13_z] at ho13a
  rw [ex_e13_p] at ho13b
  rw [ex_e14_z] at ho14a
  rw [ex_e14_p] at ho14b
  rw [ex_e15_z] at ho15a
  rw [ex_e15_p] at ho15b
  rw [ex_e23_z] at ho23a
  rw [ex_e23_p] at ho23b
  rw [ex_e24_z] at ho24a
  rw [ex_e24_p] at ho24b
  rw [ex_e25_z] at ho25a
  rw [ex_e25_p] at ho25b
  rw [ex_e34_z] at ho34a
  rw [ex_e34_p] at ho34b
  rw [ex_e35_z] at ho35a
  rw [ex_e35_p] at ho35b
  rw [ex_e45_z] at ho45a
  rw [ex_e45_p] at ho45b
  obtain ⟨hr15, hg0, hg1, hg2, hg3, hg4, hg5⟩ := hm.normalForm
  have hz15 : d z15 ≠ 0 := by
    intro hx
    rw [hx] at hr15
    simp at hr15
  have an01 : star (c y0) * d z14 + star (c y1) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho01a - (1/2 : ℂ) * ho01b
  have an02 : star (c y0) * d z13 + star (c y2) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho02a - (1/2 : ℂ) * ho02b
  have an03 : star (c y0) * d z12 + star (c y3) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho03a - (1/2 : ℂ) * ho03b
  have an04 : star (c y0) * d z11 + star (c y4) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho04a - (1/2 : ℂ) * ho04b
  have an05 : star (c y0) * d z10 + star (c y5) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho05a - (1/2 : ℂ) * ho05b
  have an12 : star (c y0) * d z9 + star (c y6) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho12a - (1/2 : ℂ) * ho12b
  have an13 : star (c y0) * d z8 + star (c y7) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho13a - (1/2 : ℂ) * ho13b
  have an14 : star (c y0) * d z7 + star (c y8) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho14a - (1/2 : ℂ) * ho14b
  have an15 : star (c y0) * d z6 + star (c y9) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho15a - (1/2 : ℂ) * ho15b
  have an23 : star (c y0) * d z5 + star (c y10) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho23a - (1/2 : ℂ) * ho23b
  have an24 : star (c y0) * d z4 + star (c y11) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho24a - (1/2 : ℂ) * ho24b
  have an25 : star (c y0) * d z3 + star (c y12) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho25a - (1/2 : ℂ) * ho25b
  have an34 : star (c y0) * d z2 + star (c y13) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho34a - (1/2 : ℂ) * ho34b
  have an35 : star (c y0) * d z1 + star (c y14) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho35a - (1/2 : ℂ) * ho35b
  have an45 : star (c y0) * d z0 + star (c y15) * d z15 = 0 := by
    linear_combination (1/2 : ℂ) * ho45a - (1/2 : ℂ) * ho45b
  have pf01 : star (c y15) * d z5 + star (c y14) * d z4 + star (c y13) * d z3 + star (c y12) * d z2 + star (c y11) * d z1 + star (c y10) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho01a + (1/2 : ℂ) * ho01b
  have pf02 : star (c y15) * d z8 + star (c y14) * d z7 + star (c y13) * d z6 + star (c y9) * d z2 + star (c y8) * d z1 + star (c y7) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho02a + (1/2 : ℂ) * ho02b
  have pf03 : star (c y15) * d z9 + star (c y12) * d z7 + star (c y11) * d z6 + star (c y9) * d z4 + star (c y8) * d z3 + star (c y6) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho03a + (1/2 : ℂ) * ho03b
  have pf04 : star (c y14) * d z9 + star (c y12) * d z8 + star (c y10) * d z6 + star (c y9) * d z5 + star (c y7) * d z3 + star (c y6) * d z1 = 0 := by
    linear_combination (1/2 : ℂ) * ho04a + (1/2 : ℂ) * ho04b
  have pf05 : star (c y13) * d z9 + star (c y11) * d z8 + star (c y10) * d z7 + star (c y8) * d z5 + star (c y7) * d z4 + star (c y6) * d z2 = 0 := by
    linear_combination (1/2 : ℂ) * ho05a + (1/2 : ℂ) * ho05b
  have pf12 : star (c y15) * d z12 + star (c y14) * d z11 + star (c y13) * d z10 + star (c y5) * d z2 + star (c y4) * d z1 + star (c y3) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho12a + (1/2 : ℂ) * ho12b
  have pf13 : star (c y15) * d z13 + star (c y12) * d z11 + star (c y11) * d z10 + star (c y5) * d z4 + star (c y4) * d z3 + star (c y2) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho13a + (1/2 : ℂ) * ho13b
  have pf14 : star (c y14) * d z13 + star (c y12) * d z12 + star (c y10) * d z10 + star (c y5) * d z5 + star (c y3) * d z3 + star (c y2) * d z1 = 0 := by
    linear_combination (1/2 : ℂ) * ho14a + (1/2 : ℂ) * ho14b
  have pf15 : star (c y13) * d z13 + star (c y11) * d z12 + star (c y10) * d z11 + star (c y4) * d z5 + star (c y3) * d z4 + star (c y2) * d z2 = 0 := by
    linear_combination (1/2 : ℂ) * ho15a + (1/2 : ℂ) * ho15b
  have pf23 : star (c y15) * d z14 + star (c y9) * d z11 + star (c y8) * d z10 + star (c y5) * d z7 + star (c y4) * d z6 + star (c y1) * d z0 = 0 := by
    linear_combination (1/2 : ℂ) * ho23a + (1/2 : ℂ) * ho23b
  have pf24 : star (c y14) * d z14 + star (c y9) * d z12 + star (c y7) * d z10 + star (c y5) * d z8 + star (c y3) * d z6 + star (c y1) * d z1 = 0 := by
    linear_combination (1/2 : ℂ) * ho24a + (1/2 : ℂ) * ho24b
  have pf25 : star (c y13) * d z14 + star (c y8) * d z12 + star (c y7) * d z11 + star (c y4) * d z8 + star (c y3) * d z7 + star (c y1) * d z2 = 0 := by
    linear_combination (1/2 : ℂ) * ho25a + (1/2 : ℂ) * ho25b
  have pf34 : star (c y12) * d z14 + star (c y9) * d z13 + star (c y6) * d z10 + star (c y5) * d z9 + star (c y2) * d z6 + star (c y1) * d z3 = 0 := by
    linear_combination (1/2 : ℂ) * ho34a + (1/2 : ℂ) * ho34b
  have pf35 : star (c y11) * d z14 + star (c y8) * d z13 + star (c y6) * d z11 + star (c y4) * d z9 + star (c y2) * d z7 + star (c y1) * d z4 = 0 := by
    linear_combination (1/2 : ℂ) * ho35a + (1/2 : ℂ) * ho35b
  have pf45 : star (c y10) * d z14 + star (c y7) * d z13 + star (c y6) * d z12 + star (c y3) * d z9 + star (c y2) * d z8 + star (c y1) * d z5 = 0 := by
    linear_combination (1/2 : ℂ) * ho45a + (1/2 : ℂ) * ho45b
  have hf0123 : star (c y1) * star (c y10) + star (c y2) * star (c y7) + star (c y3) * star (c y6) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y10) + star (c y2) * star (c y7) + star (c y3) * star (c y6)) = 0 := by
      linear_combination star (c y10) * an01 + star (c y7) * an02 + star (c y6) * an03 + star (c y3) * an12 + star (c y2) * an13 + star (c y1) * an23 - star (c y0) * pf45
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0124 : star (c y1) * star (c y11) + star (c y2) * star (c y8) + star (c y4) * star (c y6) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y11) + star (c y2) * star (c y8) + star (c y4) * star (c y6)) = 0 := by
      linear_combination star (c y11) * an01 + star (c y8) * an02 + star (c y6) * an04 + star (c y4) * an12 + star (c y2) * an14 + star (c y1) * an24 - star (c y0) * pf35
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0125 : star (c y1) * star (c y12) + star (c y2) * star (c y9) + star (c y5) * star (c y6) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y12) + star (c y2) * star (c y9) + star (c y5) * star (c y6)) = 0 := by
      linear_combination star (c y12) * an01 + star (c y9) * an02 + star (c y6) * an05 + star (c y5) * an12 + star (c y2) * an15 + star (c y1) * an25 - star (c y0) * pf34
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0134 : star (c y1) * star (c y13) + star (c y3) * star (c y8) + star (c y4) * star (c y7) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y13) + star (c y3) * star (c y8) + star (c y4) * star (c y7)) = 0 := by
      linear_combination star (c y13) * an01 + star (c y8) * an03 + star (c y7) * an04 + star (c y4) * an13 + star (c y3) * an14 + star (c y1) * an34 - star (c y0) * pf25
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0135 : star (c y1) * star (c y14) + star (c y3) * star (c y9) + star (c y5) * star (c y7) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y14) + star (c y3) * star (c y9) + star (c y5) * star (c y7)) = 0 := by
      linear_combination star (c y14) * an01 + star (c y9) * an03 + star (c y7) * an05 + star (c y5) * an13 + star (c y3) * an15 + star (c y1) * an35 - star (c y0) * pf24
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0145 : star (c y1) * star (c y15) + star (c y4) * star (c y9) + star (c y5) * star (c y8) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y1) * star (c y15) + star (c y4) * star (c y9) + star (c y5) * star (c y8)) = 0 := by
      linear_combination star (c y15) * an01 + star (c y9) * an04 + star (c y8) * an05 + star (c y5) * an14 + star (c y4) * an15 + star (c y1) * an45 - star (c y0) * pf23
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0234 : star (c y2) * star (c y13) + star (c y3) * star (c y11) + star (c y4) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y2) * star (c y13) + star (c y3) * star (c y11) + star (c y4) * star (c y10)) = 0 := by
      linear_combination star (c y13) * an02 + star (c y11) * an03 + star (c y10) * an04 + star (c y4) * an23 + star (c y3) * an24 + star (c y2) * an34 - star (c y0) * pf15
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0235 : star (c y2) * star (c y14) + star (c y3) * star (c y12) + star (c y5) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y2) * star (c y14) + star (c y3) * star (c y12) + star (c y5) * star (c y10)) = 0 := by
      linear_combination star (c y14) * an02 + star (c y12) * an03 + star (c y10) * an05 + star (c y5) * an23 + star (c y3) * an25 + star (c y2) * an35 - star (c y0) * pf14
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0245 : star (c y2) * star (c y15) + star (c y4) * star (c y12) + star (c y5) * star (c y11) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y2) * star (c y15) + star (c y4) * star (c y12) + star (c y5) * star (c y11)) = 0 := by
      linear_combination star (c y15) * an02 + star (c y12) * an04 + star (c y11) * an05 + star (c y5) * an24 + star (c y4) * an25 + star (c y2) * an45 - star (c y0) * pf13
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf0345 : star (c y3) * star (c y15) + star (c y4) * star (c y14) + star (c y5) * star (c y13) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y3) * star (c y15) + star (c y4) * star (c y14) + star (c y5) * star (c y13)) = 0 := by
      linear_combination star (c y15) * an03 + star (c y14) * an04 + star (c y13) * an05 + star (c y5) * an34 + star (c y4) * an35 + star (c y3) * an45 - star (c y0) * pf12
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1234 : star (c y6) * star (c y13) + star (c y7) * star (c y11) + star (c y8) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y6) * star (c y13) + star (c y7) * star (c y11) + star (c y8) * star (c y10)) = 0 := by
      linear_combination star (c y13) * an12 + star (c y11) * an13 + star (c y10) * an14 + star (c y8) * an23 + star (c y7) * an24 + star (c y6) * an34 - star (c y0) * pf05
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1235 : star (c y6) * star (c y14) + star (c y7) * star (c y12) + star (c y9) * star (c y10) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y6) * star (c y14) + star (c y7) * star (c y12) + star (c y9) * star (c y10)) = 0 := by
      linear_combination star (c y14) * an12 + star (c y12) * an13 + star (c y10) * an15 + star (c y9) * an23 + star (c y7) * an25 + star (c y6) * an35 - star (c y0) * pf04
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1245 : star (c y6) * star (c y15) + star (c y8) * star (c y12) + star (c y9) * star (c y11) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y6) * star (c y15) + star (c y8) * star (c y12) + star (c y9) * star (c y11)) = 0 := by
      linear_combination star (c y15) * an12 + star (c y12) * an14 + star (c y11) * an15 + star (c y9) * an24 + star (c y8) * an25 + star (c y6) * an45 - star (c y0) * pf03
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf1345 : star (c y7) * star (c y15) + star (c y8) * star (c y14) + star (c y9) * star (c y13) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y7) * star (c y15) + star (c y8) * star (c y14) + star (c y9) * star (c y13)) = 0 := by
      linear_combination star (c y15) * an13 + star (c y14) * an14 + star (c y13) * an15 + star (c y9) * an34 + star (c y8) * an35 + star (c y7) * an45 - star (c y0) * pf02
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hf2345 : star (c y10) * star (c y15) + star (c y11) * star (c y14) + star (c y12) * star (c y13) = 0 := by
    have hk : (2 : ℂ) * d z15 * (star (c y10) * star (c y15) + star (c y11) * star (c y14) + star (c y12) * star (c y13)) = 0 := by
      linear_combination star (c y15) * an23 + star (c y14) * an24 + star (c y13) * an25 + star (c y12) * an34 + star (c y11) * an35 + star (c y10) * an45 - star (c y0) * pf01
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero two_ne_zero hz15)
  have hs0 : Complex.normSq (star (c y1)) + Complex.normSq (star (c y2)) + Complex.normSq (star (c y3)) + Complex.normSq (star (c y4)) + Complex.normSq (star (c y5)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg0]
  have hs1 : Complex.normSq (star (c y1)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y7)) + Complex.normSq (star (c y8)) + Complex.normSq (star (c y9)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg1]
  have hs2 : Complex.normSq (star (c y2)) + Complex.normSq (star (c y6)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y12)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg2]
  have hs3 : Complex.normSq (star (c y3)) + Complex.normSq (star (c y7)) + Complex.normSq (star (c y10)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y14)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg3]
  have hs4 : Complex.normSq (star (c y4)) + Complex.normSq (star (c y8)) + Complex.normSq (star (c y11)) + Complex.normSq (star (c y13)) + Complex.normSq (star (c y15)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg4]
  have hs5 : Complex.normSq (star (c y5)) + Complex.normSq (star (c y9)) + Complex.normSq (star (c y12)) + Complex.normSq (star (c y14)) + Complex.normSq (star (c y15)) = 1/4 := by
    simp only [nsq_star]
    linarith [hg5]
  exact ⟨an01,an02,an03,an04,an05,an12,an13,an14,an15,an23,an24,an25,an34,an35,an45,pf01,pf02,pf03,pf04,pf05,pf12,pf13,pf14,pf15,pf23,pf24,pf25,pf34,pf35,pf45,hf0123,hf0124,hf0125,hf0134,hf0135,hf0145,hf0234,hf0235,hf0245,hf0345,hf1234,hf1235,hf1245,hf1345,hf2345,hs0,hs1,hs2,hs3,hs4,hs5⟩

theorem physical_phase_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : PhaseData c d :=
  phase_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e01 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e01 wp0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e02 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e02 wp0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e03 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e03 wp0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e04 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e04 wp0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e05 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e05 wp0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e12 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e12 wp1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e13 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e13 wp1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e14 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e14 wp1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e15 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e15 wp1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e23 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e23 wp2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e24 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e24 wp2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e25 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e25 wp2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e34 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e34 wp3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e35 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e35 wp3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e45 wz (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      e45 wp4 (by decide +kernel))

end
end MainTheory.Orbit17PhaseData
