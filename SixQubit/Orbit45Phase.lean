import Mathlib

import SixQubit.Orbit45Support

/-!
# Orbit 45: exact cross-Walsh phase relations

Only the sparse row combinations used by the Gram/frame argument are exposed.
Every incidence and sign in the expansions is independently kernel-decided.
-/

namespace SixQubit.Orbit45Phase

open scoped ComplexConjugate
open SixQubit.Realize
open SixQubit.Orbit45Support

noncomputable section

def z01 : SS.BitString 6 := nbit 1
def z02 : SS.BitString 6 := nbit 2
def z16 : SS.BitString 6 := nbit 16
def z24 : SS.BitString 6 := nbit 24

def flip5 : SS.BitString 6 := nbit 5
def flip6 : SS.BitString 6 := nbit 6
def flip17 : SS.BitString 6 := nbit 17
def flip18 : SS.BitString 6 := nbit 18
def flip33 : SS.BitString 6 := nbit 33
def flip34 : SS.BitString 6 := nbit 34

theorem off8_01 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z01 = star (c x0) * d y0 + -star (c x1) * d y1 + star (c x2) * d y2 + -star (c x3) * d y3 + star (c x4) * d y4 + -star (c x5) * d y5 + star (c x6) * d y6 + -star (c x7) * d y7 + star (c x8) * d y8 + -star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z01 y0 = false from by decide,
    show SS.bdot z01 y1 = true from by decide,
    show SS.bdot z01 y2 = false from by decide,
    show SS.bdot z01 y3 = true from by decide,
    show SS.bdot z01 y4 = false from by decide,
    show SS.bdot z01 y5 = true from by decide,
    show SS.bdot z01 y6 = false from by decide,
    show SS.bdot z01 y7 = true from by decide,
    show SS.bdot z01 y8 = false from by decide,
    show SS.bdot z01 y9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off8_02 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z02 = star (c x0) * d y0 + -star (c x1) * d y1 + star (c x2) * d y2 + -star (c x3) * d y3 + star (c x4) * d y4 + -star (c x5) * d y5 + -star (c x6) * d y6 + star (c x7) * d y7 + -star (c x8) * d y8 + star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z02 y0 = false from by decide,
    show SS.bdot z02 y1 = true from by decide,
    show SS.bdot z02 y2 = false from by decide,
    show SS.bdot z02 y3 = true from by decide,
    show SS.bdot z02 y4 = false from by decide,
    show SS.bdot z02 y5 = true from by decide,
    show SS.bdot z02 y6 = true from by decide,
    show SS.bdot z02 y7 = false from by decide,
    show SS.bdot z02 y8 = true from by decide,
    show SS.bdot z02 y9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off8_16 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z16 =
      star (c x0) * d y0 + -star (c x1) * d y1 +
      star (c x2) * d y2 + -star (c x3) * d y3 +
      -star (c x4) * d y4 + star (c x5) * d y5 +
      -star (c x6) * d y6 + star (c x7) * d y7 +
      star (c x8) * d y8 + -star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z16 y0 = false from by decide,
    show SS.bdot z16 y1 = true from by decide,
    show SS.bdot z16 y2 = false from by decide,
    show SS.bdot z16 y3 = true from by decide,
    show SS.bdot z16 y4 = true from by decide,
    show SS.bdot z16 y5 = false from by decide,
    show SS.bdot z16 y6 = true from by decide,
    show SS.bdot z16 y7 = false from by decide,
    show SS.bdot z16 y8 = false from by decide,
    show SS.bdot z16 y9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off8_24 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z24 = -star (c x0) * d y0 + star (c x1) * d y1 + -star (c x2) * d y2 + star (c x3) * d y3 + star (c x4) * d y4 + -star (c x5) * d y5 + -star (c x6) * d y6 + star (c x7) * d y7 + star (c x8) * d y8 + -star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z24 y0 = true from by decide,
    show SS.bdot z24 y1 = false from by decide,
    show SS.bdot z24 y2 = true from by decide,
    show SS.bdot z24 y3 = false from by decide,
    show SS.bdot z24 y4 = false from by decide,
    show SS.bdot z24 y5 = true from by decide,
    show SS.bdot z24 y6 = true from by decide,
    show SS.bdot z24 y7 = false from by decide,
    show SS.bdot z24 y8 = false from by decide,
    show SS.bdot z24 y9 = true from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

theorem off5_00 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip5 z00 = star (c x7) * d y0 + star (c x6) * d y1 + star (c x1) * d y6 + star (c x0) * d y7 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip5 ∈ S0) =
      ({y0,y1,y6,y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip5 = x7 from by decide,
    show SS.bxor y1 flip5 = x6 from by decide,
    show SS.bxor y6 flip5 = x1 from by decide,
    show SS.bxor y7 flip5 = x0 from by decide]
  simp only [show SS.bdot z00 y0 = false from by decide,
    show SS.bdot z00 y1 = false from by decide,
    show SS.bdot z00 y6 = false from by decide,
    show SS.bdot z00 y7 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem off5_01 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip5 z01 = star (c x7) * d y0 + -star (c x6) * d y1 + star (c x1) * d y6 + -star (c x0) * d y7 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip5 ∈ S0) =
      ({y0,y1,y6,y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip5 = x7 from by decide,
    show SS.bxor y1 flip5 = x6 from by decide,
    show SS.bxor y6 flip5 = x1 from by decide,
    show SS.bxor y7 flip5 = x0 from by decide]
  simp only [show SS.bdot z01 y0 = false from by decide,
    show SS.bdot z01 y1 = true from by decide,
    show SS.bdot z01 y6 = false from by decide,
    show SS.bdot z01 y7 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off6_00 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip6 z00 = star (c x8) * d y0 + star (c x9) * d y1 + star (c x0) * d y8 + star (c x1) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip6 ∈ S0) =
      ({y0,y1,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip6 = x8 from by decide,
    show SS.bxor y1 flip6 = x9 from by decide,
    show SS.bxor y8 flip6 = x0 from by decide,
    show SS.bxor y9 flip6 = x1 from by decide]
  simp only [show SS.bdot z00 y0 = false from by decide,
    show SS.bdot z00 y1 = false from by decide,
    show SS.bdot z00 y8 = false from by decide,
    show SS.bdot z00 y9 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem off6_02 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip6 z02 = star (c x8) * d y0 + -star (c x9) * d y1 + -star (c x0) * d y8 + star (c x1) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip6 ∈ S0) =
      ({y0,y1,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y0 flip6 = x8 from by decide,
    show SS.bxor y1 flip6 = x9 from by decide,
    show SS.bxor y8 flip6 = x0 from by decide,
    show SS.bxor y9 flip6 = x1 from by decide]
  simp only [show SS.bdot z02 y0 = false from by decide,
    show SS.bdot z02 y1 = true from by decide,
    show SS.bdot z02 y8 = true from by decide,
    show SS.bdot z02 y9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off17_00 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip17 z00 = star (c x7) * d y4 + star (c x6) * d y5 + star (c x5) * d y6 + star (c x4) * d y7 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip17 ∈ S0) =
      ({y4,y5,y6,y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y4 flip17 = x7 from by decide,
    show SS.bxor y5 flip17 = x6 from by decide,
    show SS.bxor y6 flip17 = x5 from by decide,
    show SS.bxor y7 flip17 = x4 from by decide]
  simp only [show SS.bdot z00 y4 = false from by decide,
    show SS.bdot z00 y5 = false from by decide,
    show SS.bdot z00 y6 = false from by decide,
    show SS.bdot z00 y7 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem off17_01 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip17 z01 = star (c x7) * d y4 + -star (c x6) * d y5 + star (c x5) * d y6 + -star (c x4) * d y7 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip17 ∈ S0) =
      ({y4,y5,y6,y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y4 flip17 = x7 from by decide,
    show SS.bxor y5 flip17 = x6 from by decide,
    show SS.bxor y6 flip17 = x5 from by decide,
    show SS.bxor y7 flip17 = x4 from by decide]
  simp only [show SS.bdot z01 y4 = false from by decide,
    show SS.bdot z01 y5 = true from by decide,
    show SS.bdot z01 y6 = false from by decide,
    show SS.bdot z01 y7 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off18_00 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip18 z00 = star (c x8) * d y4 + star (c x9) * d y5 + star (c x4) * d y8 + star (c x5) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip18 ∈ S0) =
      ({y4,y5,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y4 flip18 = x8 from by decide,
    show SS.bxor y5 flip18 = x9 from by decide,
    show SS.bxor y8 flip18 = x4 from by decide,
    show SS.bxor y9 flip18 = x5 from by decide]
  simp only [show SS.bdot z00 y4 = false from by decide,
    show SS.bdot z00 y5 = false from by decide,
    show SS.bdot z00 y8 = false from by decide,
    show SS.bdot z00 y9 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem off18_02 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip18 z02 = star (c x8) * d y4 + -star (c x9) * d y5 + -star (c x4) * d y8 + star (c x5) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip18 ∈ S0) =
      ({y4,y5,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y4 flip18 = x8 from by decide,
    show SS.bxor y5 flip18 = x9 from by decide,
    show SS.bxor y8 flip18 = x4 from by decide,
    show SS.bxor y9 flip18 = x5 from by decide]
  simp only [show SS.bdot z02 y4 = false from by decide,
    show SS.bdot z02 y5 = true from by decide,
    show SS.bdot z02 y8 = true from by decide,
    show SS.bdot z02 y9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off33_00 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip33 z00 = star (c x7) * d y2 + star (c x6) * d y3 + star (c x3) * d y6 + star (c x2) * d y7 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip33 ∈ S0) =
      ({y2,y3,y6,y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y2 flip33 = x7 from by decide,
    show SS.bxor y3 flip33 = x6 from by decide,
    show SS.bxor y6 flip33 = x3 from by decide,
    show SS.bxor y7 flip33 = x2 from by decide]
  simp only [show SS.bdot z00 y2 = false from by decide,
    show SS.bdot z00 y3 = false from by decide,
    show SS.bdot z00 y6 = false from by decide,
    show SS.bdot z00 y7 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem off33_01 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip33 z01 = star (c x7) * d y2 + -star (c x6) * d y3 + star (c x3) * d y6 + -star (c x2) * d y7 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip33 ∈ S0) =
      ({y2,y3,y6,y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y2 flip33 = x7 from by decide,
    show SS.bxor y3 flip33 = x6 from by decide,
    show SS.bxor y6 flip33 = x3 from by decide,
    show SS.bxor y7 flip33 = x2 from by decide]
  simp only [show SS.bdot z01 y2 = false from by decide,
    show SS.bdot z01 y3 = true from by decide,
    show SS.bdot z01 y6 = false from by decide,
    show SS.bdot z01 y7 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

theorem off34_00 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip34 z00 = star (c x8) * d y2 + star (c x9) * d y3 + star (c x2) * d y8 + star (c x3) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip34 ∈ S0) =
      ({y2,y3,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y2 flip34 = x8 from by decide,
    show SS.bxor y3 flip34 = x9 from by decide,
    show SS.bxor y8 flip34 = x2 from by decide,
    show SS.bxor y9 flip34 = x3 from by decide]
  simp only [show SS.bdot z00 y2 = false from by decide,
    show SS.bdot z00 y3 = false from by decide,
    show SS.bdot z00 y8 = false from by decide,
    show SS.bdot z00 y9 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem off34_02 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip34 z02 = star (c x8) * d y2 + -star (c x9) * d y3 + -star (c x2) * d y8 + star (c x3) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip34 ∈ S0) =
      ({y2,y3,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton,
    show SS.bxor y2 flip34 = x8 from by decide,
    show SS.bxor y3 flip34 = x9 from by decide,
    show SS.bxor y8 flip34 = x2 from by decide,
    show SS.bxor y9 flip34 = x3 from by decide]
  simp only [show SS.bdot z02 y2 = false from by decide,
    show SS.bdot z02 y3 = true from by decide,
    show SS.bdot z02 y8 = true from by decide,
    show SS.bdot z02 y9 = false from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true]
  ring

structure PhaseRelations (c d : SS.BitString 6 → ℂ) : Prop where
  triangle : star (c x0) * d y0 + star (c x2) * d y2 + star (c x4) * d y4 = 0
  fixed : star (c x7) * d y7 + star (c x8) * d y8 = 0
  block1 : star (c x0) * d y0 = star (c x1) * d y1
  block2 : star (c x3) * d y3 = star (c x2) * d y2
  block3 : star (c x4) * d y4 = star (c x5) * d y5
  block4 : star (c x7) * d y7 = star (c x6) * d y6
  block5 : star (c x8) * d y8 = star (c x9) * d y9
  e41 : star (c x7) * d y0 + star (c x1) * d y6 = 0
  e42 : star (c x7) * d y2 + star (c x3) * d y6 = 0
  e43 : star (c x7) * d y4 + star (c x5) * d y6 = 0
  e51 : star (c x8) * d y0 + star (c x1) * d y9 = 0
  e52 : star (c x8) * d y2 + star (c x3) * d y9 = 0
  e53 : star (c x8) * d y4 + star (c x5) * d y9 = 0

/-- All phase relations are exact rational combinations of genuine KL rows. -/
theorem phase_relations (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3) : PhaseRelations c d := by
  have row (e z : SS.BitString 6) (hw : (⟨e,z⟩ : SS.PauliString 6).wt ≤ 2) :
      SixQubit.offSumOn S0 S1 c d e z = 0 :=
    SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist e z hw
  have h801 := row flip8 z01 (by decide)
  have h802 := row flip8 z02 (by decide)
  have h804 := row flip8 z04 (by decide)
  have h812 := row flip8 z12 (by decide)
  have h816 := row flip8 z16 (by decide)
  have h824 := row flip8 z24 (by decide)
  have h840 := row flip8 z40 (by decide)
  rw [off8_01] at h801
  rw [off8_02] at h802
  rw [off8_04] at h804
  rw [off8_12] at h812
  rw [off8_16] at h816
  rw [off8_24] at h824
  rw [off8_40] at h840
  have hb1 : star (c x0) * d y0 = star (c x1) * d y1 := by
    linear_combination (1/2) * h816 - (1/2) * h840
  have hb2 : star (c x3) * d y3 = star (c x2) * d y2 := by
    linear_combination (1/2) * h804 + (1/2) * h824
  have hb3 : star (c x4) * d y4 = star (c x5) * d y5 := by
    linear_combination (-1/2) * h804 - (1/2) * h840
  have hb4 : star (c x7) * d y7 = star (c x6) * d y6 := by
    linear_combination (-1/4) * h801 + (1/4) * h802 -
      (1/4) * h804 - (1/4) * h812
  have hb5 : star (c x8) * d y8 = star (c x9) * d y9 := by
    linear_combination (1/4) * h801 - (1/4) * h802 -
      (1/4) * h804 - (1/4) * h812
  have h500 := row flip5 z00 (by decide)
  have h501 := row flip5 z01 (by decide)
  have h600 := row flip6 z00 (by decide)
  have h602 := row flip6 z02 (by decide)
  have h1700 := row flip17 z00 (by decide)
  have h1701 := row flip17 z01 (by decide)
  have h1800 := row flip18 z00 (by decide)
  have h1802 := row flip18 z02 (by decide)
  have h3300 := row flip33 z00 (by decide)
  have h3301 := row flip33 z01 (by decide)
  have h3400 := row flip34 z00 (by decide)
  have h3402 := row flip34 z02 (by decide)
  rw [off5_00] at h500
  rw [off5_01] at h501
  rw [off6_00] at h600
  rw [off6_02] at h602
  rw [off17_00] at h1700
  rw [off17_01] at h1701
  rw [off18_00] at h1800
  rw [off18_02] at h1802
  rw [off33_00] at h3300
  rw [off33_01] at h3301
  rw [off34_00] at h3400
  rw [off34_02] at h3402
  have he41 : star (c x7) * d y0 + star (c x1) * d y6 = 0 := by
    linear_combination (1/2) * h500 + (1/2) * h501
  have he51 : star (c x8) * d y0 + star (c x1) * d y9 = 0 := by
    linear_combination (1/2) * h600 + (1/2) * h602
  have he43 : star (c x7) * d y4 + star (c x5) * d y6 = 0 := by
    linear_combination (1/2) * h1700 + (1/2) * h1701
  have he53 : star (c x8) * d y4 + star (c x5) * d y9 = 0 := by
    linear_combination (1/2) * h1800 + (1/2) * h1802
  have he42 : star (c x7) * d y2 + star (c x3) * d y6 = 0 := by
    linear_combination (1/2) * h3300 + (1/2) * h3301
  have he52 : star (c x8) * d y2 + star (c x3) * d y9 = 0 := by
    linear_combination (1/2) * h3400 + (1/2) * h3402
  have htri := cross_triangle c d hc hd hdist
  have hfix := cross_fixed c d hc hd hdist
  refine ⟨?_,hfix,hb1,hb2,hb3,hb4,hb5,he41,he42,he43,he51,he52,he53⟩
  rw [← hb2]
  exact htri

end

end SixQubit.Orbit45Phase
