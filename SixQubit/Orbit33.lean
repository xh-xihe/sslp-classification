import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Block33

/-!
# Six-qubit no-go for moment orbit 33: a block reflection

Orbit 33 of `six_qubit_sslp_v7.tex`: q = 5, angle vector a = (0, 1, 1, 3, 3, 3),
residues 0 and 1, fibers of size twelve each.

The first qubit carries angle zero, so both fibers are closed under flipping it
and split into six blocks of two.  Writing `c_i` and `d_i` for the resulting
two-component vectors, the moment system pins every block norm to
`R = (3, 2, 2, 1, 1, 1)/10`, and the diagonal Knill-Laflamme conditions for
`F` on the first qubit together with `F Z_j` on a second give the reflection
identities `c_i c_i^dagger + d_i d_i^dagger = 2 R_i rho`.  The cross conditions
force blocks 1 and 2 to be collinear with block 0 on both fibers, and then force
blocks 3, 4, 5 to be orthogonal to block 0 on the opposite fiber.  Those two
facts push `rho` to `I/2` and simultaneously to a rank-one multiple of it, which
is impossible.  `SixQubit.Block33.block_contradiction` carries that argument;
this module supplies its hypotheses from the Knill-Laflamme conditions.

Everything computational is decided by the Lean kernel; `native_decide` is
not used.
-/

namespace SixQubit.Orbit33

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]

def y0 : SS.BitString 6 := bs false false false false false false  -- 000000
def y1 : SS.BitString 6 := bs false false true  true  true  true   -- 001111
def y2 : SS.BitString 6 := bs false true  false true  true  true   -- 010111
def y3 : SS.BitString 6 := bs false true  true  false false true   -- 011001
def y4 : SS.BitString 6 := bs false true  true  false true  false  -- 011010
def y5 : SS.BitString 6 := bs false true  true  true  false false  -- 011100
def y6 : SS.BitString 6 := bs true  false false false false false  -- 100000
def y7 : SS.BitString 6 := bs true  false true  true  true  true   -- 101111
def y8 : SS.BitString 6 := bs true  true  false true  true  true   -- 110111
def y9 : SS.BitString 6 := bs true  true  true  false false true   -- 111001
def y10 : SS.BitString 6 := bs true  true  true  false true  false  -- 111010
def y11 : SS.BitString 6 := bs true  true  true  true  false false  -- 111100

def z0 : SS.BitString 6 := bs false false false false true  true   -- 000011
def z1 : SS.BitString 6 := bs false false false true  false true   -- 000101
def z2 : SS.BitString 6 := bs false false false true  true  false  -- 000110
def z3 : SS.BitString 6 := bs false false true  false false false  -- 001000
def z4 : SS.BitString 6 := bs false true  false false false false  -- 010000
def z5 : SS.BitString 6 := bs false true  true  true  true  true   -- 011111
def z6 : SS.BitString 6 := bs true  false false false true  true   -- 100011
def z7 : SS.BitString 6 := bs true  false false true  false true   -- 100101
def z8 : SS.BitString 6 := bs true  false false true  true  false  -- 100110
def z9 : SS.BitString 6 := bs true  false true  false false false  -- 101000
def z10 : SS.BitString 6 := bs true  true  false false false false  -- 110000
def z11 : SS.BitString 6 := bs true  true  true  true  true  true   -- 111111

def S0 : Finset (SS.BitString 6) := {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11}
def S1 : Finset (SS.BitString 6) := {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11}

def av : Fin 6 -> ZMod 5 := ![0, 1, 1, 3, 3, 3]

/-- Each support is exactly its residue fiber, decided over all 64 strings. -/
theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by
  decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 1) = S1 := by
  decide

def ef0 : SS.BitString 6 := bs true  false false false false false  -- mask 100000
def ef1 : SS.BitString 6 := bs false true  false false false false  -- mask 010000
def ef2 : SS.BitString 6 := bs true  true  false false false false  -- mask 110000
def ef3 : SS.BitString 6 := bs false false true  false false false  -- mask 001000
def ef4 : SS.BitString 6 := bs true  false true  false false false  -- mask 101000
def ef5 : SS.BitString 6 := bs false false false true  true  false  -- mask 000110
def ef6 : SS.BitString 6 := bs false false false true  false true   -- mask 000101
def ef7 : SS.BitString 6 := bs false false false false true  true   -- mask 000011
def ef8 : SS.BitString 6 := bs false false true  false false true   -- mask 001001
def ef9 : SS.BitString 6 := bs false false true  false true  false  -- mask 001010
def ef10 : SS.BitString 6 := bs false false true  true  false false  -- mask 001100
def w0 : SS.BitString 6 := bs false false false false false false  -- dressing 000000
def w1 : SS.BitString 6 := bs false false false false false true   -- dressing 000001
def w2 : SS.BitString 6 := bs false false false false true  false  -- dressing 000010
def w3 : SS.BitString 6 := bs false false false true  false false  -- dressing 000100
def w4 : SS.BitString 6 := bs false false true  false false false  -- dressing 001000
def w5 : SS.BitString 6 := bs false true  false false false false  -- dressing 010000
def w6 : SS.BitString 6 := bs true  false false false false false  -- dressing 100000
def w7 : SS.BitString 6 := bs true  false false false false true   -- dressing 100001
def w8 : SS.BitString 6 := bs true  false false false true  false  -- dressing 100010
def w9 : SS.BitString 6 := bs true  false false true  false false  -- dressing 100100
def w10 : SS.BitString 6 := bs true  false true  false false false  -- dressing 101000
def w11 : SS.BitString 6 := bs true  true  false false false false  -- dressing 110000


/-! ## The Knill-Laflamme sums -/

def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

/-- `<0_L| X^e Z^z |0_L>` with the global prefactor omitted. -/
def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

/-- `<1_L| X^e Z^z |1_L>`. -/
def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=
  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),
      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)

/-- `star z * z` is the squared modulus. -/
theorem sq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, Complex.normSq_eq_conj_mul_self]; rfl

/-! ## Incidences, all decided -/

theorem diagB_inc :
    S0.filter (fun x => SS.bxor x ef0 ∈ S0) = {y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11} := by decide
theorem diagT_inc :
    S1.filter (fun y => SS.bxor y ef0 ∈ S1) = {z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11} := by decide
theorem dfb0 : SS.bxor y0 ef0 = y6 := by decide
theorem dfb1 : SS.bxor y1 ef0 = y7 := by decide
theorem dfb2 : SS.bxor y2 ef0 = y8 := by decide
theorem dfb3 : SS.bxor y3 ef0 = y9 := by decide
theorem dfb4 : SS.bxor y4 ef0 = y10 := by decide
theorem dfb5 : SS.bxor y5 ef0 = y11 := by decide
theorem dfb6 : SS.bxor y6 ef0 = y0 := by decide
theorem dfb7 : SS.bxor y7 ef0 = y1 := by decide
theorem dfb8 : SS.bxor y8 ef0 = y2 := by decide
theorem dfb9 : SS.bxor y9 ef0 = y3 := by decide
theorem dfb10 : SS.bxor y10 ef0 = y4 := by decide
theorem dfb11 : SS.bxor y11 ef0 = y5 := by decide
theorem dft0 : SS.bxor z0 ef0 = z6 := by decide
theorem dft1 : SS.bxor z1 ef0 = z7 := by decide
theorem dft2 : SS.bxor z2 ef0 = z8 := by decide
theorem dft3 : SS.bxor z3 ef0 = z9 := by decide
theorem dft4 : SS.bxor z4 ef0 = z10 := by decide
theorem dft5 : SS.bxor z5 ef0 = z11 := by decide
theorem dft6 : SS.bxor z6 ef0 = z0 := by decide
theorem dft7 : SS.bxor z7 ef0 = z1 := by decide
theorem dft8 : SS.bxor z8 ef0 = z2 := by decide
theorem dft9 : SS.bxor z9 ef0 = z3 := by decide
theorem dft10 : SS.bxor z10 ef0 = z4 := by decide
theorem dft11 : SS.bxor z11 ef0 = z5 := by decide
theorem dsbw0_0 : SS.bdot w0 y0 = false := by decide
theorem dsbw0_1 : SS.bdot w0 y1 = false := by decide
theorem dsbw0_2 : SS.bdot w0 y2 = false := by decide
theorem dsbw0_3 : SS.bdot w0 y3 = false := by decide
theorem dsbw0_4 : SS.bdot w0 y4 = false := by decide
theorem dsbw0_5 : SS.bdot w0 y5 = false := by decide
theorem dsbw0_6 : SS.bdot w0 y6 = false := by decide
theorem dsbw0_7 : SS.bdot w0 y7 = false := by decide
theorem dsbw0_8 : SS.bdot w0 y8 = false := by decide
theorem dsbw0_9 : SS.bdot w0 y9 = false := by decide
theorem dsbw0_10 : SS.bdot w0 y10 = false := by decide
theorem dsbw0_11 : SS.bdot w0 y11 = false := by decide
theorem dstw0_0 : SS.bdot w0 z0 = false := by decide
theorem dstw0_1 : SS.bdot w0 z1 = false := by decide
theorem dstw0_2 : SS.bdot w0 z2 = false := by decide
theorem dstw0_3 : SS.bdot w0 z3 = false := by decide
theorem dstw0_4 : SS.bdot w0 z4 = false := by decide
theorem dstw0_5 : SS.bdot w0 z5 = false := by decide
theorem dstw0_6 : SS.bdot w0 z6 = false := by decide
theorem dstw0_7 : SS.bdot w0 z7 = false := by decide
theorem dstw0_8 : SS.bdot w0 z8 = false := by decide
theorem dstw0_9 : SS.bdot w0 z9 = false := by decide
theorem dstw0_10 : SS.bdot w0 z10 = false := by decide
theorem dstw0_11 : SS.bdot w0 z11 = false := by decide
theorem dsbw6_0 : SS.bdot w6 y0 = false := by decide
theorem dsbw6_1 : SS.bdot w6 y1 = false := by decide
theorem dsbw6_2 : SS.bdot w6 y2 = false := by decide
theorem dsbw6_3 : SS.bdot w6 y3 = false := by decide
theorem dsbw6_4 : SS.bdot w6 y4 = false := by decide
theorem dsbw6_5 : SS.bdot w6 y5 = false := by decide
theorem dsbw6_6 : SS.bdot w6 y6 = true := by decide
theorem dsbw6_7 : SS.bdot w6 y7 = true := by decide
theorem dsbw6_8 : SS.bdot w6 y8 = true := by decide
theorem dsbw6_9 : SS.bdot w6 y9 = true := by decide
theorem dsbw6_10 : SS.bdot w6 y10 = true := by decide
theorem dsbw6_11 : SS.bdot w6 y11 = true := by decide
theorem dstw6_0 : SS.bdot w6 z0 = false := by decide
theorem dstw6_1 : SS.bdot w6 z1 = false := by decide
theorem dstw6_2 : SS.bdot w6 z2 = false := by decide
theorem dstw6_3 : SS.bdot w6 z3 = false := by decide
theorem dstw6_4 : SS.bdot w6 z4 = false := by decide
theorem dstw6_5 : SS.bdot w6 z5 = false := by decide
theorem dstw6_6 : SS.bdot w6 z6 = true := by decide
theorem dstw6_7 : SS.bdot w6 z7 = true := by decide
theorem dstw6_8 : SS.bdot w6 z8 = true := by decide
theorem dstw6_9 : SS.bdot w6 z9 = true := by decide
theorem dstw6_10 : SS.bdot w6 z10 = true := by decide
theorem dstw6_11 : SS.bdot w6 z11 = true := by decide
theorem dsbw5_0 : SS.bdot w5 y0 = false := by decide
theorem dsbw5_1 : SS.bdot w5 y1 = false := by decide
theorem dsbw5_2 : SS.bdot w5 y2 = true := by decide
theorem dsbw5_3 : SS.bdot w5 y3 = true := by decide
theorem dsbw5_4 : SS.bdot w5 y4 = true := by decide
theorem dsbw5_5 : SS.bdot w5 y5 = true := by decide
theorem dsbw5_6 : SS.bdot w5 y6 = false := by decide
theorem dsbw5_7 : SS.bdot w5 y7 = false := by decide
theorem dsbw5_8 : SS.bdot w5 y8 = true := by decide
theorem dsbw5_9 : SS.bdot w5 y9 = true := by decide
theorem dsbw5_10 : SS.bdot w5 y10 = true := by decide
theorem dsbw5_11 : SS.bdot w5 y11 = true := by decide
theorem dstw5_0 : SS.bdot w5 z0 = false := by decide
theorem dstw5_1 : SS.bdot w5 z1 = false := by decide
theorem dstw5_2 : SS.bdot w5 z2 = false := by decide
theorem dstw5_3 : SS.bdot w5 z3 = false := by decide
theorem dstw5_4 : SS.bdot w5 z4 = true := by decide
theorem dstw5_5 : SS.bdot w5 z5 = true := by decide
theorem dstw5_6 : SS.bdot w5 z6 = false := by decide
theorem dstw5_7 : SS.bdot w5 z7 = false := by decide
theorem dstw5_8 : SS.bdot w5 z8 = false := by decide
theorem dstw5_9 : SS.bdot w5 z9 = false := by decide
theorem dstw5_10 : SS.bdot w5 z10 = true := by decide
theorem dstw5_11 : SS.bdot w5 z11 = true := by decide
theorem dsbw11_0 : SS.bdot w11 y0 = false := by decide
theorem dsbw11_1 : SS.bdot w11 y1 = false := by decide
theorem dsbw11_2 : SS.bdot w11 y2 = true := by decide
theorem dsbw11_3 : SS.bdot w11 y3 = true := by decide
theorem dsbw11_4 : SS.bdot w11 y4 = true := by decide
theorem dsbw11_5 : SS.bdot w11 y5 = true := by decide
theorem dsbw11_6 : SS.bdot w11 y6 = true := by decide
theorem dsbw11_7 : SS.bdot w11 y7 = true := by decide
theorem dsbw11_8 : SS.bdot w11 y8 = false := by decide
theorem dsbw11_9 : SS.bdot w11 y9 = false := by decide
theorem dsbw11_10 : SS.bdot w11 y10 = false := by decide
theorem dsbw11_11 : SS.bdot w11 y11 = false := by decide
theorem dstw11_0 : SS.bdot w11 z0 = false := by decide
theorem dstw11_1 : SS.bdot w11 z1 = false := by decide
theorem dstw11_2 : SS.bdot w11 z2 = false := by decide
theorem dstw11_3 : SS.bdot w11 z3 = false := by decide
theorem dstw11_4 : SS.bdot w11 z4 = true := by decide
theorem dstw11_5 : SS.bdot w11 z5 = true := by decide
theorem dstw11_6 : SS.bdot w11 z6 = true := by decide
theorem dstw11_7 : SS.bdot w11 z7 = true := by decide
theorem dstw11_8 : SS.bdot w11 z8 = true := by decide
theorem dstw11_9 : SS.bdot w11 z9 = true := by decide
theorem dstw11_10 : SS.bdot w11 z10 = false := by decide
theorem dstw11_11 : SS.bdot w11 z11 = false := by decide
theorem dsbw4_0 : SS.bdot w4 y0 = false := by decide
theorem dsbw4_1 : SS.bdot w4 y1 = true := by decide
theorem dsbw4_2 : SS.bdot w4 y2 = false := by decide
theorem dsbw4_3 : SS.bdot w4 y3 = true := by decide
theorem dsbw4_4 : SS.bdot w4 y4 = true := by decide
theorem dsbw4_5 : SS.bdot w4 y5 = true := by decide
theorem dsbw4_6 : SS.bdot w4 y6 = false := by decide
theorem dsbw4_7 : SS.bdot w4 y7 = true := by decide
theorem dsbw4_8 : SS.bdot w4 y8 = false := by decide
theorem dsbw4_9 : SS.bdot w4 y9 = true := by decide
theorem dsbw4_10 : SS.bdot w4 y10 = true := by decide
theorem dsbw4_11 : SS.bdot w4 y11 = true := by decide
theorem dstw4_0 : SS.bdot w4 z0 = false := by decide
theorem dstw4_1 : SS.bdot w4 z1 = false := by decide
theorem dstw4_2 : SS.bdot w4 z2 = false := by decide
theorem dstw4_3 : SS.bdot w4 z3 = true := by decide
theorem dstw4_4 : SS.bdot w4 z4 = false := by decide
theorem dstw4_5 : SS.bdot w4 z5 = true := by decide
theorem dstw4_6 : SS.bdot w4 z6 = false := by decide
theorem dstw4_7 : SS.bdot w4 z7 = false := by decide
theorem dstw4_8 : SS.bdot w4 z8 = false := by decide
theorem dstw4_9 : SS.bdot w4 z9 = true := by decide
theorem dstw4_10 : SS.bdot w4 z10 = false := by decide
theorem dstw4_11 : SS.bdot w4 z11 = true := by decide
theorem dsbw10_0 : SS.bdot w10 y0 = false := by decide
theorem dsbw10_1 : SS.bdot w10 y1 = true := by decide
theorem dsbw10_2 : SS.bdot w10 y2 = false := by decide
theorem dsbw10_3 : SS.bdot w10 y3 = true := by decide
theorem dsbw10_4 : SS.bdot w10 y4 = true := by decide
theorem dsbw10_5 : SS.bdot w10 y5 = true := by decide
theorem dsbw10_6 : SS.bdot w10 y6 = true := by decide
theorem dsbw10_7 : SS.bdot w10 y7 = false := by decide
theorem dsbw10_8 : SS.bdot w10 y8 = true := by decide
theorem dsbw10_9 : SS.bdot w10 y9 = false := by decide
theorem dsbw10_10 : SS.bdot w10 y10 = false := by decide
theorem dsbw10_11 : SS.bdot w10 y11 = false := by decide
theorem dstw10_0 : SS.bdot w10 z0 = false := by decide
theorem dstw10_1 : SS.bdot w10 z1 = false := by decide
theorem dstw10_2 : SS.bdot w10 z2 = false := by decide
theorem dstw10_3 : SS.bdot w10 z3 = true := by decide
theorem dstw10_4 : SS.bdot w10 z4 = false := by decide
theorem dstw10_5 : SS.bdot w10 z5 = true := by decide
theorem dstw10_6 : SS.bdot w10 z6 = true := by decide
theorem dstw10_7 : SS.bdot w10 z7 = true := by decide
theorem dstw10_8 : SS.bdot w10 z8 = true := by decide
theorem dstw10_9 : SS.bdot w10 z9 = false := by decide
theorem dstw10_10 : SS.bdot w10 z10 = true := by decide
theorem dstw10_11 : SS.bdot w10 z11 = false := by decide
theorem dsbw3_0 : SS.bdot w3 y0 = false := by decide
theorem dsbw3_1 : SS.bdot w3 y1 = true := by decide
theorem dsbw3_2 : SS.bdot w3 y2 = true := by decide
theorem dsbw3_3 : SS.bdot w3 y3 = false := by decide
theorem dsbw3_4 : SS.bdot w3 y4 = false := by decide
theorem dsbw3_5 : SS.bdot w3 y5 = true := by decide
theorem dsbw3_6 : SS.bdot w3 y6 = false := by decide
theorem dsbw3_7 : SS.bdot w3 y7 = true := by decide
theorem dsbw3_8 : SS.bdot w3 y8 = true := by decide
theorem dsbw3_9 : SS.bdot w3 y9 = false := by decide
theorem dsbw3_10 : SS.bdot w3 y10 = false := by decide
theorem dsbw3_11 : SS.bdot w3 y11 = true := by decide
theorem dstw3_0 : SS.bdot w3 z0 = false := by decide
theorem dstw3_1 : SS.bdot w3 z1 = true := by decide
theorem dstw3_2 : SS.bdot w3 z2 = true := by decide
theorem dstw3_3 : SS.bdot w3 z3 = false := by decide
theorem dstw3_4 : SS.bdot w3 z4 = false := by decide
theorem dstw3_5 : SS.bdot w3 z5 = true := by decide
theorem dstw3_6 : SS.bdot w3 z6 = false := by decide
theorem dstw3_7 : SS.bdot w3 z7 = true := by decide
theorem dstw3_8 : SS.bdot w3 z8 = true := by decide
theorem dstw3_9 : SS.bdot w3 z9 = false := by decide
theorem dstw3_10 : SS.bdot w3 z10 = false := by decide
theorem dstw3_11 : SS.bdot w3 z11 = true := by decide
theorem dsbw9_0 : SS.bdot w9 y0 = false := by decide
theorem dsbw9_1 : SS.bdot w9 y1 = true := by decide
theorem dsbw9_2 : SS.bdot w9 y2 = true := by decide
theorem dsbw9_3 : SS.bdot w9 y3 = false := by decide
theorem dsbw9_4 : SS.bdot w9 y4 = false := by decide
theorem dsbw9_5 : SS.bdot w9 y5 = true := by decide
theorem dsbw9_6 : SS.bdot w9 y6 = true := by decide
theorem dsbw9_7 : SS.bdot w9 y7 = false := by decide
theorem dsbw9_8 : SS.bdot w9 y8 = false := by decide
theorem dsbw9_9 : SS.bdot w9 y9 = true := by decide
theorem dsbw9_10 : SS.bdot w9 y10 = true := by decide
theorem dsbw9_11 : SS.bdot w9 y11 = false := by decide
theorem dstw9_0 : SS.bdot w9 z0 = false := by decide
theorem dstw9_1 : SS.bdot w9 z1 = true := by decide
theorem dstw9_2 : SS.bdot w9 z2 = true := by decide
theorem dstw9_3 : SS.bdot w9 z3 = false := by decide
theorem dstw9_4 : SS.bdot w9 z4 = false := by decide
theorem dstw9_5 : SS.bdot w9 z5 = true := by decide
theorem dstw9_6 : SS.bdot w9 z6 = true := by decide
theorem dstw9_7 : SS.bdot w9 z7 = false := by decide
theorem dstw9_8 : SS.bdot w9 z8 = false := by decide
theorem dstw9_9 : SS.bdot w9 z9 = true := by decide
theorem dstw9_10 : SS.bdot w9 z10 = true := by decide
theorem dstw9_11 : SS.bdot w9 z11 = false := by decide
theorem dsbw2_0 : SS.bdot w2 y0 = false := by decide
theorem dsbw2_1 : SS.bdot w2 y1 = true := by decide
theorem dsbw2_2 : SS.bdot w2 y2 = true := by decide
theorem dsbw2_3 : SS.bdot w2 y3 = false := by decide
theorem dsbw2_4 : SS.bdot w2 y4 = true := by decide
theorem dsbw2_5 : SS.bdot w2 y5 = false := by decide
theorem dsbw2_6 : SS.bdot w2 y6 = false := by decide
theorem dsbw2_7 : SS.bdot w2 y7 = true := by decide
theorem dsbw2_8 : SS.bdot w2 y8 = true := by decide
theorem dsbw2_9 : SS.bdot w2 y9 = false := by decide
theorem dsbw2_10 : SS.bdot w2 y10 = true := by decide
theorem dsbw2_11 : SS.bdot w2 y11 = false := by decide
theorem dstw2_0 : SS.bdot w2 z0 = true := by decide
theorem dstw2_1 : SS.bdot w2 z1 = false := by decide
theorem dstw2_2 : SS.bdot w2 z2 = true := by decide
theorem dstw2_3 : SS.bdot w2 z3 = false := by decide
theorem dstw2_4 : SS.bdot w2 z4 = false := by decide
theorem dstw2_5 : SS.bdot w2 z5 = true := by decide
theorem dstw2_6 : SS.bdot w2 z6 = true := by decide
theorem dstw2_7 : SS.bdot w2 z7 = false := by decide
theorem dstw2_8 : SS.bdot w2 z8 = true := by decide
theorem dstw2_9 : SS.bdot w2 z9 = false := by decide
theorem dstw2_10 : SS.bdot w2 z10 = false := by decide
theorem dstw2_11 : SS.bdot w2 z11 = true := by decide
theorem dsbw8_0 : SS.bdot w8 y0 = false := by decide
theorem dsbw8_1 : SS.bdot w8 y1 = true := by decide
theorem dsbw8_2 : SS.bdot w8 y2 = true := by decide
theorem dsbw8_3 : SS.bdot w8 y3 = false := by decide
theorem dsbw8_4 : SS.bdot w8 y4 = true := by decide
theorem dsbw8_5 : SS.bdot w8 y5 = false := by decide
theorem dsbw8_6 : SS.bdot w8 y6 = true := by decide
theorem dsbw8_7 : SS.bdot w8 y7 = false := by decide
theorem dsbw8_8 : SS.bdot w8 y8 = false := by decide
theorem dsbw8_9 : SS.bdot w8 y9 = true := by decide
theorem dsbw8_10 : SS.bdot w8 y10 = false := by decide
theorem dsbw8_11 : SS.bdot w8 y11 = true := by decide
theorem dstw8_0 : SS.bdot w8 z0 = true := by decide
theorem dstw8_1 : SS.bdot w8 z1 = false := by decide
theorem dstw8_2 : SS.bdot w8 z2 = true := by decide
theorem dstw8_3 : SS.bdot w8 z3 = false := by decide
theorem dstw8_4 : SS.bdot w8 z4 = false := by decide
theorem dstw8_5 : SS.bdot w8 z5 = true := by decide
theorem dstw8_6 : SS.bdot w8 z6 = false := by decide
theorem dstw8_7 : SS.bdot w8 z7 = true := by decide
theorem dstw8_8 : SS.bdot w8 z8 = false := by decide
theorem dstw8_9 : SS.bdot w8 z9 = true := by decide
theorem dstw8_10 : SS.bdot w8 z10 = true := by decide
theorem dstw8_11 : SS.bdot w8 z11 = false := by decide
theorem dsbw1_0 : SS.bdot w1 y0 = false := by decide
theorem dsbw1_1 : SS.bdot w1 y1 = true := by decide
theorem dsbw1_2 : SS.bdot w1 y2 = true := by decide
theorem dsbw1_3 : SS.bdot w1 y3 = true := by decide
theorem dsbw1_4 : SS.bdot w1 y4 = false := by decide
theorem dsbw1_5 : SS.bdot w1 y5 = false := by decide
theorem dsbw1_6 : SS.bdot w1 y6 = false := by decide
theorem dsbw1_7 : SS.bdot w1 y7 = true := by decide
theorem dsbw1_8 : SS.bdot w1 y8 = true := by decide
theorem dsbw1_9 : SS.bdot w1 y9 = true := by decide
theorem dsbw1_10 : SS.bdot w1 y10 = false := by decide
theorem dsbw1_11 : SS.bdot w1 y11 = false := by decide
theorem dstw1_0 : SS.bdot w1 z0 = true := by decide
theorem dstw1_1 : SS.bdot w1 z1 = true := by decide
theorem dstw1_2 : SS.bdot w1 z2 = false := by decide
theorem dstw1_3 : SS.bdot w1 z3 = false := by decide
theorem dstw1_4 : SS.bdot w1 z4 = false := by decide
theorem dstw1_5 : SS.bdot w1 z5 = true := by decide
theorem dstw1_6 : SS.bdot w1 z6 = true := by decide
theorem dstw1_7 : SS.bdot w1 z7 = true := by decide
theorem dstw1_8 : SS.bdot w1 z8 = false := by decide
theorem dstw1_9 : SS.bdot w1 z9 = false := by decide
theorem dstw1_10 : SS.bdot w1 z10 = false := by decide
theorem dstw1_11 : SS.bdot w1 z11 = true := by decide
theorem dsbw7_0 : SS.bdot w7 y0 = false := by decide
theorem dsbw7_1 : SS.bdot w7 y1 = true := by decide
theorem dsbw7_2 : SS.bdot w7 y2 = true := by decide
theorem dsbw7_3 : SS.bdot w7 y3 = true := by decide
theorem dsbw7_4 : SS.bdot w7 y4 = false := by decide
theorem dsbw7_5 : SS.bdot w7 y5 = false := by decide
theorem dsbw7_6 : SS.bdot w7 y6 = true := by decide
theorem dsbw7_7 : SS.bdot w7 y7 = false := by decide
theorem dsbw7_8 : SS.bdot w7 y8 = false := by decide
theorem dsbw7_9 : SS.bdot w7 y9 = false := by decide
theorem dsbw7_10 : SS.bdot w7 y10 = true := by decide
theorem dsbw7_11 : SS.bdot w7 y11 = true := by decide
theorem dstw7_0 : SS.bdot w7 z0 = true := by decide
theorem dstw7_1 : SS.bdot w7 z1 = true := by decide
theorem dstw7_2 : SS.bdot w7 z2 = false := by decide
theorem dstw7_3 : SS.bdot w7 z3 = false := by decide
theorem dstw7_4 : SS.bdot w7 z4 = false := by decide
theorem dstw7_5 : SS.bdot w7 z5 = true := by decide
theorem dstw7_6 : SS.bdot w7 z6 = false := by decide
theorem dstw7_7 : SS.bdot w7 z7 = false := by decide
theorem dstw7_8 : SS.bdot w7 z8 = true := by decide
theorem dstw7_9 : SS.bdot w7 z9 = true := by decide
theorem dstw7_10 : SS.bdot w7 z10 = true := by decide
theorem dstw7_11 : SS.bdot w7 z11 = false := by decide
theorem incidence1 :
    S1.filter (fun y => SS.bxor y ef1 ∈ S0) = {z4, z5, z10, z11} := by decide
theorem fl1_4 : SS.bxor z4 ef1 = y0 := by decide
theorem fl1_5 : SS.bxor z5 ef1 = y1 := by decide
theorem fl1_10 : SS.bxor z10 ef1 = y6 := by decide
theorem fl1_11 : SS.bxor z11 ef1 = y7 := by decide
theorem sg1_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg1_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg1_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg1_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg1_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg1_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg1_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg1_w6_11 : SS.bdot w6 z11 = true := by decide
theorem incidence2 :
    S1.filter (fun y => SS.bxor y ef2 ∈ S0) = {z4, z5, z10, z11} := by decide
theorem fl2_4 : SS.bxor z4 ef2 = y6 := by decide
theorem fl2_5 : SS.bxor z5 ef2 = y7 := by decide
theorem fl2_10 : SS.bxor z10 ef2 = y0 := by decide
theorem fl2_11 : SS.bxor z11 ef2 = y1 := by decide
theorem sg2_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg2_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg2_w0_10 : SS.bdot w0 z10 = false := by decide
theorem sg2_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg2_w6_4 : SS.bdot w6 z4 = false := by decide
theorem sg2_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg2_w6_10 : SS.bdot w6 z10 = true := by decide
theorem sg2_w6_11 : SS.bdot w6 z11 = true := by decide
theorem incidence3 :
    S1.filter (fun y => SS.bxor y ef3 ∈ S0) = {z3, z5, z9, z11} := by decide
theorem fl3_3 : SS.bxor z3 ef3 = y0 := by decide
theorem fl3_5 : SS.bxor z5 ef3 = y2 := by decide
theorem fl3_9 : SS.bxor z9 ef3 = y6 := by decide
theorem fl3_11 : SS.bxor z11 ef3 = y8 := by decide
theorem sg3_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg3_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg3_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg3_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg3_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg3_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg3_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg3_w6_11 : SS.bdot w6 z11 = true := by decide
theorem incidence4 :
    S1.filter (fun y => SS.bxor y ef4 ∈ S0) = {z3, z5, z9, z11} := by decide
theorem fl4_3 : SS.bxor z3 ef4 = y6 := by decide
theorem fl4_5 : SS.bxor z5 ef4 = y8 := by decide
theorem fl4_9 : SS.bxor z9 ef4 = y0 := by decide
theorem fl4_11 : SS.bxor z11 ef4 = y2 := by decide
theorem sg4_w0_3 : SS.bdot w0 z3 = false := by decide
theorem sg4_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg4_w0_9 : SS.bdot w0 z9 = false := by decide
theorem sg4_w0_11 : SS.bdot w0 z11 = false := by decide
theorem sg4_w6_3 : SS.bdot w6 z3 = false := by decide
theorem sg4_w6_5 : SS.bdot w6 z5 = false := by decide
theorem sg4_w6_9 : SS.bdot w6 z9 = true := by decide
theorem sg4_w6_11 : SS.bdot w6 z11 = true := by decide
theorem incidence5 :
    S1.filter (fun y => SS.bxor y ef5 ∈ S0) = {z2, z5, z8, z11} := by decide
theorem fl5_2 : SS.bxor z2 ef5 = y0 := by decide
theorem fl5_5 : SS.bxor z5 ef5 = y3 := by decide
theorem fl5_8 : SS.bxor z8 ef5 = y6 := by decide
theorem fl5_11 : SS.bxor z11 ef5 = y9 := by decide
theorem sg5_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg5_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg5_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg5_w0_11 : SS.bdot w0 z11 = false := by decide
theorem incidence6 :
    S1.filter (fun y => SS.bxor y ef6 ∈ S0) = {z1, z5, z7, z11} := by decide
theorem fl6_1 : SS.bxor z1 ef6 = y0 := by decide
theorem fl6_5 : SS.bxor z5 ef6 = y4 := by decide
theorem fl6_7 : SS.bxor z7 ef6 = y6 := by decide
theorem fl6_11 : SS.bxor z11 ef6 = y10 := by decide
theorem sg6_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg6_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg6_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg6_w0_11 : SS.bdot w0 z11 = false := by decide
theorem incidence7 :
    S1.filter (fun y => SS.bxor y ef7 ∈ S0) = {z0, z5, z6, z11} := by decide
theorem fl7_0 : SS.bxor z0 ef7 = y0 := by decide
theorem fl7_5 : SS.bxor z5 ef7 = y5 := by decide
theorem fl7_6 : SS.bxor z6 ef7 = y6 := by decide
theorem fl7_11 : SS.bxor z11 ef7 = y11 := by decide
theorem sg7_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg7_w0_5 : SS.bdot w0 z5 = false := by decide
theorem sg7_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg7_w0_11 : SS.bdot w0 z11 = false := by decide
theorem incidence8 :
    S1.filter (fun y => SS.bxor y ef8 ∈ S0) = {z2, z4, z8, z10} := by decide
theorem fl8_2 : SS.bxor z2 ef8 = y1 := by decide
theorem fl8_4 : SS.bxor z4 ef8 = y3 := by decide
theorem fl8_8 : SS.bxor z8 ef8 = y7 := by decide
theorem fl8_10 : SS.bxor z10 ef8 = y9 := by decide
theorem sg8_w0_2 : SS.bdot w0 z2 = false := by decide
theorem sg8_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg8_w0_8 : SS.bdot w0 z8 = false := by decide
theorem sg8_w0_10 : SS.bdot w0 z10 = false := by decide
theorem incidence9 :
    S1.filter (fun y => SS.bxor y ef9 ∈ S0) = {z1, z4, z7, z10} := by decide
theorem fl9_1 : SS.bxor z1 ef9 = y1 := by decide
theorem fl9_4 : SS.bxor z4 ef9 = y4 := by decide
theorem fl9_7 : SS.bxor z7 ef9 = y7 := by decide
theorem fl9_10 : SS.bxor z10 ef9 = y10 := by decide
theorem sg9_w0_1 : SS.bdot w0 z1 = false := by decide
theorem sg9_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg9_w0_7 : SS.bdot w0 z7 = false := by decide
theorem sg9_w0_10 : SS.bdot w0 z10 = false := by decide
theorem incidence10 :
    S1.filter (fun y => SS.bxor y ef10 ∈ S0) = {z0, z4, z6, z10} := by decide
theorem fl10_0 : SS.bxor z0 ef10 = y1 := by decide
theorem fl10_4 : SS.bxor z4 ef10 = y5 := by decide
theorem fl10_6 : SS.bxor z6 ef10 = y7 := by decide
theorem fl10_10 : SS.bxor z10 ef10 = y11 := by decide
theorem sg10_w0_0 : SS.bdot w0 z0 = false := by decide
theorem sg10_w0_4 : SS.bdot w0 z4 = false := by decide
theorem sg10_w0_6 : SS.bdot w0 z6 = false := by decide
theorem sg10_w0_10 : SS.bdot w0 z10 = false := by decide

/-! ## Walsh expansions -/

theorem dbot_w0 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w0 = star (c y6) * c y0 + star (c y7) * c y1 + star (c y8) * c y2 + star (c y9) * c y3 + star (c y10) * c y4 + star (c y11) * c y5 + star (c y0) * c y6 + star (c y1) * c y7 + star (c y2) * c y8 + star (c y3) * c y9 + star (c y4) * c y10 + star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw0_0, dsbw0_1, dsbw0_2, dsbw0_3, dsbw0_4, dsbw0_5, dsbw0_6, dsbw0_7, dsbw0_8, dsbw0_9, dsbw0_10, dsbw0_11, SixQubit.signMul_false]
  try ring

theorem dtop_w0 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w0 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 + star (d z11) * d z5 + star (d z0) * d z6 + star (d z1) * d z7 + star (d z2) * d z8 + star (d z3) * d z9 + star (d z4) * d z10 + star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw0_0, dstw0_1, dstw0_2, dstw0_3, dstw0_4, dstw0_5, dstw0_6, dstw0_7, dstw0_8, dstw0_9, dstw0_10, dstw0_11, SixQubit.signMul_false]
  try ring

theorem dbot_w6 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w6 = star (c y6) * c y0 + star (c y7) * c y1 + star (c y8) * c y2 + star (c y9) * c y3 + star (c y10) * c y4 + star (c y11) * c y5 - star (c y0) * c y6 - star (c y1) * c y7 - star (c y2) * c y8 - star (c y3) * c y9 - star (c y4) * c y10 - star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw6_0, dsbw6_1, dsbw6_2, dsbw6_3, dsbw6_4, dsbw6_5, dsbw6_6, dsbw6_7, dsbw6_8, dsbw6_9, dsbw6_10, dsbw6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w6 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w6 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 + star (d z11) * d z5 - star (d z0) * d z6 - star (d z1) * d z7 - star (d z2) * d z8 - star (d z3) * d z9 - star (d z4) * d z10 - star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw6_0, dstw6_1, dstw6_2, dstw6_3, dstw6_4, dstw6_5, dstw6_6, dstw6_7, dstw6_8, dstw6_9, dstw6_10, dstw6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w5 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w5 = star (c y6) * c y0 + star (c y7) * c y1 - star (c y8) * c y2 - star (c y9) * c y3 - star (c y10) * c y4 - star (c y11) * c y5 + star (c y0) * c y6 + star (c y1) * c y7 - star (c y2) * c y8 - star (c y3) * c y9 - star (c y4) * c y10 - star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw5_0, dsbw5_1, dsbw5_2, dsbw5_3, dsbw5_4, dsbw5_5, dsbw5_6, dsbw5_7, dsbw5_8, dsbw5_9, dsbw5_10, dsbw5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w5 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w5 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 - star (d z10) * d z4 - star (d z11) * d z5 + star (d z0) * d z6 + star (d z1) * d z7 + star (d z2) * d z8 + star (d z3) * d z9 - star (d z4) * d z10 - star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw5_0, dstw5_1, dstw5_2, dstw5_3, dstw5_4, dstw5_5, dstw5_6, dstw5_7, dstw5_8, dstw5_9, dstw5_10, dstw5_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w11 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w11 = star (c y6) * c y0 + star (c y7) * c y1 - star (c y8) * c y2 - star (c y9) * c y3 - star (c y10) * c y4 - star (c y11) * c y5 - star (c y0) * c y6 - star (c y1) * c y7 + star (c y2) * c y8 + star (c y3) * c y9 + star (c y4) * c y10 + star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw11_0, dsbw11_1, dsbw11_2, dsbw11_3, dsbw11_4, dsbw11_5, dsbw11_6, dsbw11_7, dsbw11_8, dsbw11_9, dsbw11_10, dsbw11_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w11 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w11 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 - star (d z10) * d z4 - star (d z11) * d z5 - star (d z0) * d z6 - star (d z1) * d z7 - star (d z2) * d z8 - star (d z3) * d z9 + star (d z4) * d z10 + star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw11_0, dstw11_1, dstw11_2, dstw11_3, dstw11_4, dstw11_5, dstw11_6, dstw11_7, dstw11_8, dstw11_9, dstw11_10, dstw11_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w4 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w4 = star (c y6) * c y0 - star (c y7) * c y1 + star (c y8) * c y2 - star (c y9) * c y3 - star (c y10) * c y4 - star (c y11) * c y5 + star (c y0) * c y6 - star (c y1) * c y7 + star (c y2) * c y8 - star (c y3) * c y9 - star (c y4) * c y10 - star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw4_0, dsbw4_1, dsbw4_2, dsbw4_3, dsbw4_4, dsbw4_5, dsbw4_6, dsbw4_7, dsbw4_8, dsbw4_9, dsbw4_10, dsbw4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w4 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w4 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 - star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 + star (d z0) * d z6 + star (d z1) * d z7 + star (d z2) * d z8 - star (d z3) * d z9 + star (d z4) * d z10 - star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw4_0, dstw4_1, dstw4_2, dstw4_3, dstw4_4, dstw4_5, dstw4_6, dstw4_7, dstw4_8, dstw4_9, dstw4_10, dstw4_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w10 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w10 = star (c y6) * c y0 - star (c y7) * c y1 + star (c y8) * c y2 - star (c y9) * c y3 - star (c y10) * c y4 - star (c y11) * c y5 - star (c y0) * c y6 + star (c y1) * c y7 - star (c y2) * c y8 + star (c y3) * c y9 + star (c y4) * c y10 + star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw10_0, dsbw10_1, dsbw10_2, dsbw10_3, dsbw10_4, dsbw10_5, dsbw10_6, dsbw10_7, dsbw10_8, dsbw10_9, dsbw10_10, dsbw10_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w10 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w10 = star (d z6) * d z0 + star (d z7) * d z1 + star (d z8) * d z2 - star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 - star (d z0) * d z6 - star (d z1) * d z7 - star (d z2) * d z8 + star (d z3) * d z9 - star (d z4) * d z10 + star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw10_0, dstw10_1, dstw10_2, dstw10_3, dstw10_4, dstw10_5, dstw10_6, dstw10_7, dstw10_8, dstw10_9, dstw10_10, dstw10_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w3 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w3 = star (c y6) * c y0 - star (c y7) * c y1 - star (c y8) * c y2 + star (c y9) * c y3 + star (c y10) * c y4 - star (c y11) * c y5 + star (c y0) * c y6 - star (c y1) * c y7 - star (c y2) * c y8 + star (c y3) * c y9 + star (c y4) * c y10 - star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw3_0, dsbw3_1, dsbw3_2, dsbw3_3, dsbw3_4, dsbw3_5, dsbw3_6, dsbw3_7, dsbw3_8, dsbw3_9, dsbw3_10, dsbw3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w3 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w3 = star (d z6) * d z0 - star (d z7) * d z1 - star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 + star (d z0) * d z6 - star (d z1) * d z7 - star (d z2) * d z8 + star (d z3) * d z9 + star (d z4) * d z10 - star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw3_0, dstw3_1, dstw3_2, dstw3_3, dstw3_4, dstw3_5, dstw3_6, dstw3_7, dstw3_8, dstw3_9, dstw3_10, dstw3_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w9 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w9 = star (c y6) * c y0 - star (c y7) * c y1 - star (c y8) * c y2 + star (c y9) * c y3 + star (c y10) * c y4 - star (c y11) * c y5 - star (c y0) * c y6 + star (c y1) * c y7 + star (c y2) * c y8 - star (c y3) * c y9 - star (c y4) * c y10 + star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw9_0, dsbw9_1, dsbw9_2, dsbw9_3, dsbw9_4, dsbw9_5, dsbw9_6, dsbw9_7, dsbw9_8, dsbw9_9, dsbw9_10, dsbw9_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w9 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w9 = star (d z6) * d z0 - star (d z7) * d z1 - star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 - star (d z0) * d z6 + star (d z1) * d z7 + star (d z2) * d z8 - star (d z3) * d z9 - star (d z4) * d z10 + star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw9_0, dstw9_1, dstw9_2, dstw9_3, dstw9_4, dstw9_5, dstw9_6, dstw9_7, dstw9_8, dstw9_9, dstw9_10, dstw9_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w2 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w2 = star (c y6) * c y0 - star (c y7) * c y1 - star (c y8) * c y2 + star (c y9) * c y3 - star (c y10) * c y4 + star (c y11) * c y5 + star (c y0) * c y6 - star (c y1) * c y7 - star (c y2) * c y8 + star (c y3) * c y9 - star (c y4) * c y10 + star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw2_0, dsbw2_1, dsbw2_2, dsbw2_3, dsbw2_4, dsbw2_5, dsbw2_6, dsbw2_7, dsbw2_8, dsbw2_9, dsbw2_10, dsbw2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w2 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w2 = - star (d z6) * d z0 + star (d z7) * d z1 - star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 - star (d z0) * d z6 + star (d z1) * d z7 - star (d z2) * d z8 + star (d z3) * d z9 + star (d z4) * d z10 - star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw2_0, dstw2_1, dstw2_2, dstw2_3, dstw2_4, dstw2_5, dstw2_6, dstw2_7, dstw2_8, dstw2_9, dstw2_10, dstw2_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w8 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w8 = star (c y6) * c y0 - star (c y7) * c y1 - star (c y8) * c y2 + star (c y9) * c y3 - star (c y10) * c y4 + star (c y11) * c y5 - star (c y0) * c y6 + star (c y1) * c y7 + star (c y2) * c y8 - star (c y3) * c y9 + star (c y4) * c y10 - star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw8_0, dsbw8_1, dsbw8_2, dsbw8_3, dsbw8_4, dsbw8_5, dsbw8_6, dsbw8_7, dsbw8_8, dsbw8_9, dsbw8_10, dsbw8_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w8 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w8 = - star (d z6) * d z0 + star (d z7) * d z1 - star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 + star (d z0) * d z6 - star (d z1) * d z7 + star (d z2) * d z8 - star (d z3) * d z9 - star (d z4) * d z10 + star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw8_0, dstw8_1, dstw8_2, dstw8_3, dstw8_4, dstw8_5, dstw8_6, dstw8_7, dstw8_8, dstw8_9, dstw8_10, dstw8_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w1 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w1 = star (c y6) * c y0 - star (c y7) * c y1 - star (c y8) * c y2 - star (c y9) * c y3 + star (c y10) * c y4 + star (c y11) * c y5 + star (c y0) * c y6 - star (c y1) * c y7 - star (c y2) * c y8 - star (c y3) * c y9 + star (c y4) * c y10 + star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw1_0, dsbw1_1, dsbw1_2, dsbw1_3, dsbw1_4, dsbw1_5, dsbw1_6, dsbw1_7, dsbw1_8, dsbw1_9, dsbw1_10, dsbw1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w1 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w1 = - star (d z6) * d z0 - star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 - star (d z0) * d z6 - star (d z1) * d z7 + star (d z2) * d z8 + star (d z3) * d z9 + star (d z4) * d z10 - star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw1_0, dstw1_1, dstw1_2, dstw1_3, dstw1_4, dstw1_5, dstw1_6, dstw1_7, dstw1_8, dstw1_9, dstw1_10, dstw1_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dbot_w7 (c : SS.BitString 6 -> ℂ) :
    diagBot c ef0 w7 = star (c y6) * c y0 - star (c y7) * c y1 - star (c y8) * c y2 - star (c y9) * c y3 + star (c y10) * c y4 + star (c y11) * c y5 - star (c y0) * c y6 + star (c y1) * c y7 + star (c y2) * c y8 + star (c y3) * c y9 - star (c y4) * c y10 - star (c y5) * c y11 := by
  unfold diagBot
  rw [diagB_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dfb0, dfb1, dfb2, dfb3, dfb4, dfb5, dfb6, dfb7, dfb8, dfb9, dfb10, dfb11]
  simp only [dsbw7_0, dsbw7_1, dsbw7_2, dsbw7_3, dsbw7_4, dsbw7_5, dsbw7_6, dsbw7_7, dsbw7_8, dsbw7_9, dsbw7_10, dsbw7_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem dtop_w7 (d : SS.BitString 6 -> ℂ) :
    diagTop d ef0 w7 = - star (d z6) * d z0 - star (d z7) * d z1 + star (d z8) * d z2 + star (d z9) * d z3 + star (d z10) * d z4 - star (d z11) * d z5 + star (d z0) * d z6 + star (d z1) * d z7 - star (d z2) * d z8 - star (d z3) * d z9 - star (d z4) * d z10 + star (d z5) * d z11 := by
  unfold diagTop
  rw [diagT_inc]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [dft0, dft1, dft2, dft3, dft4, dft5, dft6, dft7, dft8, dft9, dft10, dft11]
  simp only [dstw7_0, dstw7_1, dstw7_2, dstw7_3, dstw7_4, dstw7_5, dstw7_6, dstw7_7, dstw7_8, dstw7_9, dstw7_10, dstw7_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex1_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w0 = star (c y0) * d z4 + star (c y1) * d z5 + star (c y6) * d z10 + star (c y7) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_10, fl1_11]
  simp only [sg1_w0_4, sg1_w0_5, sg1_w0_10, sg1_w0_11, SixQubit.signMul_false]
  try ring

theorem ex1_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef1 w6 = star (c y0) * d z4 + star (c y1) * d z5 - star (c y6) * d z10 - star (c y7) * d z11 := by
  unfold offSum
  rw [incidence1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl1_4, fl1_5, fl1_10, fl1_11]
  simp only [sg1_w6_4, sg1_w6_5, sg1_w6_10, sg1_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex2_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w0 = star (c y6) * d z4 + star (c y7) * d z5 + star (c y0) * d z10 + star (c y1) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_4, fl2_5, fl2_10, fl2_11]
  simp only [sg2_w0_4, sg2_w0_5, sg2_w0_10, sg2_w0_11, SixQubit.signMul_false]
  try ring

theorem ex2_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef2 w6 = star (c y6) * d z4 + star (c y7) * d z5 - star (c y0) * d z10 - star (c y1) * d z11 := by
  unfold offSum
  rw [incidence2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl2_4, fl2_5, fl2_10, fl2_11]
  simp only [sg2_w6_4, sg2_w6_5, sg2_w6_10, sg2_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex3_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w0 = star (c y0) * d z3 + star (c y2) * d z5 + star (c y6) * d z9 + star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w0_3, sg3_w0_5, sg3_w0_9, sg3_w0_11, SixQubit.signMul_false]
  try ring

theorem ex3_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef3 w6 = star (c y0) * d z3 + star (c y2) * d z5 - star (c y6) * d z9 - star (c y8) * d z11 := by
  unfold offSum
  rw [incidence3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl3_3, fl3_5, fl3_9, fl3_11]
  simp only [sg3_w6_3, sg3_w6_5, sg3_w6_9, sg3_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex4_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w0 = star (c y6) * d z3 + star (c y8) * d z5 + star (c y0) * d z9 + star (c y2) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_3, fl4_5, fl4_9, fl4_11]
  simp only [sg4_w0_3, sg4_w0_5, sg4_w0_9, sg4_w0_11, SixQubit.signMul_false]
  try ring

theorem ex4_w6 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef4 w6 = star (c y6) * d z3 + star (c y8) * d z5 - star (c y0) * d z9 - star (c y2) * d z11 := by
  unfold offSum
  rw [incidence4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl4_3, fl4_5, fl4_9, fl4_11]
  simp only [sg4_w6_3, sg4_w6_5, sg4_w6_9, sg4_w6_11, SixQubit.signMul_true, SixQubit.signMul_false]
  try ring

theorem ex5_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef5 w0 = star (c y0) * d z2 + star (c y3) * d z5 + star (c y6) * d z8 + star (c y9) * d z11 := by
  unfold offSum
  rw [incidence5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl5_2, fl5_5, fl5_8, fl5_11]
  simp only [sg5_w0_2, sg5_w0_5, sg5_w0_8, sg5_w0_11, SixQubit.signMul_false]
  try ring

theorem ex6_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef6 w0 = star (c y0) * d z1 + star (c y4) * d z5 + star (c y6) * d z7 + star (c y10) * d z11 := by
  unfold offSum
  rw [incidence6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl6_1, fl6_5, fl6_7, fl6_11]
  simp only [sg6_w0_1, sg6_w0_5, sg6_w0_7, sg6_w0_11, SixQubit.signMul_false]
  try ring

theorem ex7_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef7 w0 = star (c y0) * d z0 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y11) * d z11 := by
  unfold offSum
  rw [incidence7]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl7_0, fl7_5, fl7_6, fl7_11]
  simp only [sg7_w0_0, sg7_w0_5, sg7_w0_6, sg7_w0_11, SixQubit.signMul_false]
  try ring

theorem ex8_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef8 w0 = star (c y1) * d z2 + star (c y3) * d z4 + star (c y7) * d z8 + star (c y9) * d z10 := by
  unfold offSum
  rw [incidence8]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl8_2, fl8_4, fl8_8, fl8_10]
  simp only [sg8_w0_2, sg8_w0_4, sg8_w0_8, sg8_w0_10, SixQubit.signMul_false]
  try ring

theorem ex9_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef9 w0 = star (c y1) * d z1 + star (c y4) * d z4 + star (c y7) * d z7 + star (c y10) * d z10 := by
  unfold offSum
  rw [incidence9]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl9_1, fl9_4, fl9_7, fl9_10]
  simp only [sg9_w0_1, sg9_w0_4, sg9_w0_7, sg9_w0_10, SixQubit.signMul_false]
  try ring

theorem ex10_w0 (c d : SS.BitString 6 -> ℂ) :
    offSum c d ef10 w0 = star (c y1) * d z0 + star (c y5) * d z4 + star (c y7) * d z6 + star (c y11) * d z10 := by
  unfold offSum
  rw [incidence10]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [fl10_0, fl10_4, fl10_6, fl10_10]
  simp only [sg10_w0_0, sg10_w0_4, sg10_w0_6, sg10_w0_10, SixQubit.signMul_false]
  try ring


/-! ## The moment system -/

/-- The two normalizations and the moment equalities, with every probability
nonnegative. -/
structure MomentSystem (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real) : Prop where
  n0 : q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 = 1
  n1 : r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 = 1
  m1 : q6 + q7 + q8 + q9 + q10 + q11 = r6 + r7 + r8 + r9 + r10 + r11
  m2 : q2 + q3 + q4 + q5 + q8 + q9 + q10 + q11 = r4 + r5 + r10 + r11
  m3 : q1 + q3 + q4 + q5 + q7 + q9 + q10 + q11 = r3 + r5 + r9 + r11
  m4 : q1 + q2 + q5 + q7 + q8 + q11 = r1 + r2 + r5 + r7 + r8 + r11
  m5 : q1 + q2 + q4 + q7 + q8 + q10 = r0 + r2 + r5 + r6 + r8 + r11
  m6 : q1 + q2 + q3 + q7 + q8 + q9 = r0 + r1 + r5 + r6 + r7 + r11
  c12 : q8 + q9 + q10 + q11 = r10 + r11
  c13 : q7 + q9 + q10 + q11 = r9 + r11
  c14 : q7 + q8 + q11 = r7 + r8 + r11
  c15 : q7 + q8 + q10 = r6 + r8 + r11
  c16 : q7 + q8 + q9 = r6 + r7 + r11
  c23 : q3 + q4 + q5 + q9 + q10 + q11 = r5 + r11
  c24 : q2 + q5 + q8 + q11 = r5 + r11
  c25 : q2 + q4 + q8 + q10 = r5 + r11
  c26 : q2 + q3 + q8 + q9 = r5 + r11
  c34 : q1 + q5 + q7 + q11 = r5 + r11
  c35 : q1 + q4 + q7 + q10 = r5 + r11
  c36 : q1 + q3 + q7 + q9 = r5 + r11
  c45 : q1 + q2 + q7 + q8 = r2 + r5 + r8 + r11
  c46 : q1 + q2 + q7 + q8 = r1 + r5 + r7 + r11
  c56 : q1 + q2 + q7 + q8 = r0 + r5 + r6 + r11

  nq0 : 0 ≤ q0
  nq1 : 0 ≤ q1
  nq2 : 0 ≤ q2
  nq3 : 0 ≤ q3
  nq4 : 0 ≤ q4
  nq5 : 0 ≤ q5
  nq6 : 0 ≤ q6
  nq7 : 0 ≤ q7
  nq8 : 0 ≤ q8
  nq9 : 0 ≤ q9
  nq10 : 0 ≤ q10
  nq11 : 0 ≤ q11
  nr0 : 0 ≤ r0
  nr1 : 0 ≤ r1
  nr2 : 0 ≤ r2
  nr3 : 0 ≤ r3
  nr4 : 0 ≤ r4
  nr5 : 0 ≤ r5
  nr6 : 0 ≤ r6
  nr7 : 0 ≤ r7
  nr8 : 0 ≤ r8
  nr9 : 0 ≤ r9
  nr10 : 0 ≤ r10
  nr11 : 0 ≤ r11

/-- Bottom block 0 has norm 3/10. -/
theorem blkc0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    q0 + q6 - 3/10 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (1) * n0 + (-7/10) * n1 + (-7/10) * m2 + (-7/10) * m3 + (-4/5) * c23 + (9/5) * c26 + (6/5) * c34 + (6/5) * c35 + (-3/5) * c36 + (-7/10) * c45 + (-7/10) * c46 + (-7/10) * c56

/-- Bottom block 1 has norm 1/5. -/
theorem blkc1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    q1 + q7 - 1/5 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (1/5) * n1 + (1/5) * m2 + (1/5) * m3 + (-1/5) * c23 + (-4/5) * c26 + (-1/5) * c34 + (-1/5) * c35 + (3/5) * c36 + (1/5) * c45 + (1/5) * c46 + (1/5) * c56

/-- Bottom block 2 has norm 1/5. -/
theorem blkc2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    q2 + q8 - 1/5 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (1/5) * n1 + (1/5) * m2 + (1/5) * m3 + (-1/5) * c23 + (1/5) * c26 + (-1/5) * c34 + (-1/5) * c35 + (-2/5) * c36 + (1/5) * c45 + (1/5) * c46 + (1/5) * c56

/-- Bottom block 3 has norm 1/10. -/
theorem blkc3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    q3 + q9 - 1/10 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (1/10) * n1 + (1/10) * m2 + (1/10) * m3 + (2/5) * c23 + (-2/5) * c26 + (-3/5) * c34 + (-3/5) * c35 + (4/5) * c36 + (1/10) * c45 + (1/10) * c46 + (1/10) * c56

/-- Bottom block 4 has norm 1/10. -/
theorem blkc4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    q10 + q4 - 1/10 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (1/10) * n1 + (1/10) * m2 + (1/10) * m3 + (2/5) * c23 + (-2/5) * c26 + (-3/5) * c34 + (2/5) * c35 + (-1/5) * c36 + (1/10) * c45 + (1/10) * c46 + (1/10) * c56

/-- Bottom block 5 has norm 1/10. -/
theorem blkc5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    q11 + q5 - 1/10 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (1/10) * n1 + (1/10) * m2 + (1/10) * m3 + (2/5) * c23 + (-2/5) * c26 + (2/5) * c34 + (-3/5) * c35 + (-1/5) * c36 + (1/10) * c45 + (1/10) * c46 + (1/10) * c56

/-- Top block 0 has norm 3/10. -/
theorem blkd0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    r11 + r5 - 3/10 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (3/10) * n1 + (3/10) * m2 + (3/10) * m3 + (1/5) * c23 + (-6/5) * c26 + (-4/5) * c34 + (-4/5) * c35 + (2/5) * c36 + (3/10) * c45 + (3/10) * c46 + (3/10) * c56

/-- Top block 3 has norm 1/10. -/
theorem blkd3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    r2 + r8 - 1/10 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (1/10) * n1 + (1/10) * m2 + (1/10) * m3 + (-3/5) * c23 + (3/5) * c26 + (2/5) * c34 + (2/5) * c35 + (-1/5) * c36 + (-9/10) * c45 + (1/10) * c46 + (1/10) * c56

/-- Reflection identity, block 0, entry (0,0). -/
theorem rr00_0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    2*q0/5 - 3*q1/5 - 3*q2/5 - 3*q3/5 - 3*q4/5 - 3*q5/5 + r5 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (2/5) * n0 + (-2/5) * n1 + (-2/5) * m1 + (-2/5) * m2 + (-2/5) * m3 + (2/5) * c12 + (2/5) * c13 + (1/5) * c14 + (1/5) * c15 + (1/5) * c16 + (-3/5) * c23 + (3/5) * c26 + (2/5) * c34 + (2/5) * c35 + (-1/5) * c36 + (-2/5) * c45 + (-2/5) * c46 + (-2/5) * c56

/-- Reflection identity, block 0, entry (1,1). -/
theorem rr11_0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    -3*q10/5 - 3*q11/5 + 2*q6/5 - 3*q7/5 - 3*q8/5 - 3*q9/5 + r11 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (2/5) * m1 + (-2/5) * c12 + (-2/5) * c13 + (-1/5) * c14 + (-1/5) * c15 + (-1/5) * c16

/-- Reflection identity, block 3, entry (0,0). -/
theorem rr00_3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : Real} (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) :
    -q0/5 - q1/5 - q2/5 + 4*q3/5 - q4/5 - q5/5 + r2 = 0 := by
  obtain ⟨n0, n1, m1, m2, m3, m4, m5, m6, c12, c13, c14, c15, c16, c23, c24, c25, c26, c34, c35, c36, c45, c46, c56, nq0, nq1, nq2, nq3, nq4, nq5, nq6, nq7, nq8, nq9, nq10, nq11, nr0, nr1, nr2, nr3, nr4, nr5, nr6, nr7, nr8, nr9, nr10, nr11⟩ := h
  linear_combination (-1/5) * n0 + (1/5) * n1 + (1/5) * m1 + (1/5) * m2 + (1/5) * m3 + (-1/5) * c12 + (-1/5) * c13 + (2/5) * c14 + (2/5) * c15 + (-3/5) * c16 + (-1/5) * c23 + (1/5) * c26 + (-1/5) * c34 + (-1/5) * c35 + (3/5) * c36 + (-4/5) * c45 + (1/5) * c46 + (1/5) * c56

/-! ## The reflection identity off the diagonal -/

set_option maxHeartbeats 1000000 in
/-- Entry `(0,1)` of the reflection identity at block 0. -/
theorem refl01_0 (c d : SS.BitString 6 -> ℂ)
    (Dg_w0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11 = diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10 = diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3 = diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2 = diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y0 * star (c y6) + d z5 * star (d z11)
      = (3/5 : ℂ) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0, dtop_w0] at Dg_w0
  rw [dbot_w6, dtop_w6] at Dg_w6
  rw [dbot_w5, dtop_w5] at Dg_w5
  rw [dbot_w11, dtop_w11] at Dg_w11
  rw [dbot_w4, dtop_w4] at Dg_w4
  rw [dbot_w10, dtop_w10] at Dg_w10
  rw [dbot_w3, dtop_w3] at Dg_w3
  rw [dbot_w9, dtop_w9] at Dg_w9
  rw [dbot_w2, dtop_w2] at Dg_w2
  rw [dbot_w8, dtop_w8] at Dg_w8
  rw [dbot_w1, dtop_w1] at Dg_w1
  rw [dbot_w7, dtop_w7] at Dg_w7
  linear_combination (-3/20 : ℂ) * Dg_w0 + (1/10 : ℂ) * Dg_w5 + (1/10 : ℂ) * Dg_w4 + (1/20 : ℂ) * Dg_w3 + (1/20 : ℂ) * Dg_w2 + (1/20 : ℂ) * Dg_w1 + (-3/20 : ℂ) * Dg_w6 + (1/10 : ℂ) * Dg_w11 + (1/10 : ℂ) * Dg_w10 + (1/20 : ℂ) * Dg_w9 + (1/20 : ℂ) * Dg_w8 + (1/20 : ℂ) * Dg_w7

set_option maxHeartbeats 1000000 in
/-- Entry `(0,1)` of the reflection identity at block 3. -/
theorem refl01_3 (c d : SS.BitString 6 -> ℂ)
    (Dg_w0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11 = diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10 = diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3 = diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2 = diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    : c y3 * star (c y9) + d z2 * star (d z8)
      = (1/5 : ℂ) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0, dtop_w0] at Dg_w0
  rw [dbot_w6, dtop_w6] at Dg_w6
  rw [dbot_w5, dtop_w5] at Dg_w5
  rw [dbot_w11, dtop_w11] at Dg_w11
  rw [dbot_w4, dtop_w4] at Dg_w4
  rw [dbot_w10, dtop_w10] at Dg_w10
  rw [dbot_w3, dtop_w3] at Dg_w3
  rw [dbot_w9, dtop_w9] at Dg_w9
  rw [dbot_w2, dtop_w2] at Dg_w2
  rw [dbot_w8, dtop_w8] at Dg_w8
  rw [dbot_w1, dtop_w1] at Dg_w1
  rw [dbot_w7, dtop_w7] at Dg_w7
  linear_combination (-1/20 : ℂ) * Dg_w0 + (-1/20 : ℂ) * Dg_w5 + (-1/20 : ℂ) * Dg_w4 + (1/10 : ℂ) * Dg_w3 + (1/10 : ℂ) * Dg_w2 + (-3/20 : ℂ) * Dg_w1 + (-1/20 : ℂ) * Dg_w6 + (-1/20 : ℂ) * Dg_w11 + (-1/20 : ℂ) * Dg_w10 + (1/10 : ℂ) * Dg_w9 + (1/10 : ℂ) * Dg_w8 + (-3/20 : ℂ) * Dg_w7


/-! ## The cross relations -/

/-- Entry `(0,0)` of the vanishing rank-one sum at block 1. -/
theorem xr1_00 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w6 = 0)
    : d z4 * star (c y0) + d z5 * star (c y1) = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Entry `(1,1)` of the vanishing rank-one sum at block 1. -/
theorem xr1_11 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w6 = 0)
    : d z10 * star (c y6) + d z11 * star (c y7) = 0 := by
  rw [ex1_w0] at h0
  rw [ex1_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Entry `(0,1)` of the vanishing rank-one sum at block 1. -/
theorem xr1_01 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w6 = 0)
    : d z4 * star (c y6) + d z5 * star (c y7) = 0 := by
  rw [ex2_w0] at h0
  rw [ex2_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Entry `(1,0)` of the vanishing rank-one sum at block 1. -/
theorem xr1_10 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w6 = 0)
    : d z10 * star (c y0) + d z11 * star (c y1) = 0 := by
  rw [ex2_w0] at h0
  rw [ex2_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Entry `(0,0)` of the vanishing rank-one sum at block 2. -/
theorem xr2_00 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w6 = 0)
    : d z3 * star (c y0) + d z5 * star (c y2) = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Entry `(1,1)` of the vanishing rank-one sum at block 2. -/
theorem xr2_11 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w6 = 0)
    : d z9 * star (c y6) + d z11 * star (c y8) = 0 := by
  rw [ex3_w0] at h0
  rw [ex3_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- Entry `(0,1)` of the vanishing rank-one sum at block 2. -/
theorem xr2_01 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w6 = 0)
    : d z3 * star (c y6) + d z5 * star (c y8) = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (1/2 : ℂ) * h1

/-- Entry `(1,0)` of the vanishing rank-one sum at block 2. -/
theorem xr2_10 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef4 w0 = 0)
    (h1 : offSum c d ef4 w6 = 0)
    : d z9 * star (c y0) + d z11 * star (c y2) = 0 := by
  rw [ex4_w0] at h0
  rw [ex4_w6] at h1
  linear_combination (1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1

/-- The scalar cross relation joining block 0 to block 3. -/
theorem yr0_3 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef5 w0 = 0)
    : star (c y3) * d z5 + star (c y9) * d z11
      + (star (c y0) * d z2 + star (c y6) * d z8) = 0 := by
  rw [ex5_w0] at h
  linear_combination h

/-- The scalar cross relation joining block 1 to block 3. -/
theorem yr1_3 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef8 w0 = 0)
    : star (c y3) * d z4 + star (c y9) * d z10
      + (star (c y1) * d z2 + star (c y7) * d z8) = 0 := by
  rw [ex8_w0] at h
  linear_combination h

/-- The scalar cross relation joining block 0 to block 4. -/
theorem yr0_4 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef6 w0 = 0)
    : star (c y4) * d z5 + star (c y10) * d z11
      + (star (c y0) * d z1 + star (c y6) * d z7) = 0 := by
  rw [ex6_w0] at h
  linear_combination h

/-- The scalar cross relation joining block 1 to block 4. -/
theorem yr1_4 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef9 w0 = 0)
    : star (c y4) * d z4 + star (c y10) * d z10
      + (star (c y1) * d z1 + star (c y7) * d z7) = 0 := by
  rw [ex9_w0] at h
  linear_combination h

/-- The scalar cross relation joining block 0 to block 5. -/
theorem yr0_5 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef7 w0 = 0)
    : star (c y5) * d z5 + star (c y11) * d z11
      + (star (c y0) * d z0 + star (c y6) * d z6) = 0 := by
  rw [ex7_w0] at h
  linear_combination h

/-- The scalar cross relation joining block 1 to block 5. -/
theorem yr1_5 (c d : SS.BitString 6 -> ℂ)
    (h : offSum c d ef10 w0 = 0)
    : star (c y5) * d z4 + star (c y11) * d z10
      + (star (c y1) * d z0 + star (c y7) * d z6) = 0 := by
  rw [ex10_w0] at h
  linear_combination h

/-! ## The no-go -/

set_option maxHeartbeats 1000000 in
/-- Orbit 33 admits no six-qubit `((6,2,3))` code. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (Dg_w0 : diagBot c ef0 w0 = diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6 = diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5 = diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11 = diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4 = diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10 = diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3 = diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9 = diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2 = diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8 = diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1 = diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7 = diagTop d ef0 w7)
    (E1_w0 : offSum c d ef1 w0 = 0)
    (E1_w6 : offSum c d ef1 w6 = 0)
    (E2_w0 : offSum c d ef2 w0 = 0)
    (E2_w6 : offSum c d ef2 w6 = 0)
    (E3_w0 : offSum c d ef3 w0 = 0)
    (E3_w6 : offSum c d ef3 w6 = 0)
    (E4_w0 : offSum c d ef4 w0 = 0)
    (E4_w6 : offSum c d ef4 w6 = 0)
    (E5_w0 : offSum c d ef5 w0 = 0)
    (E6_w0 : offSum c d ef6 w0 = 0)
    (E7_w0 : offSum c d ef7 w0 = 0)
    (E8_w0 : offSum c d ef8 w0 = 0)
    (E9_w0 : offSum c d ef9 w0 = 0)
    (E10_w0 : offSum c d ef10 w0 = 0)
    : False := by
  have nc0r : Complex.normSq (c y0) + Complex.normSq (c y6) = 3/10 := by
    have h := blkc0 hm; linarith
  have nc0 : c y0 * star (c y0) + c y6 * star (c y6) = (3/10 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nc0r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nc1r : Complex.normSq (c y1) + Complex.normSq (c y7) = 1/5 := by
    have h := blkc1 hm; linarith
  have nc1 : c y1 * star (c y1) + c y7 * star (c y7) = (1/5 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nc1r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nc2r : Complex.normSq (c y2) + Complex.normSq (c y8) = 1/5 := by
    have h := blkc2 hm; linarith
  have nc2 : c y2 * star (c y2) + c y8 * star (c y8) = (1/5 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nc2r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nc3r : Complex.normSq (c y3) + Complex.normSq (c y9) = 1/10 := by
    have h := blkc3 hm; linarith
  have nc3 : c y3 * star (c y3) + c y9 * star (c y9) = (1/10 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nc3r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nc4r : Complex.normSq (c y4) + Complex.normSq (c y10) = 1/10 := by
    have h := blkc4 hm; linarith
  have nc4 : c y4 * star (c y4) + c y10 * star (c y10) = (1/10 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nc4r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nc5r : Complex.normSq (c y5) + Complex.normSq (c y11) = 1/10 := by
    have h := blkc5 hm; linarith
  have nc5 : c y5 * star (c y5) + c y11 * star (c y11) = (1/10 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nc5r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nd0r : Complex.normSq (d z5) + Complex.normSq (d z11) = 3/10 := by
    have h := blkd0 hm; linarith
  have nd0 : d z5 * star (d z5) + d z11 * star (d z11) = (3/10 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nd0r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have nd3r : Complex.normSq (d z2) + Complex.normSq (d z8) = 1/10 := by
    have h := blkd3 hm; linarith
  have nd3 : d z2 * star (d z2) + d z8 * star (d z8) = (1/10 : ℂ) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) nd3r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have r00_0r : Complex.normSq (c y0) + Complex.normSq (d z5)
      = (3/5) * (Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5)) := by
    have h := rr00_0 hm; linarith
  have r00_0 : c y0 * star (c y0) + d z5 * star (d z5)
      = (3/5 : ℂ) * (c y0 * star (c y0) + c y1 * star (c y1) + c y2 * star (c y2) + c y3 * star (c y3) + c y4 * star (c y4) + c y5 * star (c y5)) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) r00_0r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have r11_0r : Complex.normSq (c y6) + Complex.normSq (d z11)
      = (3/5) * (Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11)) := by
    have h := rr11_0 hm; linarith
  have r11_0 : c y6 * star (c y6) + d z11 * star (d z11)
      = (3/5 : ℂ) * (c y6 * star (c y6) + c y7 * star (c y7) + c y8 * star (c y8) + c y9 * star (c y9) + c y10 * star (c y10) + c y11 * star (c y11)) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) r11_0r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have r00_3r : Complex.normSq (c y3) + Complex.normSq (d z2)
      = (1/5) * (Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5)) := by
    have h := rr00_3 hm; linarith
  have r00_3 : c y3 * star (c y3) + d z2 * star (d z2)
      = (1/5 : ℂ) * (c y0 * star (c y0) + c y1 * star (c y1) + c y2 * star (c y2) + c y3 * star (c y3) + c y4 * star (c y4) + c y5 * star (c y5)) := by
    have hc := congrArg (fun x : Real => (x : ℂ)) r00_3r
    push_cast at hc
    simp only [sq]
    linear_combination hc
  have r01_0 := refl01_0 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
  have r01_3 := refl01_3 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
  exact Block33.block_contradiction
    (c y0) (c y1) (c y2) (c y3) (c y4) (c y5)
    (c y6) (c y7) (c y8) (c y9) (c y10) (c y11)
    (d z5) (d z4) (d z3) (d z2) (d z1) (d z0)
    (d z11) (d z10) (d z9) (d z8) (d z7) (d z6)
    nc0 nc1 nc2 nc3 nc4 nc5 nd0 nd3
    r00_0 r01_0 r11_0 r00_3 r01_3
    (xr1_00 c d E1_w0 E1_w6) (xr1_10 c d E2_w0 E2_w6) (xr1_01 c d E2_w0 E2_w6) (xr1_11 c d E1_w0 E1_w6)
    (xr2_00 c d E3_w0 E3_w6) (xr2_10 c d E4_w0 E4_w6) (xr2_01 c d E4_w0 E4_w6) (xr2_11 c d E3_w0 E3_w6)
    (yr0_3 c d E5_w0) (yr1_3 c d E8_w0) (yr0_4 c d E6_w0) (yr1_4 c d E9_w0) (yr0_5 c d E7_w0) (yr1_5 c d E10_w0)

end

end SixQubit.Orbit33
