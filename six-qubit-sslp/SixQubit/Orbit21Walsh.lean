import Mathlib
import SixQubit.Orbit21Coef

/-!
# Orbit 21: the finite Walsh table

This module contains only the 64-mask arithmetic at the heart of the corrected
orbit-21 certificate.  Keeping it over `Nat` makes kernel reduction much
smaller than enumerating function-valued bit strings.
-/

namespace SixQubit.Orbit21Walsh

/-- Two words stay in the same residue-0 or residue-2 fibre after the flip
`x`.  All arguments are six-bit masks. -/
def sameFiber (x s : Nat) : Bool :=
  let w := Orbit21Coef.wtA s
  (w = 0 || w = 2) && Orbit21Coef.wtA (s ^^^ x) = w

/-- For each `x`, bit `u` records whether `u` occurs as the difference of two
allowed autocorrelations.  This compact 64-word table avoids repeatedly
searching the fibres during kernel reduction. -/
def activeTable : List Nat :=
  [10851025924953565545, 0, 0, 10416984886409234697,
   0, 9548902812958662945, 9404222467855171905, 0,
   0, 0, 0, 10416984886409234697,
   0, 9548902812958662945, 9404222467855171905, 0,
   0, 0, 0, 10416984886409234697,
   0, 9548902812958662945, 9404222467855171905, 0,
   10851025924953565545, 0, 0, 10416984886409234697,
   0, 9548902812958662945, 9404222467855171905, 0,
   0, 9404222467855171905, 9548902812958662945, 0,
   10416984886409234697, 0, 0, 0,
   0, 9404222467855171905, 9548902812958662945, 0,
   10416984886409234697, 0, 0, 10851025924953565545,
   0, 9404222467855171905, 9548902812958662945, 0,
   10416984886409234697, 0, 0, 10851025924953565545,
   0, 9404222467855171905, 9548902812958662945, 0,
   10416984886409234697, 0, 0, 0]

def active (x u : Nat) : Bool :=
  ((activeTable.getD x 0 >>> u) &&& 1) = 1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The table contains every frequency produced by two allowed fibre pairs. -/
theorem active_of_sameFiber : ∀ x < 64, ∀ s < 64, ∀ t < 64,
    sameFiber x s = true → sameFiber x t = true →
      active x (s ^^^ t) = true := by
  decide

/-- Exact integral Walsh transform of the certificate coefficient. -/
def fourierCoef (x u : Nat) : Int :=
  ∑ z ∈ Finset.range 64,
    Orbit21Coef.coef x z * Orbit21Coef.sgn (Orbit21Coef.pc (z &&& u))

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
/-- **The 512-entry finite certificate.** -/
theorem fourierCoef_zero : ∀ x < 64, ∀ u < 64,
    active x u = true → fourierCoef x u = 0 := by
  decide

end SixQubit.Orbit21Walsh
