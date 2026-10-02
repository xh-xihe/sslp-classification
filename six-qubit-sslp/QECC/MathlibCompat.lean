import Mathlib

/-!
# Lean core and Mathlib backports for the LeanSecIII port

LeanSecIII was written against Lean 4.28.0 and Mathlib v4.28.0. This
repository pins Lean 4.27.0 and the Mathlib revision that goes with it. The
declarations below exist upstream in 4.28.0 but not in the pinned versions.
Each one is copied with its upstream statement, name and proof, so that the
ported files stay as they were written.

Delete this file when the repository moves to Lean and Mathlib 4.28.0 or
later. The names will then clash with the upstream ones, which is the signal.
-/

namespace AddCircle

variable {T : ℝ}

/-- Upstream: `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`, v4.28.0. -/
theorem toCircle_neg (x : AddCircle T) : toCircle (-x) = (toCircle x)⁻¹ :=
  (mul_left_inj (toCircle x)).mp <| by simp [← toCircle_add]

end AddCircle

namespace Nat

/-- Upstream: Lean core `Init/Data/Nat/Gcd.lean`, v4.28.0. -/
theorem gcd_left_comm (m n k : Nat) : gcd m (gcd n k) = gcd n (gcd m k) := by
  rw [← gcd_assoc, ← gcd_assoc, gcd_comm m n]

end Nat
