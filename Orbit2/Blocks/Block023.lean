import Orbit2.Certificate

/-! Generated, untrusted data for character IYZY.
Global monomial indices: [7, 129, 477, 504].
All assertions below are checked by Lean's kernel using `decide +kernel`.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2.Block023

def M : Matrix (Fin 4) (Fin 4) ℚ := ![![68, 20, 28, 30], ![20, 68, 30, 28], ![28, 30, 104, 56], ![30, 28, 56, 104]]
def L : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![(5 / 16), 1, 0, 0], ![(7 / 16), (85 / 231), 1, 0], ![(15 / 32), (149 / 462), (8321 / 18464), 1]]
def d : Fin 4 → ℚ := ![64, (231 / 4), (18464 / 231), (1176105 / 18464)]

def certificate : LDLCertificate 4 4 where
  A := fun i j => M i j - if i = j then 4 else 0
  L := L
  d := d
  positive := by decide +kernel
  factorization := by decide +kernel

theorem coercivity (z : Fin 4 → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z :=
  shifted_coercivity M certificate (fun _ _ => rfl) z

end Orbit2.Block023
