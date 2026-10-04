import Orbit2.Certificate

/-! Generated, untrusted data for character IYYI.
Global monomial indices: [153, 467, 505].
All assertions below are checked by Lean's kernel using `decide +kernel`.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2.Block020

def M : Matrix (Fin 3) (Fin 3) ℚ := ![![176, 8, 124], ![8, 160, 8], ![124, 8, 176]]
def L : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 0, 0], ![(2 / 43), 1, 0], ![(31 / 43), (24 / 1673), 1]]
def d : Fin 3 → ℚ := ![172, (6692 / 43), (138144 / 1673)]

def certificate : LDLCertificate 3 3 where
  A := fun i j => M i j - if i = j then 4 else 0
  L := L
  d := d
  positive := by decide +kernel
  factorization := by decide +kernel

theorem coercivity (z : Fin 3 → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z :=
  shifted_coercivity M certificate (fun _ _ => rfl) z

end Orbit2.Block020
