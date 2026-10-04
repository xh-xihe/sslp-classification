import Orbit2.Certificate

/-! Generated, untrusted data for character ZYZY.
Global monomial indices: [58, 173, 194, 289].
All assertions below are checked by Lean's kernel using `decide +kernel`.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2.Block103

def M : Matrix (Fin 4) (Fin 4) ℚ := ![![68, 4, 12, 4], ![4, 172, 4, 128], ![12, 4, 68, 4], ![4, 128, 4, 172]]
def L : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![(1 / 16), 1, 0, 0], ![(3 / 16), (13 / 671), 1, 0], ![(1 / 16), (511 / 671), (5 / 398), 1]]
def d : Fin 4 → ℚ := ![64, (671 / 4), (41392 / 671), (14020 / 199)]

def certificate : LDLCertificate 4 4 where
  A := fun i j => M i j - if i = j then 4 else 0
  L := L
  d := d
  positive := by decide +kernel
  factorization := by decide +kernel

theorem coercivity (z : Fin 4 → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z :=
  shifted_coercivity M certificate (fun _ _ => rfl) z

end Orbit2.Block103
