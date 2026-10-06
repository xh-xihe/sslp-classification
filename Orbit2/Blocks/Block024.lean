import Orbit2.Certificate

/-! Generated, untrusted data for character IZII.
Global monomial indices: [152, 494, 502].
All assertions below are checked by Lean's kernel using `decide +kernel`.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2.Block024

def M : Matrix (Fin 3) (Fin 3) ℚ := ![![160, 112, 112], ![112, 160, 112], ![112, 112, 160]]
def L : Matrix (Fin 3) (Fin 3) ℚ := ![![1, 0, 0], ![(28 / 39), 1, 0], ![(28 / 39), (28 / 67), 1]]
def d : Fin 3 → ℚ := ![156, (2948 / 39), (4180 / 67)]

def certificate : LDLCertificate 3 3 where
  A := fun i j => M i j - if i = j then 4 else 0
  L := L
  d := d
  positive := by decide +kernel
  factorization := by decide +kernel

theorem coercivity (z : Fin 3 → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z :=
  shifted_coercivity M certificate (fun _ _ => rfl) z

end Orbit2.Block024
