import Orbit2.Certificate

/-! Generated, untrusted data for character ZXIY.
Global monomial indices: [24, 167, 200, 313].
All assertions below are checked by Lean's kernel using `decide +kernel`.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2.Block089

def M : Matrix (Fin 4) (Fin 4) ℚ := ![![68, 28, (-20), (-30)], ![28, 104, (-30), (-56)], ![(-20), (-30), 68, 28], ![(-30), (-56), 28, 104]]
def L : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![(7 / 16), 1, 0, 0], ![(-5 / 16), (-85 / 351), 1, 0], ![(-15 / 32), (-343 / 702), (2893 / 18464), 1]]
def d : Fin 4 → ℚ := ![64, (351 / 4), (18464 / 351), (1176105 / 18464)]

def certificate : LDLCertificate 4 4 where
  A := fun i j => M i j - if i = j then 4 else 0
  L := L
  d := d
  positive := by decide +kernel
  factorization := by decide +kernel

theorem coercivity (z : Fin 4 → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z :=
  shifted_coercivity M certificate (fun _ _ => rfl) z

end Orbit2.Block089
