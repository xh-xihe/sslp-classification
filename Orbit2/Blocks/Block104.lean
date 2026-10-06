import Orbit2.Certificate

/-! Generated, untrusted data for character ZZII.
Global monomial indices: [28, 60, 91, 121, 240, 264, 287, 309].
All assertions below are checked by Lean's kernel using `decide +kernel`.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Orbit2.Block104

def M : Matrix (Fin 8) (Fin 8) ℚ := ![![68, (-12), 12, 12, 32, 32, 88, (-24)], ![(-12), 68, 12, 12, 32, 32, (-24), 88], ![12, 12, 68, (-12), 88, (-24), 32, 32], ![12, 12, (-12), 68, (-24), 88, 32, 32], ![32, 32, 88, (-24), 224, (-48), 76, 76], ![32, 32, (-24), 88, (-48), 224, 76, 76], ![88, (-24), 32, 32, 76, 76, 224, (-48)], ![(-24), 88, 32, 32, 76, 76, (-48), 224]]
def L : Matrix (Fin 8) (Fin 8) ℚ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![(-3 / 16), 1, 0, 0, 0, 0, 0, 0], ![(3 / 16), (3 / 13), 1, 0, 0, 0, 0, 0], ![(3 / 16), (3 / 13), (-3 / 10), 1, 0, 0, 0, 0], ![(1 / 2), (8 / 13), (119 / 95), (-6 / 19), 1, 0, 0, 0], ![(1 / 2), (8 / 13), (-63 / 95), (22 / 19), (-92 / 397), 1, 0, 0], ![(11 / 8), (-30 / 247), (28 / 95), (8 / 19), (105 / 397), (21 / 61), 1, 0], ![(-3 / 8), (334 / 247), (28 / 95), (8 / 19), (105 / 397), (21 / 61), (-10022 / 19807), 1]]
def d : Fin 8 → ℚ := ![64, (247 / 4), (760 / 13), (266 / 5), (1588 / 19), (596580 / 7543), (79228 / 1159), (1007340 / 19807)]

def certificate : LDLCertificate 8 8 where
  A := fun i j => M i j - if i = j then 4 else 0
  L := L
  d := d
  positive := by decide +kernel
  factorization := by decide +kernel

theorem coercivity (z : Fin 8 → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z :=
  shifted_coercivity M certificate (fun _ _ => rfl) z

end Orbit2.Block104
