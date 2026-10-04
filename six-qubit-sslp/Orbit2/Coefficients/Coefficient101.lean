import Orbit2.QuarticCoefficients
import Orbit2.ZeroExtension

/-! Exact coefficient check for character ZYYZ.
Coordinates include the weight-one/weight-one zero monomials. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Orbit2.Quartic.Coefficient101

def indices : Fin 4 → Fin 528 := ![116, 175, 192, 245]
def expected : Matrix (Fin 4) (Fin 4) ℤ := ![![136, 8, 24, 8], ![8, 344, 8, 256], ![24, 8, 136, 8], ![8, 256, 8, 344]]
def active : Fin 4 → Bool := ![true, true, true, true]
def position : Fin 4 → Fin 4 := ![0, 1, 2, 3]
def positivePosition : Fin 4 → Fin 4 := ![0, 1, 2, 3]

/-- Reconstructing 24Q gives exactly twice the integer Gram matrix. -/
theorem coefficient_identity : ∀ i j,
    twiceCoefficient (indices i) (indices j) = expected i j := by
  decide +kernel

/-- The reconstructed coefficients are the very matrices whose LDL factors
were checked, with zero coordinates retained explicitly. -/
theorem certified_matrix : ∀ i j, (expected i j : ℚ) =
    if active i ∧ active j then 2 * Orbit2.Block101.M (position i) (position j) else 0 := by
  decide +kernel

theorem certified_indices : ∀ k,
    indices (positivePosition k) = (checkedBlocks 101).indices k := by
  decide +kernel

theorem positive_retraction : ∀ k, position (positivePosition k) = k := by
  decide +kernel

theorem active_embedding : ∀ i, active i → positivePosition (position i) = i := by
  decide +kernel

theorem positive_active : ∀ k, active (positivePosition k) := by
  decide +kernel

theorem energy_identity (z : Fin 528 → ℂ) :
    complexEnergy (fun i j => (expected i j : ℚ)) (fun i => z (indices i)) =
      2 * blockEnergy (checkedBlocks 101) z := by
  have h := complexEnergy_zero_extension (fun i j => (expected i j : ℚ))
    Orbit2.Block101.M active position positivePosition positive_retraction
    positive_active active_embedding certified_matrix (fun i => z (indices i))
  change _ = 2 * complexEnergy Orbit2.Block101.M
    (fun k => z ((checkedBlocks 101).indices k))
  simpa only [certified_indices] using h

end Orbit2.Quartic.Coefficient101
