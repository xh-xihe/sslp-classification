import Orbit2.QuarticCoefficients
import Orbit2.ZeroExtension

/-! Exact coefficient check for character ZIIZ.
Coordinates include the weight-one/weight-one zero monomials. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Orbit2.Quartic.Coefficient081

def indices : Fin 8 → Fin 528 := ![81, 111, 142, 170, 197, 223, 250, 274]
def expected : Matrix (Fin 8) (Fin 8) ℤ := ![![136, (-24), 24, 64, 24, 64, 176, (-48)], ![(-24), 136, 24, 64, 24, 64, (-48), 176], ![24, 24, 136, 176, (-24), (-48), 64, 64], ![64, 64, 176, 448, (-48), (-96), 152, 152], ![24, 24, (-24), (-48), 136, 176, 64, 64], ![64, 64, (-48), (-96), 176, 448, 152, 152], ![176, (-48), 64, 152, 64, 152, 448, (-96)], ![(-48), 176, 64, 152, 64, 152, (-96), 448]]
def active : Fin 8 → Bool := ![true, true, true, true, true, true, true, true]
def position : Fin 8 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6, 7]
def positivePosition : Fin 8 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6, 7]

/-- Reconstructing 24Q gives exactly twice the integer Gram matrix. -/
theorem coefficient_identity : ∀ i j,
    twiceCoefficient (indices i) (indices j) = expected i j := by
  decide +kernel

/-- The reconstructed coefficients are the very matrices whose LDL factors
were checked, with zero coordinates retained explicitly. -/
theorem certified_matrix : ∀ i j, (expected i j : ℚ) =
    if active i ∧ active j then 2 * Orbit2.Block081.M (position i) (position j) else 0 := by
  decide +kernel

theorem certified_indices : ∀ k,
    indices (positivePosition k) = (checkedBlocks 81).indices k := by
  decide +kernel

theorem positive_retraction : ∀ k, position (positivePosition k) = k := by
  decide +kernel

theorem active_embedding : ∀ i, active i → positivePosition (position i) = i := by
  decide +kernel

theorem positive_active : ∀ k, active (positivePosition k) := by
  decide +kernel

theorem energy_identity (z : Fin 528 → ℂ) :
    complexEnergy (fun i j => (expected i j : ℚ)) (fun i => z (indices i)) =
      2 * blockEnergy (checkedBlocks 81) z := by
  have h := complexEnergy_zero_extension (fun i j => (expected i j : ℚ))
    Orbit2.Block081.M active position positivePosition positive_retraction
    positive_active active_embedding certified_matrix (fun i => z (indices i))
  change _ = 2 * complexEnergy Orbit2.Block081.M
    (fun k => z ((checkedBlocks 81).indices k))
  simpa only [certified_indices] using h

end Orbit2.Quartic.Coefficient081
