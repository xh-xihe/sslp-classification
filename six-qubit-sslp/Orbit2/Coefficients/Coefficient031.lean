import Orbit2.QuarticCoefficients
import Orbit2.ZeroExtension

/-! Exact coefficient check for character IZZZ.
Coordinates include the weight-one/weight-one zero monomials. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Orbit2.Quartic.Coefficient031

def indices : Fin 12 → Fin 528 := ![11, 41, 70, 98, 125, 151, 461, 471, 480, 488, 495, 501]
def expected : Matrix (Fin 12) (Fin 12) ℤ := ![![136, 24, 40, (-40), 40, (-40), (-4), 4, 112, 112, (-4), 4], ![24, 136, (-40), 40, (-40), 40, 4, (-4), 112, 112, 4, (-4)], ![40, (-40), 136, 24, 40, (-40), 112, 112, (-4), 4, 4, (-4)], ![(-40), 40, 24, 136, (-40), 40, 112, 112, 4, (-4), (-4), 4], ![40, (-40), 40, (-40), 136, 24, 4, (-4), 4, (-4), 112, 112], ![(-40), 40, (-40), 40, 24, 136, (-4), 4, (-4), 4, 112, 112], ![(-4), 4, 112, 112, 4, (-4), 320, 224, 0, 0, 0, 0], ![4, (-4), 112, 112, (-4), 4, 224, 320, 0, 0, 0, 0], ![112, 112, (-4), 4, 4, (-4), 0, 0, 320, 224, 0, 0], ![112, 112, 4, (-4), (-4), 4, 0, 0, 224, 320, 0, 0], ![(-4), 4, 4, (-4), 112, 112, 0, 0, 0, 0, 320, 224], ![4, (-4), (-4), 4, 112, 112, 0, 0, 0, 0, 224, 320]]
def active : Fin 12 → Bool := ![true, true, true, true, true, true, true, true, true, true, true, true]
def position : Fin 12 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def positivePosition : Fin 12 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- Reconstructing 24Q gives exactly twice the integer Gram matrix. -/
theorem coefficient_identity : ∀ i j,
    twiceCoefficient (indices i) (indices j) = expected i j := by
  decide +kernel

/-- The reconstructed coefficients are the very matrices whose LDL factors
were checked, with zero coordinates retained explicitly. -/
theorem certified_matrix : ∀ i j, (expected i j : ℚ) =
    if active i ∧ active j then 2 * Orbit2.Block031.M (position i) (position j) else 0 := by
  decide +kernel

theorem certified_indices : ∀ k,
    indices (positivePosition k) = (checkedBlocks 31).indices k := by
  decide +kernel

theorem positive_retraction : ∀ k, position (positivePosition k) = k := by
  decide +kernel

theorem active_embedding : ∀ i, active i → positivePosition (position i) = i := by
  decide +kernel

theorem positive_active : ∀ k, active (positivePosition k) := by
  decide +kernel

theorem energy_identity (z : Fin 528 → ℂ) :
    complexEnergy (fun i j => (expected i j : ℚ)) (fun i => z (indices i)) =
      2 * blockEnergy (checkedBlocks 31) z := by
  have h := complexEnergy_zero_extension (fun i j => (expected i j : ℚ))
    Orbit2.Block031.M active position positivePosition positive_retraction
    positive_active active_embedding certified_matrix (fun i => z (indices i))
  change _ = 2 * complexEnergy Orbit2.Block031.M
    (fun k => z ((checkedBlocks 31).indices k))
  simpa only [certified_indices] using h

end Orbit2.Quartic.Coefficient031
