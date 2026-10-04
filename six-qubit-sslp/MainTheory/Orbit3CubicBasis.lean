import MainTheory.Orbit3ActualSampling
import SixQubit.Generated.Orbit3CubicTriples

/-! # The 715-dimensional ordinary cubic basis is an actual moment basis

The pair-index table covers every XOR-zero ordered triple, and has a right
inverse on all 715 sorted triples. The 36-term positive square is a principal
submatrix of this actual Gram matrix, with no multiplicity rescaling.
-/

namespace MainTheory.Orbit3CubicBasis

open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.FiniteCubicMoments MainTheory.Orbit3PhaseBlocks
open MainTheory.CubicTripleCanonical
open SixQubit.Generated
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

def moment (W : Encoder) : Matrix (Fin 715) (Fin 715) ℝ :=
  cubicMoment Orbit3CubicTriples.physical (wave W)

theorem moment_posSemidef (W : Encoder) : (moment W).PosSemidef :=
  cubicMoment_posSemidef _ _

theorem moment_eq_pairMoment (W : Encoder) (i j : Fin 715) :
    moment W i j = pairMoment W
      ((Orbit3CubicTriples.physical i).1, (Orbit3CubicTriples.physical i).2.1)
      ((Orbit3CubicTriples.physical j).1, (Orbit3CubicTriples.physical j).2.1) := by
  unfold moment pairMoment
  rw [cubicMoment_apply, cubicMoment_apply]
  simp only [triple]
  simp_rw [Orbit3CubicTriples.physical_xor]

theorem zero_outside_phase_block (W : Encoder) (i j : Fin 715)
    (h : block (Orbit3CubicTriples.physical i).1 (Orbit3CubicTriples.physical i).2.1 ≠
      block (Orbit3CubicTriples.physical j).1 (Orbit3CubicTriples.physical j).2.1) :
    moment W i j = 0 := by
  rw [moment_eq_pairMoment]
  exact pairMoment_zero_outside_block W _ _ _ _ h

def squareIndex (i : Fin 36) : Fin 715 :=
  Orbit3CubicTriples.pairIndex (Orbit3PositiveSquare.cubicTriples i).1
    (Orbit3PositiveSquare.cubicTriples i).2.1

theorem square_triples : ∀ i : Fin 36,
    Orbit3CubicTriples.triples (squareIndex i) = Orbit3PositiveSquare.cubicTriples i := by
  decide +kernel

theorem square_feature (W : Encoder) (g : Index) (i : Fin 36) :
    MainTheory.Orbit3PositiveMoments.actualCubic (wave W) g i =
      cubic Orbit3CubicTriples.physical (wave W) g (squareIndex i) := by
  unfold MainTheory.Orbit3PositiveMoments.actualCubic cubic Orbit3CubicTriples.physical
  rw [square_triples]

theorem square_principal_submatrix (W : Encoder) (i j : Fin 36) :
    MainTheory.Orbit3PositiveMoments.actualMoment (wave W) i j =
      moment W (squareIndex i) (squareIndex j) := by
  unfold MainTheory.Orbit3PositiveMoments.actualMoment moment cubicMoment
  rw [realGram_apply, realGram_apply]
  simp_rw [square_feature]

end
end MainTheory.Orbit3CubicBasis
