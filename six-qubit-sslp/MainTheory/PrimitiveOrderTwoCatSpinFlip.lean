import MainTheory.PrimitiveOrderTwoCatKL

/-! Orthogonality of the actual cat code to its six-qubit spin flip. -/

namespace MainTheory.PrimitiveOrderTwoCatSpinFlip
open MainTheory.PrimitiveOrderTwoCatCompression
open MainTheory.PrimitiveOrderTwoCatEncoder
open Orbit2.TensorPauli
open scoped Matrix Kronecker
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem spin_raw : ∀ j k : Fin 5,rawCompression (![2,2,2,2,2] : Label 5) j k=0 := by
  decide +kernel

theorem tail_spin_zero : cats.conjTranspose*operator (![2,2,2,2,2] : Label 5)*cats=0 := by
  ext j k
  rw [compression,spin_raw]
  norm_num

theorem lift_real : liftCat.map (starRingEnd ℂ)=liftCat := by
  ext ij kl
  change star (((1 : Matrix (Fin 2) (Fin 2) ℂ) ij.1 kl.1) * cats ij.2 kl.2) =
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ij.1 kl.1) * cats ij.2 kl.2
  simp only [star_mul,cats_star,Matrix.one_apply]
  split_ifs <;> simp

def spinY : Matrix PhysicalBasis PhysicalBasis ℂ :=
  localC 2 ⊗ₖ operator (![2,2,2,2,2] : Label 5)

theorem overlap_zero (a b : ℝ) :
    (encoder a b).conjTranspose*spinY*(encoder a b).map (starRingEnd ℂ)=0 := by
  rw [encoder,Matrix.conjTranspose_mul,Matrix.map_mul,lift_real]
  calc
    _ = (spinors a b).conjTranspose*(liftCat.conjTranspose*spinY*liftCat)*
        (spinors a b).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
    _ = 0 := by
      rw [spinY,lift_compression,tail_spin_zero,Matrix.kronecker_zero,
        Matrix.mul_zero,Matrix.zero_mul]

def projector (a b : ℝ) := encoder a b*(encoder a b).conjTranspose
def spinProjector (a b : ℝ) := spinY*(projector a b).map (starRingEnd ℂ)*spinY.conjTranspose

theorem projectors_orthogonal (a b : ℝ) : projector a b*spinProjector a b=0 := by
  rw [projector,spinProjector,projector,Matrix.map_mul]
  calc
    _ = encoder a b*((encoder a b).conjTranspose*spinY*
        (encoder a b).map (starRingEnd ℂ))*
        ((encoder a b).conjTranspose).map (starRingEnd ℂ)*spinY.conjTranspose := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [overlap_zero,Matrix.mul_zero,Matrix.zero_mul,Matrix.zero_mul]

theorem spin_trace_zero (a b : ℝ) : Matrix.trace (projector a b*spinProjector a b)=0 := by
  rw [projectors_orthogonal,Matrix.trace_zero]

end
end MainTheory.PrimitiveOrderTwoCatSpinFlip
