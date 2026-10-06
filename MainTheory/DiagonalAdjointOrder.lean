import MainTheory.DiagonalLogicalMatrixBridge
import MainTheory.UnitaryAdjointRepresentation

/-! The intrinsic diagonal quotient has the projective order of its actual
logical matrix, including arbitrary global unit scalars. -/

namespace MainTheory.DiagonalAdjointOrder

open CodeSpec ClassificationLevels GlobalClassificationBridge PauliKernelBTrace
open DiagonalLogicalOrder DiagonalLogicalMatrixBridge UnitaryAdjointRepresentation

noncomputable section

variable {n K d : ℕ}

theorem intrinsic_order (C : ExactCode n K d) (hK : 0 < K)
    (v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame))
    (Q : Matrix.unitaryGroup (Fin K) ℂ)
    (hQ : diagonalKernel v.val * frameMatrix C.frame = frameMatrix C.frame * Q.val) :
    orderOf (intrinsicClass (CodeProjector.ofFrame C.frame) v) = orderOf (adjoint Q) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro m
  have hp : diagonalKernel (v ^ m).val * frameMatrix C.frame =
      frameMatrix C.frame * Q.val ^ m := by
    simpa only [Subgroup.coe_pow] using intertwining_pow C.frame v.val Q.val hQ m
  have ht : intrinsicClass (CodeProjector.ofFrame C.frame) (v ^ m) =
      intrinsicClass (CodeProjector.ofFrame C.frame) v ^ m :=
    (QuotientGroup.mk' _).map_pow v m
  rw [← ht, intrinsicClass_eq_one_iff,
    projectivelyTrivial_iff_scalar C.frame (v ^ m) (Q.val ^ m) hp,
    adjoint_pow_eq_one_iff]
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc⟩
    intro hz
    have hh := congrArg (fun M : Matrix (Fin K) (Fin K) ℂ =>
      M ⟨0, hK⟩ ⟨0, hK⟩) (Q ^ m).property.1
    simp [hc, hz] at hh

theorem scalar_order (Q R : Matrix.unitaryGroup (Fin K) ℂ)
    (a : ℂ) (hR : R.val = a • Q.val) :
    orderOf (adjoint R) = orderOf (adjoint Q) := by
  have he : adjoint R = adjoint Q := (adjoint_eq_iff R Q).2 ⟨a, hR⟩
  rw [he]

theorem normalized_intrinsic_order (C : ExactCode n K d) (hK : 0 < K)
    (u : LocalPhase n) (Q : Matrix.unitaryGroup (Fin K) ℂ) (a : unitary ℂ)
    (hQ : diagonalKernel u * frameMatrix C.frame =
      frameMatrix C.frame * ((a : ℂ) • Q.val)) :
    ∃ g : IntrinsicGroup C, orderOf g = orderOf (adjoint Q) := by
  let R : Matrix.unitaryGroup (Fin K) ℂ :=
    ⟨(a : ℂ) • Q.val, logicalMatrix_unitary C.frame u _ hQ⟩
  let v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame) :=
    ⟨u, symmetry_of_intertwining C.frame u R.val R.property.2 hQ⟩
  refine ⟨intrinsicClass (CodeProjector.ofFrame C.frame) v, ?_⟩
  calc
    _ = orderOf (adjoint R) := intrinsic_order C hK v R hQ
    _ = orderOf (adjoint Q) := scalar_order Q R (a : ℂ) rfl

end

end MainTheory.DiagonalAdjointOrder
