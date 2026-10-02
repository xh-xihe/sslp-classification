import MainTheory.AncillaGatePadding
import MainTheory.TransversalDiagonalization
import MainTheory.DiagonalLogicalMatrixBridge
import MainTheory.UnitaryAdjointRepresentation
import MainTheory.OrderFiveEnumerator
import MainTheory.WImageIntrinsicBridge

/-!
# Minimum length for a transversal logical gate of projective order five

The hypotheses use arbitrary literal tensor products of one-qubit unitary
matrices, their action on an exact rank-two code, and the order of the faithful
adjoint representation of the logical unitary. Thus no physical finite order,
preselected diagonal basis, padding certificate or intrinsic-group witness is
assumed. The proof uses the six-qubit classification after actual KL-preserving
padding and local diagonalization.
-/

namespace MainTheory.MinimumLengthOrderFive

open CodeSpec ClassificationLevels LocalTensorKernel PauliKernelBTrace
open AncillaPadding AncillaGatePadding UnitaryAdjointRepresentation

noncomputable section

set_option maxHeartbeats 1000000

variable {n d : ℕ}

theorem scalar_fifth_power (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : orderOf (adjoint Q) = 5) :
    (∃ c : ℂ, c ≠ 0 ∧ Q.val ^ 5 = c • 1) ∧ ¬ ∃ c : ℂ, Q.val = c • 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hpow, hne⟩ := orderOf_eq_prime_iff.mp hQ
  obtain ⟨c, hc⟩ := (adjoint_pow_eq_one_iff Q 5).1 hpow
  have hc0 : c ≠ 0 := by
    intro hz
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (Q ^ 5).property.1
    simp [hc, hz] at hh
  exact ⟨⟨c, hc0, hc⟩, fun h => hne ((adjoint_eq_one_iff Q).2 h)⟩

theorem scalar_fifth_power_smul (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : orderOf (adjoint Q) = 5) (a : unitary ℂ) :
    (∃ c : ℂ, c ≠ 0 ∧ ((a : ℂ) • Q.val) ^ 5 = c • 1) ∧
      ¬ ∃ c : ℂ, (a : ℂ) • Q.val = c • 1 := by
  obtain ⟨⟨c, hc, hpow⟩, hnot⟩ := scalar_fifth_power Q hQ
  have ha : (a : ℂ) ≠ 0 := by
    intro hz
    have hh := a.property.1
    simp [hz] at hh
  constructor
  · refine ⟨(a : ℂ) ^ 5 * c, mul_ne_zero (pow_ne_zero _ ha) hc, ?_⟩
    rw [smul_pow, hpow, smul_smul]
  · rintro ⟨b, hb⟩
    apply hnot
    refine ⟨(a : ℂ)⁻¹ * b, ?_⟩
    have hh := congrArg (fun M => (a : ℂ)⁻¹ • M) hb
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hh

/-- The six-qubit uniqueness statement applies to arbitrary transversal U(2) gates. -/
theorem six_qubit_lu_unique (C : ExactCode 6 2 3)
    (U : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q.val)
    (horder : orderOf (adjoint Q) = 5) :
    LUEquivalent (CodeProjector.ofFrame C.frame)
      (CodeProjector.ofFrame Orbit36LUBridge.canonicalFrame) := by
  obtain ⟨C', u, c, hlu, hinter⟩ :=
    TransversalDiagonalization.exists_diagonal_normal_form C U hU Q.val hQ
  have hp := scalar_fifth_power_smul Q horder c
  obtain ⟨g, hg⟩ := DiagonalLogicalMatrixBridge.exists_intrinsic_order_five
    C' u ((c : ℂ) • Q.val) hinter hp.1 hp.2
  exact Relation.EqvGen.trans _ _ _ hlu
    (OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive C' g hg)

theorem six_qubit_AWeight_one_zero (C : ExactCode 6 2 3)
    (U : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q.val)
    (horder : orderOf (adjoint Q) = 5) : AWeight C.frame 1 = 0 := by
  have hlu := six_qubit_lu_unique C U hU Q hQ horder
  have heq := LocalUnitaryEnumerators.AWeight_luEquivalent
    C.frame Orbit36LUBridge.canonicalFrame hlu 1
  rw [← heq]
  have h := OrderFiveEnumerator.canonical_enumerator 1
  simpa [AWeight, WImages.R5A] using h

theorem AWeight_one_zero_of_length_six (hn : n = 6) (C : ExactCode n 2 3)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q.val)
    (horder : orderOf (adjoint Q) = 5) : AWeight C.frame 1 = 0 := by
  subst n
  exact six_qubit_AWeight_one_zero C U hU Q hQ horder

/-- **20260924 minimum-length corollary: every such code has at least six qubits.** -/
theorem minimum_length (C : ExactCode n 2 d) (hd : 3 ≤ d)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q.val)
    (horder : orderOf (adjoint Q) = 5) : 6 ≤ n := by
  by_contra hshort
  have hn : n < 6 := by omega
  let C3 : ExactCode n 2 3 := {
    positiveRank := C.positiveRank
    frame := C.frame
    hasDistance := fun P hP => C.hasDistance P (by omega) }
  have hpad := intertwining_padFrame C3.frame U Q.val hQ (6 - n)
  have hunit := padLocal_unitary U hU (6 - n)
  have hpos := AWeight_padFrame_one_pos C3.frame C3.positiveRank (by omega : 0 < 6 - n)
  let Cp := padCode C3 (6 - n)
  have hzero : AWeight Cp.frame 1 = 0 :=
    AWeight_one_zero_of_length_six (by omega) Cp _ hunit Q hpad horder
  change 0 < AWeight Cp.frame 1 at hpos
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- Uniqueness retains the manuscript's original distance-at-least-three scope. -/
theorem six_qubit_lu_unique_of_distance_ge_three (C : ExactCode 6 2 d) (hd : 3 ≤ d)
    (U : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q.val)
    (horder : orderOf (adjoint Q) = 5) :
    LUEquivalent (CodeProjector.ofFrame C.frame)
      (CodeProjector.ofFrame Orbit36LUBridge.canonicalFrame) := by
  let C3 : ExactCode 6 2 3 := {
    positiveRank := C.positiveRank
    frame := C.frame
    hasDistance := fun P hP => C.hasDistance P (by omega) }
  exact six_qubit_lu_unique C3 U hU Q hQ horder

def canonicalCode : ExactCode 6 2 3 where
  positiveRank := by decide
  frame := Orbit36LUBridge.canonicalFrame
  hasDistance := SixQubit.Orbit36Code.canonical_is_code

/-- The specific canonical states attain six in the same arbitrary-transversal interface. -/
theorem canonical_attains :
    ∃ U : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ, ∃ Q : Matrix.unitaryGroup (Fin 2) ℂ,
      (∀ j, IsOneQubitUnitary (U j)) ∧
      tensorKernel U * frameMatrix canonicalCode.frame = frameMatrix canonicalCode.frame * Q.val ∧
      orderOf (adjoint Q) = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let G := WImageIntrinsicBridge.finiteGeneratorOfSupportedPair
    WImageIntrinsicBridge.rootFive WImageIntrinsicBridge.rootFive_primitive
    SixQubit.Orbit36Code.av WImageIntrinsicBridge.orbit36_angle_primitive
    0 4 SixQubit.Orbit36Code.c36 SixQubit.Orbit36Code.d36
    WImageIntrinsicBridge.orbit36_c36_support WImageIntrinsicBridge.orbit36_d36_support
    SixQubit.Orbit36Code.c36_normalized SixQubit.Orbit36Code.d36_normalized
    SixQubit.Orbit36Code.canonical_is_code WImageIntrinsicBridge.rootFive_zero_four_distinct
  let u := GlobalClassificationBridge.finiteLocalPhase G.zeta G.primitiveRoot G.angle
  let M := Matrix.diagonal G.eigenvalue
  have hmat : diagonalKernel u * frameMatrix canonicalCode.frame =
      frameMatrix canonicalCode.frame * M := by
    ext x k
    rw [Matrix.mul_diagonal]
    have hh := congrFun (G.diagonalEigen k) x
    simpa [diagonalAction, Matrix.mul_apply, diagonalKernel, frameMatrix, mul_comm]
      using hh
  have hp : M ^ 5 = 1 := by
    have hh := DiagonalLogicalOrder.intertwining_pow canonicalCode.frame u M hmat 5
    have hu : u ^ 5 = 1 := GlobalClassificationBridge.finiteLocalPhase_pow_order
      G.zeta G.primitiveRoot G.angle
    rw [hu, DiagonalLogicalOrder.diagonalKernel_one, Matrix.one_mul] at hh
    have h := congrArg (fun A => (frameMatrix canonicalCode.frame).conjTranspose * A) hh
    dsimp only at h
    rw [← Matrix.mul_assoc, KLCodeBridge.frameMatrix_gram, Matrix.one_mul] at h
    exact h.symm
  have hnonscalar : ¬ ∃ c : ℂ, M = c • 1 := by
    rintro ⟨c, hc⟩
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp only [M, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at h0 h1
    exact G.projectively_nontrivial (h0.trans h1.symm)
  let Q : Matrix.unitaryGroup (Fin 2) ℂ :=
    ⟨M, DiagonalLogicalMatrixBridge.logicalMatrix_unitary canonicalCode.frame u M hmat⟩
  refine ⟨DiagonalLocalKernel.localMatrix u, Q, DiagonalLocalKernel.local_unitary u, ?_, ?_⟩
  · rw [DiagonalLocalKernel.tensor_diagonal]
    exact hmat
  · apply orderOf_eq_prime
    · apply (adjoint_pow_eq_one_iff Q 5).2
      exact ⟨1, by simpa only [one_smul] using hp⟩
    · intro h
      exact hnonscalar ((adjoint_eq_one_iff Q).1 h)

end

end MainTheory.MinimumLengthOrderFive
