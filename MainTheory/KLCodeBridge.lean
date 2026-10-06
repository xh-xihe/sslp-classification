import MainTheory.KLNecessity
import MainTheory.KLTensorSupport

/-! # Frame, projector, and low-weight error formulations of KL

The projector equations are equivalent to scalar compression by the actual
orthonormal frame. Genuine distance detects every pair product from the
linear span of sufficiently small Pauli errors.
-/

namespace MainTheory.KLCodeBridge

open CodeSpec PauliKernelBTrace PauliKernelTrace ClassificationLevels
open KLTensorSupport PauliTensorTransfer PauliWordBridge PauliTransferTwo LocalTensorKernel
open scoped Matrix

noncomputable section

set_option maxHeartbeats 1000000

variable {n K d t : ℕ}

theorem frameMatrix_gram (F : OrthonormalFrame n K) :
    (frameMatrix F).conjTranspose * frameMatrix F = 1 := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, frameMatrix, SS.innerC,
    Matrix.one_apply] using F.orthonormal i j

theorem projector_compression_iff (F : OrthonormalFrame n K)
    (M : OperatorKernel n) (c : ℂ) :
    (CodeProjector.ofFrame F).kernel * M * (CodeProjector.ofFrame F).kernel =
        c • (CodeProjector.ofFrame F).kernel ↔
      (frameMatrix F).conjTranspose * M * frameMatrix F = c • 1 := by
  have hP : (CodeProjector.ofFrame F).kernel =
      frameMatrix F * (frameMatrix F).conjTranspose :=
    projector_eq_frame_mul_conjTranspose F
  have hV := frameMatrix_gram F
  rw [hP]
  constructor
  · intro h
    have hc := congrArg (fun A => (frameMatrix F).conjTranspose * A * frameMatrix F) h
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hV,
      Matrix.one_mul] at hc
    simpa only [Matrix.mul_assoc, hV, Matrix.mul_one, Matrix.one_mul] using hc
  · intro h
    calc
      _ = frameMatrix F * ((frameMatrix F).conjTranspose * M * frameMatrix F) *
          (frameMatrix F).conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The paper's literal projector form of the Knill--Laflamme equations. -/
def ProjectorKnillLaflamme {I : Type*} (F : OrthonormalFrame n K)
    (E : I → OperatorKernel n) : Prop :=
  ∃ c : Matrix I I ℂ, ∀ i j,
    (CodeProjector.ofFrame F).kernel * (E i).conjTranspose * E j *
      (CodeProjector.ofFrame F).kernel = c i j • (CodeProjector.ofFrame F).kernel

theorem projectorKnillLaflamme_iff {I : Type*} [Fintype I]
    (F : OrthonormalFrame n K) (E : I → OperatorKernel n) :
    ProjectorKnillLaflamme F E ↔ FiniteKrausChannel.KnillLaflamme (frameMatrix F) E := by
  simp only [ProjectorKnillLaflamme, FiniteKrausChannel.KnillLaflamme]
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, fun i j => ?_⟩
  · simpa only [Matrix.mul_assoc] using
      (projector_compression_iff F ((E i).conjTranspose * E j) (c i j)).1
      (by simpa only [Matrix.mul_assoc] using hc i j)
  · simpa only [Matrix.mul_assoc] using
      (projector_compression_iff F ((E i).conjTranspose * E j) (c i j)).2
        (by simpa only [Matrix.mul_assoc] using hc i j)

theorem pauli_product_mem_detectedOperators (C : ExactCode n K d)
    (P Q : SS.PauliString n) (hP : P.wt ≤ t) (hQ : Q.wt ≤ t) (ht : 2 * t < d) :
    (pauliKernel P).conjTranspose * pauliKernel Q ∈ detectedOperators C.frame := by
  classical
  let p := pauliWordEquiv P
  let q := pauliWordEquiv Q
  let s : Finset (Fin n) := Finset.univ.filter (fun j => p j ≠ 0)
  let u : Finset (Fin n) := Finset.univ.filter (fun j => q j ≠ 0)
  have hs : s.card ≤ t := by
    change wordWeight p ≤ t
    simpa only [p, wordWeight_pauliWordEquiv] using hP
  have hu : u.card ≤ t := by
    change wordWeight q ≤ t
    simpa only [q, wordWeight_pauliWordEquiv] using hQ
  have hsu : (s ∪ u).card < d := by
    have := Finset.card_union_le s u
    omega
  rw [← wordKernel_pauliWordEquiv P, ← wordKernel_pauliWordEquiv Q]
  change star (tensorKernel (fun j => pauli (p j))) *
    tensorKernel (fun j => pauli (q j)) ∈ detectedOperators C.frame
  rw [← tensorKernel_star, ← tensorKernel_mul]
  apply tensor_mem_detectedOperators C (s ∪ u) hsu
  intro j hj
  have hp : p j = 0 := by
    by_contra hn
    exact hj (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
  have hq : q j = 0 := by
    by_contra hn
    exact hj (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
  simp [hp, hq, pauli_zero]

/-- Arbitrary finite linear combinations of Paulis of weight at most `t`. -/
def pauliErrorSpace (n t : ℕ) : Submodule ℂ (OperatorKernel n) :=
  Submodule.span ℂ (pauliKernel '' {P : SS.PauliString n | P.wt ≤ t})

theorem error_product_mem_detectedOperators (C : ExactCode n K d) (ht : 2 * t < d)
    (A B : OperatorKernel n) (hA : A ∈ pauliErrorSpace n t) (hB : B ∈ pauliErrorSpace n t) :
    A.conjTranspose * B ∈ detectedOperators C.frame := by
  let D := detectedOperators C.frame
  let right (X : OperatorKernel n) : Submodule ℂ (OperatorKernel n) := {
    carrier := {Y | X.conjTranspose * Y ∈ D}
    zero_mem' := by simp
    add_mem' := by
      intro Y Z hY hZ
      simpa only [Set.mem_setOf_eq, Matrix.mul_add] using D.add_mem hY hZ
    smul_mem' := by
      intro c Y hY
      simpa only [Set.mem_setOf_eq, Matrix.mul_smul] using D.smul_mem c hY }
  have hright (P : SS.PauliString n) (hP : P.wt ≤ t) :
      pauliErrorSpace n t ≤ right (pauliKernel P) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q, hQ, rfl⟩
    exact pauli_product_mem_detectedOperators C P Q hP hQ ht
  let left : Submodule ℂ (OperatorKernel n) := {
    carrier := {X | X.conjTranspose * B ∈ D}
    zero_mem' := by simp
    add_mem' := by
      intro X Y hX hY
      simpa only [Set.mem_setOf_eq, Matrix.conjTranspose_add, Matrix.add_mul] using D.add_mem hX hY
    smul_mem' := by
      intro c X hX
      simpa only [Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.smul_mul] using D.smul_mem (star c) hX }
  have hleft : pauliErrorSpace n t ≤ left := by
    apply Submodule.span_le.mpr
    rintro _ ⟨P, hP, rfl⟩
    exact hright P hP hB
  exact hleft hA

/-- Genuine distance implies KL for every finite error family in the full
linear span of weight-at-most-t Paulis, whenever 2t < d. -/
theorem knillLaflamme_of_error_span {I : Type*} [Fintype I]
    (C : ExactCode n K d) (E : I → OperatorKernel n) (ht : 2 * t < d)
    (hE : ∀ i, E i ∈ pauliErrorSpace n t) :
    FiniteKrausChannel.KnillLaflamme (frameMatrix C.frame) E := by
  have hc (i j : I) : ∃ c : ℂ,
      (frameMatrix C.frame).conjTranspose * ((E i).conjTranspose * E j) *
        frameMatrix C.frame = c • 1 :=
    error_product_mem_detectedOperators C ht (E i) (E j) (hE i) (hE j)
  choose c hc using hc
  exact ⟨c, fun i j => by simpa only [Matrix.mul_assoc] using hc i j⟩

end

end MainTheory.KLCodeBridge
