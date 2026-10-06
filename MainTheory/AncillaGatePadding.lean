import MainTheory.AncillaPadding
import MainTheory.PauliKernelBTrace

/-! # Identity extension preserves the very same logical gate matrix -/

namespace MainTheory.AncillaGatePadding

open scoped BigOperators
open AncillaPadding TensorAppendZero LocalTensorKernel ClassificationLevels
open PauliKernelBTrace CodeSpec

noncomputable section

variable {n K : ℕ}

/-- Matrix entries of the actual projector P ⊗ |0⟩⟨0|, not an abstract isometry. -/
theorem projector_appendFrame (F : OrthonormalFrame n K) (x y : SS.BitString n)
    (a b : Bool) :
    (CodeProjector.ofFrame (appendFrame F)).kernel (Fin.snoc x a) (Fin.snoc y b) =
      (CodeProjector.ofFrame F).kernel x y * (if a = false ∧ b = false then 1 else 0) := by
  cases a <;> cases b <;>
    simp [CodeProjector.ofFrame, projectorKernel, appendFrame, appendZero]

theorem snoc_eq_zero_iff {m : ℕ} (y : SS.BitString m) (b : Bool) :
    Fin.snoc y b = (fun _ => false) ↔ y = (fun _ => false) ∧ b = false := by
  constructor
  · intro h
    constructor
    · funext i
      simpa using congrFun h i.castSucc
    · simpa using congrFun h (Fin.last m)
  · rintro ⟨rfl, rfl⟩
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem padFrame_vec_append (F : OrthonormalFrame n K) (m : ℕ) (k : Fin K)
    (x : SS.BitString n) (y : SS.BitString m) :
    (padFrame F m).vec k (Fin.append x y) = if y = (fun _ => false) then F.vec k x else 0 := by
  induction m with
  | zero =>
    have hz : y = (fun _ => false) := Subsingleton.elim _ _
    simp [hz, padFrame, Fin.append_right_nil]
  | succ m ih =>
    rw [← Fin.snoc_init_self y, Fin.append_snoc]
    change appendZero ((padFrame F m).vec k) (Fin.snoc _ _) = _
    simp only [appendZero, Fin.snoc_last, Fin.init_snoc, ih, snoc_eq_zero_iff]
    cases y (Fin.last m) <;> simp

/-- Literal matrix entries of P tensored with m copies of |0⟩⟨0|. -/
theorem projector_padFrame (F : OrthonormalFrame n K) (m : ℕ)
    (x x' : SS.BitString n) (y y' : SS.BitString m) :
    (CodeProjector.ofFrame (padFrame F m)).kernel (Fin.append x y) (Fin.append x' y') =
      (CodeProjector.ofFrame F).kernel x x' *
        (if y = (fun _ => false) ∧ y' = (fun _ => false) then 1 else 0) := by
  simp only [CodeProjector.ofFrame, projectorKernel, padFrame_vec_append]
  by_cases hy : y = (fun _ => false) <;> by_cases hy' : y' = (fun _ => false) <;>
    simp [hy, hy']

theorem action_appendZero (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (f : SS.State n ℂ) :
    (tensorKernel (Fin.snoc U 1)).mulVec (appendZero f) =
      appendZero ((tensorKernel U).mulVec f) := by
  funext y
  rw [← Fin.snoc_init_self y]
  generalize Fin.init y = x
  generalize y (Fin.last n) = b
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_snoc]
  cases b <;> simp [tensor_snoc, appendZero, bitIndex, Matrix.mulVec, dotProduct]

theorem intertwining_appendFrame (F : OrthonormalFrame n K)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (Q : Matrix (Fin K) (Fin K) ℂ)
    (h : tensorKernel U * frameMatrix F = frameMatrix F * Q) :
    tensorKernel (Fin.snoc U 1) * frameMatrix (appendFrame F) =
      frameMatrix (appendFrame F) * Q := by
  ext x k
  have hh := congrArg (fun M => fun y => M y k) h
  change (tensorKernel U).mulVec (F.vec k) =
    (fun y => ∑ j, F.vec j y * Q j k) at hh
  change ((tensorKernel (Fin.snoc U 1)).mulVec (appendZero (F.vec k))) x = _
  rw [action_appendZero, hh]
  simp only [appendZero, Matrix.mul_apply, frameMatrix, appendFrame]
  cases x (Fin.last n) <;> simp

def padLocal (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (m : ℕ) → Fin (n + m) → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => U
  | m + 1 => Fin.snoc (padLocal U m) 1

theorem padLocal_unitary (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j, IsOneQubitUnitary (U j)) (m : ℕ) :
    ∀ j, IsOneQubitUnitary (padLocal U m j) := by
  induction m with
  | zero => exact hU
  | succ m ih =>
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [padLocal, IsOneQubitUnitary]
    · simpa only [padLocal, Fin.snoc_castSucc] using ih i

/-- Equality of logical matrices also preserves every projective logical order. -/
theorem intertwining_padFrame (F : OrthonormalFrame n K)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (Q : Matrix (Fin K) (Fin K) ℂ)
    (h : tensorKernel U * frameMatrix F = frameMatrix F * Q) (m : ℕ) :
    tensorKernel (padLocal U m) * frameMatrix (padFrame F m) =
      frameMatrix (padFrame F m) * Q := by
  induction m with
  | zero => exact h
  | succ m ih => exact intertwining_appendFrame (padFrame F m) (padLocal U m) Q ih

end

end MainTheory.AncillaGatePadding
