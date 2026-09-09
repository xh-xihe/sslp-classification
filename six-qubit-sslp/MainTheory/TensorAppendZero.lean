import MainTheory.LocalTensorKernel

set_option autoImplicit false

namespace MainTheory.TensorAppendZero

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel

variable {n : ℕ}

noncomputable def appendZero (f : SS.State n ℂ) : SS.State (n+1) ℂ :=
  fun x => if x (Fin.last n) then 0 else f (Fin.init x)

theorem appendZero_snoc (f : SS.State n ℂ) (x : SS.BitString n) :
    appendZero f (Fin.snoc x false)=f x := by simp [appendZero]

theorem sum_snoc {R : Type*} [AddCommMonoid R] (f : SS.BitString (n+1) → R) :
    (∑ x,f x)=∑ b : Bool,∑ x : SS.BitString n,f (Fin.snoc x b) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  exact Fintype.sum_prod_type _

theorem tensor_snoc (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (V : Matrix (Fin 2) (Fin 2) ℂ) (x y : SS.BitString n) (a b : Bool) :
    tensorKernel (Fin.snoc U V) (Fin.snoc x a) (Fin.snoc y b)=
      tensorKernel U x y*V (bitIndex a) (bitIndex b) := by
  unfold tensorKernel
  rw [Fin.prod_univ_castSucc]
  simp

theorem action_snoc (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (f : SS.State n ℂ)
    (x : SS.BitString n) :
    (tensorKernel (Fin.snoc U 1)).mulVec (appendZero f) (Fin.snoc x false)=
      (tensorKernel U).mulVec f x := by
  simp only [Matrix.mulVec,dotProduct]
  rw [sum_snoc]
  simp [tensor_snoc,appendZero]

theorem not_preserves_append (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (f : Fin 2 → SS.State n ℂ)
    (h : ¬ ∃ a : Fin 2 → ℂ,(tensorKernel U).mulVec (f 0)=fun x => ∑ j,a j*f j x) :
    ¬ ∃ a : Fin 2 → ℂ,(tensorKernel (Fin.snoc U 1)).mulVec (appendZero (f 0))=
      fun x => ∑ j,a j*appendZero (f j) x := by
  rintro ⟨a,ha⟩
  apply h
  refine ⟨a,?_⟩
  ext x
  have hh := congrFun ha (Fin.snoc x false)
  simpa only [action_snoc,appendZero_snoc] using hh

end MainTheory.TensorAppendZero
