import MainTheory.PairPartialTrace

set_option autoImplicit false

namespace MainTheory.Orbit8ExcitationRotation

open MainTheory.PairPartialTrace

noncomputable def rotation (C S : ℝ) : Matrix Pair Pair ℂ := fun p q =>
  if p=(0,0) then if q=(0,0) then 1 else 0 else
  if p=(0,1) then if q=(0,1) then (C : ℂ) else if q=(1,0) then -(S : ℂ) else 0 else
  if p=(1,0) then if q=(0,1) then (S : ℂ) else if q=(1,0) then (C : ℂ) else 0 else
  if q=(1,1) then 1 else 0

noncomputable def ket (a b : Fin 2) : Pair → ℂ := fun p => if p=(a,b) then 1 else 0

theorem act_ket (C S : ℝ) (a b : Fin 2) :
    (rotation C S).mulVec (ket a b)=fun p => rotation C S p (a,b) := by
  funext p
  simp [Matrix.mulVec,dotProduct,ket]

theorem basis_actions (C S : ℝ) :
    (rotation C S).mulVec (ket 0 0)=ket 0 0 ∧
    (rotation C S).mulVec (ket 1 1)=ket 1 1 ∧
    (rotation C S).mulVec (ket 0 1)=(C : ℂ) • ket 0 1+(S : ℂ) • ket 1 0 ∧
    (rotation C S).mulVec (ket 1 0)=-(S : ℂ) • ket 0 1+(C : ℂ) • ket 1 0 := by
  simp only [act_ket]
  refine ⟨?_,?_,?_,?_⟩ <;>
    (funext p; rcases p with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> simp [rotation,ket])

theorem unitary (C S : ℝ) (hCS : C^2+S^2=1) :
    (rotation C S).conjTranspose*rotation C S=1 := by
  have h : (C : ℂ)^2+(S : ℂ)^2=1 := by exact_mod_cast hCS
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [rotation,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two] <;> (first | ring1 | linear_combination h)

theorem commutes_diagonal (C S : ℝ) (z : Fin 2 → ℂ) :
    rotation C S*Matrix.diagonal (fun p : Pair => z p.1*z p.2)=
      Matrix.diagonal (fun p : Pair => z p.1*z p.2)*rotation C S := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [rotation,Matrix.mul_diagonal,Matrix.diagonal_mul] <;> ring

noncomputable def outer (f : Pair → ℂ) : Matrix Pair Pair ℂ := fun p q => f p*star (f q)
noncomputable def initialDensity : Matrix Pair Pair ℂ :=
  Matrix.diagonal (fun p => if p.1=1 then 1/2 else 0)
noncomputable def psi (C S : ℝ) : Pair → ℂ := (C : ℂ) • ket 1 0-(S : ℂ) • ket 0 1

theorem rotated_density (C S : ℝ) :
    rotation C S*initialDensity*(rotation C S).conjTranspose=
      (1/2 : ℂ) • outer (ket 1 1)+(1/2 : ℂ) • outer (psi C S) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [rotation,initialDensity,outer,psi,ket,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fintype.sum_prod_type,Fin.sum_univ_two] <;> ring

end MainTheory.Orbit8ExcitationRotation
