import MainTheory.QuaternionBoundedGroup
import MainTheory.PauliTransferTwo

/-! Quaternion axes are the literal Pauli normalizer in the actual U(2) spin matrices. -/

namespace MainTheory.QuaternionCliffordMatrixBridge

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionAxisGeometry
  MainTheory.QuaternionCliffordAxes MainTheory.QuaternionSpinMatrices
  MainTheory.UnitaryAdjointRepresentation

def pauli (p : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := PauliTransferTwo.pauli p.succ

def axis (p : Fin 3) : unitary ℍ[ℝ] := ![axisK,axisJ,axisI] p

def IsClifford (U : Matrix.unitaryGroup (Fin 2) ℂ) : Prop :=
  ∀ p : Fin 3,∃ r : Fin 3,
    U.val*pauli p*U.val.conjTranspose=pauli r ∨
    U.val*pauli p*U.val.conjTranspose= -pauli r

theorem spin_axis (p : Fin 3) : spin (axis p).val=Complex.I • pauli p := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [spin,axis,axisI,axisJ,axisK,pauli,PauliTransferTwo.pauli,
      Matrix.smul_apply,Complex.I_mul_I,Fin.succ]

theorem spin_negative (q : ℍ[ℝ]) : spin (-q)= -spin q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spin] <;> ring

theorem spin_conjugate (q a : unitary ℍ[ℝ]) :
    spin (conjugate q a).val=spin q.val*spin a.val*(spin q.val).conjTranspose := by
  rw [conjugate_value,spin_mul,spin_mul,spin_star]

theorem signed_axis (s : unitary ℍ[ℝ]) (h : CoordinateAxis s) :
    ∃ r : Fin 3,s=axis r ∨ s= -axis r := by
  rcases h with h | h | h | h | h | h
  · exact ⟨2,Or.inl h⟩
  · exact ⟨2,Or.inr h⟩
  · exact ⟨1,Or.inl h⟩
  · exact ⟨1,Or.inr h⟩
  · exact ⟨0,Or.inl h⟩
  · exact ⟨0,Or.inr h⟩

theorem normalizer_clifford (q : unitary ℍ[ℝ]) (hq : Normalizes q) :
    IsClifford (unitarySpin q) := by
  intro p
  have hc : CoordinateAxis (conjugate q (axis p)) := by
    fin_cases p
    · exact hq.2.2
    · exact hq.2.1
    · exact hq.1
  obtain ⟨r,hr⟩ := signed_axis _ hc
  have hn : Complex.I≠0 := Complex.I_ne_zero
  refine ⟨r,?_⟩
  rcases hr with hr | hr
  · left
    have he := congrArg (fun s : unitary ℍ[ℝ] => spin s.val) hr
    change spin (conjugate q (axis p)).val=spin (axis r).val at he
    rw [spin_conjugate,spin_axis,spin_axis,Matrix.mul_smul,Matrix.smul_mul] at he
    have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => Complex.I⁻¹ • M) he
    simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hc
  · right
    have he := congrArg (fun s : unitary ℍ[ℝ] => spin s.val) hr
    change spin (conjugate q (axis p)).val=spin (-(axis r).val) at he
    rw [spin_conjugate,spin_negative,spin_axis,spin_axis,Matrix.mul_smul,Matrix.smul_mul,
      ← smul_neg] at he
    have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => Complex.I⁻¹ • M) he
    simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using hc

theorem same_action (U V : Matrix.unitaryGroup (Fin 2) ℂ) (h : adjoint U=adjoint V)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : U.val*A*U.val.conjTranspose=V.val*A*V.val.conjTranspose := by
  have he := congrArg (fun Q : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ =>
    Q.val.mulVec (fun p => A p.1 p.2)) h
  change (adjoint U).val.mulVec (fun p => A p.1 p.2)=
    (adjoint V).val.mulVec (fun p => A p.1 p.2) at he
  rw [adjoint_mulVec,adjoint_mulVec] at he
  ext i j
  exact congrFun he (i,j)

theorem clifford_of_same_adjoint (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (h : adjoint U=adjoint V) (hU : IsClifford U) : IsClifford V := by
  intro p
  obtain ⟨r,hr⟩ := hU p
  refine ⟨r,?_⟩
  rw [← same_action U V h]
  exact hr

end

end MainTheory.QuaternionCliffordMatrixBridge
