import MainTheory.Orbit8SpinProjector

set_option autoImplicit false

namespace MainTheory.SpinMatrixIdentity

open MainTheory.Orbit8SpinProjector SixQubit.Orbit8Universal

noncomputable def conjugate (A : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) :
    Matrix (SS.BitString 6) (SS.BitString 6) ℂ := fun x y => star (A x y)

noncomputable def tensorY : Matrix (SS.BitString 6) (SS.BitString 6) ℂ :=
  MainTheory.LocalTensorKernel.tensorKernel (fun _ : Fin 6 => MainTheory.PauliTransferTwo.pauli 2)

theorem conjugate_action (A : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) (f : SS.State 6 ℂ) :
    (fun x => star (A.mulVec f x))=(conjugate A).mulVec (fun x => star (f x)) := by
  funext x
  simp only [Matrix.mulVec,dotProduct,star_sum,star_mul',conjugate]

theorem spin_star (f : SS.State 6 ℂ) :
    (fun x => star (spinJ f x))=tensorY.mulVec f := by
  have h := MainTheory.Orbit8SpinSemantics.spinJ_tensor (fun x => star (f x))
  funext x
  simpa only [spinJ,star_mul',star_sign,star_star,tensorY] using congrFun h x

theorem spin_matrix (A : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) :
    spinConjugate A=tensorY*conjugate A*tensorY := by
  apply Matrix.ext_iff_mulVec.mpr
  intro f
  rw [← spin_conjugate_action,MainTheory.Orbit8SpinSemantics.spinJ_tensor,
    conjugate_action,spin_star]
  change tensorY.mulVec ((conjugate A).mulVec (tensorY.mulVec f))=_
  simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

end MainTheory.SpinMatrixIdentity
