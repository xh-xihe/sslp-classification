import MainTheory.Orbit8RotationSemantics
import MainTheory.Orbit8FamilyDisplays
import MainTheory.PairPauliTrace
import MainTheory.PairPauliReconstruction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit8PairDensity

open SixQubit.Orbit8Family SS.MacWilliams
open MainTheory.PairPartialTrace MainTheory.PairPauliSupport MainTheory.PairPauliPurity
open SixQubit.Orbit7DirectMarginal

noncomputable def traceValue (C S : ℝ) (p q : Fin 4) : ℂ :=
  if p=0 ∧ q=0 then 1 else
  if p=3 ∧ q=0 then -(S : ℂ)^2 else
  if p=0 ∧ q=3 then -(C : ℂ)^2 else
  if (p=1 ∧ q=1) ∨ (p=2 ∧ q=2) then -(C : ℂ)*S else 0

theorem identity_action (f : SS.State 6 ℂ) : SS.pauliAct PId f=f := by
  funext x
  simp [SS.pauliAct,PId,SixQubit.Orbit8Family.z0,SS.PauliString.numY,SS.bdot,SS.signC]
  change f (SS.bxor x (fun _ => false))=f x
  rw [SS.bxor_zero]

theorem identity_trace (C S : ℝ) (hCS : C^2+S^2=1) : trProj (code C S) PId=2 := by
  simp only [trProj,code,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,identity_action]
  rw [w0_normalized C S hCS,w1_normalized C S hCS]
  norm_num

theorem actual_traces (C S : ℝ) (hCS : C^2+S^2=1) (p q : Fin 4) :
    (1/2 : ℂ)*trProj (code C S) (pairString 3 p q)=traceValue C S p q := by
  have h00 : pairString 3 0 0=PId := by
    apply MainTheory.PauliWordBridge.pauliWordEquiv.injective
    funext i; fin_cases i <;> rfl
  have h30 : pairString 3 3 0=PZ0 := by
    apply MainTheory.PauliWordBridge.pauliWordEquiv.injective
    funext i; fin_cases i <;> rfl
  have h03 : pairString 3 0 3=PZ4 := by
    apply MainTheory.PauliWordBridge.pauliWordEquiv.injective
    funext i; fin_cases i <;> rfl
  have h11 : pairString 3 1 1=PXX := by
    apply MainTheory.PauliWordBridge.pauliWordEquiv.injective
    funext i; fin_cases i <;> rfl
  have h22 : pairString 3 2 2=PYY := by
    apply MainTheory.PauliWordBridge.pauliWordEquiv.injective
    funext i; fin_cases i <;> rfl
  have hne {p q a b : Fin 4} (hn : (p,q) ≠ (a,b)) :
      pairString 3 p q ≠ pairString 3 a b := fun h => hn (pair_injective 3 h)
  have hI : (1/2 : ℂ)*trProj (code C S) (pairString 3 0 0)=1 := by
    rw [h00,identity_trace C S hCS]; norm_num
  have hZ0 : (1/2 : ℂ)*trProj (code C S) (pairString 3 3 0)= -(S : ℂ)^2 := by
    rw [h30,trProj_Z0 C S hCS]; push_cast; ring
  have hZ4 : (1/2 : ℂ)*trProj (code C S) (pairString 3 0 3)= -(C : ℂ)^2 := by
    rw [h03,trProj_Z4 C S hCS]; push_cast; ring
  have hXX : (1/2 : ℂ)*trProj (code C S) (pairString 3 1 1)= -(C : ℂ)*S := by
    rw [h11,trProj_XX]; push_cast; ring
  have hYY : (1/2 : ℂ)*trProj (code C S) (pairString 3 2 2)= -(C : ℂ)*S := by
    rw [h22,trProj_YY]; push_cast; ring
  have hzero (a b : Fin 4)
      (hi : (a,b) ≠ (0,0)) (hz0 : (a,b) ≠ (3,0)) (hz4 : (a,b) ≠ (0,3))
      (hxx : (a,b) ≠ (1,1)) (hyy : (a,b) ≠ (2,2)) :
      (1/2 : ℂ)*trProj (code C S) (pairString 3 a b)=0 := by
    have hw : (pairString 3 a b).wt ≤ 2 := by
      revert a b
      decide +kernel
    rw [trProj_sparse C S hCS _ hw
      (by rw [← h00]; exact hne hi) (by rw [← h30]; exact hne hz0)
      (by rw [← h03]; exact hne hz4) (by rw [← h11]; exact hne hxx)
      (by rw [← h22]; exact hne hyy),mul_zero]
  fin_cases p <;> fin_cases q
  · exact hI
  · exact hzero 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hzero 0 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hZ4
  · exact hzero 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hXX
  · exact hzero 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hzero 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hzero 2 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hzero 2 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hYY
  · exact hzero 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hZ0
  · exact hzero 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hzero 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hzero 3 3 (by decide) (by decide) (by decide) (by decide) (by decide)

noncomputable def density (C S : ℝ) : Matrix Pair Pair ℂ := fun p q =>
  ((1/2 : ℂ) • MainTheory.Orbit8ExcitationRotation.outer
    (MainTheory.Orbit8ExcitationRotation.ket 1 1)+
    (1/2 : ℂ) • MainTheory.Orbit8ExcitationRotation.outer
    (MainTheory.Orbit8ExcitationRotation.psi C S)) (p.2,p.1) (q.2,q.1)

theorem density_traces (C S : ℝ) (hCS : C^2+S^2=1) (p q : Fin 4) :
    (pairPauli p q*density C S).trace=traceValue C S p q := by
  have h : (C : ℂ)^2+(S : ℂ)^2=1 := by exact_mod_cast hCS
  fin_cases p <;> fin_cases q <;>
    simp [density,MainTheory.Orbit8ExcitationRotation.outer,
      MainTheory.Orbit8ExcitationRotation.ket,MainTheory.Orbit8ExcitationRotation.psi,
      pairPauli,MainTheory.PauliTransferTwo.pauli,traceValue,Matrix.trace,
      Matrix.diag_apply,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two] <;>
    (first | ring1 | linear_combination h/2 | linear_combination -h/2)

theorem actual_pair_density (C S : ℝ) (hCS : C^2+S^2=1) :
    directPairMarginal (code C S) 3=density C S := by
  apply MainTheory.PairPauliReconstruction.ext_traces
  intro p q
  rw [MainTheory.PairPauliTrace.local_global_trace,
    MainTheory.PauliFamilyTrace.trace_family,actual_traces C S hCS,
    density_traces C S hCS]

end MainTheory.Orbit8PairDensity
