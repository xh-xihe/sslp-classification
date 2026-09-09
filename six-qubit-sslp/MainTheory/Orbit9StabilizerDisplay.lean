import MainTheory.Orbit9DiagonalGauge
import MainTheory.PauliKernelTrace
import SixQubit.Orbit9EqualPairBridge

set_option autoImplicit false

namespace MainTheory.Orbit9StabilizerDisplay

open SixQubit.Orbit9Universal MainTheory.CodeSpec MainTheory.PauliKernelTrace

noncomputable def projector {n K : ℕ} (F : OrthonormalFrame n K) :
    Matrix (SS.BitString n) (SS.BitString n) ℂ := projectorKernel F

theorem fixed_projector {n K : ℕ} (F : OrthonormalFrame n K) (P : SS.PauliString n)
    (hP : ∀ i,SS.pauliAct P (F.vec i)=F.vec i) :
    pauliKernel P*projector F=projector F := by
  classical
  ext x y
  simp only [Matrix.mul_apply,projector,projectorKernel,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have h := congrFun (kernelAction_pauliKernel P (F.vec i)) x
  rw [hP i] at h
  change (∑ z,pauliKernel P x z*F.vec i z)=F.vec i x at h
  rw [h]

def zz (r s : Fin 6) : SS.PauliString 6 :=
  ⟨fun _ => false,SS.bxor (SS.stdBasis r) (SS.stdBasis s)⟩

theorem stabilizer (c d : SS.State 6 ℂ) (H : FullKL c d)
    (r s : Fin 6) (hc : EqualBitsSupport c r s) (hd : EqualBitsSupport d r s) :
    pauliKernel (zz r s)*projector (MainTheory.Orbit9DiagonalGauge.frame c d H)=
      projector (MainTheory.Orbit9DiagonalGauge.frame c d H) := by
  apply fixed_projector
  intro i
  fin_cases i
  · exact zpair_fixes_of_equalBits c r s hc
  · exact zpair_fixes_of_equalBits d r s hd

theorem exists_stabilizer (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hfour : (ActiveSet c).card=4) :
    ∃ r s, (zz r s).wt=2 ∧
      pauliKernel (zz r s)*projector (MainTheory.Orbit9DiagonalGauge.frame c d H)=
        projector (MainTheory.Orbit9DiagonalGauge.frame c d H) := by
  obtain ⟨r,s,hrs,hc,hd⟩ := exists_equalBits_pair_of_card_four c d H hfour
  exact ⟨r,s,zpair_wt r s hrs,stabilizer c d H r s hc hd⟩

theorem A2_lower (c d : SS.State 6 ℂ) (H : FullKL c d)
    (r s : Fin 6) (hrs : r ≠ s)
    (hc : EqualBitsSupport c r s) (hd : EqualBitsSupport d r s) :
    1 ≤ SS.MacWilliams.Aco ![c,d] 2/4 := by
  have h := SixQubit.Pin.four_le_Aco ![c,d] (zz r s)
    (by intro i; fin_cases i
        · exact zpair_fixes_of_equalBits c r s hc
        · exact zpair_fixes_of_equalBits d r s hd)
    (by intro i; fin_cases i; exact H.norm0; exact H.norm1)
  rw [show (zz r s).wt=2 from zpair_wt r s hrs] at h
  linarith

end MainTheory.Orbit9StabilizerDisplay
