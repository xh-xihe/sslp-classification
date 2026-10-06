import MainTheory.IndexedCodeMoments
import MainTheory.RectangularFlipCharacters
import MainTheory.Orbit45PrintedAlgebra
import MainTheory.SupportKetExpansion

/-! Every displayed orbit-45 probability and half-angle row is obtained
from the actual supported code. Character rows evaluated on the top fiber
differ from the printed bottom-fiber rows by a verified nonzero row sign. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PrintedFibers SixQubit.Orbit45Support
open scoped BigOperators Matrix
noncomputable section

def p (c : SS.State 6 ℂ) (i : Fin 10) := Complex.normSq (c (bottom i))
def q (d : SS.State 6 ℂ) (i : Fin 10) := Complex.normSq (d (top i))
def z (c d : SS.State 6 ℂ) (i : Fin 10) := star (c (bottom i))*d (top i)
def flip : SS.BitString 6 := SS.stdBasis 3
def characters : Fin 12 → SS.BitString 6 :=
  fun i => SixQubit.Realize.nbit (Orbit45PrintedWalsh.masks i)
def rowSign (i : Fin 12) : ℤ := if characters i 3 then -1 else 1

theorem codewords (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0) :
    c=(∑ i, c (bottom i) • SupportKetExpansion.ket (bottom i)) ∧
    d=(∑ i, d (top i) • SupportKetExpansion.ket (top i)) :=
  ⟨SupportKetExpansion.indexed_expansion S0 bottom bottom_injective full_fibers.1 c hc,
   SupportKetExpansion.indexed_expansion S1 top top_injective full_fibers.2 d hd⟩

theorem feasible (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    MomentPolytope.Feasible bottom top (IndexedCodeMoments.probabilities bottom top c d) :=
  IndexedCodeMoments.physical_feasible S0 S1 bottom top bottom_injective top_injective
    full_fibers.1 full_fibers.2 c d hc hd hnc hnd hkl

theorem actual_incidence : Finset.univ.image top=S1.filter (fun y => SS.bxor y flip ∈ S0) := by
  decide +kernel
theorem actual_images : ∀ i, SS.bxor (top i) flip=bottom i := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem actual_row_signs : ∀ i j,
    (if SS.bdot (characters i) (top j) then (-1 : ℤ) else 1)=
      rowSign i*Orbit45PrintedWalsh.rows i j := by decide +kernel
theorem row_sign_nonzero : ∀ i, rowSign i ≠ 0 := by decide +kernel
theorem complex_rows (i : Fin 12) (j : Fin 10) :
    RectangularFlipCharacters.matrix characters top i j=
      (rowSign i : ℂ)*Orbit45PrintedWalsh.W i j := by
  have h := congrArg (fun k : ℤ => (k : ℂ)) (actual_row_signs i j)
  unfold RectangularFlipCharacters.matrix FlipCharacter.character Orbit45PrintedWalsh.W
  split_ifs at h ⊢ <;> simpa using h

theorem physical_walsh (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : Orbit45PrintedWalsh.W *ᵥ z c d=0 := by
  have he := RectangularFlipCharacters.physical_rows S0 S1 c d hc hd hkl
    flip characters top top_injective actual_incidence weights
  have hz : (fun j => FlipCharacter.incidenceMonomial c d flip (top j))=z c d := by
    funext j
    rw [FlipCharacter.incidenceMonomial,actual_images]
    rfl
  rw [hz] at he
  ext i
  have hi := congrFun he i
  change (∑ j, RectangularFlipCharacters.matrix characters top i j*z c d j)=0 at hi
  simp_rw [complex_rows,mul_assoc] at hi
  rw [← Finset.mul_sum] at hi
  have hs : (rowSign i : ℂ) ≠ 0 := by exact_mod_cast row_sign_nonzero i
  exact (mul_eq_zero.mp hi).resolve_left hs

theorem physical_normal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    p c=Orbit45PrintedMoments.pattern (p c 3) (p c 1) (p c 0) ∧
    q d=Orbit45PrintedMoments.pattern (p c 3) (p c 1) (p c 0) :=
  Orbit45PrintedMoments.probabilities _ (feasible c d hc hd hnc hnd hkl)

theorem physical_cross_kernel (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    z c d=Orbit45PrintedWalsh.pattern (z c d 3) (z c d 1) (z c d 0) :=
  (Orbit45PrintedWalsh.kernel_iff _).1 (physical_walsh c d hc hd hkl)

theorem physical_reversal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 10) :
    p c i.rev=p c i ∧ z c d i.rev=z c d i := by
  constructor
  · rw [(physical_normal c d hc hd hnc hnd hkl).1]
    exact Orbit45PrintedAlgebra.moment_reversal _ _ _ i
  · rw [physical_cross_kernel c d hc hd hkl]
    exact Orbit45PrintedAlgebra.cross_reversal _ _ _ i

theorem physical_paired_products (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 10) :
    c (bottom i)*d (top i.rev)=c (bottom i.rev)*d (top i) := by
  obtain ⟨hp,hz⟩ := physical_reversal c d hc hd hnc hnd hkl i
  exact Orbit45PrintedAlgebra.paired_products _ _ _ _ hp.symm hz.symm

def spinSum (c d : SS.State 6 ℂ) : ℂ :=
  ∑ i, ((-1 : ℤ)^SS.hammingWt (bottom i) : ℂ)*c (bottom i)*d (top i.rev)
theorem physical_spin_sum_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : spinSum c d=0 := by
  have hp := physical_paired_products c d hc hd hnc hnd hkl
  have hs : spinSum c d= -spinSum c d := by
    unfold spinSum
    conv_lhs => rw [← Equiv.sum_comp Fin.revPerm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.revPerm_apply,Fin.rev_rev]
    have hsign : ((-1 : ℤ)^SS.hammingWt (bottom i.rev) : ℂ)=
        -((-1 : ℤ)^SS.hammingWt (bottom i) : ℂ) := by exact_mod_cast reverse_sign i
    rw [hsign,mul_assoc,mul_assoc,← hp i]
    ring
  linear_combination hs/2
end
end MainTheory.Orbit45PhysicalPrintedRows
