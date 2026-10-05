import MainTheory.Orbit45PhysicalSpinFlip
import MainTheory.CompleteShadowTrace

/-! The manuscript's zeroth shadow coefficient is the actual identity-label
coefficient, with the precise projector-trace normalization used in the SI. -/
set_option autoImplicit false
namespace MainTheory.Orbit45ShadowNormalization
open MainTheory.Orbit45PhysicalSpinFlip MainTheory.Orbit8SpinProjector
open MainTheory.PairPartialTrace MainTheory.PauliKernelTrace
open MainTheory.Orbit45PrintedFibers SixQubit.Orbit45Support
noncomputable section
def identity : SS.PauliString 6 := ⟨fun _ => false,fun _ => false⟩
theorem identity_kernel : pauliKernel identity=1 := by
  have hy : identity.numY=0 := by decide +kernel
  have hz : ∀ x : SS.BitString 6, SS.bdot identity.z x=false := by decide +kernel
  ext x y
  simp only [pauliKernel,hy,pow_zero,hz,SS.signC,one_mul,Matrix.one_apply]
  change (if y=SS.bxor x (fun _ => false) then 1 else 0)=(if x=y then 1 else 0)
  rw [SS.bxor_zero]
  by_cases he : x=y
  · subst y
    simp
  · rw [if_neg he,if_neg (Ne.symm he)]
def S0 (psi : Fin 2 → SS.State 6 ℂ) : ℝ := CompleteShadowTrace.coefficient psi identity
theorem shadow_trace (psi : Fin 2 → SS.State 6 ℂ) :
    (S0 psi : ℂ)=(1/2 : ℂ)*Matrix.trace (familyKernel psi*spinConjugate (familyKernel psi)) := by
  rw [S0,CompleteShadowTrace.coefficient_trace,identity_kernel,Matrix.mul_one,Matrix.mul_one]
theorem shadow_normal_form (psi : Fin 2 → SS.State 6 ℂ)
    (hn : ∀ i, SS.innerC (psi i) (psi i)=1) (hkl : SS.HasDistance psi 3) :
    S0 psi=(1/4 : ℝ)*(1-Orbit8EnumeratorDisplays.normalizedA psi 1-
      Orbit8EnumeratorDisplays.normalizedA psi 2-Orbit8EnumeratorDisplays.normalizedA psi 3) := by
  apply Complex.ofReal_injective
  rw [shadow_trace,general_shadow_trace psi hn hkl]
  push_cast
  ring
theorem physical_shadow_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit45Support.S0 → c x=0)
    (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : S0 ![c,d]=0 := by
  apply Complex.ofReal_injective
  rw [shadow_trace,physical_spin_trace_zero c d hc hd hnc hnd hkl]
  simp
end
end MainTheory.Orbit45ShadowNormalization
