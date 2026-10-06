import MainTheory.PairPauliSupport
import MainTheory.PairPauliExpansion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace MainTheory.PairPauliTrace

open MainTheory.PairPartialTrace MainTheory.PairPauliSupport
open MainTheory.PairPauliPurity MainTheory.PairPauliExpansion
open SixQubit.Orbit7DirectMarginal

def supportedNonidentity (s : Fin 5) : Finset (SS.PauliString 6) :=
  Finset.univ.filter (fun P => P ≠ pairString s 0 0 ∧ SS.MacWilliams.supp P ⊆ pairSites s)

theorem identity_bits (s : Fin 5) :
    pairString s 0 0 = (⟨fun _ => false,fun _ => false⟩ : SS.PauliString 6) := by
  apply MainTheory.PauliWordBridge.pauliWordEquiv.injective
  simp only [pairString,Equiv.apply_symm_apply]
  funext i
  fin_cases s <;> fin_cases i <;> rfl

theorem local_global_trace (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5) (p q : Fin 4) :
    (pairPauli p q*directPairMarginal code s).trace =
      (1/2 : ℂ)*(MainTheory.PauliKernelTrace.pauliKernel (pairString s p q)*familyKernel code).trace := by
  rw [kernel_embed]
  exact partial_trace_identity code s _

theorem nonidentity_sum (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5) :
    (∑ r ∈ nonidentity,Complex.normSq ((pairPauli r.1 r.2*directPairMarginal code s).trace)) =
      ∑ P ∈ supportedNonidentity s,
        Complex.normSq ((1/2 : ℂ)*(MainTheory.PauliKernelTrace.pauliKernel P*familyKernel code).trace) := by
  apply Finset.sum_bij (fun r _ => pairString s r.1 r.2)
  · intro r hr
    simp only [supportedNonidentity,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨?_,pair_supported s r.1 r.2⟩
    intro he
    have hz := @pair_injective s r (0,0) he
    exact (Finset.mem_erase.mp hr).1 hz
  · intro a _ b _ hab
    exact @pair_injective s a b hab
  · intro P hP
    obtain ⟨hP0,hPs⟩ := (Finset.mem_filter.mp hP).2
    obtain ⟨p,q,hpq⟩ := supported_surjective s P hPs
    refine ⟨(p,q),?_,hpq.symm⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    intro hzero
    have he := congrArg (fun r : Fin 4 × Fin 4 => pairString s r.1 r.2) hzero
    exact hP0 (hpq.trans he)
  · intro r _
    rw [local_global_trace]

theorem direct_hermitian (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5) :
    (directPairMarginal code s).conjTranspose=directPairMarginal code s := by
  ext p q
  simp [Matrix.conjTranspose_apply,directPairMarginal,directPurePairMarginal,mul_comm]

theorem pair_purity_expansion (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5)
    (ht : (directPairMarginal code s).trace=1) :
    4*(directPairMarginal code s*directPairMarginal code s).trace = 1+
      ((∑ P ∈ supportedNonidentity s,
        Complex.normSq ((1/2 : ℂ)*(MainTheory.PauliKernelTrace.pauliKernel P*familyKernel code).trace) : ℝ) : ℂ) := by
  rw [normalized_expansion _ (direct_hermitian code s) ht,nonidentity_sum]

end MainTheory.PairPauliTrace
