import MainTheory.CompletePauliCoefficients
import MainTheory.WImageIntrinsicBridge

set_option autoImplicit false

namespace MainTheory.Orbit21CoefficientDisplays

open MainTheory.CompletePauliCoefficients MainTheory.WImageIntrinsicBridge SS.MacWilliams

theorem identity_value (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ i,SS.innerC (psi i) (psi i)=1) : a psi identityPauli=1 := by
  have ht : trProj psi identityPauli=2 := by
    unfold trProj
    simp only [pauliAct_identity,hnorm]
    norm_num
  unfold a
  rw [ht]
  norm_num [Complex.normSq_apply]

theorem low_kl (psi : Fin 2 → SS.State 6 ℂ) (hd : SS.HasDistance psi 3)
    (E : SS.PauliString 6) (hE : E.wt ≤ 2) : b psi E=a psi E :=
  kl_equality psi E (hd E (by omega))

theorem weight_relation (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ i,SS.innerC (psi i) (psi i)=1) (hd : SS.HasDistance psi 3) :
    Aco psi 6/4+4*(Aco psi 1/4)+Aco psi 2/4+Aco psi 3/4=4 := by
  have h := macwilliams_six psi hd (SixQubit.Pin.Aco_zero psi hnorm)
  linarith [h.2.2]

end MainTheory.Orbit21CoefficientDisplays
