import MainTheory.MixedFamilyTrace
import MainTheory.Orbit8SpinProjector
import SixQubit.ShadowTwisted

set_option autoImplicit false

namespace MainTheory.SpinPauliShadowPairing

open SS.MacWilliams SS.Shadow SS.ShadowTwisted SixQubit.Orbit8Universal
open MainTheory.Orbit8SpinProjector

theorem character_square (u v : SS.BitString 6) : (chi u v)^2=1 := by
  rw [chi_eq_pow,← pow_mul]
  rw [Nat.mul_comm, pow_mul]
  norm_num

theorem sign_relation (u ex ez : SS.BitString 6) :
    (spinSign u : ℂ)*(chi ez (SS.bxor (SS.complement u) ex) : ℂ)=
      -(chi ez (SS.bxor (SS.ones 6) ex) : ℂ)*(psignT ez u : ℂ) := by
  rw [spinSign_psign,SS.complement_eq_bxor_ones]
  simp only [chi_bxor_right,psignT,psign,chi_comm ez u]
  push_cast
  ring

theorem pairing (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) (a b : Fin 2) :
    SS.innerC (spinJ (psi a)) (SS.pauliAct E (psi b))=
      -(Complex.I^E.numY)*(chi E.z (SS.bxor (SS.ones 6) E.x) : ℂ)*TfT psi E.x E.z a b := by
  unfold SS.innerC
  rw [← MainTheory.Orbit8SpinProjector.complementEquiv.sum_comp]
  simp only [MainTheory.Orbit8SpinProjector.complementEquiv,Equiv.coe_fn_mk,spinJ,SS.pauliAct,
    SS.complement_complement,spinSign_complement,star_mul,star_sign,star_star,signC_bdot]
  rw [TfT,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hb : SS.bxor (SS.complement u) E.x=SS.complement (SS.bxor u E.x) := by
    rw [SS.bxor_comm,SS.Shadow.bxor_complement_right,SS.bxor_comm E.x u]
  have hs := sign_relation u E.x E.z
  rw [hb] at hs ⊢
  linear_combination Complex.I^E.numY*psi a u*psi b (SS.complement (SS.bxor u E.x))*hs

theorem norm_pairing (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) (a b : Fin 2) :
    Complex.normSq (SS.innerC (spinJ (psi a)) (SS.pauliAct E (psi b)))=
      Complex.normSq (TfT psi E.x E.z a b) := by
  rw [pairing,Complex.normSq_mul,Complex.normSq_mul,Complex.normSq_neg,
    map_pow,Complex.normSq_I,one_pow,one_mul,Complex.normSq_ofReal]
  rw [← pow_two,character_square,one_mul]

end MainTheory.SpinPauliShadowPairing
