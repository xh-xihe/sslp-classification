import MainTheory.OrderEightSupportDisplays
import MainTheory.FlipCharacterObstruction

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderEightBFlipDisplays

open MainTheory.OrderEightSupportDisplays MainTheory.FlipCharacter
open SixQubit.Orbit65 (S0 S1)

noncomputable def alpha0 (c : SS.State 6 ℂ) := c (bits 38)
noncomputable def alpha1 (d : SS.State 6 ℂ) := d (bits 25)
noncomputable def beta0 (c : SS.State 6 ℂ) := c (bits 49)
noncomputable def beta1 (d : SS.State 6 ℂ) := d (bits 14)
noncomputable def gamma0 (c : SS.State 6 ℂ) := c (bits 31)
noncomputable def gamma1 (d : SS.State 6 ℂ) := d (bits 32)
noncomputable def R (c d : SS.State 6 ℂ) :=
  star (c (bits 5))*d (bits 3)+star (c (bits 60))*d (bits 58)


def edge1_sources : Fin 2 → SS.BitString 6 := ![bits 25,bits 14]

theorem edge1_injective : Function.Injective edge1_sources := by decide +kernel
theorem edge1_incidences : Finset.univ.image edge1_sources=incidenceSet S0 S1 (bits 40) := by decide +kernel
theorem edge1_flips : ∀ i,SS.bxor (edge1_sources i) (bits 40)=(![bits 49,bits 38] : Fin 2 → SS.BitString 6) i := by decide +kernel
theorem edge1_signs : ∀ i,SS.bdot (bits 0) (edge1_sources i)=(![false,false] : Fin 2 → Bool) i := by decide +kernel

theorem edge1_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 40) (bits 0)=star (beta0 c)*alpha1 d+star (alpha0 c)*beta1 d := by
  rw [offSum_eq_indexed S0 S1 c d (bits 40) (bits 0) edge1_sources
    edge1_injective edge1_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [edge1_flips,edge1_signs]
  norm_num [edge1_sources,Fin.sum_univ_succ,alpha0,alpha1,beta0,beta1,gamma0,gamma1,R]


theorem edge1 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (beta0 c)*alpha1 d+star (alpha0 c)*beta1 d=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 40) (bits 0)
    (by decide +kernel : (⟨bits 40,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [edge1_sum] using h


def edge2_sources : Fin 2 → SS.BitString 6 := ![bits 14,bits 32]

theorem edge2_injective : Function.Injective edge2_sources := by decide +kernel
theorem edge2_incidences : Finset.univ.image edge2_sources=incidenceSet S0 S1 (bits 17) := by decide +kernel
theorem edge2_flips : ∀ i,SS.bxor (edge2_sources i) (bits 17)=(![bits 31,bits 49] : Fin 2 → SS.BitString 6) i := by decide +kernel
theorem edge2_signs : ∀ i,SS.bdot (bits 0) (edge2_sources i)=(![false,false] : Fin 2 → Bool) i := by decide +kernel

theorem edge2_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 17) (bits 0)=star (gamma0 c)*beta1 d+star (beta0 c)*gamma1 d := by
  rw [offSum_eq_indexed S0 S1 c d (bits 17) (bits 0) edge2_sources
    edge2_injective edge2_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [edge2_flips,edge2_signs]
  norm_num [edge2_sources,Fin.sum_univ_succ,alpha0,alpha1,beta0,beta1,gamma0,gamma1,R]


theorem edge2 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (gamma0 c)*beta1 d+star (beta0 c)*gamma1 d=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 17) (bits 0)
    (by decide +kernel : (⟨bits 17,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [edge2_sum] using h


def plain45_sources : Fin 4 → SS.BitString 6 := ![bits 3,bits 25,bits 58,bits 32]

theorem plain45_injective : Function.Injective plain45_sources := by decide +kernel
theorem plain45_incidences : Finset.univ.image plain45_sources=incidenceSet S0 S1 (bits 6) := by decide +kernel
theorem plain45_flips : ∀ i,SS.bxor (plain45_sources i) (bits 6)=(![bits 5,bits 31,bits 60,bits 38] : Fin 4 → SS.BitString 6) i := by decide +kernel
theorem plain45_signs : ∀ i,SS.bdot (bits 0) (plain45_sources i)=(![false,false,false,false] : Fin 4 → Bool) i := by decide +kernel

theorem plain45_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 6) (bits 0)=R c d+star (gamma0 c)*alpha1 d+star (alpha0 c)*gamma1 d := by
  rw [offSum_eq_indexed S0 S1 c d (bits 6) (bits 0) plain45_sources
    plain45_injective plain45_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [plain45_flips,plain45_signs]
  norm_num [plain45_sources,Fin.sum_univ_succ,alpha0,alpha1,beta0,beta1,gamma0,gamma1,R]
  ring

theorem plain45 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : R c d+star (gamma0 c)*alpha1 d+star (alpha0 c)*gamma1 d=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 6) (bits 0)
    (by decide +kernel : (⟨bits 6,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [plain45_sum] using h


def signed45_sources : Fin 4 → SS.BitString 6 := ![bits 3,bits 25,bits 58,bits 32]

theorem signed45_injective : Function.Injective signed45_sources := by decide +kernel
theorem signed45_incidences : Finset.univ.image signed45_sources=incidenceSet S0 S1 (bits 6) := by decide +kernel
theorem signed45_flips : ∀ i,SS.bxor (signed45_sources i) (bits 6)=(![bits 5,bits 31,bits 60,bits 38] : Fin 4 → SS.BitString 6) i := by decide +kernel
theorem signed45_signs : ∀ i,SS.bdot (bits 2) (signed45_sources i)=(![true,false,true,false] : Fin 4 → Bool) i := by decide +kernel

theorem signed45_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 6) (bits 2)=-R c d+star (gamma0 c)*alpha1 d+star (alpha0 c)*gamma1 d := by
  rw [offSum_eq_indexed S0 S1 c d (bits 6) (bits 2) signed45_sources
    signed45_injective signed45_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [signed45_flips,signed45_signs]
  norm_num [signed45_sources,Fin.sum_univ_succ,alpha0,alpha1,beta0,beta1,gamma0,gamma1,R]
  ring

theorem signed45 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : -R c d+star (gamma0 c)*alpha1 d+star (alpha0 c)*gamma1 d=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 6) (bits 2)
    (by decide +kernel : (⟨bits 6,bits 2⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [signed45_sum] using h


theorem edge3 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (gamma0 c)*alpha1 d+star (alpha0 c)*gamma1 d=0 := by
  have h := plain45 c d hc hd hkl
  have h' := signed45 c d hc hd hkl
  linear_combination (h+h')/2

end MainTheory.OrderEightBFlipDisplays
