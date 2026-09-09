import MainTheory.OrderSevenSupportDisplays
import MainTheory.FlipCharacterObstruction

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderSeven61PhaseFlips
open MainTheory.OrderSevenSupportDisplays MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit61 (S0 S1)

noncomputable def z (c d : SS.State 6 ℂ) (i j : Fin 9) := star (c (bottom61 i))*d (top61 j)


def edge34_sources : Fin 2 → SS.BitString 6 := ![top61 4,top61 3]
theorem edge34_injective : Function.Injective edge34_sources := by decide +kernel
theorem edge34_incidences : Finset.univ.image edge34_sources=incidenceSet S0 S1 (bits 40) := by decide +kernel
theorem edge34_flips : ∀ j,SS.bxor (edge34_sources j) (bits 40)=(![bottom61 3,bottom61 4] : Fin 2 → SS.BitString 6) j := by decide +kernel
theorem edge34_signs : ∀ j,SS.bdot (bits 0) (edge34_sources j)=false := by decide +kernel

theorem edge34_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 40) (bits 0)=z c d 3 4+z c d 4 3 := by
  rw [offSum_eq_indexed S0 S1 c d (bits 40) (bits 0) edge34_sources edge34_injective edge34_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [edge34_flips,edge34_signs]
  norm_num [edge34_sources,z,Fin.sum_univ_succ]

theorem edge34 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : z c d 3 4+z c d 4 3=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 40) (bits 0)
    (by decide +kernel : (⟨bits 40,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [edge34_sum] using h


def edge48_sources : Fin 2 → SS.BitString 6 := ![top61 8,top61 4]
theorem edge48_injective : Function.Injective edge48_sources := by decide +kernel
theorem edge48_incidences : Finset.univ.image edge48_sources=incidenceSet S0 S1 (bits 17) := by decide +kernel
theorem edge48_flips : ∀ j,SS.bxor (edge48_sources j) (bits 17)=(![bottom61 4,bottom61 8] : Fin 2 → SS.BitString 6) j := by decide +kernel
theorem edge48_signs : ∀ j,SS.bdot (bits 0) (edge48_sources j)=false := by decide +kernel

theorem edge48_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 17) (bits 0)=z c d 4 8+z c d 8 4 := by
  rw [offSum_eq_indexed S0 S1 c d (bits 17) (bits 0) edge48_sources edge48_injective edge48_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [edge48_flips,edge48_signs]
  norm_num [edge48_sources,z,Fin.sum_univ_succ]

theorem edge48 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : z c d 4 8+z c d 8 4=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 17) (bits 0)
    (by decide +kernel : (⟨bits 17,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [edge48_sum] using h


def edge38_sources : Fin 2 → SS.BitString 6 := ![top61 8,top61 3]
theorem edge38_injective : Function.Injective edge38_sources := by decide +kernel
theorem edge38_incidences : Finset.univ.image edge38_sources=incidenceSet S0 S1 (bits 6) := by decide +kernel
theorem edge38_flips : ∀ j,SS.bxor (edge38_sources j) (bits 6)=(![bottom61 3,bottom61 8] : Fin 2 → SS.BitString 6) j := by decide +kernel
theorem edge38_signs : ∀ j,SS.bdot (bits 0) (edge38_sources j)=false := by decide +kernel

theorem edge38_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 6) (bits 0)=z c d 3 8+z c d 8 3 := by
  rw [offSum_eq_indexed S0 S1 c d (bits 6) (bits 0) edge38_sources edge38_injective edge38_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [edge38_flips,edge38_signs]
  norm_num [edge38_sources,z,Fin.sum_univ_succ]

theorem edge38 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : z c d 3 8+z c d 8 3=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 6) (bits 0)
    (by decide +kernel : (⟨bits 6,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [edge38_sum] using h


end MainTheory.OrderSeven61PhaseFlips
