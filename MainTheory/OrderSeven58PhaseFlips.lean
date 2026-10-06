import MainTheory.OrderSevenSupportDisplays
import MainTheory.FlipCharacterObstruction

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderSeven58PhaseFlips
open MainTheory.OrderSevenSupportDisplays MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit58 (S0 S1)

noncomputable def z (c d : SS.State 6 ℂ) (i j : Fin 9) := star (c (bottom58 i))*d (top58 j)


def edge35_sources : Fin 2 → SS.BitString 6 := ![top58 5,top58 3]
theorem edge35_injective : Function.Injective edge35_sources := by decide +kernel
theorem edge35_incidences : Finset.univ.image edge35_sources=incidenceSet S0 S1 (bits 40) := by decide +kernel
theorem edge35_flips : ∀ j,SS.bxor (edge35_sources j) (bits 40)=(![bottom58 3,bottom58 5] : Fin 2 → SS.BitString 6) j := by decide +kernel
theorem edge35_signs : ∀ j,SS.bdot (bits 0) (edge35_sources j)=false := by decide +kernel

theorem edge35_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 40) (bits 0)=z c d 3 5+z c d 5 3 := by
  rw [offSum_eq_indexed S0 S1 c d (bits 40) (bits 0) edge35_sources edge35_injective edge35_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [edge35_flips,edge35_signs]
  norm_num [edge35_sources,z,Fin.sum_univ_succ]

theorem edge35 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : z c d 3 5+z c d 5 3=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 40) (bits 0)
    (by decide +kernel : (⟨bits 40,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [edge35_sum] using h


def edge57_sources : Fin 2 → SS.BitString 6 := ![top58 7,top58 5]
theorem edge57_injective : Function.Injective edge57_sources := by decide +kernel
theorem edge57_incidences : Finset.univ.image edge57_sources=incidenceSet S0 S1 (bits 33) := by decide +kernel
theorem edge57_flips : ∀ j,SS.bxor (edge57_sources j) (bits 33)=(![bottom58 5,bottom58 7] : Fin 2 → SS.BitString 6) j := by decide +kernel
theorem edge57_signs : ∀ j,SS.bdot (bits 0) (edge57_sources j)=false := by decide +kernel

theorem edge57_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 33) (bits 0)=z c d 5 7+z c d 7 5 := by
  rw [offSum_eq_indexed S0 S1 c d (bits 33) (bits 0) edge57_sources edge57_injective edge57_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [edge57_flips,edge57_signs]
  norm_num [edge57_sources,z,Fin.sum_univ_succ]

theorem edge57 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : z c d 5 7+z c d 7 5=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 33) (bits 0)
    (by decide +kernel : (⟨bits 33,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [edge57_sum] using h


def four45_sources : Fin 4 → SS.BitString 6 := ![top58 8,top58 7,top58 4,top58 3]
theorem four45_injective : Function.Injective four45_sources := by decide +kernel
theorem four45_incidences : Finset.univ.image four45_sources=incidenceSet S0 S1 (bits 6) := by decide +kernel
theorem four45_flips : ∀ j,SS.bxor (four45_sources j) (bits 6)=(![bottom58 3,bottom58 4,bottom58 7,bottom58 8] : Fin 4 → SS.BitString 6) j := by decide +kernel
theorem four45_signs : ∀ j,SS.bdot (bits 0) (four45_sources j)=false := by decide +kernel

theorem four45_sum (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (bits 6) (bits 0)=z c d 3 8+z c d 4 7+z c d 7 4+z c d 8 3 := by
  rw [offSum_eq_indexed S0 S1 c d (bits 6) (bits 0) four45_sources four45_injective four45_incidences]
  simp only [character,incidenceMonomial]
  simp_rw [four45_flips,four45_signs]
  norm_num [four45_sources,z,Fin.sum_univ_succ]
  ring
theorem four45 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : z c d 3 8+z c d 4 7+z c d 7 4+z c d 8 3=0 := by
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (bits 6) (bits 0)
    (by decide +kernel : (⟨bits 6,bits 0⟩ : SS.PauliString 6).wt ≤ 2)
  simpa only [four45_sum] using h


end MainTheory.OrderSeven58PhaseFlips
