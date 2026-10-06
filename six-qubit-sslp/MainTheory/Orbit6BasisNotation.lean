import MainTheory.SupportedBasisExpansion
import MainTheory.Orbit6SpinorDisplays
set_option autoImplicit false
namespace MainTheory.Orbit6BasisNotation
open scoped BigOperators
open SixQubit.Orbit6 MainTheory.Orbit6MomentDisplays MainTheory.Orbit6SpinorDisplays
open MainTheory.SupportedBasisExpansion
noncomputable section

def bottomWord (p : Fin 2 × Fin 11) : SS.BitString 6 :=
  bottom ⟨11*p.1.val+p.2.val,by omega⟩
def bottomCoefficient (c : SS.State 6 ℂ) (p : Fin 2 × Fin 11) : ℂ :=
  if p.2=0 then anchor c p.1 else bottomEdge c ⟨p.2.val-1,by omega⟩ p.1
def topSlot : Fin 10 → Fin 10 := ![5,3,2,1,0,4,6,7,8,9]
def topWord (p : Fin 2 × Fin 10) : SS.BitString 6 :=
  top ⟨10*p.1.val+(topSlot p.2).val,by omega⟩
def topCoefficient (d : SS.State 6 ℂ) (p : Fin 2 × Fin 10) : ℂ :=
  if h : p.2.val<5 then topSingleton d ⟨p.2.val,h⟩ p.1
  else topComplement d ⟨p.2.val-5,by omega⟩ p.1

theorem bottom_injective : Function.Injective bottomWord := by decide +kernel
theorem top_injective : Function.Injective topWord := by decide +kernel
theorem literal_fibers : S0=Finset.univ.image bottomWord ∧ S1=Finset.univ.image topWord := by
  decide +kernel

theorem bottom_coefficients (c : SS.State 6 ℂ) (p : Fin 2 × Fin 11) :
    c (bottomWord p)=bottomCoefficient c p := by
  rcases p with ⟨a,e⟩
  fin_cases a <;> fin_cases e <;> rfl
theorem top_coefficients (d : SS.State 6 ℂ) (p : Fin 2 × Fin 10) :
    d (topWord p)=topCoefficient d p := by
  rcases p with ⟨a,i⟩
  fin_cases a <;> fin_cases i <;> rfl

theorem physical_bottom_expansion (c : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (x : SS.BitString 6) :
    c x=∑ p : Fin 2 × Fin 11,if x=bottomWord p then bottomCoefficient c p else 0 := by
  have h := indexed_sum bottomWord bottom_injective c (by simpa only [← literal_fibers.1] using hc) x
  simpa only [bottom_coefficients] using h

theorem physical_top_expansion (d : SS.State 6 ℂ)
    (hd : ∀ x,x∉S1 → d x=0) (x : SS.BitString 6) :
    d x=∑ p : Fin 2 × Fin 10,if x=topWord p then topCoefficient d p else 0 := by
  have h := indexed_sum topWord top_injective d (by simpa only [← literal_fibers.2] using hd) x
  simpa only [top_coefficients] using h

end
end MainTheory.Orbit6BasisNotation
