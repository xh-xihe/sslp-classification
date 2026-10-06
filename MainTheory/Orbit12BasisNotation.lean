import MainTheory.SupportedBasisExpansion
import MainTheory.Orbit12MomentDisplays
import MainTheory.Orbit12Frames
set_option autoImplicit false
namespace MainTheory.Orbit12BasisNotation
open scoped BigOperators
open SixQubit.Orbit12 MainTheory.Orbit12MomentDisplays MainTheory.Orbit12Frames
open MainTheory.SupportedBasisExpansion
noncomputable section

def slot : Fin 8 → Fin 8 := ![0,7,6,5,4,3,2,1]
def bottomWord (p : Fin 2 × Fin 8) : SS.BitString 6 :=
  bottom ⟨8*p.1.val+(slot p.2).val,by omega⟩
def topWord (p : Fin 2 × Fin 8) : SS.BitString 6 :=
  top ⟨8*p.1.val+(slot p.2).val,by omega⟩
def bottomCoefficient (c : SS.State 6 ℂ) (p : Fin 2 × Fin 8) : ℂ :=
  if p.2=0 then u c p.1 else if p.2=1 then v c p.1
  else a c ⟨p.2.val-2,by omega⟩ p.1
def topCoefficient (d : SS.State 6 ℂ) (p : Fin 2 × Fin 8) : ℂ :=
  if p.2=0 then ut d p.1 else if p.2=1 then vt d p.1
  else b d ⟨p.2.val-2,by omega⟩ p.1

theorem bottom_injective : Function.Injective bottomWord := by decide +kernel
theorem top_injective : Function.Injective topWord := by decide +kernel
theorem literal_fibers : S0=Finset.univ.image bottomWord ∧ S1=Finset.univ.image topWord := by
  decide +kernel
theorem active_patterns : ∀ f : Fin 2,∀ i : Fin 8,∀ j : Fin 4,
    bottomWord (f,i) j.succ.castSucc=topWord (f,i) j.succ.castSucc ∧
    bottomWord (f,i) j.succ.castSucc=
      (if i=0 then false else if i=1 then true else
        (j=(edges ⟨i.val-2,by omega⟩).1 ∨ j=(edges ⟨i.val-2,by omega⟩).2)) ∧
    bottomWord (f,i) 5=!(i=0 ∨ i=1) ∧ topWord (f,i) 5=(i=0 ∨ i=1) := by
  decide +kernel

theorem bottom_coefficients (c : SS.State 6 ℂ) (p : Fin 2 × Fin 8) :
    c (bottomWord p)=bottomCoefficient c p := by
  rcases p with ⟨f,i⟩
  fin_cases f <;> fin_cases i <;> rfl
theorem top_coefficients (d : SS.State 6 ℂ) (p : Fin 2 × Fin 8) :
    d (topWord p)=topCoefficient d p := by
  rcases p with ⟨f,i⟩
  fin_cases f <;> fin_cases i <;> rfl

theorem physical_bottom_expansion (c : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (x : SS.BitString 6) :
    c x=∑ p : Fin 2 × Fin 8,if x=bottomWord p then bottomCoefficient c p else 0 := by
  have h := indexed_sum bottomWord bottom_injective c (by simpa only [← literal_fibers.1] using hc) x
  simpa only [bottom_coefficients] using h
theorem physical_top_expansion (d : SS.State 6 ℂ)
    (hd : ∀ x,x∉S1 → d x=0) (x : SS.BitString 6) :
    d x=∑ p : Fin 2 × Fin 8,if x=topWord p then topCoefficient d p else 0 := by
  have h := indexed_sum topWord top_injective d (by simpa only [← literal_fibers.2] using hd) x
  simpa only [top_coefficients] using h

end
end MainTheory.Orbit12BasisNotation
