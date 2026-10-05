import MainTheory.Orbit2StandardFiveQubit

/-! Literal single-site syndromes for the printed standard generators.
The table and every nonidentity Pauli of weight at most two are checked in
the kernel; the actual operator anticommutation follows by matrix algebra. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
namespace MainTheory.StandardFiveSyndromeDisplays
open scoped BigOperators
open Orbit2.TensorPauli MainTheory.Orbit2StandardFiveQubit
def syndrome (p : Label 5) : Fin 4 → Bool := fun g => decide (phase (generators g) p≠phase p (generators g))
def single (i : Fin 5) (a : Fin 4) : Label 5 := Function.update (fun _ => 0) i a
def table : Fin 5 → Fin 3 → Fin 4 → Bool :=
  ![![![false,false,false,true],![true,false,true,true],![true,false,true,false]],
    ![![true,false,false,false],![true,true,false,true],![false,true,false,true]],
    ![![true,true,false,false],![true,true,true,false],![false,false,true,false]],
    ![![false,true,true,false],![true,true,true,true],![true,false,false,true]],
    ![![false,false,true,true],![false,true,true,true],![false,true,false,false]]]
theorem literal_table : ∀ i a, syndrome (single i a.succ)=table i a := by decide +kernel
theorem all_nonzero_unique : Function.Injective (fun ia : Fin 5 × Fin 3 => table ia.1 ia.2) ∧
    (Finset.univ.image (fun ia : Fin 5 × Fin 3 => table ia.1 ia.2))=
      Finset.univ.erase (fun _ => false) := by decide +kernel
theorem low_weight_nonzero : ∀ p : Label 5,
    Orbit2.FiveQubit.weight p ≤ 2 → p≠(fun _ => 0) → syndrome p≠(fun _ => false) := by decide +kernel
theorem phase_opposite : ∀ p : Label 5, ∀ g : Fin 4,
    syndrome p g=true → phase (generators g) p=-(phase p (generators g)) := by decide +kernel
theorem commuting_generators : ∀ g h : Fin 4,
    phase (generators g) (generators h)=phase (generators h) (generators g) := by decide +kernel
theorem generators_commute (g h : Fin 4) :
    operator (generators g)*operator (generators h)=operator (generators h)*operator (generators g) := by
  rw [operator_mul,operator_mul,product_comm (generators g) (generators h),commuting_generators]
theorem anticommutes (p : Label 5) (g : Fin 4) (h : syndrome p g=true) :
    operator (generators g)*operator p=-(operator p*operator (generators g)) := by
  rw [operator_mul,operator_mul,phase_opposite p g h,product_comm (generators g) p]
  simp only [map_neg,neg_smul]
theorem low_weight_anticommutes (p : Label 5) (hw : Orbit2.FiveQubit.weight p ≤ 2)
    (hp : p≠(fun _ => 0)) : ∃ g : Fin 4,
    operator (generators g)*operator p=-(operator p*operator (generators g)) := by
  have hs := low_weight_nonzero p hw hp
  obtain ⟨g,hg⟩ : ∃ g, syndrome p g=true := by
    by_contra h
    push_neg at h
    apply hs
    funext g
    exact Bool.eq_false_iff.2 (h g)
  exact ⟨g,anticommutes p g hg⟩
theorem logical_X : ∀ j s,
    Orbit2.FiveQubit.act ![1,1,1,1,1] (standard j) s=standard (if j=0 then 1 else 0) s := by decide +kernel
theorem logical_anticommute : operator (![3,3,3,3,3] : Label 5)*operator (![1,1,1,1,1] : Label 5)=
    -(operator (![1,1,1,1,1] : Label 5)*operator (![3,3,3,3,3] : Label 5)) := by
  rw [operator_mul,operator_mul,product_comm]
  have hp : phase (![3,3,3,3,3] : Label 5) ![1,1,1,1,1]=
      -phase (![1,1,1,1,1] : Label 5) ![3,3,3,3,3] := by decide +kernel
  rw [hp]
  simp only [map_neg,neg_smul]
end MainTheory.StandardFiveSyndromeDisplays
