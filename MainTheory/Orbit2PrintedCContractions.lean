import MainTheory.Orbit2QuarticContractions

/-! Exact forbidden-set multipliers in the printed quartic certificate. -/

namespace MainTheory.Orbit2PrintedCContractions

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic MainTheory.Orbit2QuarticContractions
open scoped BigOperators

set_option maxHeartbeats 8000000

def V3 (p : Label 4) : Prop := pauliWeight p=3 ∧ transverseCount p=2
def F4 (p : Label 4) : Prop := pauliWeight p=4 ∧ transverseCount p=2
def D3 (p : Label 4) : Prop := pauliWeight p=3 ∧ transverseCount p=0
def D2 (p : Label 4) : Prop := pauliWeight p=2 ∧ transverseCount p=0

instance (p) : Decidable (V3 p) := inferInstanceAs (Decidable (_ ∧ _))
instance (p) : Decidable (F4 p) := inferInstanceAs (Decidable (_ ∧ _))
instance (p) : Decidable (D3 p) := inferInstanceAs (Decidable (_ ∧ _))
instance (p) : Decidable (D2 p) := inferInstanceAs (Decidable (_ ∧ _))

theorem weighted_add (t : Fin 32 → ℂ) (a b : Label 4 → Fin 32 → Fin 32 → ℤ)
    (p : Label 4) :
    weightedCorrelation t (fun p v y => a p v y+b p v y) p=
      weightedCorrelation t a p+weightedCorrelation t b p := by
  simp only [weightedCorrelation,Int.cast_add,mul_add,add_mul,Finset.sum_add_distrib]

theorem weighted_scale (t : Fin 32 → ℂ) (a : ℤ)
    (m : Label 4 → Fin 32 → Fin 32 → ℤ) (p : Label 4) :
    weightedCorrelation t (fun p v y => a*m p v y) p=(a : ℂ)*weightedCorrelation t m p := by
  simp only [weightedCorrelation,Int.cast_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem weighted_ite (t : Fin 32 → ℂ) (h : Label 4 → Prop) [DecidablePred h]
    (m : Label 4 → Fin 32 → Fin 32 → ℤ) (p : Label 4) :
    weightedCorrelation t (fun p v y => if h p then m p v y else 0) p=
      if h p then weightedCorrelation t m p else 0 := by
  by_cases hp : h p <;> simp [weightedCorrelation,hp]

theorem multiplier_decomposition (p : Label 4) (v y : Fin 32) :
    cMultiplier p v y=
      (if V3 p then -24 else 0)+
      (if F4 p then 68*(if isThree y != isThree v then 1 else 0)+
        76*(if isThree y && isThree v then 1 else 0) else 0)+
      (if D3 p then 100*(if isThree y != isThree v then 1 else 0) else 0)+
      (if D2 p then 8*(if isThree y && isThree v then 1 else 0) else 0) := by
  unfold cMultiplier V3 F4 D3 D2
  split_ifs <;> simp_all

theorem weighted_multiplier (t : Fin 32 → ℂ) (p : Label 4) :
    weightedCorrelation t cMultiplier p=
      (if V3 p then (-24 : ℂ)*Defects.correlation (expansion basis t) (operator p) else 0)+
      (if F4 p then 68*c13 t p+76*c33 t p else 0)+
      (if D3 p then 100*c13 t p else 0)+(if D2 p then 8*c33 t p else 0) := by
  have he : cMultiplier=fun p v y =>
      (if V3 p then -24 else 0)+
      (if F4 p then 68*(if isThree y != isThree v then 1 else 0)+
        76*(if isThree y && isThree v then 1 else 0) else 0)+
      (if D3 p then 100*(if isThree y != isThree v then 1 else 0) else 0)+
      (if D2 p then 8*(if isThree y && isThree v then 1 else 0) else 0) := by
    funext p v y
    exact multiplier_decomposition p v y
  rw [he,weighted_add,weighted_add,weighted_add]
  congr 1
  · congr 1
    · congr 1
      · rw [weighted_ite,weightedCorrelation_const]
        split_ifs <;> norm_num
      · rw [weighted_ite,weighted_add,weighted_scale,weighted_scale,weighted_c13,weighted_c33]
        norm_num
    · rw [weighted_ite,weighted_scale,weighted_c13]
      norm_num
  · rw [weighted_ite,weighted_scale,weighted_c33]
    norm_num

end

end MainTheory.Orbit2PrintedCContractions
