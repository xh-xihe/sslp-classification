import Orbit2.Complete

/-! The SI's mixed and weight-three correlation contractions are literal traces. -/

namespace MainTheory.Orbit2QuarticContractions

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic
open scoped BigOperators

set_option maxHeartbeats 8000000

def onePart (t : Fin 32 → ℂ) : Defects.ActiveMatrix :=
  expansion basis (fun u => if isThree u then 0 else t u)

def c13 (t : Fin 32 → ℂ) (p : Label 4) : ℂ :=
  tau (operator p*(onePart t*(threePart t).conjTranspose+
    threePart t*(onePart t).conjTranspose))

def c33 (t : Fin 32 → ℂ) (p : Label 4) : ℂ :=
  tau (operator p*threePart t*(threePart t).conjTranspose)

theorem cross_expansion (a b : Fin 32 → ℂ) (p : Label 4) :
    tau (operator p*expansion basis a*(expansion basis b).conjTranspose)=
      ∑ v,∑ y,a y*star (b v)*pairKernel p y v := by
  rw [expansion_conjTranspose]
  unfold expansion
  simp only [Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    tau_sum,tau_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  rw [triple_trace_pair]
  unfold pairKernel
  ring

theorem weighted_c33 (t : Fin 32 → ℂ) (p : Label 4) :
    weightedCorrelation t (fun _ v y => if isThree y && isThree v then 1 else 0) p=c33 t p := by
  rw [c33,threePart,cross_expansion]
  unfold weightedCorrelation
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  cases hv : isThree v <;> cases hy : isThree y <;> simp [hv,hy]

theorem weighted_c13 (t : Fin 32 → ℂ) (p : Label 4) :
    weightedCorrelation t (fun _ v y => if isThree y != isThree v then 1 else 0) p=c13 t p := by
  rw [c13,Matrix.mul_add]
  simp only [tau,Matrix.trace_add,add_div]
  change weightedCorrelation t _ p=
    tau (operator p*(onePart t*(threePart t).conjTranspose))+
      tau (operator p*(threePart t*(onePart t).conjTranspose))
  simp only [← Matrix.mul_assoc,onePart,threePart,cross_expansion,← Finset.sum_add_distrib]
  unfold weightedCorrelation
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  cases hv : isThree v <;> cases hy : isThree y <;> simp [hv,hy]

theorem part_sum (t : Fin 32 → ℂ) : onePart t+threePart t=expansion basis t := by
  unfold onePart threePart expansion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  cases h : isThree u <;> simp [h]

theorem c33_real (t : Fin 32 → ℂ) (p : Label 4) : star (c33 t p)=c33 t p :=
  correlation_real (threePart t) p

theorem c13_real (t : Fin 32 → ℂ) (p : Label 4) : star (c13 t p)=c13 t p := by
  unfold c13 tau
  change (starRingEnd ℂ) (_ / _)=_
  rw [map_div₀]
  simp only [starRingEnd_apply,star_pow,star_ofNat]
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose,operator_hermitian]
  rw [Matrix.trace_mul_comm]
  congr 1
  rw [add_comm]

end

end MainTheory.Orbit2QuarticContractions
