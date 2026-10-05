import MainTheory.ArbitrarySplitSixQubit
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.ArbitrarySplitTrace
open MainTheory.ArbitrarySplitPerfectCode MainTheory.ArbitrarySplitSixQubit
open Orbit2.TensorPauli
open scoped BigOperators Matrix Kronecker
noncomputable section

theorem small_tail_trace : ∀ p : Label 4,weight p≤2 → p≠(fun _ => 0) →
    ∀ a b : Fin 2,(∑ j : Fin 2,coefficient p j j a b)=0 := by decide +kernel

theorem triple_tail_trace : ∀ p : Label 4,weight p≤3 → p≠(fun _ => 0) →
    (∑ a : Fin 2,∑ j : Fin 2,coefficient p j j a a)=0 := by decide +kernel

theorem trace_compression (F : Matrix (Fin 2) (Fin 2) ℂ) (p : Label 4) :
    Matrix.trace (C.conjTranspose*(F ⊗ₖ operator p)*C)=
      (1/16 : ℂ)*(∑ a : Fin 2,∑ b : Fin 2,F a b*
        (∑ j : Fin 2,(coefficient p j j a b : ℂ))) := by
  simp only [Matrix.trace,Matrix.diag_apply,compression]
  simp only [Fin.sum_univ_two]
  ring

theorem trace_small_zero (F : Matrix (Fin 2) (Fin 2) ℂ) (p : Label 4)
    (hp : weight p≤2) (hn : p≠(fun _ => 0)) :
    Matrix.trace (C.conjTranspose*(F ⊗ₖ operator p)*C)=0 := by
  have hz (a b : Fin 2) : (∑ j : Fin 2,(coefficient p j j a b : ℂ))=0 := by
    have h := congrArg (fun z : GaussianInt => (z : ℂ)) (small_tail_trace p hp hn a b)
    simpa only [map_sum,map_zero] using h
  rw [trace_compression]
  simp only [hz,mul_zero,Finset.sum_const_zero]

theorem trace_triple_zero (p : Label 4) (hp : weight p≤3) (hn : p≠(fun _ => 0)) :
    Matrix.trace (C.conjTranspose*((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator p)*C)=0 := by
  have hz : (∑ a : Fin 2,∑ j : Fin 2,(coefficient p j j a a : ℂ))=0 := by
    have h := congrArg (fun z : GaussianInt => (z : ℂ)) (triple_tail_trace p hp hn)
    simpa only [map_sum,map_zero] using h
  rw [trace_compression]
  have hd : (∑ a : Fin 2,∑ b : Fin 2,
      (1 : Matrix (Fin 2) (Fin 2) ℂ) a b *
      (∑ j : Fin 2,(coefficient p j j a b : ℂ))) =
      (∑ a : Fin 2,∑ j : Fin 2,(coefficient p j j a a : ℂ)) := by
    simp only [Fin.sum_univ_two,Matrix.one_apply]
    norm_num
  rw [hd,hz,mul_zero]

theorem weight_three_cases : ∀ p : Label 6,weight6 p=3 →
    tailLabel p≠(fun _ => 0) ∧
      (weight (tailLabel p)≤2 ∨ (weight (tailLabel p)=3 ∧ p 0=0 ∧ p 1=0)) := by
  decide +kernel

theorem split_weight_three_trace (W : Matrix (Fin 4) (Fin 2) ℂ)
    (hW : W.conjTranspose*W=1) (p : Label 6) (hp : weight6 p=3) :
    Matrix.trace ((split W).conjTranspose*(pairOperator p ⊗ₖ operator (tailLabel p))*split W)=0 := by
  have h := weight_three_cases p hp
  rw [split_compression]
  rcases h.2 with hs | ⟨ht,h0,h1⟩
  · exact trace_small_zero _ _ hs h.1
  · rw [pair_identity p h0 h1,Matrix.mul_one,hW]
    exact trace_triple_zero _ (by omega) h.1
end
end MainTheory.ArbitrarySplitTrace
