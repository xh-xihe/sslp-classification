import MainTheory.Orbit2PhysicalMarginals
import MainTheory.Orbit2StandardFiveQubit

/-! The actual spectator-pair/active-site partial trace is a product. -/

namespace MainTheory.Orbit2ProductMarginal

noncomputable section
open Orbit2 Orbit2.TensorPauli Orbit2.Quartic
open scoped BigOperators

abbrev Tail := Fin 3 → Fin 2

def assembly (i : Fin 4) : (Fin 2 × Tail) ≃ ActiveBits :=
  Fin.insertNthEquiv (fun _ : Fin 4 => Fin 2) i

theorem assembly_apply (i : Fin 4) (r : Fin 2) (t : Tail) :
    assembly i (r,t)=Fin.insertNth i r t := rfl

def wordConditional (V : Encoder) (i : Fin 4) (b c : SpectatorBits) (j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ := fun r s =>
  ∑ t : Tail, V.tensorMatrix (joinBits b (Fin.insertNth i r t)) j *
    star (V.tensorMatrix (joinBits c (Fin.insertNth i s t)) j)

def conditional (V : Encoder) (i : Fin 4) (b c : SpectatorBits) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (wordConditional V i b c 0+wordConditional V i b c 1)

def one (V : Encoder) (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ b : SpectatorBits, conditional V i b b

def joint (V : Encoder) (i : Fin 4) :
    Matrix (SpectatorBits × Fin 2) (SpectatorBits × Fin 2) ℂ :=
  fun x y => conditional V i x.1 y.1 x.2 y.2

theorem single_insert (i a : Fin 4) (r s : Fin 2) (t u : Tail) :
    operator (single i a) (Fin.insertNth i r t) (Fin.insertNth i s u)=
      localC a r s*(1 : Matrix Tail Tail ℂ) t u := by
  unfold operator tensor
  rw [Fin.prod_univ_succAbove _ i]
  simp only [single, if_true, Fin.insertNth_apply_same,
    Fin.succAbove_ne, if_false, Fin.insertNth_apply_succAbove]
  have h : (∏ k : Fin 3, localC 0 (t k) (u k))=(1 : Matrix Tail Tail ℂ) t u :=
    congrArg (fun M => M t u) (operator_zero (n := 3))
  rw [h]

theorem word_coefficient (V : Encoder) (i a : Fin 4) (b c : SpectatorBits) (j : Fin 2) :
    Matrix.trace (localC a*wordConditional V i b c j)=
      ((V.schmidtFrame j).conjTranspose*operator (single i a)*V.schmidtFrame j) c b/4 := by
  classical
  simp only [Matrix.mul_apply,
    Matrix.conjTranspose_apply, Encoder.schmidtFrame]
  simp_rw [← (assembly i).sum_comp]
  simp only [Fintype.sum_prod_type, assembly_apply,
    single_insert, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, wordConditional,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_div, star_mul, star_ofNat]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext s
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem conditional_coefficient (V : Encoder) (i a : Fin 4) (b c : SpectatorBits) :
    Matrix.trace (localC a*conditional V i b c)=
      V.diagonalFrameSum (single i a) c b/8 := by
  rw [conditional, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, word_coefficient, word_coefficient]
  simp only [Encoder.diagonalFrameSum, Matrix.add_apply, smul_eq_mul]
  ring

theorem diagonal_scalar (V : Encoder) (i a : Fin 4) :
    V.diagonalFrameSum (single i a)=
      (Matrix.trace (V.diagonalFrameSum (single i a))/4) • 1 := by
  by_cases ha : a=0
  · subst a
    have hs : single i 0=(fun _ => 0) := by funext j; simp [single]
    rw [hs, Encoder.diagonalFrameSum, operator_zero, Matrix.mul_one,
      Matrix.mul_one, V.schmidtFrame_cross, V.schmidtFrame_cross]
    simp only [if_true]
    have he : (1 : Matrix SpectatorBits SpectatorBits ℂ)+1=(2 : ℂ) • 1 := by
      ext b c
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [he, Matrix.trace_smul, Matrix.trace_one]
    norm_num [SpectatorBits]
  · exact V.diagonalFrameSum_scalar i a ha

theorem local_traces_ext (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ a : Fin 4, Matrix.trace (localC a*M)=Matrix.trace (localC a*N)) : M=N := by
  have hc : ∀ a, MainTheory.PauliTransferTwo.coefficient a M=
      MainTheory.PauliTransferTwo.coefficient a N := by
    intro a
    unfold MainTheory.PauliTransferTwo.coefficient
    rw [← MainTheory.Orbit2StandardFiveQubit.localC_pauli, h]
  rw [← MainTheory.PauliTransferTwo.pauli_expansion M,
    ← MainTheory.PauliTransferTwo.pauli_expansion N]
  simp_rw [hc]

theorem conditional_product (V : Encoder) (i : Fin 4) (b c : SpectatorBits) :
    conditional V i b c=(if b=c then (1/4 : ℂ) else 0) • one V i := by
  apply local_traces_ext
  intro a
  rw [conditional_coefficient, Matrix.mul_smul, Matrix.trace_smul]
  have ht : Matrix.trace (localC a*one V i)=
      Matrix.trace (V.diagonalFrameSum (single i a))/8 := by
    simp only [one, Matrix.mul_sum, Matrix.trace_sum, conditional_coefficient,
      ← Finset.sum_div]
    rfl
  rw [ht]
  have h := congrArg (fun M => M c b) (diagonal_scalar V i a)
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h
  rw [h]
  by_cases hb : b=c
  · simp [hb]
    ring
  · simp [hb, Ne.symm hb]

theorem product_marginal (V : Encoder) (i : Fin 4) :
    joint V i=(fun x y => ((1/4 : ℂ) •
      (1 : Matrix SpectatorBits SpectatorBits ℂ)) x.1 y.1 * one V i x.2 y.2) := by
  ext x y
  have h := congrArg (fun M => M x.2 y.2) (conditional_product V i x.1 y.1)
  simpa only [joint, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    mul_ite, mul_one, mul_zero] using h

end
end MainTheory.Orbit2ProductMarginal
