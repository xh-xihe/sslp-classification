import Orbit2.SpectatorFrames

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

abbrev SpectatorBits := Fin 2 → Fin 2
abbrev ActiveBits := Fin 4 → Fin 2

def joinBits (b : SpectatorBits) (a : ActiveBits) : Fin 6 → Fin 2 :=
  ![b 0,b 1,a 0,a 1,a 2,a 3]

def joinLabel (p : Label 2) (q : Label 4) : Label 6 := ![p 0,p 1,q 0,q 1,q 2,q 3]

def splitBits : (Fin 6 → Fin 2) ≃ SpectatorBits × ActiveBits where
  toFun s := (![s 0,s 1],![s 2,s 3,s 4,s 5])
  invFun x := joinBits x.1 x.2
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨b,a⟩
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

theorem sum_splitBits (f : (Fin 6 → Fin 2) → ℂ) :
    (∑ s, f s) = ∑ b, ∑ a, f (joinBits b a) := by
  simpa [Fintype.sum_prod_type,splitBits] using (splitBits.symm.sum_comp f).symm

theorem operator_split (p : Label 2) (q : Label 4) (b c : SpectatorBits)
    (a d : ActiveBits) :
    operator (joinLabel p q) (joinBits b a) (joinBits c d) =
      operator p b c * operator q a d := by
  simp only [operator,tensor,joinLabel,joinBits,Fin.prod_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.succ_zero_eq_one]
  change localC (p 0) (b 0) (c 0) * (localC (p 1) (b 1) (c 1) *
    (localC (q 0) (a 0) (d 0) * (localC (q 1) (a 1) (d 1) *
    (localC (q 2) (a 2) (d 2) * (localC (q 3) (a 3) (d 3) * 1))))) =
    (localC (p 0) (b 0) (c 0) * (localC (p 1) (b 1) (c 1) * 1)) *
    (localC (q 0) (a 0) (d 0) * (localC (q 1) (a 1) (d 1) *
    (localC (q 2) (a 2) (d 2) * (localC (q 3) (a 3) (d 3) * 1))))
  ring

theorem active_action_split (Q : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ)
    (p : Label 4) (b : SpectatorBits) (a : ActiveBits) (k : Fin 2) :
    (operator (joinLabel (fun _ => 0) p) * Q) (joinBits b a) k =
      ∑ d, operator p a d * Q (joinBits b d) k := by
  rw [Matrix.mul_apply,sum_splitBits]
  simp_rw [operator_split,operator_zero]
  simp [Matrix.one_apply,ite_mul,Finset.sum_ite_eq']

theorem spectator_operator_split (p : Label 2) (b c : SpectatorBits)
    (a d : ActiveBits) :
    operator (spectatorPauli p) (joinBits b a) (joinBits c d) =
      operator p b c * (1 : Matrix ActiveBits ActiveBits ℂ) a d := by
  have h := congrFun (congrFun (@operator_zero 4) a) d
  change operator (fun _ : Fin 4 => 0) a d = _ at h
  rw [← h]
  simp only [operator,tensor,spectatorPauli,joinBits,Fin.prod_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.succ_zero_eq_one]
  change localC (p 0) (b 0) (c 0) * (localC (p 1) (b 1) (c 1) *
    (localC 0 (a 0) (d 0) * (localC 0 (a 1) (d 1) *
    (localC 0 (a 2) (d 2) * (localC 0 (a 3) (d 3) * 1))))) =
    (localC (p 0) (b 0) (c 0) * (localC (p 1) (b 1) (c 1) * 1)) *
    (localC 0 (a 0) (d 0) * (localC 0 (a 1) (d 1) *
    (localC 0 (a 2) (d 2) * (localC 0 (a 3) (d 3) * 1))))
  ring

noncomputable def Encoder.spectatorDensity (V : Encoder) (j k : Fin 2) :
    Matrix SpectatorBits SpectatorBits ℂ :=
  fun b c => ∑ a, V.tensorMatrix (joinBits b a) k * star (V.tensorMatrix (joinBits c a) j)

theorem spectator_action_split (Q : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ)
    (p : Label 2) (b : SpectatorBits) (a : ActiveBits) (k : Fin 2) :
    (operator (spectatorPauli p) * Q) (joinBits b a) k =
      ∑ c, operator p b c * Q (joinBits c a) k := by
  rw [Matrix.mul_apply,sum_splitBits]
  simp_rw [spectator_operator_split]
  simp [Matrix.one_apply,ite_mul]

theorem Encoder.spectatorDensity_trace (V : Encoder) (j k : Fin 2) (p : Label 2) :
    Matrix.trace (operator p * V.spectatorDensity j k) =
      (V.tensorMatrix.conjTranspose * operator (spectatorPauli p) * V.tensorMatrix) j k := by
  rw [Matrix.mul_assoc,Matrix.mul_apply,sum_splitBits]
  simp_rw [spectator_action_split]
  simp only [Matrix.conjTranspose_apply,Encoder.spectatorDensity,
    Matrix.trace,Matrix.diag,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem Encoder.spectatorDensity_flat (V : Encoder) (j k : Fin 2) :
    V.spectatorDensity j k = (if j=k then (1/4 : ℂ) else 0) • 1 := by
  have ht (p : Label 2) : tau (operator p * V.spectatorDensity j k) =
      if p=(fun _ => 0) then (if j=k then (1/4 : ℂ) else 0) else 0 := by
    unfold tau
    rw [V.spectatorDensity_trace,V.spectator_detection]
    split_ifs <;> simp_all [Matrix.one_apply,Matrix.zero_apply] <;> norm_num
  rw [matrix_reconstruction (V.spectatorDensity j k)]
  simp_rw [ht]
  simp [ite_smul,operator_zero]

/-- Schmidt frames are defined directly from the encoder coefficients. -/
noncomputable def Encoder.schmidtFrame (V : Encoder) (j : Fin 2) :
    Matrix ActiveBits SpectatorBits ℂ := fun a b => 2 * V.tensorMatrix (joinBits b a) j

theorem Encoder.schmidtFrame_cross (V : Encoder) (j k : Fin 2) :
    (V.schmidtFrame j).conjTranspose * V.schmidtFrame k =
      if j=k then 1 else 0 := by
  ext b c
  have h := congrFun (congrFun (V.spectatorDensity_flat j k) c) b
  change (∑ a, V.tensorMatrix (joinBits c a) k * star (V.tensorMatrix (joinBits b a) j)) =
    (if j=k then (1/4 : ℂ) else 0) * (1 : Matrix SpectatorBits SpectatorBits ℂ) c b at h
  have he : ((V.schmidtFrame j).conjTranspose * V.schmidtFrame k) b c =
      4 * V.spectatorDensity j k c b := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Encoder.schmidtFrame,
      star_mul,star_ofNat,Encoder.spectatorDensity,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  change 4 * (∑ a, V.tensorMatrix (joinBits c a) k * star (V.tensorMatrix (joinBits b a) j)) = _
  rw [h]
  by_cases hj : j=k <;> simp [hj,Matrix.one_apply,eq_comm]

def spectatorIndex : Fin 4 ≃ SpectatorBits where
  toFun b := ![![0,0],![0,1],![1,0],![1,1]] b
  invFun s := ⟨2 * (s 0).val + (s 1).val,by have := (s 0).isLt; have := (s 1).isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

noncomputable def Encoder.computationalFrames (V : Encoder) :
    Matrix ActiveBits (Sum (Fin 4) (Fin 4)) ℂ :=
  fun a c => match c with
    | Sum.inl b => V.schmidtFrame 0 a (spectatorIndex b)
    | Sum.inr b => V.schmidtFrame 1 a (spectatorIndex b)

/-- The eight frame columns, extracted from any orbit-2 encoder, are orthonormal. -/
theorem Encoder.computationalFrames_isometry (V : Encoder) :
    V.computationalFrames.conjTranspose * V.computationalFrames = 1 := by
  ext b c
  rcases b with b|b <;> rcases c with c|c
  · have h := congrFun (congrFun (V.schmidtFrame_cross 0 0) (spectatorIndex b)) (spectatorIndex c)
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Encoder.computationalFrames,
      Matrix.one_apply,spectatorIndex.injective.eq_iff] using h
  · have h := congrFun (congrFun (V.schmidtFrame_cross 0 1) (spectatorIndex b)) (spectatorIndex c)
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Encoder.computationalFrames,
      Matrix.one_apply] using h
  · have h := congrFun (congrFun (V.schmidtFrame_cross 1 0) (spectatorIndex b)) (spectatorIndex c)
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Encoder.computationalFrames,
      Matrix.one_apply] using h
  · have h := congrFun (congrFun (V.schmidtFrame_cross 1 1) (spectatorIndex b)) (spectatorIndex c)
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Encoder.computationalFrames,
      Matrix.one_apply,spectatorIndex.injective.eq_iff] using h

/-- The two four-column frames lie in the prescribed opposite parity sectors. -/
theorem Encoder.schmidtFrame_parity (V : Encoder) (j : Fin 2) :
    operator (fun _ : Fin 4 => 3) * V.schmidtFrame j =
      (if j=0 then (1 : ℂ) else -1) • V.schmidtFrame j := by
  ext a b
  have h := congrFun (congrFun V.tensor_logical (joinBits b a)) j
  change (operator (joinLabel (fun _ => 0) (fun _ => 3)) * V.tensorMatrix)
    (joinBits b a) j = _ at h
  rw [active_action_split] at h
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,Encoder.schmidtFrame]
  calc
    _ = 2 * (∑ d, operator (fun _ => 3) a d * V.tensorMatrix (joinBits b d) j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [h]; ring

end Orbit2
