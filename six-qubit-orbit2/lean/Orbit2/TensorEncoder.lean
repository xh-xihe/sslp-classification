import Orbit2.HilbertBridge

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.HilbertBridge

def decode {n : ℕ} (p : Label n) : SS.PauliString n :=
  ⟨fun i => decide (p i = 1 ∨ p i = 2), fun i => decide (p i = 2 ∨ p i = 3)⟩

theorem label_decode {n : ℕ} (p : Label n) : label (decode p) = p := by
  have h : ∀ a : Fin 4, labelSite (decide (a=1 ∨ a=2)) (decide (a=2 ∨ a=3)) = a := by
    decide +kernel
  funext i
  exact h _

def pauliEquiv (n : ℕ) : SS.PauliString n ≃ Label n where
  toFun := label
  invFun := decode
  left_inv p := label_injective (label_decode (label p))
  right_inv := label_decode

def Encoder.tensorMatrix (V : Encoder) : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ :=
  fun s j => V.psi j ((bitsEquiv 6).symm s)

theorem Encoder.tensor_words (V : Encoder) : words V.tensorMatrix = V.psi := by
  funext j x
  simp [words,Encoder.tensorMatrix]

theorem Encoder.tensor_isometry (V : Encoder) : V.tensorMatrix.conjTranspose * V.tensorMatrix = 1 := by
  ext j k
  have h := compression V.tensorMatrix (identityPauli 6) j k
  rw [V.tensor_words,pauliAct_identity] at h
  have hi : label (identityPauli 6) = (fun _ => 0) := by funext i; rfl
  rw [hi,operator_zero,Matrix.mul_one,V.orthonormal] at h
  simpa [Matrix.one_apply] using h.symm

theorem Encoder.tensor_KL (V : Encoder) (p : Label 6)
    (hp : (∑ i, if p i = 0 then 0 else 1 : ℕ) ≤ 2) :
    ∃ c : ℂ, V.tensorMatrix.conjTranspose * operator p * V.tensorMatrix = c • 1 := by
  have hw : (decode p).wt ≤ 2 := by
    have hw := label_weight (decode p)
    rw [label_decode] at hw
    omega
  obtain ⟨c,hc⟩ := V.detects (decode p) hw
  refine ⟨c, ?_⟩
  ext j k
  have h := compression V.tensorMatrix (decode p) j k
  rw [V.tensor_words,label_decode,hc] at h
  simpa [Matrix.smul_apply,Matrix.one_apply] using h.symm

theorem Encoder.tensor_logical (V : Encoder) :
    operator ![0,0,3,3,3,3] * V.tensorMatrix =
      fun s j => (if j=0 then 1 else -1) * V.tensorMatrix s j := by
  ext s j
  let p : SS.PauliString 6 := ⟨fun _ => false, ![false,false,true,true,true,true]⟩
  have hl : label p = ![0,0,3,3,3,3] := by funext i; fin_cases i <;> rfl
  have h := pauli_action p (V.psi j) ((bitsEquiv 6).symm s)
  rw [hl,V.logicalZ j] at h
  simpa [Encoder.tensorMatrix,Matrix.mul_apply] using h

end Orbit2
