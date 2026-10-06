import MainTheory.CubeCompletionTransport
import MainTheory.CodeSpec

/-! # Actual completions supply orthonormal exact-code frames

Normalization and genuine KL detection of the identity already force the
off-diagonal inner products to vanish. No disjoint-support assumption is
needed to enter the existing local-unitary and projector libraries.
-/

namespace MainTheory.CompletionCodeBridge

open MainTheory.CubeCompletionTransport MainTheory.CodeSpec

noncomputable section
variable {n : ℕ} {F : MainTheory.CubeAction.FiberPair n}

def identity : SS.PauliString n := ⟨fun _ => false, fun _ => false⟩

theorem identity_act (v : SS.State n ℂ) : SS.pauliAct identity v = v := by
  funext s
  simp [SS.pauliAct, identity, SS.PauliString.numY, SS.bdot, SS.bxor, SS.signC]

theorem identity_weight : (identity (n := n)).wt = 0 := by
  simp [identity, SS.PauliString.wt]

theorem orthonormal (W : Completion F) (j k : Fin 2) :
    SS.innerC (W.states j) (W.states k) = if j = k then 1 else 0 := by
  obtain ⟨c, hc⟩ := W.hasDistance identity (by rw [identity_weight]; decide)
  simp only [identity_act] at hc
  have h00 := hc 0 0
  rw [W.normalized, if_pos rfl] at h00
  rw [← h00] at hc
  exact hc j k

def frame (W : Completion F) : OrthonormalFrame n 2 where
  vec := W.states
  orthonormal := orthonormal W

def code (W : Completion F) : ExactCode n 2 3 where
  positiveRank := by decide
  frame := frame W
  hasDistance := W.hasDistance

end
end MainTheory.CompletionCodeBridge
