import MainTheory.CompletionCodeBridge
import MainTheory.QuantumSingleton

namespace MainTheory.CompletionExactDistance

theorem not_distance_four {F : MainTheory.CubeAction.FiberPair 6}
    (W : MainTheory.CubeCompletionTransport.Completion F) :
    ¬ SS.HasDistance W.states 4 := by
  intro h
  let C : MainTheory.CodeSpec.ExactCode 6 2 4 := {
    positiveRank := by decide
    frame := MainTheory.CompletionCodeBridge.frame W
    hasDistance := h
  }
  have hd := MainTheory.QuantumSingleton.six_qubit_distance_le_three C
  omega

end MainTheory.CompletionExactDistance
