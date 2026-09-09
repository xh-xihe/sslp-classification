import MainTheory.Orbit36ExpectationSign

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MainTheory.Orbit36ExceptionalMasks

open SixQubit.Orbit36 MainTheory.Orbit36ExpectationSign

def exceptional (i : Fin 4) : SS.BitString 6 :=
  fun j => decide (j.val = i.val ∨ 4 ≤ j.val)

theorem mask_classification : ∀ P : SS.PauliString 6,
    P.wt = 3 → Even (firstZCount P + lastNontrivialCount P) →
      (∃ i : Fin 4, P.x = exceptional i) ∨
        (S0.filter (fun x => SS.bxor x P.x ∈ S0)) = ∅ := by decide +kernel

theorem exceptional_incidences : ∀ i : Fin 4,
    (S0.filter (fun x => SS.bxor x (exceptional i) ∈ S0)).card = 6 := by decide +kernel

end MainTheory.Orbit36ExceptionalMasks
