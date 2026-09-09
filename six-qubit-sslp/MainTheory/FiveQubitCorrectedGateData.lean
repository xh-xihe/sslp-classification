import MainTheory.FiveQubitCitedGateData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.FiveQubitCorrectedGateData

open SixQubit.Realize MainTheory.FiveQubitPerfectCore
open MainTheory.ExactZQFinite MainTheory.FiveQubitCitedGateData

def Tcorrected : Fin 2 → Fin 2 → ZQ :=
  !![z8 0 0 0 0 (-1) 0 0 0, z8 1 0 0 0 0 0 0 0;
     z8 0 0 0 0 1 0 0 0, z8 1 0 0 0 0 0 0 0]
def correctedKernel (x y : Fin 32) : ZQ := ZQ.mul
  (prod 4 (fun j => Tcorrected (index (bits x j.castSucc)) (index (bits y j.castSucc))))
  (D (index (bits x 4)) (index (bits y 4)))

def logical : Fin 2 → Fin 2 → ZQ :=
  ![![z8 (-4) 0 0 0 4 0 0 0,
    z8 4 0 0 0 4 0 0 0],
  ![z8 (-4) 0 0 0 4 0 0 0,
    z8 (-4) 0 0 0 (-4) 0 0 0]]

theorem corrected_checked : ∀ i x,
    sum 32 (fun y => ZQ.mul (correctedKernel x y) (rawWord i y)) =
    sum 2 (fun j => ZQ.mul (logical j i) (rawWord j x)) := by decide

end MainTheory.FiveQubitCorrectedGateData
