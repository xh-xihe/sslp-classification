import MainTheory.PaperSupplementaryNoGo
import MainTheory.SupplementaryImageStatus

/-! The SI's exact order-two remainder, read from the actual 66-key directory.
The existence classification and the weight-enumerator-image status are separate
statements. Unknown image converses for paper orbits 1 and 4 are not asserted.
-/

namespace MainTheory.SupplementaryOrderTwoReduction

open MainTheory.FiniteOrbitPipeline
open MainTheory.Generated.FiniteOrbitBase
open MainTheory.CubeCompletionTransport

set_option maxRecDepth 20000

def orderTwoKeys : Finset (Fin 66) := Finset.univ.filter fun k => (keyAt k).m = 2

def retainedPaperIds : Finset ℕ := {1,2,3,4,10,11,16,21,22,23,45}

def excludedPaperIds : Finset ℕ := {12,13,14,15,17,18,19,20,24,41,42,43,44,46}

theorem order_two_count : orderTwoKeys.card = 25 := by decide

theorem order_two_partition : orderTwoKeys.image paperOrbitId =
    retainedPaperIds ∪ excludedPaperIds ∧
    Disjoint retainedPaperIds excludedPaperIds ∧
    retainedPaperIds.card = 11 ∧ excludedPaperIds.card = 14 := by
  decide

theorem exact_reduction (k : Fin 66) (hm : (keyAt k).m = 2) :
    HasCompletion (keyAt k).fibers ↔ paperOrbitId k ∈ retainedPaperIds := by
  rw [MainTheory.PaperSupplementaryNoGo.hasCompletion_iff_paperOrbitId]
  revert hm
  revert k
  decide

theorem excluded_no_completion (k : Fin 66)
    (hk : paperOrbitId k ∈ excludedPaperIds) : NoCompletion (keyAt k).fibers := by
  apply MainTheory.PaperSupplementaryNoGo.no_completion_of_paperOrbitId k
  revert hk
  revert k
  decide

theorem image_scope : retainedPaperIds ∩ MainTheory.SupplementaryImageStatus.provedPaperIds =
      ({2,3,10,11,16,21,22,23,45} : Finset ℕ) ∧
    retainedPaperIds \ MainTheory.SupplementaryImageStatus.provedPaperIds =
      MainTheory.SupplementaryImageStatus.pendingPaperIds := by
  decide

end MainTheory.SupplementaryOrderTwoReduction
