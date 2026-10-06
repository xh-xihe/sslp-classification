import MainTheory.OrderSixSupportDisplays
import MainTheory.FlipCharacterObstruction

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.OrderSix55IncidenceLists
open MainTheory.OrderSixSupportDisplays MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit55 (S0 S1)

def pairs1 : Fin 6 → Fin 11 × Fin 11 := ![(7,1),(10,2),(9,3),(1,7),(3,9),(2,10)]
def pairs2 : Fin 6 → Fin 11 × Fin 11 := ![(8,1),(10,4),(9,5),(1,8),(5,9),(4,10)]
def pairs3 : Fin 6 → Fin 11 × Fin 11 := ![(1,0),(0,1),(5,2),(4,3),(3,4),(2,5)]
theorem list1 :
    Finset.univ.image (fun k => top55 (pairs1 k).2)=incidenceSet S0 S1 (bits 10) ∧
    (∀ k,SS.bxor (top55 (pairs1 k).2) (bits 10)=bottom55 (pairs1 k).1) := by decide +kernel
theorem list2 :
    Finset.univ.image (fun k => top55 (pairs2 k).2)=incidenceSet S0 S1 (bits 6) ∧
    (∀ k,SS.bxor (top55 (pairs2 k).2) (bits 6)=bottom55 (pairs2 k).1) := by decide +kernel
theorem list3 :
    Finset.univ.image (fun k => top55 (pairs3 k).2)=incidenceSet S0 S1 (bits 3) ∧
    (∀ k,SS.bxor (top55 (pairs3 k).2) (bits 3)=bottom55 (pairs3 k).1) := by decide +kernel
end MainTheory.OrderSix55IncidenceLists
