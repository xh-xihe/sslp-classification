import MainTheory.OrderFourNoCompletion
import MainTheory.EndpointLiftDisplays
import MainTheory.OrderEightRecordLists
import MainTheory.Generated.OrbitTableNumeric

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace MainTheory.OrderFourTableDisplays
open MainTheory.Generated MainTheory.OrderEightRecordLists

theorem lift_arithmetic (q : ℕ) (hq : 0 < q) (hd : 4 ∣ q) (hb : q ≤ 9) : q=4 ∨ q=8 := by
  obtain ⟨k,hk⟩ := hd
  omega
theorem lift (C : MainTheory.CodeSpec.ExactCode 6 2 3)
    (S : MainTheory.SortedForm.SortedNormalForm C) (hb : S.q ≤ 9) (hm : S.m=4) :
    4 ∣ S.q ∧ S.q ≤ 9 ∧ (S.q=4 ∨ S.q=8) := by
  have hd : 4 ∣ S.q := by simpa only [hm] using S.m_dvd_q
  exact ⟨hd,hb,lift_arithmetic S.q (by have h := S.two_le_q; omega) hd hb⟩

def row : Fin 10 → Fin 66 := ![24,25,26,27,28,29,30,31,61,62]
def q : Fin 10 → ℕ := ![4,4,4,4,4,4,4,4,8,8]
def angle : Fin 10 → Fin 6 → ℕ :=
  ![![0,1,1,1,1,1],![0,1,1,2,2,3],![1,1,1,1,1,1],![1,1,1,1,1,2],
    ![1,1,1,1,2,2],![1,1,1,1,2,3],![1,1,1,2,2,2],![1,1,2,2,2,3],
    ![1,1,1,5,5,5],![1,1,2,4,5,5]]
def dimension : Fin 10 → ℕ := ![6,12,5,0,8,9,9,9,0,1]
theorem displayed_data : ∀ i,OrbitTableNumericData.paperQ (row i)=q i ∧
    OrbitTableNumericData.paperM (row i)=4 ∧
    OrbitTableNumericData.paperAngle (row i)=angle i ∧
    OrbitTableNumericData.paperDimension (row i)=dimension i := by decide +kernel
theorem exhaustive : ∀ k : Fin 66,(FiniteOrbitBase.keyAt k).m=4 ↔
    ∃ i : Fin 10,OrbitTableRecords.paperKey (row i)=k := by decide +kernel
theorem row_injective : Function.Injective row := by decide +kernel
theorem no_completion (i : Fin 10) :
    MainTheory.CubeCompletionTransport.NoCompletion
      (FiniteOrbitBase.keyAt (OrbitTableRecords.paperKey (row i))).fibers := by
  apply MainTheory.OrderFourNoCompletion.noCompletion_of_orderFour
  exact (exhaustive _).2 ⟨i,rfl⟩

def records26 : Finset MainTheory.OuterEnumeration.Angle6 := {![0,1,1,2,2,3],![0,2,2,3,3,3]}
theorem records26_checked : assignedAngles 25=records26 := by decide +kernel
theorem records26_exact (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,MainTheory.OrbitRecordMultiplicity.InOrbit 25 r ∧
      (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records26 := by
  rw [← mem_assigned_iff,records26_checked]
end MainTheory.OrderFourTableDisplays
