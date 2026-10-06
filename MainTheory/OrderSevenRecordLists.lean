import MainTheory.OrderEightRecordLists
import MainTheory.EndpointLiftDisplays

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderSevenRecordLists

open MainTheory.OrbitRecordMultiplicity MainTheory.Generated
open MainTheory.OrderEightRecordLists

theorem seven_arithmetic (q : ℕ) (hq : 0<q) (hd : 7 ∣ q) (hb : q ≤ 9) :
    q=7 ∧ q/7=1 := by
  obtain ⟨k,hk⟩ := hd
  omega

theorem seven_lift (C : MainTheory.CodeSpec.ExactCode 6 2 3)
    (S : MainTheory.SortedForm.SortedNormalForm C) (hb : S.q ≤ 9) (hm : S.m=7) :
    S.q=7 ∧ S.q/S.m=1 := by
  rw [hm]
  exact seven_arithmetic S.q (by have h := S.two_le_q; omega) (hm ▸ S.m_dvd_q) hb

def records57 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,1,1,4,4,4],![1,3,3,3,6,6],![3,4,4,6,6,6]}

theorem checked57 : assignedAngles 57=records57 := by decide +kernel

theorem exact57 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 57 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records57 := by
  rw [← mem_assigned_iff,checked57]

def records58 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,1,2,3,3,5],![1,2,4,4,5,6],![2,2,3,3,6,6],![3,4,5,5,6,6]}

theorem checked58 : assignedAngles 59=records58 := by decide +kernel

theorem exact58 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 59 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records58 := by
  rw [← mem_assigned_iff,checked58]

def records59 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,1,5,5,5,5],![1,2,2,2,2,6],![2,5,5,5,6,6]}

theorem checked59 : assignedAngles 56=records59 := by decide +kernel

theorem exact59 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 56 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records59 := by
  rw [← mem_assigned_iff,checked59]

def records60 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,2,2,2,4,4],![1,3,3,5,5,5],![2,2,3,4,5,6],![4,4,5,5,5,6]}

theorem checked60 : assignedAngles 60=records60 := by decide +kernel

theorem exact60 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 60 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records60 := by
  rw [← mem_assigned_iff,checked60]

def records61 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,2,2,3,3,4],![1,3,4,4,5,5],![2,2,4,4,4,6],![2,3,3,3,5,6]}

theorem checked61 : assignedAngles 58=records61 := by decide +kernel

theorem exact61 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 58 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records61 := by
  rw [← mem_assigned_iff,checked61]

end MainTheory.OrderSevenRecordLists
