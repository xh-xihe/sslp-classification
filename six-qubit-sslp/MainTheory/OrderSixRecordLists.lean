import MainTheory.OrderEightRecordLists
import MainTheory.EndpointLiftDisplays

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderSixRecordLists

open MainTheory.OrbitRecordMultiplicity MainTheory.Generated
open MainTheory.OrderEightRecordLists

theorem six_arithmetic (q : ℕ) (hq : 0<q) (hd : 6 ∣ q) (hb : q ≤ 9) :
    q=6 ∧ q/6=1 := by
  obtain ⟨k,hk⟩ := hd
  omega

theorem six_lift (C : MainTheory.CodeSpec.ExactCode 6 2 3)
    (S : MainTheory.SortedForm.SortedNormalForm C) (hb : S.q ≤ 9) (hm : S.m=6) :
    S.q=6 ∧ S.q/S.m=1 := by
  rw [hm]
  exact six_arithmetic S.q (by have h := S.two_le_q; omega) (by simpa only [hm] using S.m_dvd_q) hb

def records53 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,1,1,3,3,4],![1,2,3,3,5,5],![3,3,4,5,5,5]}

theorem checked53 : assignedAngles 53=records53 := by decide +kernel

theorem exact53 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 53 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records53 := by
  rw [← mem_assigned_iff,checked53]

def records54 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,1,2,2,2,5],![1,1,4,4,4,5],![2,4,4,5,5,5]}

theorem checked54 : assignedAngles 52=records54 := by decide +kernel

theorem exact54 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 52 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records54 := by
  rw [← mem_assigned_iff,checked54]

def records55 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,1,2,2,3,4],![1,2,3,4,4,5],![2,2,2,3,5,5],![3,4,4,4,5,5]}

theorem checked55 : assignedAngles 54=records55 := by decide +kernel

theorem exact55 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 54 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records55 := by
  rw [← mem_assigned_iff,checked55]

def records56 : Finset MainTheory.OuterEnumeration.Angle6 := {![1,2,2,2,3,3],![1,3,3,4,4,4],![2,2,3,3,4,5]}

theorem checked56 : assignedAngles 55=records56 := by decide +kernel

theorem exact56 (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 55 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ records56 := by
  rw [← mem_assigned_iff,checked56]

end MainTheory.OrderSixRecordLists
