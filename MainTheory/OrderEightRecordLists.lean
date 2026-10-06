import MainTheory.OrbitRecordMultiplicity

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.OrderEightRecordLists

open MainTheory.OrbitRecordMultiplicity MainTheory.Generated

def A : Finset MainTheory.OuterEnumeration.Angle6 :=
  {![1,1,3,3,3,6],![1,2,5,5,5,7],![2,3,3,3,7,7],![3,5,5,6,7,7]}

def B : Finset MainTheory.OuterEnumeration.Angle6 :=
  {![1,2,2,3,4,5],![1,3,4,5,6,6],![2,2,4,5,5,7],
    ![2,3,3,4,6,7],![4,5,5,6,6,7]}

def assignedAngles (k : Fin 66) : Finset MainTheory.OuterEnumeration.Angle6 :=
  (Finset.univ.filter fun i : Fin 216 => OrbitTableRecords.key i=k).image
    (fun i => (FinitePairRecordData.generatedRecord (OrbitTableRecords.record i)).a)

theorem A_checked : assignedAngles 63=A := by decide +kernel
theorem B_checked : assignedAngles 64=B := by decide +kernel

theorem mem_assigned_iff (k : Fin 66) (a : MainTheory.OuterEnumeration.Angle6) :
    a ∈ assignedAngles k ↔ ∃ r,InOrbit k r ∧ (FinitePairRecordData.generatedRecord r).a=a := by
  classical
  simp only [assignedAngles,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,ha⟩
    exact ⟨OrbitTableRecords.record i,(candidate_inOrbit_iff i k).2 hi,ha⟩
  · rintro ⟨r,hr,ha⟩
    obtain ⟨i,rfl⟩ := (records_complete r).1 hr.1
    exact ⟨i,(candidate_inOrbit_iff i k).1 hr,ha⟩

theorem orbit_A_exact (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 63 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ A := by
  rw [← mem_assigned_iff,A_checked]

theorem orbit_B_exact (a : MainTheory.OuterEnumeration.Angle6) :
    (∃ r,InOrbit 64 r ∧ (FinitePairRecordData.generatedRecord r).a=a) ↔ a ∈ B := by
  rw [← mem_assigned_iff,B_checked]

end MainTheory.OrderEightRecordLists
