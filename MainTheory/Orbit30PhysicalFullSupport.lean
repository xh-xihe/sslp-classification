import MainTheory.Orbit30PhysicalHafnians
import MainTheory.Orbit30FullSupport
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit30PhysicalFullSupport
open MainTheory.Orbit30PhysicalRows MainTheory.Orbit30PhysicalGraph
open MainTheory.Orbit30PhysicalHafnians MainTheory.Orbit30FullSupport
open SixQubit.Orbit30
open scoped BigOperators Matrix
noncomputable section
variable (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
include hc hd hnc hnd hkl in
theorem actual_point_vector_nonzero : pointC c≠0 := by
  have h := (physicalData c d hc hd hnc hnd hkl).total_point
  change (∑ i,Complex.normSq (pointC c i))=3/8 at h
  intro hz
  rw [hz] at h
  norm_num at h
include hc hd hnc hnd hkl in
theorem actual_matrix_kernel : (edgeMatrix c).mulVec (pointC c)=0 := by
  funext i
  change (∑ j,edgeC c i j*pointC c j)=0
  simpa only [mul_comm] using bilinear_row c d hc hd hnc hnd hkl i
include hc hd hnc hnd hkl in
theorem actual_full_support_no_go (he : ∀ i j,i≠j → edgeC c i j≠0) : False := by
  have hdet := full_hafnian_det_ne_zero (edgeMatrix c) (edge_symmetric c)
    (by intro i; simp [edgeMatrix,edgeC])
    (he ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide))
    (he ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide))
    (he ⟨1,by decide⟩ ⟨2,by decide⟩ (by decide))
    (he ⟨3,by decide⟩ ⟨4,by decide⟩ (by decide))
    (actual_hafnians c d hc hd hnc hnd hkl)
  exact actual_point_vector_nonzero c d hc hd hnc hnd hkl
    (Matrix.eq_zero_of_mulVec_eq_zero hdet (actual_matrix_kernel c d hc hd hnc hnd hkl))
end
end MainTheory.Orbit30PhysicalFullSupport
