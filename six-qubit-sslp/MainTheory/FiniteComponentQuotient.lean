import Mathlib

namespace MainTheory.FiniteComponentQuotient

theorem quotient_eq_of_component_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {x y : G}
    (h : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    (QuotientGroup.mk x : G ⧸ Subgroup.connectedComponentOfOne G) = QuotientGroup.mk y := by
  apply QuotientGroup.eq.mpr
  have hy : y ∈ connectedComponent x :=
    ConnectedComponents.coe_eq_coe'.mp h.symm
  have him := Continuous.image_connectedComponent_subset
    (continuous_const.mul continuous_id : Continuous (fun z : G => x⁻¹ * z)) x
  have hm := him (Set.mem_image_of_mem _ hy)
  simpa [Subgroup.connectedComponentOfOne] using hm

theorem finite_component_quotient {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Finite (ConnectedComponents G)] :
    Finite (G ⧸ Subgroup.connectedComponentOfOne G) := by
  classical
  let f : ConnectedComponents G → G ⧸ Subgroup.connectedComponentOfOne G :=
    fun c => QuotientGroup.mk (Quotient.out c)
  apply Finite.of_surjective f
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    refine ⟨ConnectedComponents.mk x, ?_⟩
    apply quotient_eq_of_component_eq
    exact Quotient.out_eq _

end MainTheory.FiniteComponentQuotient
