import Mathlib

/-!
Finite covers by continuous images of convex sets have only finitely many
connected components. This elementary alternative to Lie subgroup theory is
useful for torus stabilizers: bounded angle lifts split into finitely many
integer level sets of linear equations.
-/

namespace MainTheory.FiniteConnectedCover

open Set

theorem finite_components_of_label {X I : Type*} [TopologicalSpace X] [Finite I]
    (label : X → I)
    (h : ∀ x y, label x = label y →
      ConnectedComponents.mk x = ConnectedComponents.mk y) :
    Finite (ConnectedComponents X) := by
  classical
  apply Finite.of_injective (fun c : ConnectedComponents X => label (Quotient.out c))
  intro c d hcd
  have he := h (Quotient.out c) (Quotient.out d) hcd
  simpa only [ConnectedComponents.mk, Quotient.out_eq] using he

theorem finite_components_of_preconnected_cover {X I : Type*}
    [TopologicalSpace X] [Finite I] (S : I → Set X)
    (hs : ∀ i, IsPreconnected (S i)) (hcover : ∀ x, ∃ i, x ∈ S i) :
    Finite (ConnectedComponents X) := by
  classical
  choose label hl using hcover
  apply finite_components_of_label label
  intro x y hxy
  apply ConnectedComponents.coe_eq_coe'.2
  apply (hs (label y)).subset_connectedComponent (hl y)
  simpa only [← hxy] using hl x

theorem finite_components_of_convex_images {X I V : Type*}
    [TopologicalSpace X] [Finite I]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    (S : I → Set V) (f : ∀ i, S i → X)
    (hconvex : ∀ i, Convex ℝ (S i)) (hcont : ∀ i, Continuous (f i))
    (hcover : ∀ x, ∃ i a, f i a = x) : Finite (ConnectedComponents X) := by
  apply finite_components_of_preconnected_cover (fun i => Set.range (f i))
  · intro i
    haveI : PreconnectedSpace (S i) := Subtype.preconnectedSpace (hconvex i).isPreconnected
    exact isPreconnected_range (hcont i)
  · intro x
    obtain ⟨i, a, ha⟩ := hcover x
    exact ⟨i, a, ha⟩

end MainTheory.FiniteConnectedCover
