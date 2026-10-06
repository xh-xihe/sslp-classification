import Mathlib

namespace MainTheory.FiniteImageComponents

theorem finite_range_of_label {X Y I : Type*} [Finite I]
    (f : X → Y) (label : X → I)
    (h : ∀ x y, label x = label y → f x = f y) : (Set.range f).Finite := by
  classical
  let pick (a : Set.range f) : X := a.property.choose
  have hp (a : Set.range f) : f (pick a) = a.val := a.property.choose_spec
  haveI : Finite (Set.range f) := Finite.of_injective
    (fun a : Set.range f => label (pick a)) (by
      intro a b hab
      apply Subtype.ext
      exact (hp a).symm.trans ((h (pick a) (pick b) hab).trans (hp b)))
  exact Set.toFinite _

theorem constant_on_component {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space Y] (f : X → Y) (hc : Continuous f)
    (hf : (Set.range f).Finite) {x y : X} (hy : y ∈ connectedComponent x) : f y = f x := by
  classical
  letI : Finite (Set.range f) := hf.fintype.finite
  let g : X → Set.range f := fun x => ⟨f x, x, rfl⟩
  have hg : Continuous g := hc.subtype_mk _
  have hm := Set.mem_image_of_mem g hy
  rw [hg.image_connectedComponent_eq_singleton x] at hm
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp hm)

end MainTheory.FiniteImageComponents
