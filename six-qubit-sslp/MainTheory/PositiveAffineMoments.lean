import MainTheory.Covariance

/-! Equal positive affine-square moments for arbitrary finite real point sets. -/
namespace MainTheory.PositiveAffineMoments

open scoped BigOperators
noncomputable section
variable {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]

theorem zero_transfer (p : α → ℝ) (r : β → ℝ)
    (pt : α → Fin n → ℝ) (qt : β → Fin n → ℝ)
    (hr : ∀ y, 0 < r y)
    (hs : ∀ f : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      (∑ x, p x * (f (pt x)) ^ 2) = ∑ y, r y * (f (qt y)) ^ 2)
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (hf : ∀ x, f (pt x) = 0) :
    ∀ y, f (qt y) = 0 := by
  have hz : (∑ y, r y * (f (qt y)) ^ 2) = 0 := by rw [← hs f]; simp [hf]
  intro y
  have hn : ∀ z ∈ Finset.univ, 0 ≤ r z * (f (qt z)) ^ 2 :=
    fun z _ => mul_nonneg (hr z).le (sq_nonneg _)
  have he := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz y (Finset.mem_univ y)
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left (hr y).ne')

theorem affineSpan_le [Nonempty α] (p : α → ℝ) (r : β → ℝ)
    (pt : α → Fin n → ℝ) (qt : β → Fin n → ℝ)
    (hr : ∀ y, 0 < r y)
    (hs : ∀ f : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      (∑ x, p x * (f (pt x)) ^ 2) = ∑ y, r y * (f (qt y)) ^ 2) :
    affineSpan ℝ (Set.range qt) ≤ affineSpan ℝ (Set.range pt) := by
  apply _root_.affineSpan_le.2
  rintro y ⟨b, rfl⟩
  let a0 : α := Classical.choice inferInstance
  have ha0 : pt a0 ∈ Set.range pt := Set.mem_range_self a0
  have hv : qt b - pt a0 ∈ vectorSpan ℝ (Set.range pt) := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (vectorSpan ℝ (Set.range pt)) (qt b - pt a0)).mp
    intro phi hphi
    let f : (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
      phi.toAffineMap - AffineMap.const ℝ (Fin n → ℝ) (phi (pt a0))
    have hf : ∀ a, f (pt a) = 0 := by
      intro a
      have hsub : pt a - pt a0 ∈ vectorSpan ℝ (Set.range pt) := by
        rw [vectorSpan_eq_span_vsub_set_right ℝ ha0]
        apply Submodule.subset_span
        exact ⟨pt a, Set.mem_range_self a, rfl⟩
      have hz := (Submodule.mem_dualAnnihilator phi).mp hphi _ hsub
      simpa [f, map_sub] using hz
    have hy := zero_transfer p r pt qt hr hs f hf b
    simpa [f, map_sub] using hy
  have hanchor : pt a0 ∈ affineSpan ℝ (Set.range pt) := subset_affineSpan ℝ _ ha0
  simpa using vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hanchor hv

theorem affineSpan_eq [Nonempty α] [Nonempty β] (p : α → ℝ) (r : β → ℝ)
    (pt : α → Fin n → ℝ) (qt : β → Fin n → ℝ)
    (hp : ∀ x, 0 < p x) (hr : ∀ y, 0 < r y)
    (hs : ∀ f : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      (∑ x, p x * (f (pt x)) ^ 2) = ∑ y, r y * (f (qt y)) ^ 2) :
    affineSpan ℝ (Set.range pt) = affineSpan ℝ (Set.range qt) :=
  le_antisymm (affineSpan_le r p qt pt hp (fun f => (hs f).symm))
    (affineSpan_le p r pt qt hr hs)

end
end MainTheory.PositiveAffineMoments
