import MainTheory.PositiveAffineMoments

/-! Coordinate-form affine functions in the manuscript's geometric lemma. -/
namespace MainTheory.PositiveAffineFunctionExpansion

open scoped BigOperators
noncomputable section
variable {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]

theorem expansion (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (x : Fin n → ℝ) :
    f x = f 0 + ∑ j, f.linear (Pi.single j 1) * x j := by
  have hmap := f.map_vadd (0 : Fin n → ℝ) x
  simp only [vadd_eq_add, add_zero] at hmap
  rw [hmap, LinearMap.pi_apply_eq_sum_univ f.linear x, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun k : Fin n => if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  rw [he]
  simp [smul_eq_mul, mul_comm]

theorem affineSpan_eq_of_coordinate_squares [Nonempty α] [Nonempty β]
    (p : α → ℝ) (r : β → ℝ) (pt : α → Fin n → ℝ) (qt : β → Fin n → ℝ)
    (hp : ∀ x, 0 < p x) (hr : ∀ y, 0 < r y)
    (hs : ∀ (c : ℝ) (w : Fin n → ℝ),
      (∑ x, p x * (c + ∑ j, w j * pt x j) ^ 2) =
        ∑ y, r y * (c + ∑ j, w j * qt y j) ^ 2) :
    affineSpan ℝ (Set.range pt) = affineSpan ℝ (Set.range qt) := by
  apply MainTheory.PositiveAffineMoments.affineSpan_eq p r pt qt hp hr
  intro f
  calc
    (∑ x, p x * (f (pt x)) ^ 2) =
        ∑ x, p x * (f 0 + ∑ j, f.linear (Pi.single j 1) * pt x j) ^ 2 :=
      Finset.sum_congr rfl (fun x _ =>
        congrArg (fun u : ℝ => p x * u ^ 2) (expansion f (pt x)))
    _ = ∑ y, r y * (f 0 + ∑ j, f.linear (Pi.single j 1) * qt y j) ^ 2 :=
      hs (f 0) (fun j => f.linear (Pi.single j 1))
    _ = ∑ y, r y * (f (qt y)) ^ 2 :=
      Finset.sum_congr rfl (fun y _ =>
        congrArg (fun u : ℝ => r y * u ^ 2) (expansion f (qt y)).symm)

end
end MainTheory.PositiveAffineFunctionExpansion
