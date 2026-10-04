import Orbit2.Reconstruction

namespace Orbit2.Quartic
open scoped BigOperators
set_option maxHeartbeats 0

noncomputable def blockCoordinate : (Σ b : Fin 111, Fin (reconstructedBlocks b).n) → Fin 528 :=
  fun p => (reconstructedBlocks p.1).indices p.2

theorem blockCoordinate_bijective : Function.Bijective blockCoordinate := by
  constructor
  · rintro ⟨b,i⟩ ⟨c,j⟩ h
    change (reconstructedBlocks b).indices i = (reconstructedBlocks c).indices j at h
    have hb := (coordinate_unique b i).1
    have hc := (coordinate_unique c j).1
    have hbc : b=c := by rw [h,hc] at hb; exact hb.symm
    subst c
    have hi := (coordinate_unique b i).2
    have hj := (coordinate_unique b j).2
    have hij : i=j := by
      apply Fin.ext
      rw [h,hj] at hi
      exact hi.symm
    subst j
    rfl
  · intro r
    exact ⟨⟨coordinateOwner r,coordinateIndex r⟩,coordinate_covered r⟩

noncomputable def blockCoordinateEquiv : (Σ b : Fin 111, Fin (reconstructedBlocks b).n) ≃ Fin 528 :=
  Equiv.ofBijective blockCoordinate blockCoordinate_bijective

theorem sum_coordinates (f : Fin 528 → ℂ) :
    (∑ r, f r) = ∑ b : Fin 111, ∑ i : Fin (reconstructedBlocks b).n,
      f ((reconstructedBlocks b).indices i) := by
  calc
    _ = ∑ p, f (blockCoordinateEquiv p) := (Equiv.sum_comp blockCoordinateEquiv f).symm
    _ = _ := by rw [Fintype.sum_sigma]; rfl

noncomputable def fullCoefficientEnergy (z : Fin 528 → ℂ) : ℂ :=
  ∑ r, ∑ c, star (z r) * z c * (twiceCoefficient r c : ℂ)

theorem fullCoefficientEnergy_blocks (z : Fin 528 → ℂ) :
    fullCoefficientEnergy z =
      ∑ b : Fin 111, ∑ i : Fin (reconstructedBlocks b).n,
        ∑ j : Fin (reconstructedBlocks b).n,
          star (z ((reconstructedBlocks b).indices i)) * z ((reconstructedBlocks b).indices j) *
            ((reconstructedBlocks b).expected i j : ℂ) := by
  unfold fullCoefficientEnergy
  rw [sum_coordinates]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_coordinates]
  rw [Finset.sum_eq_single b]
  · apply Finset.sum_congr rfl
    intro j _
    rw [(reconstructedBlocks b).coefficients]
  · intro c _ hcb
    apply Finset.sum_eq_zero
    intro j _
    rw [cross_block_zero b c hcb.symm]
    simp
  · simp

theorem fullCoefficientEnergy_eq_certificate (z : Fin 528 → ℂ) :
    (fullCoefficientEnergy z).re / 24 = familyEnergy checkedBlocks z := by
  rw [← reconstructed_polynomial_eq_certificate]
  unfold reconstructedEnergy
  rw [fullCoefficientEnergy_blocks,Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [complexEnergy_eq_re]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply]
  push_cast
  ring

end Orbit2.Quartic
