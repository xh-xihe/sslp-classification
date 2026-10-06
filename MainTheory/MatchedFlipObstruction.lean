import MainTheory.FlipCharacterObstruction

/-! Full-rank matched flip criteria, including the supplementary ten-column
matrix of X/Y rows.  Normalization and matched endpoint probabilities are
physical amplitude statements, not independent linear-system assumptions. -/

namespace MainTheory.FlipCharacter
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

variable {n N : ℕ}

def matchedTop (e : SS.BitString n) (x : Fin N → SS.BitString n) :
    Fin N → SS.BitString n := fun r => SS.bxor (x r) e

theorem matchedTop_injective (e : SS.BitString n) (x : Fin N → SS.BitString n)
    (hx : Function.Injective x) : Function.Injective (matchedTop e x) :=
  (SS.bxorEquiv e).injective.comp hx

theorem complete_matching_incidence (e : SS.BitString n) (x : Fin N → SS.BitString n) :
    Finset.univ.image (matchedTop e x) =
      incidenceSet (Finset.univ.image x) (Finset.univ.image (matchedTop e x)) e := by
  classical
  symm
  apply Finset.filter_eq_self.mpr
  intro y hy
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, (SS.bxor_bxor_cancel (x r) e).symm⟩

/-- On a complete matching, equal endpoint magnitudes convert vanishing
incidence products into the zero logical state, contradicting normalization. -/
theorem full_rank_matched_obstruction
    (c d : SS.State n ℂ) (e : SS.BitString n) (x z : Fin N → SS.BitString n)
    (hx : Function.Injective x)
    (hc : ∀ v, v ∉ Finset.univ.image x → c v = 0)
    (hd : ∀ v, v ∉ Finset.univ.image (matchedTop e x) → d v = 0)
    (hnc : SS.innerC c c = 1)
    (hm : ∀ r, Complex.normSq (c (x r)) = Complex.normSq (d (matchedTop e x r)))
    (hw : ∀ a, (⟨e,z a⟩ : SS.PauliString n).wt ≤ 2)
    (hdet : (restrictedCharacterMatrix z (matchedTop e x)).det ≠ 0) :
    ¬ SS.HasDistance ![c,d] 3 := by
  intro hdist
  have hz := monomials_zero_of_det_ne_zero _ _ c d hc hd hdist e z (matchedTop e x)
    (matchedTop_injective e x hx) (complete_matching_incidence e x) hw hdet
  have hall : ∀ r, c (x r) = 0 := by
    intro r
    have hnorm := normSq_incidenceMonomial c d e (matchedTop e x r)
    rw [hz r, Complex.normSq_zero] at hnorm
    change 0 = Complex.normSq (c (SS.bxor (SS.bxor (x r) e) e)) *
      Complex.normSq (d (matchedTop e x r)) at hnorm
    rw [SS.bxor_bxor_cancel, ← hm r] at hnorm
    apply Complex.normSq_eq_zero.mp
    nlinarith [Complex.normSq_nonneg (c (x r))]
  have hc0 : c = 0 := by
    funext v
    by_cases hv : v ∈ Finset.univ.image x
    · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
      exact hall r
    · exact hc v hv
  rw [hc0] at hnc
  simp [SS.innerC] at hnc

/-- The ten masks of the displayed character rows:
`1, χ_i, χ_j0, χ_(i,j0), ..., χ_j3, χ_(i,j3)`. -/
def matchedTenDressings (i : Fin n) (j : Fin 4 → Fin n) : Fin 10 → SS.BitString n :=
  ![fun _ => false, SS.stdBasis i,
    SS.stdBasis (j 0), SS.bxor (SS.stdBasis i) (SS.stdBasis (j 0)),
    SS.stdBasis (j 1), SS.bxor (SS.stdBasis i) (SS.stdBasis (j 1)),
    SS.stdBasis (j 2), SS.bxor (SS.stdBasis i) (SS.stdBasis (j 2)),
    SS.stdBasis (j 3), SS.bxor (SS.stdBasis i) (SS.stdBasis (j 3))]

def matchedTenCharacterMatrix (i : Fin n) (j : Fin 4 → Fin n)
    (x : Fin 10 → SS.BitString n) : Matrix (Fin 10) (Fin 10) ℂ :=
  restrictedCharacterMatrix (matchedTenDressings i j) (matchedTop (SS.stdBasis i) x)

theorem matchedTenDressings_low_weight (i : Fin n) (j : Fin 4 → Fin n) :
    ∀ a, (⟨SS.stdBasis i,matchedTenDressings i j a⟩ : SS.PauliString n).wt ≤ 2 := by
  intro a
  fin_cases a
  · exact wt_single_flip_zero_dressing i
  · exact wt_single_flip_single_dressing i i
  · exact wt_single_flip_single_dressing i (j 0)
  · exact wt_single_flip_pair_dressing i (j 0)
  · exact wt_single_flip_single_dressing i (j 1)
  · exact wt_single_flip_pair_dressing i (j 1)
  · exact wt_single_flip_single_dressing i (j 2)
  · exact wt_single_flip_pair_dressing i (j 2)
  · exact wt_single_flip_single_dressing i (j 3)
  · exact wt_single_flip_pair_dressing i (j 3)

/-- First clause of supplementary `lem:m2-fullrank-matching`: the ten
actual incidence monomials vanish, even before matched magnitudes are used. -/
theorem matched_ten_monomials_zero
    (c d : SS.State n ℂ) (i : Fin n) (j : Fin 4 → Fin n)
    (x : Fin 10 → SS.BitString n) (hx : Function.Injective x)
    (hc : ∀ v, v ∉ Finset.univ.image x → c v = 0)
    (hd : ∀ v, v ∉ Finset.univ.image (matchedTop (SS.stdBasis i) x) → d v = 0)
    (hdist : SS.HasDistance ![c,d] 3)
    (hdet : (matchedTenCharacterMatrix i j x).det ≠ 0) :
    ∀ r, star (c (x r)) * d (SS.bxor (x r) (SS.stdBasis i)) = 0 := by
  have h := monomials_zero_of_det_ne_zero _ _ c d hc hd hdist (SS.stdBasis i)
    (matchedTenDressings i j) (matchedTop (SS.stdBasis i) x)
    (matchedTop_injective _ x hx) (complete_matching_incidence _ x)
    (matchedTenDressings_low_weight i j) hdet
  intro r
  simpa only [incidenceMonomial, matchedTop, SS.bxor_bxor_cancel] using h r

/-- Supplementary `lem:m2-fullrank-matching`, for any physical qubit count.
No nonzero-support or interior assumption is added to the matched probabilities. -/
theorem matched_ten_obstruction
    (c d : SS.State n ℂ) (i : Fin n) (j : Fin 4 → Fin n)
    (x : Fin 10 → SS.BitString n) (hx : Function.Injective x)
    (hc : ∀ v, v ∉ Finset.univ.image x → c v = 0)
    (hd : ∀ v, v ∉ Finset.univ.image (matchedTop (SS.stdBasis i) x) → d v = 0)
    (hnc : SS.innerC c c = 1)
    (hm : ∀ r, Complex.normSq (c (x r)) =
      Complex.normSq (d (SS.bxor (x r) (SS.stdBasis i))))
    (hdet : (matchedTenCharacterMatrix i j x).det ≠ 0) :
    ¬ SS.HasDistance ![c,d] 3 :=
  full_rank_matched_obstruction c d (SS.stdBasis i) x (matchedTenDressings i j)
    hx hc hd hnc hm (matchedTenDressings_low_weight i j) hdet

end
end MainTheory.FlipCharacter
