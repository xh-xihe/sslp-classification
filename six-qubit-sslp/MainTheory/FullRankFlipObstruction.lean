import MainTheory.FlipCharacterObstruction

/-! The two-edge and full-rank one-coordinate flip lemmas, with arbitrary
physical qubit count and complete support incidence sets. -/

namespace MainTheory.FlipCharacter
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

variable {n N : ℕ}

def flipDressings (j : Fin N → Fin n) : Fin (N+1) → SS.BitString n :=
  Fin.cases (fun _ => false) (fun k => SS.stdBasis (j k))

/-- The manuscript's matrix evaluated on bottom incidence endpoints. -/
def flipCharacterMatrix (i : Fin n) (j : Fin N → Fin n)
    (y : Fin (N+1) → SS.BitString n) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  restrictedCharacterMatrix (flipDressings j) (fun r => SS.bxor (y r) (SS.stdBasis i))

theorem character_single_flip_outside (i j : Fin n) (hji : j ≠ i) (y : SS.BitString n) :
    character (SS.stdBasis j) (SS.bxor y (SS.stdBasis i)) = character (SS.stdBasis j) y := by
  rw [character_single, character_single, SS.bxor_apply, SS.stdBasis_apply_ne hji]
  simp

theorem flipCharacterMatrix_eq_restricted (i : Fin n) (j : Fin N → Fin n)
    (hji : ∀ k, j k ≠ i) (y : Fin (N+1) → SS.BitString n) :
    flipCharacterMatrix i j y = restrictedCharacterMatrix (flipDressings j) y := by
  ext a b
  induction a using Fin.cases with
  | zero => simp [flipCharacterMatrix, restrictedCharacterMatrix, flipDressings, character_zero]
  | succ k =>
    exact character_single_flip_outside i (j k) (hji k) (y b)

theorem flipDressings_low_weight (i : Fin n) (j : Fin N → Fin n) :
    ∀ a, (⟨SS.stdBasis i, flipDressings j a⟩ : SS.PauliString n).wt ≤ 2 := by
  intro a
  induction a using Fin.cases with
  | zero => exact wt_single_flip_zero_dressing i
  | succ k => exact wt_single_flip_single_dressing i (j k)

/-- Supplementary `lem:m3lift-fullrank`: nonsingularity of the actual
bottom-endpoint character matrix kills every incidence product. -/
theorem full_rank_flip_monomials_zero (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.State n ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ x, x ∉ S₁ → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3)
    (i : Fin n) (j : Fin N → Fin n) (hji : ∀ k, j k ≠ i)
    (y : Fin (N+1) → SS.BitString n) (hy : Function.Injective y)
    (hI : Finset.univ.image y = incidenceSet S₀ S₁ (SS.stdBasis i))
    (hdet : (flipCharacterMatrix i j y).det ≠ 0) :
    ∀ r, star (c (SS.bxor (y r) (SS.stdBasis i))) * d (y r) = 0 := by
  rw [flipCharacterMatrix_eq_restricted i j hji] at hdet
  exact monomials_zero_of_det_ne_zero S₀ S₁ c d hc hd hdist (SS.stdBasis i)
    (flipDressings j) y hy hI (flipDressings_low_weight i j) hdet

theorem full_rank_flip_positive_obstruction (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.State n ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ x, x ∉ S₁ → d x = 0)
    (i : Fin n) (j : Fin N → Fin n) (hji : ∀ k, j k ≠ i)
    (y : Fin (N+1) → SS.BitString n) (hy : Function.Injective y)
    (hI : Finset.univ.image y = incidenceSet S₀ S₁ (SS.stdBasis i))
    (hdet : (flipCharacterMatrix i j y).det ≠ 0)
    (r : Fin (N+1))
    (hp : 0 < Complex.normSq (c (SS.bxor (y r) (SS.stdBasis i))) *
      Complex.normSq (d (y r))) : ¬ SS.HasDistance ![c,d] 3 := by
  rw [flipCharacterMatrix_eq_restricted i j hji] at hdet
  exact not_hasDistance_of_positive_incidence S₀ S₁ c d hc hd (SS.stdBasis i)
    (flipDressings j) y hy hI (flipDressings_low_weight i j) hdet r hp

/-- Supplementary `lem:twoedge`.  Only one nonzero endpoint pair is needed;
the manuscript's four-endpoint assumption therefore follows immediately. -/
theorem two_edge_flip_obstruction (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.State n ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ x, x ∉ S₁ → d x = 0)
    (i j : Fin n) (_hji : j ≠ i) (y y' : SS.BitString n)
    (hI : incidenceSet S₀ S₁ (SS.stdBasis i) = {y,y'})
    (hbit : y j ≠ y' j)
    (hcne : c (SS.bxor y (SS.stdBasis i)) ≠ 0) (hdne : d y ≠ 0) :
    ¬ SS.HasDistance ![c,d] 3 := by
  classical
  let ys : Fin 2 → SS.BitString n := ![y,y']
  let zs : Fin 2 → SS.BitString n := ![fun _ => false, SS.stdBasis j]
  have hyy : y ≠ y' := fun h => hbit (congrFun h j)
  have hy : Function.Injective ys := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [ys]
  have hIs : Finset.univ.image ys = incidenceSet S₀ S₁ (SS.stdBasis i) := by
    rw [hI, show (Finset.univ : Finset (Fin 2)) = {0,1} from by decide]
    simp [ys]
  have hw : ∀ a, (⟨SS.stdBasis i,zs a⟩ : SS.PauliString n).wt ≤ 2 := by
    intro a
    fin_cases a
    · exact wt_single_flip_zero_dressing i
    · exact wt_single_flip_single_dressing i j
  have hdet : (restrictedCharacterMatrix zs ys).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [restrictedCharacterMatrix, zs, ys, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, character_zero, character_single]
    cases hybit : y j <;> cases hy'bit : y' j
    all_goals simp_all
    all_goals norm_num
  apply not_hasDistance_of_positive_incidence S₀ S₁ c d hc hd (SS.stdBasis i)
    zs ys hy hIs hw hdet 0
  exact mul_pos (Complex.normSq_pos.mpr hcne) (Complex.normSq_pos.mpr hdne)

def actualSupport (c : SS.State n ℂ) : Finset (SS.BitString n) :=
  Finset.univ.filter (fun x => c x ≠ 0)

theorem actualSupport_contains (c : SS.State n ℂ) :
    ∀ x, x ∉ actualSupport c → c x = 0 := by
  intro x hx
  simpa [actualSupport] using hx

/-- The exact actual-support formulation in the supplementary lemma, with
endpoint nonvanishing derived from support membership. -/
theorem two_edge_actual_support_obstruction (c d : SS.State n ℂ)
    (i j : Fin n) (hji : j ≠ i) (y y' : SS.BitString n)
    (hI : incidenceSet (actualSupport c) (actualSupport d) (SS.stdBasis i) = {y,y'})
    (hbit : y j ≠ y' j) : ¬ SS.HasDistance ![c,d] 3 := by
  have hymem : y ∈ incidenceSet (actualSupport c) (actualSupport d) (SS.stdBasis i) := by
    rw [hI]
    simp
  have he : d y ≠ 0 ∧ c (SS.bxor y (SS.stdBasis i)) ≠ 0 := by
    simpa [incidenceSet, actualSupport] using hymem
  exact two_edge_flip_obstruction _ _ c d (actualSupport_contains c) (actualSupport_contains d)
    i j hji y y' hI hbit he.2 he.1

end
end MainTheory.FlipCharacter
