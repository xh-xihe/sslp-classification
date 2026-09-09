import SixQubit.Orbit7DirectMarginal

set_option autoImplicit false

namespace MainTheory.Orbit7MatrixDisplays

open SixQubit.Orbit7Universal SixQubit.Orbit7DirectMarginal

theorem spinMass_eq_norm (f : SS.State 6 ℂ) (base : SS.BitString 6) :
    spinMass f base = ∑ i : Fin 2, Complex.normSq (spinor f base i) := by
  simp [spinMass,spinor,Fin.sum_univ_two]

noncomputable def Pu (c : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (6 : ℂ) • U c
noncomputable def Pv (d : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (6 : ℂ) • W d

noncomputable def normalizedOuter (s : Spinor) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => 6 * (s i * star (s j))

theorem outer_idempotent (s : Spinor)
    (hn : ∑ i : Fin 2, Complex.normSq (s i) = 1/6) :
    normalizedOuter s * normalizedOuter s = normalizedOuter s := by
  have hnC : (∑ i : Fin 2, star (s i) * s i) = (1/6 : ℂ) := by
    simp_rw [SixQubit.star_mul_self]
    rw [← Complex.ofReal_sum,hn]
    norm_num
  ext i j
  simp only [Matrix.mul_apply,normalizedOuter]
  calc
    (∑ x : Fin 2, (6 * (s i * star (s x))) * (6 * (s x * star (s j)))) =
        36 * s i * (∑ x : Fin 2, star (s x) * s x) * star (s j) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 6 * (s i * star (s j)) := by rw [hnC]; ring

theorem outer_hermitian (s : Spinor) :
    (normalizedOuter s).conjTranspose = normalizedOuter s := by
  ext i j
  simp [Matrix.conjTranspose_apply,normalizedOuter,mul_comm]

theorem extreme_projectors (c d : SS.State 6 ℂ) (hu : uMass c = 1/6) (hv : vMass d = 1/6) :
    Pu c * Pu c = Pu c ∧ (Pu c).conjTranspose = Pu c ∧
    Pv d * Pv d = Pv d ∧ (Pv d).conjTranspose = Pv d := by
  have hu' : ∑ i : Fin 2, Complex.normSq (spinor c zero i) = 1/6 := by
    rw [← spinMass_eq_norm]; exact hu
  have hv' : ∑ i : Fin 2, Complex.normSq (spinor d activeAll i) = 1/6 := by
    rw [← spinMass_eq_norm]; exact hv
  exact ⟨outer_idempotent _ hu',outer_hermitian _,outer_idempotent _ hv',outer_hermitian _⟩

theorem target_stars (c d : SS.State 6 ℂ) (s : Fin 5)
    (hA : ∀ i j, starA c s i j = 2 * U c i j)
    (hB : ∀ i j, starB d s i j = 2 * W d i j) :
    starA c s = (1/3 : ℂ) • Pu c ∧ starB d s = (1/3 : ℂ) • Pv d := by
  constructor
  · ext i j
    simp [Pu,hA]
    ring
  · ext i j
    simp [Pv,hB]
    ring

theorem target_pair_blocks (c d : SS.State 6 ℂ) (s : Fin 5)
    (hA : ∀ i j, starA c s i j = 2 * U c i j)
    (hB : ∀ i j, starB d s i j = 2 * W d i j) :
    pairMarginal c d s = Matrix.blockDiagonal ![(1/2 : ℂ) • Pu c, (1/2 : ℂ) • Pv d] := by
  have h0 : pairZeroBlock c s = (1/2 : ℂ) • Pu c := by
    ext i j
    simp [pairZeroBlock,Pu,hA]
    ring
  have h1 : pairOneBlock d s = (1/2 : ℂ) • Pv d := by
    ext i j
    simp [pairOneBlock,Pv,hB]
    ring
  rw [pairMarginal,h0,h1]

end MainTheory.Orbit7MatrixDisplays
