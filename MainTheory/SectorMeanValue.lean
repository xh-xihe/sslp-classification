import MainTheory.PhaseSectorFull

/-!
# The common sector mean is the number-operator scalar

`PhaseSectorFull.exists_common_sector_mean` shows that all sectors share one
first-moment vector, but never says what that vector is.  The paper does:
`eq:Nj-detection` sets `N_j := (I - Z_j)/2` and states `P N_j P = mu_j P` with

  mu_j = (1 - lambda_j) / 2,

`lambda_j` being the `Z_j` Knill--Laflamme scalar.  This file supplies the
identification.

The arithmetic already occurred inside the proof that the means agree --
`charOn = massOn - 2 * occOn`, with `massOn = 1` by orthonormality -- but the
scalar was discarded there.  Here it is kept.
-/

namespace MainTheory.SectorMeanValue

open MainTheory.PhaseSectorFull
open SixQubit

variable {n t : ℕ} {theta : Fin n → ℝ}

/-- The `Z_j` Knill--Laflamme scalar of a sector decomposition, i.e. the
paper's `lambda_j`. -/
noncomputable def klScalar (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (j : Fin n) : ℂ :=
  Classical.choose (hZ j)

theorem klScalar_spec (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (j : Fin n) (u v : D.Index) :
    SS.innerC (D.vec u)
      (SS.pauliAct (⟨fun _ => false, SS.stdBasis j⟩ : SS.PauliString n)
        (D.vec v)) = if u = v then klScalar D hZ j else 0 :=
  Classical.choose_spec (hZ j) u v

/-- **Every sector vector has occupation `(1 - lambda_j)/2` at site `j`.** -/
theorem occOn_eq_klScalar (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (u : D.Index) (j : Fin n) :
    ((occOn Finset.univ (D.vec u) j : ℝ) : ℂ)
      = (1 - klScalar D hZ j) / 2 := by
  have huu := klScalar_spec D hZ j u u
  rw [if_pos rfl] at huu
  have hchar := innerC_pureZ_eq_charOn
    (Finset.univ : Finset (SS.BitString n)) (D.vec u) (by simp)
    (SS.stdBasis j)
  have hmass := massOn_eq_one
    (Finset.univ : Finset (SS.BitString n)) (D.vec u) (by simp)
    (innerC_vec_self D u)
  have hcast : ((charOn Finset.univ (D.vec u) (SS.stdBasis j) : ℝ) : ℂ)
      = klScalar D hZ j := by rw [← hchar]; exact huu
  rw [charOn_stdBasis, hmass] at hcast
  push_cast at hcast
  linear_combination -hcast / 2

/-- **The sector mean is the number-operator scalar**, exactly
`eq:Nj-detection`. -/
theorem sectorMean_eq_klScalar (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (alpha : Fin t) (j : Fin n) :
    ((sectorMean D alpha j : ℝ) : ℂ) = (1 - klScalar D hZ j) / 2 := by
  rw [sectorMean_eq_average_occOn]
  have hconst : ∀ r : Fin (D.rank alpha),
      occOn Finset.univ (D.vec ⟨alpha, r⟩) j
        = occOn Finset.univ (D.vec ⟨alpha, ⟨0, D.rank_pos alpha⟩⟩) j := by
    intro r
    have h1 := occOn_eq_klScalar D hZ ⟨alpha, r⟩ j
    have h2 := occOn_eq_klScalar D hZ
      ⟨alpha, ⟨0, D.rank_pos alpha⟩⟩ j
    exact_mod_cast h1.trans h2.symm
  rw [Finset.sum_congr rfl (fun r _ => hconst r)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast (D.rank_pos alpha).ne')]
  exact occOn_eq_klScalar D hZ ⟨alpha, ⟨0, D.rank_pos alpha⟩⟩ j

end MainTheory.SectorMeanValue
