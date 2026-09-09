import MainTheory.Orbit36PhaseMap
import MainTheory.Orbit36MomentCharacters

set_option autoImplicit false

namespace MainTheory.Orbit36PhaseMapSemantics

open MainTheory.Orbit36PhaseMapMatrix MainTheory.Orbit36PhaseMap
open MainTheory.Orbit36MomentCharacters

def basisExponents (x : SS.BitString 6) : Fin 7 → ℕ :=
  Fin.cases 1 (fun j => if x j then 1 else 0)

def basisPhase (z : Fin 7 → ℂ) (x : SS.BitString 6) : ℂ :=
  z 0 * ∏ j : Fin 6, if x j then z j.succ else 1

theorem first_six_rows : ∀ (r : Fin 6), exponents (r.castLE (by decide)) =
    basisExponents (vertices (r.castLE (by decide))) := by decide +kernel

theorem last_row_weights : exponents 6 = fun j =>
    basisExponents (vertices 2) j + basisExponents (vertices 3) j +
      basisExponents (vertices 6) j := by decide +kernel

theorem basis_phase_product (z : Fin 7 → ℂ) (x : SS.BitString 6) :
    (∏ j, z j ^ basisExponents x j) = basisPhase z x := by
  rw [Fin.prod_univ_succ]
  simp [basisExponents, basisPhase]

theorem first_six_phase_actions (z : Fin 7 → ℂ) (r : Fin 6) :
    monomialMap z (r.castLE (by decide)) =
      basisPhase z (vertices (r.castLE (by decide))) := by
  unfold monomialMap
  rw [first_six_rows, basis_phase_product]

theorem edge_product_phase_action (z : Fin 7 → ℂ) : monomialMap z 6 =
    basisPhase z (vertices 2) * basisPhase z (vertices 3) * basisPhase z (vertices 6) := by
  unfold monomialMap
  simp_rw [last_row_weights, pow_add]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [basis_phase_product]

end MainTheory.Orbit36PhaseMapSemantics
