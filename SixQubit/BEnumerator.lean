import Mathlib

import SixQubit.MacWilliams

/-!
# The six-qubit `B` weight enumerator

`SixQubit.MacWilliams` proves the Pauli Parseval identity and its subset form,
but the orbit files previously exposed only the `A` coefficients.  This file
packages the Frobenius side by weight and derives the complete six-qubit
MacWilliams transform inside Lean.

For a `K`-dimensional code, `Bco` is the same unnormalised convention as
`Aco`:

    Bco_j = K * sum_{wt P = j} sum_{a,b} |<psi_a|P|psi_b>|^2 = K^2 B_j.

In particular, for the two-dimensional codes below, both `Aco` and `Bco` are
four times the coefficients printed in the manuscript.

The proof does not inspect any exhibited code.  We sum `subset_duality` over
all `m`-subsets of the six qubits.  The two incidence numbers are checked over
the finite type `Finset (Fin 6)` by kernel `decide`.  The seven resulting
triangular equations determine every `Bco_j` from every `Aco_j`.

No `sorry`, no `native_decide`.
-/

namespace SS.MacWilliams

open scoped BigOperators
open Finset

/-! ## Weight packaging on the Frobenius side -/

/-- The Frobenius weight carried by Paulis with support exactly `T`. -/
noncomputable def bsub {n K : ℕ} (psi : Fin K → SS.State n ℂ)
    (T : Finset (Fin n)) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => supp P = T), frob psi P

/-- The unnormalised Shor--Laflamme coefficient `K² B_j`. -/
noncomputable def Bco {n K : ℕ} (psi : Fin K → SS.State n ℂ) (j : ℕ) : ℝ :=
  (K : ℝ) * ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j), frob psi P

lemma fiber_bsupp {n K : ℕ} (psi : Fin K → SS.State n ℂ)
    (pred : Finset (Fin n) → Prop) [DecidablePred pred] :
    ∑ T ∈ Finset.univ.filter pred, bsub psi T
      = ∑ P ∈ Finset.univ.filter (fun P => pred (supp P)), frob psi P := by
  classical
  simp only [bsub]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  refine Finset.sum_congr (Finset.filter_congr (fun P _ => ?_)) (fun _ _ => rfl)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma sum_bsub_card {K : ℕ} (psi : Fin K → SS.State 6 ℂ) (j : ℕ) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin 6) => T.card = j), bsub psi T
      = ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = j), frob psi P :=
  fiber_bsupp psi (fun T => T.card = j)

lemma sum_bsub_subset {K : ℕ} (psi : Fin K → SS.State 6 ℂ)
    (S : Finset (Fin 6)) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin 6) => T ⊆ S), bsub psi T
      = ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString 6 => supp P ⊆ S), frob psi P :=
  fiber_bsupp psi (fun T => T ⊆ S)

/-! ## The two finite incidence counts -/

/-- Number of `m`-subsets of six coordinates containing a fixed `k`-subset. -/
def containCount6 (m k : ℕ) : ℕ :=
  if k ≤ m then Nat.choose (6 - k) (m - k) else 0

/-- Number of `m`-subsets of six coordinates disjoint from a fixed `k`-subset. -/
def disjointCount6 (m k : ℕ) : ℕ := Nat.choose (6 - k) m

lemma count_containing6 (m : ℕ) (hm : m ≤ 6) : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard m).filter (fun S => T ⊆ S)).card
      = containCount6 m T.card := by
  interval_cases m <;> decide

lemma count_disjoint6 (m : ℕ) (hm : m ≤ 6) : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard m).filter (fun S => T ⊆ Sᶜ)).card
      = disjointCount6 m T.card := by
  interval_cases m <;> decide

/-! ## Averaged duality and the two enumerator pairs used by the five orbits -/

/-- The subset MacWilliams identity, averaged over all `m`-subsets of six
qubits and expressed in the unnormalised `Aco`/`Bco` convention. -/
theorem summed_duality_six {K : ℕ} (psi : Fin K → SS.State 6 ℂ)
    (m : ℕ) (hm : m ≤ 6) :
    (2 : ℝ) ^ 6 * ∑ k ∈ Finset.range 7,
        (containCount6 m k : ℝ) * Bco psi k
      = (K : ℝ) * 4 ^ m * ∑ k ∈ Finset.range 7,
          (disjointCount6 m k : ℝ) * Aco psi k := by
  classical
  have hstep : ∀ S ∈ (Finset.univ : Finset (Fin 6)).powersetCard m,
      (2 : ℝ) ^ 6 * ∑ T ∈ Finset.univ.filter
          (fun T : Finset (Fin 6) => T ⊆ S), bsub psi T
        = 4 ^ m * ∑ T ∈ Finset.univ.filter
            (fun T : Finset (Fin 6) => T ⊆ Sᶜ), gsub psi T := by
    intro S hS
    have hcard : S.card = m := (Finset.mem_powersetCard.mp hS).2
    have h := subset_duality psi S
    rw [← sum_bsub_subset, ← sum_gsub_compl] at h
    rw [hcard] at h
    exact h
  have hsum := Finset.sum_congr rfl hstep
  rw [← Finset.mul_sum, ← Finset.mul_sum, swap_count, swap_count] at hsum
  simp only [count_containing6 m hm, count_disjoint6 m hm] at hsum
  rw [card_fiber6 (fun k => (containCount6 m k : ℝ)) (bsub psi),
    card_fiber6 (fun k => (disjointCount6 m k : ℝ)) (gsub psi)] at hsum
  simp only [sum_bsub_card, sum_gsub_card] at hsum
  simp only [Bco]
  have hfactor :
      ∑ k ∈ Finset.range 7, (containCount6 m k : ℝ) *
          ((K : ℝ) * ∑ P ∈ Finset.univ.filter
            (fun P : SS.PauliString 6 => P.wt = k), frob psi P)
        = (K : ℝ) * ∑ k ∈ Finset.range 7, (containCount6 m k : ℝ) *
            ∑ P ∈ Finset.univ.filter
              (fun P : SS.PauliString 6 => P.wt = k), frob psi P := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hfactor]
  calc
    (2 : ℝ) ^ 6 * ((K : ℝ) * ∑ k ∈ Finset.range 7,
            (containCount6 m k : ℝ) *
              ∑ P ∈ Finset.univ.filter
                (fun P : SS.PauliString 6 => P.wt = k), frob psi P)
        = (K : ℝ) * ((2 : ℝ) ^ 6 * ∑ k ∈ Finset.range 7,
            (containCount6 m k : ℝ) *
              ∑ P ∈ Finset.univ.filter
                (fun P : SS.PauliString 6 => P.wt = k), frob psi P) := by ring
    _ = (K : ℝ) * (4 ^ m * ∑ k ∈ Finset.range 7,
          (disjointCount6 m k : ℝ) * Aco psi k) := by rw [hsum]
    _ = (K : ℝ) * 4 ^ m * ∑ k ∈ Finset.range 7,
          (disjointCount6 m k : ℝ) * Aco psi k := by ring

/-- **The complete six-qubit quantum MacWilliams transform.**  This is the
usual quaternary Krawtchouk matrix, but every row is derived here from
`subset_duality`; the integer coefficients are therefore not trusted input.
The factor `32 = 2⁶ / 2` is the transform factor for a two-dimensional code. -/
theorem bco_transform_six (psi : Fin 2 → SS.State 6 ℂ) :
    32 * Bco psi 0 =
        Aco psi 0 + Aco psi 1 + Aco psi 2 + Aco psi 3 + Aco psi 4 + Aco psi 5 + Aco psi 6
    ∧ 32 * Bco psi 1 =
        18 * Aco psi 0 + 14 * Aco psi 1 + 10 * Aco psi 2 + 6 * Aco psi 3 +
          2 * Aco psi 4 - 2 * Aco psi 5 - 6 * Aco psi 6
    ∧ 32 * Bco psi 2 =
        135 * Aco psi 0 + 75 * Aco psi 1 + 31 * Aco psi 2 + 3 * Aco psi 3 -
          9 * Aco psi 4 - 5 * Aco psi 5 + 15 * Aco psi 6
    ∧ 32 * Bco psi 3 =
        540 * Aco psi 0 + 180 * Aco psi 1 + 12 * Aco psi 2 - 28 * Aco psi 3 -
          4 * Aco psi 4 + 20 * Aco psi 5 - 20 * Aco psi 6
    ∧ 32 * Bco psi 4 =
        1215 * Aco psi 0 + 135 * Aco psi 1 - 81 * Aco psi 2 - 9 * Aco psi 3 +
          31 * Aco psi 4 - 25 * Aco psi 5 + 15 * Aco psi 6
    ∧ 32 * Bco psi 5 =
        1458 * Aco psi 0 - 162 * Aco psi 1 - 54 * Aco psi 2 + 54 * Aco psi 3 -
          30 * Aco psi 4 + 14 * Aco psi 5 - 6 * Aco psi 6
    ∧ 32 * Bco psi 6 =
        729 * Aco psi 0 - 243 * Aco psi 1 + 81 * Aco psi 2 - 27 * Aco psi 3 +
          9 * Aco psi 4 - 3 * Aco psi 5 + Aco psi 6 := by
  have h0 := summed_duality_six psi 0 (by norm_num)
  have h1 := summed_duality_six psi 1 (by norm_num)
  have h2 := summed_duality_six psi 2 (by norm_num)
  have h3 := summed_duality_six psi 3 (by norm_num)
  have h4 := summed_duality_six psi 4 (by norm_num)
  have h5 := summed_duality_six psi 5 (by norm_num)
  have h6 := summed_duality_six psi 6 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h0 h1 h2 h3 h4 h5 h6
  norm_num [containCount6, disjointCount6, Nat.choose] at h0 h1 h2 h3 h4 h5 h6
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The manuscript's first rigid `A` enumerator, in the `Aco = 4 A` convention. -/
def IsE1A (psi : Fin 2 → SS.State 6 ℂ) : Prop :=
  Aco psi 0 = 4 ∧ Aco psi 1 = 4 ∧ Aco psi 2 = 0 ∧ Aco psi 3 = 0 ∧
    Aco psi 4 = 60 ∧ Aco psi 5 = 60 ∧ Aco psi 6 = 0

/-- The manuscript's first rigid `B` enumerator, in the `Bco = 4 B` convention. -/
def IsE1B (psi : Fin 2 → SS.State 6 ℂ) : Prop :=
  Bco psi 0 = 4 ∧ Bco psi 1 = 4 ∧ Bco psi 2 = 0 ∧ Bco psi 3 = 120 ∧
    Bco psi 4 = 180 ∧ Bco psi 5 = 132 ∧ Bco psi 6 = 72

/-- The manuscript's second rigid `A` enumerator, in the `Aco = 4 A` convention. -/
def IsE2A (psi : Fin 2 → SS.State 6 ℂ) : Prop :=
  Aco psi 0 = 4 ∧ Aco psi 1 = 0 ∧ Aco psi 2 = 4 ∧ Aco psi 3 = 0 ∧
    Aco psi 4 = 44 ∧ Aco psi 5 = 64 ∧ Aco psi 6 = 12

/-- The manuscript's second rigid `B` enumerator, in the `Bco = 4 B` convention. -/
def IsE2B (psi : Fin 2 → SS.State 6 ℂ) : Prop :=
  Bco psi 0 = 4 ∧ Bco psi 1 = 0 ∧ Bco psi 2 = 4 ∧ Bco psi 3 = 96 ∧
    Bco psi 4 = 140 ∧ Bco psi 5 = 160 ∧ Bco psi 6 = 108

/-- The full, kernel-checked MacWilliams transform of `E₁ᴬ`. -/
theorem e1B_of_e1A (psi : Fin 2 → SS.State 6 ℂ) (hA : IsE1A psi) : IsE1B psi := by
  have h0 := summed_duality_six psi 0 (by norm_num)
  have h1 := summed_duality_six psi 1 (by norm_num)
  have h2 := summed_duality_six psi 2 (by norm_num)
  have h3 := summed_duality_six psi 3 (by norm_num)
  have h4 := summed_duality_six psi 4 (by norm_num)
  have h5 := summed_duality_six psi 5 (by norm_num)
  have h6 := summed_duality_six psi 6 (by norm_num)
  rcases hA with ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h0 h1 h2 h3 h4 h5 h6
  norm_num [containCount6, disjointCount6, Nat.choose, hA0, hA1, hA2, hA3, hA4, hA5, hA6]
    at h0 h1 h2 h3 h4 h5 h6
  dsimp only [IsE1B]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The full, kernel-checked MacWilliams transform of `E₂ᴬ`. -/
theorem e2B_of_e2A (psi : Fin 2 → SS.State 6 ℂ) (hA : IsE2A psi) : IsE2B psi := by
  have h0 := summed_duality_six psi 0 (by norm_num)
  have h1 := summed_duality_six psi 1 (by norm_num)
  have h2 := summed_duality_six psi 2 (by norm_num)
  have h3 := summed_duality_six psi 3 (by norm_num)
  have h4 := summed_duality_six psi 4 (by norm_num)
  have h5 := summed_duality_six psi 5 (by norm_num)
  have h6 := summed_duality_six psi 6 (by norm_num)
  rcases hA with ⟨hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h0 h1 h2 h3 h4 h5 h6
  norm_num [containCount6, disjointCount6, Nat.choose, hA0, hA1, hA2, hA3, hA4, hA5, hA6]
    at h0 h1 h2 h3 h4 h5 h6
  dsimp only [IsE2B]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SS.MacWilliams
