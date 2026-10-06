import Mathlib

/-!
# `lem:q4o30threepoints`, `lem:q4o30exceptional`, `lem:q4o30mindegree`

The manuscript's orbit-30 argument runs on a `K_5` support graph.  Its
`eq:q4o30K5labels` labels the sixteen points of the bottom fibre by one symbol
`star`, five vertices `v_i` and the ten edges `e_ij` of a complete graph on
`V = {0,1,2,3,4}`, and `eq:q4o30probnotation` writes

  `p_star`, `r_i := p(v_i)`, `w_ij := p(e_ij)`, `D_i := sum_{j /= i} w_ij`.

The exact moment normal form then gives `eq:q4o30degreeprob`,
`p_star = 1/8` and `D_i - r_i = 1/8`, and summing gives `eq:q4o30RW`,
`R = 3/8` and `W = 1/2`.  The active set is `A = {i : r_i > 0}` and the
support graph `G` has edge `ij` exactly when `w_ij > 0`.

Three lemmas of that section are proved here.  The package's own orbit-30
no-go takes a different route, so these are the manuscript's steps rather than
part of the certified chain; the headline `thm:q4o30nogo` is proved elsewhere.

## What is assumed, and why

`Orbit30Data` carries the manuscript's probabilities together with the
*amplitudes* `b i` and `c i j` underneath them, `‖b i‖^2 = r i` and
`‖c i j‖^2 = w i j`, and the weight-one rows in the bilinear form

  `sum_{j /= i} b j * c i j = 0`.

That bilinear form is the manuscript's own: it is what
`eq:q4o30weightonediff` and `eq:q4o30starsign` produce once the phases are
synchronised, and the manuscript writes the reduced rows exactly this way in
`eq:q4o30triangle1`--`eq:q4o30triangle3`.  Taking it as the interface is
therefore faithful, and it is what makes all three lemmas one argument: every
one of them turns on counting the nonzero terms of such a row.

`W = 1/2` is *not* assumed.  It is derived, from `D_i = r_i + 1/8` and
`R = 3/8`, in `total_weight`.
-/

namespace MainTheory.Orbit30

open scoped BigOperators

/-- The orbit-30 support-graph data: five vertices, point and edge
probabilities with their amplitudes, and the synchronised weight-one rows. -/
structure Data where
  /-- Point amplitudes; `r i = ‖b i‖^2`. -/
  b : Fin 5 → ℂ
  /-- Edge amplitudes; `w i j = ‖c i j‖^2`. -/
  c : Fin 5 → Fin 5 → ℂ
  c_symm : ∀ i j, c i j = c j i
  c_diag : ∀ i, c i i = 0
  /-- `eq:q4o30degreeprob`: `D_i - r_i = 1/8`. -/
  degree : ∀ i, (∑ j, Complex.normSq (c i j)) = Complex.normSq (b i) + 1 / 8
  /-- `eq:q4o30RW`: `R = 3/8`. -/
  total_point : (∑ i, Complex.normSq (b i)) = 3 / 8
  /-- The weight-one row centred at `i`, in the manuscript's synchronised
  bilinear form. -/
  row : ∀ i, (∑ j ∈ Finset.univ.erase i, b j * c i j) = 0

namespace Data

variable (d : Data)

/-- `r i`, the point probability. -/
def r (i : Fin 5) : ℝ := Complex.normSq (d.b i)

/-- `w i j`, the edge probability. -/
def w (i j : Fin 5) : ℝ := Complex.normSq (d.c i j)

/-- `D i`, the weighted edge degree. -/
def D (i : Fin 5) : ℝ := ∑ j, d.w i j

/-- The active set `A = {i : r i > 0}`. -/
def Active (i : Fin 5) : Prop := 0 < d.r i

/-- The support graph's edge relation, `w i j > 0`. -/
def Edge (i j : Fin 5) : Prop := 0 < d.w i j

noncomputable instance (i : Fin 5) : Decidable (d.Active i) := Classical.dec _

noncomputable instance (i j : Fin 5) : Decidable (d.Edge i j) := Classical.dec _

theorem total_point' : (∑ i, d.r i) = 3 / 8 := d.total_point

theorem r_nonneg (i : Fin 5) : 0 ≤ d.r i := Complex.normSq_nonneg _

theorem w_nonneg (i j : Fin 5) : 0 ≤ d.w i j := Complex.normSq_nonneg _

theorem w_symm (i j : Fin 5) : d.w i j = d.w j i := by
  simp [w, d.c_symm i j]

theorem w_diag (i : Fin 5) : d.w i i = 0 := by simp [w, d.c_diag i]

theorem degree_eq (i : Fin 5) : d.D i = d.r i + 1 / 8 := d.degree i

/-- **`eq:q4o30RW`, the edge half.**  `W = 1/2`, derived rather than assumed. -/
theorem total_weight : (∑ i, ∑ j, d.w i j) = 1 := by
  have h : (∑ i, ∑ j, d.w i j) = ∑ i, (d.r i + 1 / 8) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact d.degree_eq i
  rw [h, Finset.sum_add_distrib, d.total_point']
  norm_num

/-- A term of the row at `i` is nonzero exactly at an active neighbour. -/
theorem term_ne_zero_iff (i j : Fin 5) :
    d.b j * d.c i j ≠ 0 ↔ (d.Active j ∧ d.Edge i j) := by
  constructor
  · intro h
    have hb : d.b j ≠ 0 := by
      intro h0; exact h (by rw [h0, zero_mul])
    have hc : d.c i j ≠ 0 := by
      intro h0; exact h (by rw [h0, mul_zero])
    exact ⟨Complex.normSq_pos.2 hb, Complex.normSq_pos.2 hc⟩
  · rintro ⟨ha, he⟩
    have hb : d.b j ≠ 0 := Complex.normSq_pos.1 ha
    have hc : d.c i j ≠ 0 := Complex.normSq_pos.1 he
    exact mul_ne_zero hb hc

/-- The neighbours of `i` that carry a nonzero row term: the active vertices
adjacent to `i`. -/
noncomputable def rowSupport (i : Fin 5) : Finset (Fin 5) :=
  (Finset.univ.erase i).filter fun j => d.Active j ∧ d.Edge i j

/-- **No row has exactly one nonzero term.**

This is the step every one of the three lemmas uses: a vanishing sum with a
single nonzero summand is a contradiction. -/
theorem rowSupport_card_ne_one (i : Fin 5) : (d.rowSupport i).card ≠ 1 := by
  intro hcard
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hcard
  have hmem : j ∈ d.rowSupport i := by rw [hj]; exact Finset.mem_singleton_self j
  have hjmem := Finset.mem_filter.1 hmem
  have hzero : (∑ k ∈ Finset.univ.erase i, d.b k * d.c i k) = 0 := d.row i
  have hsplit : (∑ k ∈ Finset.univ.erase i, d.b k * d.c i k)
      = d.b j * d.c i j := by
    refine Finset.sum_eq_single_of_mem j hjmem.1 fun k hk hkj => ?_
    by_contra hne
    have : k ∈ d.rowSupport i :=
      Finset.mem_filter.2 ⟨hk, (d.term_ne_zero_iff i k).1 hne⟩
    rw [hj, Finset.mem_singleton] at this
    exact hkj this
  rw [hsplit] at hzero
  exact (d.term_ne_zero_iff i j).2 hjmem.2 hzero


/-- The neighbours of `i` in the support graph. -/
noncomputable def nbhd (i : Fin 5) : Finset (Fin 5) :=
  (Finset.univ.erase i).filter fun j => d.Edge i j

theorem rowSupport_subset_nbhd (i : Fin 5) : d.rowSupport i ⊆ d.nbhd i := by
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_filter.2 ⟨hj1, hj2.2⟩

/-- The weighted degree is the sum over the neighbours. -/
theorem degree_eq_sum_nbhd (i : Fin 5) : d.D i = ∑ j ∈ d.nbhd i, d.w i j := by
  rw [D]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  by_contra hne
  refine hj (Finset.mem_filter.2 ⟨?_, lt_of_le_of_ne (d.w_nonneg i j) (Ne.symm hne)⟩)
  refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ j⟩
  rintro rfl
  exact hne (d.w_diag _)

theorem nbhd_nonempty (i : Fin 5) : (d.nbhd i).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have h0 : d.D i = 0 := by rw [d.degree_eq_sum_nbhd i, hempty, Finset.sum_empty]
  have h1 : d.D i = d.r i + 1 / 8 := d.degree_eq i
  have := d.r_nonneg i
  rw [h0] at h1
  linarith

/-- **`lem:q4o30mindegree`.**

On the regular branch -- every support edge is incident to an active point,
`eq:q4o30regular` -- the support graph has minimum degree at least two. -/
theorem two_le_nbhd_card
    (hreg : ∀ i j, d.Edge i j → d.Active i ∨ d.Active j) (i : Fin 5) :
    2 ≤ (d.nbhd i).card := by
  by_contra hlt
  push_neg at hlt
  have hcases : (d.nbhd i).card = 0 ∨ (d.nbhd i).card = 1 := by omega
  rcases hcases with h | h
  · exact absurd (Finset.card_eq_zero.1 h) (Finset.nonempty_iff_ne_empty.1 (d.nbhd_nonempty i))
  · -- exactly one neighbour `j`
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h
    have hjmem : j ∈ d.nbhd i := by rw [hj]; exact Finset.mem_singleton_self j
    obtain ⟨hjerase, hjedge⟩ := Finset.mem_filter.1 hjmem
    have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hjerase)
    by_cases hact : d.Active j
    · -- the row at `i` then has exactly one nonzero term
      have hsub : d.rowSupport i = {j} := by
        apply Finset.Subset.antisymm
        · intro k hk
          have : k ∈ d.nbhd i := d.rowSupport_subset_nbhd i hk
          rw [hj] at this
          exact this
        · intro k hk
          rw [Finset.mem_singleton] at hk
          subst hk
          exact Finset.mem_filter.2 ⟨hjerase, hact, hjedge⟩
      exact d.rowSupport_card_ne_one i (by rw [hsub, Finset.card_singleton])
    · -- `j` inactive: regularity makes `i` active, and the degrees collide
      have hi : d.Active i := (hreg i j hjedge).resolve_right hact
      have hrj : d.r j = 0 := le_antisymm (not_lt.1 hact) (d.r_nonneg j)
      have hDi : d.D i = d.w i j := by
        rw [d.degree_eq_sum_nbhd i, hj, Finset.sum_singleton]
      have hDi' : d.w i j = d.r i + 1 / 8 := by rw [← hDi]; exact d.degree_eq i
      have hDj : d.D j = 1 / 8 := by rw [d.degree_eq j, hrj]; ring
      have hle : d.w j i ≤ d.D j := by
        rw [D]
        exact Finset.single_le_sum (fun k _ => d.w_nonneg j k) (Finset.mem_univ i)
      rw [d.w_symm j i, hDi', hDj] at hle
      exact absurd hi (not_lt.2 (by linarith))


end Data

/-! ## The triangle obstruction -/

/-- **`eq:q4o30triangle1`--`eq:q4o30triangle3` are inconsistent.**

Three synchronised weight-one rows on a triangle of active points cannot hold
together.  The manuscript reads the contradiction off as
`c_02/c_12 = b_1/b_0` from the first two and `= -b_1/b_0` from the third; the
same cancellation is `b_0 e_1 + b_1 e_2 - b_2 e_3`.

Only three of the manuscript's six nonvanishing factors are needed. -/
theorem triangle_contradiction {b0 b1 b2 c01 c02 c12 : ℂ}
    (hb0 : b0 ≠ 0) (hb1 : b1 ≠ 0) (hc01 : c01 ≠ 0)
    (e1 : b1 * c01 + b2 * c02 = 0)
    (e2 : b0 * c01 + b2 * c12 = 0)
    (e3 : b0 * c02 + b1 * c12 = 0) : False := by
  have key : (2 : ℂ) * b0 * b1 * c01 = 0 := by
    linear_combination b0 * e1 + b1 * e2 - b2 * e3
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact (mul_ne_zero h2 hb0) h'
    · exact hb1 h'
  · exact hc01 h

namespace Data

variable (d : Data)

/-- The active set as a `Finset`. -/
noncomputable def A : Finset (Fin 5) := Finset.univ.filter fun i => d.Active i

theorem mem_A {i : Fin 5} : i ∈ d.A ↔ d.Active i := by
  simp [A]

theorem r_eq_zero_of_not_mem_A {i : Fin 5} (hi : i ∉ d.A) : d.r i = 0 :=
  le_antisymm (not_lt.1 fun h => hi (d.mem_A.2 h)) (d.r_nonneg i)

/-- `sum over A of the weighted degrees`, from `eq:q4o30degreeprob`. -/
theorem sum_degree_A : (∑ i ∈ d.A, ∑ j, d.w i j) = 3 / 8 + d.A.card / 8 := by
  have hstep : (∑ i ∈ d.A, ∑ j, d.w i j) = ∑ i ∈ d.A, (d.r i + 1 / 8) :=
    Finset.sum_congr rfl fun i _ => d.degree_eq i
  have hr : (∑ i ∈ d.A, d.r i) = 3 / 8 := by
    have hext : (∑ i ∈ d.A, d.r i) = ∑ i, d.r i :=
      Finset.sum_subset (Finset.subset_univ d.A)
        (fun i _ hi => d.r_eq_zero_of_not_mem_A hi)
    rw [hext, d.total_point']
  rw [hstep, Finset.sum_add_distrib, hr, Finset.sum_const, nsmul_eq_mul]
  ring

theorem sum_degree_compl :
    (∑ i ∈ d.Aᶜ, ∑ j, d.w i j) = (5 - d.A.card : ℝ) / 8 := by
  have hstep : (∑ i ∈ d.Aᶜ, ∑ j, d.w i j) = ∑ i ∈ d.Aᶜ, (d.r i + 1 / 8) :=
    Finset.sum_congr rfl fun i _ => d.degree_eq i
  have hr : (∑ i ∈ d.Aᶜ, d.r i) = 0 :=
    Finset.sum_eq_zero fun i hi => d.r_eq_zero_of_not_mem_A (Finset.mem_compl.1 hi)
  have hcard : (d.Aᶜ).card = 5 - d.A.card := by
    rw [Finset.card_compl]; simp
  rw [hstep, Finset.sum_add_distrib, hr, Finset.sum_const, nsmul_eq_mul, hcard]
  have hle : d.A.card ≤ 5 := by
    simpa using Finset.card_le_card (Finset.subset_univ d.A)
  push_cast [Nat.cast_sub hle]
  ring


/-- `b i` vanishes off the active set. -/
theorem b_eq_zero_of_not_mem_A {i : Fin 5} (hi : i ∉ d.A) : d.b i = 0 := by
  have := d.r_eq_zero_of_not_mem_A hi
  simpa [r, Complex.normSq_eq_zero] using this

/-- The four-way split of the total weight.  `SAA - SII = (|A| - 1)/4`. -/
theorem split_identity :
    ((∑ i ∈ d.A, ∑ j ∈ d.A, d.w i j) - ∑ i ∈ d.Aᶜ, ∑ j ∈ d.Aᶜ, d.w i j)
      = (d.A.card - 1 : ℝ) / 4 := by
  have hA : (∑ i ∈ d.A, ∑ j ∈ d.A, d.w i j) + ∑ i ∈ d.A, ∑ j ∈ d.Aᶜ, d.w i j
      = 3 / 8 + d.A.card / 8 := by
    rw [← Finset.sum_add_distrib]
    have hsplit : ∀ i, (∑ j ∈ d.A, d.w i j) + ∑ j ∈ d.Aᶜ, d.w i j = ∑ j, d.w i j :=
      fun i => Finset.sum_add_sum_compl d.A _
    rw [Finset.sum_congr rfl fun i _ => hsplit i]
    exact d.sum_degree_A
  have hI : (∑ i ∈ d.Aᶜ, ∑ j ∈ d.A, d.w i j) + ∑ i ∈ d.Aᶜ, ∑ j ∈ d.Aᶜ, d.w i j
      = (5 - d.A.card : ℝ) / 8 := by
    rw [← Finset.sum_add_distrib]
    have hsplit : ∀ i, (∑ j ∈ d.A, d.w i j) + ∑ j ∈ d.Aᶜ, d.w i j = ∑ j, d.w i j :=
      fun i => Finset.sum_add_sum_compl d.A _
    rw [Finset.sum_congr rfl fun i _ => hsplit i]
    exact d.sum_degree_compl
  have hsymm : (∑ i ∈ d.Aᶜ, ∑ j ∈ d.A, d.w i j)
      = ∑ i ∈ d.A, ∑ j ∈ d.Aᶜ, d.w i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => d.w_symm j i
  rw [hsymm] at hI
  linarith

theorem sum_AA_nonneg : 0 ≤ ∑ i ∈ d.A, ∑ j ∈ d.A, d.w i j :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => d.w_nonneg i j

theorem sum_II_nonneg : 0 ≤ ∑ i ∈ d.Aᶜ, ∑ j ∈ d.Aᶜ, d.w i j :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => d.w_nonneg i j

/-- Rows at an active vertex see only active neighbours, so `rowSupport` is the
degree in the graph induced on `A`. -/
theorem rowSupport_subset_A (i : Fin 5) : d.rowSupport i ⊆ d.A.erase i := by
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_erase.2 ⟨Ne.symm (Ne.symm (Finset.ne_of_mem_erase hj1)),
    d.mem_A.2 hj2.1⟩

/-- If `A` has an internal edge at `i`, then `i` is adjacent to every other
active vertex: the induced degree cannot be one. -/
theorem rowSupport_eq_erase_of_mem {i j : Fin 5} (hcard : d.A.card = 3)
    (hi : i ∈ d.A) (hj : j ∈ d.rowSupport i) : d.rowSupport i = d.A.erase i := by
  have hsub := d.rowSupport_subset_A i
  have hcard2 : (d.A.erase i).card = 2 := by
    rw [Finset.card_erase_of_mem hi, hcard]
  have hne1 : (d.rowSupport i).card ≠ 1 := d.rowSupport_card_ne_one i
  have hpos : 0 < (d.rowSupport i).card := Finset.card_pos.2 ⟨j, hj⟩
  have hle : (d.rowSupport i).card ≤ 2 := by
    rw [← hcard2]; exact Finset.card_le_card hsub
  have : (d.rowSupport i).card = 2 := by omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, this])


/-- A row at `i`, restricted to the active set: terms off `A` carry `b j = 0`. -/
theorem row_over_A (i : Fin 5) :
    (∑ j ∈ d.A.erase i, d.b j * d.c i j) = 0 := by
  rw [← d.row i]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    obtain ⟨hji, hjA⟩ := Finset.mem_erase.1 hj
    exact Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩
  · intro j hjuniv hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hjuniv
    have hjA : j ∉ d.A := fun hmem => hj (Finset.mem_erase.2 ⟨hji, hmem⟩)
    rw [d.b_eq_zero_of_not_mem_A hjA, zero_mul]

/-! ## The size of the active set -/

theorem card_A_ne_zero : d.A.card ≠ 0 := by
  intro h
  have hempty : d.A = ∅ := Finset.card_eq_zero.1 h
  have : (∑ i, d.r i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => d.r_eq_zero_of_not_mem_A ?_
    rw [hempty]; simp
  rw [d.total_point'] at this
  norm_num at this

theorem card_A_ne_one : d.A.card ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
  obtain ⟨k, hk⟩ := d.nbhd_nonempty a
  obtain ⟨hka, hkedge⟩ := Finset.mem_filter.1 hk
  have hane : a ≠ k := Ne.symm (Finset.ne_of_mem_erase hka)
  have haA : a ∈ d.A := by rw [ha]; exact Finset.mem_singleton_self a
  have hsingle : d.rowSupport k = {a} := by
    apply Finset.Subset.antisymm
    · intro j hj
      have : j ∈ d.A.erase k := d.rowSupport_subset_A k hj
      have hjA : j ∈ d.A := (Finset.mem_erase.1 this).2
      rw [ha] at hjA
      exact hjA
    · intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      refine Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hane, Finset.mem_univ j⟩, ?_, ?_⟩
      · exact d.mem_A.1 haA
      · rw [Edge, d.w_symm]; exact hkedge
  exact d.rowSupport_card_ne_one k (by rw [hsingle, Finset.card_singleton])

theorem card_A_ne_two : d.A.card ≠ 2 := by
  intro h
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.1 h
  have haA : a ∈ d.A := by rw [hset]; simp
  have hbA : b ∈ d.A := by rw [hset]; simp
  by_cases hedge : d.Edge a b
  · -- the row at `a` then has the single active neighbour `b`
    have hsingle : d.rowSupport a = {b} := by
      apply Finset.Subset.antisymm
      · intro j hj
        have hj' : j ∈ d.A.erase a := d.rowSupport_subset_A a hj
        obtain ⟨hja, hjA⟩ := Finset.mem_erase.1 hj'
        rw [hset, Finset.mem_insert, Finset.mem_singleton] at hjA
        rcases hjA with rfl | rfl
        · exact absurd rfl hja
        · exact Finset.mem_singleton_self j
      · intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ j⟩,
          d.mem_A.1 hbA, hedge⟩
    exact d.rowSupport_card_ne_one a (by rw [hsingle, Finset.card_singleton])
  · -- otherwise the internal weight vanishes and the split identity is negative
    have hw : d.w a b = 0 := le_antisymm (not_lt.1 hedge) (d.w_nonneg a b)
    have hAA : (∑ i ∈ d.A, ∑ j ∈ d.A, d.w i j) = 0 := by
      rw [hset]
      rw [Finset.sum_pair hab]
      rw [Finset.sum_pair hab, Finset.sum_pair hab]
      rw [d.w_diag a, d.w_diag b, hw, d.w_symm b a, hw]
      ring
    have hsplit := d.split_identity
    rw [hAA, h] at hsplit
    have hII := d.sum_II_nonneg
    norm_num at hsplit
    linarith

/-- **`lem:q4o30threepoints`.**  At least three point amplitudes are active. -/
theorem three_le_card_A : 3 ≤ d.A.card := by
  have h0 := d.card_A_ne_zero
  have h1 := d.card_A_ne_one
  have h2 := d.card_A_ne_two
  omega


/-- With three active points the induced weight is at least `1/2`, so the
graph induced on `A` has an edge. -/
theorem exists_internal_edge (h : d.A.card = 3) :
    ∃ x ∈ d.A, ∃ y ∈ d.A, 0 < d.w x y := by
  have hsplit := d.split_identity
  rw [h] at hsplit
  have hII := d.sum_II_nonneg
  by_contra hcon
  push_neg at hcon
  have hAA : (∑ i ∈ d.A, ∑ j ∈ d.A, d.w i j) = 0 :=
    Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
      le_antisymm (hcon i hi j hj) (d.w_nonneg i j)
  rw [hAA] at hsplit
  norm_num at hsplit
  linarith

/-- **`lem:q4o30exceptional`, in its stronger form.**

Under the synchronised weight-one interface the active set cannot have exactly
three elements at all.  The manuscript's own computation already gives
`W_AA - w_rs = 1/4`, so the induced graph on `A` is nonempty whether or not
the inactive-inactive edge is present; the induced degree cannot be one, so
the induced graph is the full triangle, and the triangle rows are
inconsistent.

The manuscript states the weaker conclusion because at that point in its
argument the synchronisation of `eq:q4o30globalsync` is not yet available in
general and has to be produced separately for the exceptional branch.  This
file takes the synchronised rows as its interface throughout, which is why the
conclusion here is the stronger one; `q4o30_exceptional` below is the
manuscript's statement. -/
theorem card_A_ne_three : d.A.card ≠ 3 := by
  intro h
  obtain ⟨x, hxA, y, hyA, hxy⟩ := d.exists_internal_edge h
  have hxyne : x ≠ y := by
    rintro rfl
    rw [d.w_diag x] at hxy
    exact lt_irrefl 0 hxy
  -- `y` is an active neighbour of `x`, so the induced degree at `x` is two
  have hymem : y ∈ d.rowSupport x :=
    Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨Ne.symm hxyne, Finset.mem_univ y⟩,
      d.mem_A.1 hyA, hxy⟩
  have hrx : d.rowSupport x = d.A.erase x := d.rowSupport_eq_erase_of_mem h hxA hymem
  have hcard2 : (d.A.erase x).card = 2 := by rw [Finset.card_erase_of_mem hxA, h]
  obtain ⟨u, v, huv, hset⟩ := Finset.card_eq_two.1 hcard2
  -- name the third vertex `z`
  have hymem' : y ∈ d.A.erase x := by rw [← hrx]; exact hymem
  rw [hset, Finset.mem_insert, Finset.mem_singleton] at hymem'
  obtain ⟨z, hyz, hsetyz⟩ : ∃ z, y ≠ z ∧ d.A.erase x = {y, z} := by
    rcases hymem' with rfl | rfl
    · exact ⟨v, huv, hset⟩
    · exact ⟨u, Ne.symm huv, by rw [hset, Finset.pair_comm]⟩
  have hzmem : z ∈ d.A.erase x := by rw [hsetyz]; simp
  obtain ⟨hxz', hzA⟩ := Finset.mem_erase.1 hzmem
  have hxz : x ≠ z := Ne.symm hxz'
  have hAxyz : d.A = {x, y, z} := by
    rw [← Finset.insert_erase hxA, hsetyz]
  -- the three edges of the triangle
  have hEdgexz : d.Edge x z := by
    have : z ∈ d.rowSupport x := by rw [hrx, hsetyz]; simp
    exact (Finset.mem_filter.1 this).2.2
  have hymemA : y ∈ d.A := hyA
  have hxymem : x ∈ d.rowSupport y :=
    Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hxyne, Finset.mem_univ x⟩,
      d.mem_A.1 hxA, by rw [Edge, d.w_symm]; exact hxy⟩
  have hry : d.rowSupport y = d.A.erase y := d.rowSupport_eq_erase_of_mem h hymemA hxymem
  have heraseY : d.A.erase y = {x, z} := by
    rw [hAxyz]
    ext t
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, (rfl | rfl | rfl)⟩
      · exact Or.inl rfl
      · exact absurd rfl ht
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hxyne, Or.inl rfl⟩
      · exact ⟨Ne.symm hyz, Or.inr (Or.inr rfl)⟩
  have heraseZ : d.A.erase z = {x, y} := by
    rw [hAxyz]
    ext t
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, (rfl | rfl | rfl)⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl ht
    · rintro (rfl | rfl)
      · exact ⟨hxz, Or.inl rfl⟩
      · exact ⟨hyz, Or.inr (Or.inl rfl)⟩
  -- the three synchronised rows
  have rowx := d.row_over_A x
  have rowy := d.row_over_A y
  have rowz := d.row_over_A z
  rw [hsetyz, Finset.sum_pair hyz] at rowx
  rw [heraseY, Finset.sum_pair hxz] at rowy
  rw [heraseZ, Finset.sum_pair hxyne] at rowz
  refine triangle_contradiction (b0 := d.b x) (b1 := d.b y) (b2 := d.b z)
    (c01 := d.c x y) (c02 := d.c x z) (c12 := d.c y z) ?_ ?_ ?_ rowx ?_ ?_
  · exact fun h0 => absurd (d.mem_A.1 hxA) (by simp [Active, r, h0])
  · exact fun h0 => absurd (d.mem_A.1 hyA) (by simp [Active, r, h0])
  · exact fun h0 => absurd hxy (by simp [w, h0])
  · rw [d.c_symm y x] at rowy; exact rowy
  · rw [d.c_symm z x, d.c_symm z y] at rowz; exact rowz

/-- **`lem:q4o30exceptional`**, as the manuscript states it: when three point
amplitudes are active, the edge joining the two inactive vertices is absent. -/
theorem q4o30_exceptional (h : d.A.card = 3) {rr ss : Fin 5}
    (_hr : rr ∉ d.A) (_hs : ss ∉ d.A) : ¬ d.Edge rr ss :=
  absurd h d.card_A_ne_three

/-- Combining `lem:q4o30threepoints` with the stronger form: at least four
point amplitudes are active. -/
theorem four_le_card_A : 4 ≤ d.A.card := by
  have h3 := d.three_le_card_A
  have hne := d.card_A_ne_three
  omega

end Data

end MainTheory.Orbit30
