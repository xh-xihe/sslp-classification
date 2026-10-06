import Mathlib

import SS.HilbertKL
import SS.BridgeD3
import SixQubit.Common

/-!
# From a genuine code to the combinatorial no-go systems

Every headline in this directory takes its Knill--Laflamme rows as *hypotheses*:
`offSum c d e z = 0`, `diagBot c e z = diagTop d e z`, and a `MomentSystem` of
occupation-number equalities.  Read literally, such a theorem says only that a
finite system of equations has no solution.

This module supplies the missing quantifier.  Given

* two finite supports `S₀`, `S₁` and amplitude vectors `c`, `d` supported on them,
* normalization `⟪c, c⟫ = ⟪d, d⟫ = 1`,
* and `SS.HasDistance ![c, d] 3`, i.e. the honest Knill--Laflamme conditions
  `⟪ψⱼ, P ψₖ⟫ = c_P δⱼₖ` for every Pauli of weight `≤ 2`,

it *derives* each of those rows.  The three obligations are

* **(A) off-diagonal**: `SS.KLCondition` at `j ≠ k` gives `offSumOn S₀ S₁ c d e z = 0`
  for the flip mask `e` and dressing `z` of the Pauli `P = ⟨e, z⟩`
  (`offSumOn_eq_zero_of_hasDistance`);
* **(B) diagonal**: `SS.KLCondition` at `j = k`, whose scalar `c_P` is the *same*
  on both logical states, gives `diagOn S₀ c e z = diagOn S₁ d e z`
  (`diagOn_eq_of_hasDistance`);
* **(B') occupation numbers**: for a pure-`Z` Pauli the diagonal condition is an
  equality of Walsh characters, and the explicit change of basis
  `character = mass - 2 · occupation` (resp. its two-coordinate version) turns it
  into the occupation-number rows of a `MomentSystem`
  (`occOn_eq_of_hasDistance`, `occ2On_eq_of_hasDistance`).

Orthogonality `⟪c, d⟫ = 0` is *not* assumed: it is proved from disjoint supports
(`innerC_eq_zero_of_disjoint`).

The prefactor that `SixQubit.diagTerm` / `offdiagTerm` deliberately drop is
computed here rather than assumed to be `1`: it is `Complex.I ^ P.numY`, nonzero
by `SS.pauliPrefactor_ne_zero`, and for the pure-`Z` Paulis used by (B') it is
literally `1` because `numY = 0` (`numY_of_x_zero`).

No `sorry`, no `native_decide`.
-/

namespace SixQubit

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

/-! ## Bitstring dot products against standard basis vectors -/

/-- `bdot` is symmetric. -/
lemma bdot_comm (s t : SS.BitString n) : SS.bdot s t = SS.bdot t s := by
  classical
  have h : (Finset.univ.filter (fun i => s i && t i))
      = (Finset.univ.filter (fun i => t i && s i)) := by
    ext i; simp [Bool.and_comm]
  unfold SS.bdot
  rw [h]

/-- `bdot` is additive over `GF(2)` in its **first** argument. -/
lemma bdot_bxor_left (s t u : SS.BitString n) :
    SS.bdot (SS.bxor s t) u = xor (SS.bdot s u) (SS.bdot t u) := by
  rw [bdot_comm, SS.bdot_bxor_right, bdot_comm s u, bdot_comm t u]

/-- Pairing with the standard basis vector `eᵢ` reads off the `i`-th bit. -/
lemma bdot_stdBasis (i : Fin n) (x : SS.BitString n) :
    SS.bdot (SS.stdBasis i) x = x i := by
  classical
  unfold SS.bdot
  by_cases h : x i = true
  · have hf : (Finset.univ.filter (fun k => SS.stdBasis i k && x k)) = {i} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        SS.stdBasis, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨hk, -⟩; exact hk
      · rintro rfl; exact ⟨rfl, h⟩
    rw [hf, Finset.card_singleton, h]
    rfl
  · have hx : x i = false := by
      cases hb : x i with
      | false => rfl
      | true => exact absurd hb h
    have hf : (Finset.univ.filter (fun k => SS.stdBasis i k && x k)) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, Bool.and_eq_true, SS.stdBasis, beq_iff_eq, not_and]
      rintro rfl
      simp [hx]
    rw [hf, Finset.card_empty, hx]
    rfl

/-- Pairing with `eᵢ ⊕ eⱼ` reads off the parity of the two bits. -/
lemma bdot_stdBasis_pair (i j : Fin n) (x : SS.BitString n) :
    SS.bdot (SS.bxor (SS.stdBasis i) (SS.stdBasis j)) x = xor (x i) (x j) := by
  rw [bdot_bxor_left, bdot_stdBasis, bdot_stdBasis]

/-! ## Pauli weights -/

/-- A Pauli supported inside `T` has weight at most `T.card`. -/
lemma wt_le_of_support (P : SS.PauliString n) (T : Finset (Fin n))
    (h : ∀ k, (P.x k = true ∨ P.z k = true) → k ∈ T) : P.wt ≤ T.card := by
  classical
  unfold SS.PauliString.wt
  refine Finset.card_le_card ?_
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true] at hk
  exact h k hk

/-- `Zᵢ` has weight one. -/
lemma wt_pureZ_single (i : Fin n) :
    (⟨fun _ => false, SS.stdBasis i⟩ : SS.PauliString n).wt ≤ 1 := by
  classical
  have h := wt_le_of_support (⟨fun _ => false, SS.stdBasis i⟩ : SS.PauliString n)
    ({i} : Finset (Fin n)) (by
      intro k hk
      rcases hk with hk | hk
      · exact absurd hk (by simp)
      · simp only [SS.stdBasis, beq_iff_eq] at hk
        simp [hk])
  simpa using h

/-- `Zᵢ Zⱼ` has weight at most two. -/
lemma wt_pureZ_pair (i j : Fin n) :
    (⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩ : SS.PauliString n).wt ≤ 2 := by
  classical
  have h := wt_le_of_support
    (⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩ : SS.PauliString n)
    ({i, j} : Finset (Fin n)) (by
      intro k hk
      rcases hk with hk | hk
      · exact absurd hk (by simp)
      · by_cases hki : k = i
        · simp [hki]
        · by_cases hkj : k = j
          · simp [hkj]
          · have hk' : SS.bxor (SS.stdBasis i) (SS.stdBasis j) k = true := hk
            rw [SS.bxor_apply, SS.stdBasis_apply_ne hki,
              SS.stdBasis_apply_ne hkj] at hk'
            simp at hk')
  refine h.trans ?_
  exact (Finset.card_insert_le _ _).trans (by simp)

/-- A Pauli with trivial `X` part has no `Y` factors, so its prefactor is `1`. -/
lemma numY_of_x_zero (z : SS.BitString n) :
    (⟨fun _ => false, z⟩ : SS.PauliString n).numY = 0 := by
  classical
  unfold SS.PauliString.numY
  simp

/-! ## The generic support sums

These are the orbit modules' `offSum`, `diagBot` and `diagTop`, with the two
supports abstracted out.  Each orbit module's definition is this one applied to
its own `S0` / `S1`, so the per-orbit identification is `rfl`. -/

/-- The off-diagonal support sum: `∑_{y ∈ S₁, y⊕e ∈ S₀} (-1)^{z·y} conj(c_{y⊕e}) d_y`.
The global prefactor `i^{#Y}` is dropped, exactly as in `SixQubit.offdiagTerm`. -/
def offSumOn (S₀ S₁ : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (e z : SS.BitString n) : ℂ :=
  ∑ y ∈ S₁.filter (fun y => SS.bxor y e ∈ S₀),
      signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

/-- The diagonal support sum on one fiber. -/
def diagOn (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (e z : SS.BitString n) : ℂ :=
  ∑ x ∈ S.filter (fun x => SS.bxor x e ∈ S),
      signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

/-- The matrix element `⟪c, P d⟫` is the off-diagonal support sum times `i^{#Y}`. -/
theorem innerC_eq_offSumOn (S₀ S₁ : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0) (P : SS.PauliString n) :
    SS.innerC c (SS.pauliAct P d)
      = Complex.I ^ P.numY * offSumOn S₀ S₁ c d P.x P.z := by
  rw [SS.innerC_pauliAct_support S₀ S₁ c d P hc hd]
  rfl

/-- The matrix element `⟪c, P c⟫` is the diagonal support sum times `i^{#Y}`. -/
theorem innerC_eq_diagOn (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S → c x = 0) (P : SS.PauliString n) :
    SS.innerC c (SS.pauliAct P c)
      = Complex.I ^ P.numY * diagOn S c P.x P.z := by
  rw [SS.innerC_pauliAct_support S S c c P hc hc]
  rfl

/-! ## Reading the two logical states out of `![c, d]` -/

@[simp] lemma pair_zero (c d : SS.BitString n → ℂ) :
    (![c, d] : Fin 2 → SS.State n ℂ) 0 = c := rfl

@[simp] lemma pair_one (c d : SS.BitString n → ℂ) :
    (![c, d] : Fin 2 → SS.State n ℂ) 1 = d := rfl

/-! ## Obligation (A): the off-diagonal rows -/

/-- **Obligation (A).**  A distance-three code makes every off-diagonal support
sum vanish, for every flip mask/dressing pair of Pauli weight at most two. -/
theorem offSumOn_eq_zero_of_hasDistance
    (S₀ S₁ : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0)
    (hdist : SS.HasDistance ![c, d] 3)
    (e z : SS.BitString n) (hw : (⟨e, z⟩ : SS.PauliString n).wt ≤ 2) :
    offSumOn S₀ S₁ c d e z = 0 := by
  have hdet : SS.Detects (![c, d] : Fin 2 → SS.State n ℂ) 2 := hdist
  obtain ⟨κ, hκ⟩ := hdet ⟨e, z⟩ hw
  have h01 := hκ 0 1
  rw [if_neg (by decide)] at h01
  rw [pair_zero, pair_one, innerC_eq_offSumOn S₀ S₁ c d hc hd] at h01
  exact (mul_eq_zero.mp h01).resolve_left (SS.pauliPrefactor_ne_zero _)

/-! ## Obligation (B): the diagonal rows -/

/-- **Obligation (B).**  The Knill--Laflamme scalar `c_P` is the same on both
logical states, so the two diagonal support sums agree. -/
theorem diagOn_eq_of_hasDistance
    (S₀ S₁ : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0)
    (hdist : SS.HasDistance ![c, d] 3)
    (e z : SS.BitString n) (hw : (⟨e, z⟩ : SS.PauliString n).wt ≤ 2) :
    diagOn S₀ c e z = diagOn S₁ d e z := by
  have hdet : SS.Detects (![c, d] : Fin 2 → SS.State n ℂ) 2 := hdist
  obtain ⟨κ, hκ⟩ := hdet ⟨e, z⟩ hw
  have h00 := hκ 0 0
  have h11 := hκ 1 1
  rw [if_pos rfl] at h00
  rw [if_pos rfl] at h11
  rw [pair_zero, innerC_eq_diagOn S₀ c hc] at h00
  rw [pair_one, innerC_eq_diagOn S₁ d hd] at h11
  have h : Complex.I ^ (⟨e, z⟩ : SS.PauliString n).numY * diagOn S₀ c e z
      = Complex.I ^ (⟨e, z⟩ : SS.PauliString n).numY * diagOn S₁ d e z := by
    rw [h00, h11]
  exact mul_left_cancel₀ (SS.pauliPrefactor_ne_zero _) h

/-! ## Obligation (B'): occupation numbers

The `MomentSystem` rows are occupation-number equalities.  They are the diagonal
conditions for `Zᵢ` and `Zᵢ Zⱼ` after the change of basis between Walsh characters
and occupation numbers, which is carried out explicitly below. -/

/-- Total probability mass carried by a support. -/
def massOn (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ) : ℝ :=
  ∑ x ∈ S, Complex.normSq (c x)

/-- Occupation number of coordinate `i`. -/
def occOn (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ) (i : Fin n) : ℝ :=
  ∑ x ∈ S.filter (fun x => x i = true), Complex.normSq (c x)

/-- Joint occupation number of the coordinate pair `(i, j)`. -/
def occ2On (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ) (i j : Fin n) : ℝ :=
  ∑ x ∈ S.filter (fun x => x i = true ∧ x j = true), Complex.normSq (c x)

/-- The Walsh character sum `∑ₓ (-1)^{z·x} |c_x|²`. -/
def charOn (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (z : SS.BitString n) : ℝ :=
  ∑ x ∈ S, (if SS.bdot z x then -Complex.normSq (c x) else Complex.normSq (c x))

/-- The self-inner-product is the total mass. -/
lemma innerC_self_eq_massOn (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S → c x = 0) :
    SS.innerC c c = ((massOn S c : ℝ) : ℂ) := by
  classical
  unfold SS.innerC massOn
  rw [Complex.ofReal_sum]
  refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm.trans ?_
  · intro x _ hx
    simp [hc x hx]
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    simp [Complex.normSq_eq_conj_mul_self]

/-- Normalization pins the total mass to one. -/
lemma massOn_eq_one (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S → c x = 0) (hn : SS.innerC c c = 1) :
    massOn S c = 1 := by
  have h := (innerC_self_eq_massOn S c hc).symm.trans hn
  exact_mod_cast h

/-- The pure-`Z` matrix element is exactly the Walsh character sum: the prefactor
`i^{#Y}` is `1` here, since a pure-`Z` Pauli has no `Y` factors. -/
lemma innerC_pureZ_eq_charOn (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S → c x = 0) (z : SS.BitString n) :
    SS.innerC c (SS.pauliAct (⟨fun _ => false, z⟩ : SS.PauliString n) c)
      = ((charOn S c z : ℝ) : ℂ) := by
  classical
  rw [innerC_eq_diagOn S c hc, numY_of_x_zero, pow_zero, one_mul]
  unfold diagOn charOn
  rw [Complex.ofReal_sum]
  have hfil : S.filter (fun x => SS.bxor x (fun _ => false) ∈ S) = S := by
    refine Finset.filter_true_of_mem (fun x hx => ?_)
    simpa using hx
  rw [hfil]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx : SS.bxor x (fun _ => false) = x := SS.bxor_zero x
  rw [hx]
  cases hb : SS.bdot z x <;>
    simp [signMul, Complex.normSq_eq_conj_mul_self]

/-- The Walsh characters of the two logical states agree, for every dressing `z`
of Hamming weight at most two. -/
theorem charOn_eq_of_hasDistance
    (S₀ S₁ : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0)
    (hdist : SS.HasDistance ![c, d] 3)
    (z : SS.BitString n) (hw : (⟨fun _ => false, z⟩ : SS.PauliString n).wt ≤ 2) :
    charOn S₀ c z = charOn S₁ d z := by
  have hdet : SS.Detects (![c, d] : Fin 2 → SS.State n ℂ) 2 := hdist
  obtain ⟨κ, hκ⟩ := hdet ⟨fun _ => false, z⟩ hw
  have h00 := hκ 0 0
  have h11 := hκ 1 1
  rw [if_pos rfl] at h00
  rw [if_pos rfl] at h11
  rw [pair_zero, innerC_pureZ_eq_charOn S₀ c hc] at h00
  rw [pair_one, innerC_pureZ_eq_charOn S₁ d hd] at h11
  have : ((charOn S₀ c z : ℝ) : ℂ) = ((charOn S₁ d z : ℝ) : ℂ) := by rw [h00, h11]
  exact_mod_cast this

/-! ### The change of basis: characters ↔ occupation numbers -/

/-- One-coordinate change of basis: `∑ₓ (-1)^{xᵢ}|c_x|² = mass − 2·occᵢ`. -/
lemma charOn_stdBasis (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (i : Fin n) :
    charOn S c (SS.stdBasis i) = massOn S c - 2 * occOn S c i := by
  classical
  have key : ∀ x : SS.BitString n,
      (if SS.bdot (SS.stdBasis i) x then -Complex.normSq (c x) else Complex.normSq (c x))
        = Complex.normSq (c x)
            - 2 * (if x i = true then Complex.normSq (c x) else 0) := by
    intro x
    rw [bdot_stdBasis]
    cases x i
    · simp
    · simp
      ring
  unfold charOn massOn occOn
  rw [Finset.sum_filter, Finset.sum_congr rfl (fun x _ => key x),
    Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Two-coordinate change of basis:
`∑ₓ (-1)^{xᵢ ⊕ xⱼ}|c_x|² = mass − 2·occᵢ − 2·occⱼ + 4·occᵢⱼ`. -/
lemma charOn_stdBasis_pair (S : Finset (SS.BitString n)) (c : SS.BitString n → ℂ)
    (i j : Fin n) :
    charOn S c (SS.bxor (SS.stdBasis i) (SS.stdBasis j))
      = massOn S c - 2 * occOn S c i - 2 * occOn S c j + 4 * occ2On S c i j := by
  classical
  have key : ∀ x : SS.BitString n,
      (if SS.bdot (SS.bxor (SS.stdBasis i) (SS.stdBasis j)) x
        then -Complex.normSq (c x) else Complex.normSq (c x))
        = Complex.normSq (c x)
            - 2 * (if x i = true then Complex.normSq (c x) else 0)
            - 2 * (if x j = true then Complex.normSq (c x) else 0)
            + 4 * (if x i = true ∧ x j = true then Complex.normSq (c x) else 0) := by
    intro x
    rw [bdot_stdBasis_pair]
    cases x i <;> cases x j <;> simp <;> ring
  unfold charOn massOn occOn occ2On
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_congr rfl (fun x _ => key x),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Obligation (B'), one-bit rows.**  A distance-three code has equal
occupation numbers on the two fibers. -/
theorem occOn_eq_of_hasDistance
    (S₀ S₁ : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) (i : Fin n) :
    occOn S₀ c i = occOn S₁ d i := by
  have hm0 := massOn_eq_one S₀ c hc hnc
  have hm1 := massOn_eq_one S₁ d hd hnd
  have hch := charOn_eq_of_hasDistance S₀ S₁ c d hc hd hdist (SS.stdBasis i)
    ((wt_pureZ_single i).trans (by norm_num))
  rw [charOn_stdBasis, charOn_stdBasis, hm0, hm1] at hch
  linarith

/-- **Obligation (B'), two-bit rows.**  Likewise for the joint occupation numbers. -/
theorem occ2On_eq_of_hasDistance
    (S₀ S₁ : Finset (SS.BitString n)) (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) (i j : Fin n) :
    occ2On S₀ c i j = occ2On S₁ d i j := by
  have hm0 := massOn_eq_one S₀ c hc hnc
  have hm1 := massOn_eq_one S₁ d hd hnd
  have hi := occOn_eq_of_hasDistance S₀ S₁ c d hc hd hnc hnd hdist i
  have hj := occOn_eq_of_hasDistance S₀ S₁ c d hc hd hnc hnd hdist j
  have hch := charOn_eq_of_hasDistance S₀ S₁ c d hc hd hdist
    (SS.bxor (SS.stdBasis i) (SS.stdBasis j)) (wt_pureZ_pair i j)
  rw [charOn_stdBasis_pair, charOn_stdBasis_pair, hm0, hm1, hi, hj] at hch
  linarith

/-! ## Orthogonality is free -/

/-- Two states supported on disjoint sets are orthogonal.  The orbit modules
therefore never need to assume `⟪c, d⟫ = 0`. -/
theorem innerC_eq_zero_of_disjoint (S₀ S₁ : Finset (SS.BitString n))
    (c d : SS.BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0)
    (hdisj : Disjoint S₀ S₁) :
    SS.innerC c d = 0 := by
  classical
  unfold SS.innerC
  refine Finset.sum_eq_zero (fun s _ => ?_)
  by_cases h : s ∈ S₀
  · rw [hd s (Finset.disjoint_left.mp hdisj h), mul_zero]
  · rw [hc s h, star_zero, zero_mul]

end

end SixQubit
