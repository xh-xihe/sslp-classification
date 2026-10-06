import Mathlib

import SS.HilbertKL
import SS.BridgeD3
import SixQubit.Common

/-!
# From an actual distance-3 code to the orbit-level algebraic systems

Every headline theorem in `SixQubit/Orbit*.lean` takes its Knill--Laflamme rows
as *hypotheses*: `offSum c d e z = 0`, `diagBot c e z = diagTop d e z`, and a
`MomentSystem` record of occupation-number equalities.  Read literally, those
theorems say "this finite system of equations is unsatisfiable".

This module supplies the missing implication

  `SS.HasDistance ![c, d] 3`  ⟹  every one of those rows,

so that the orbit theorems can be restated as "no code of this shape exists".

It is deliberately *not* a general theory of stabiliser codes.  It is exactly the
bridge the orbit files need: a pair of supports `S₀ S₁ : Finset (BitString n)`, a
pair of fibre amplitude vectors `c d`, and Paulis `P = X^e Z^z` with
`|supp e ∪ supp z| ≤ 2` (which is all that distance 3 controls).  Everything is
stated with `e` and `z` as **explicit bit strings**, so an orbit instantiates it
at its own masks and discharges the weight side condition by `decide`.

## Contents

* `offSumG`, `diagBotG`, `diagTopG` --- the three orbit-level sums, verbatim as
  the orbit files write them but over arbitrary `S₀`, `S₁`.  Each orbit's local
  `offSum`/`diagBot`/`diagTop` is *definitionally* the corresponding `…G` at its
  own supports, so the connecting lemma is `rfl`.
* `IsCode` --- the code-side hypotheses: supported on the two fibres, both
  normalised, and `SS.HasDistance … 3`.  Nothing about Walsh sums or moments.
* `IsCode.orthogonal` --- the logical states are orthogonal, *derived* from
  disjointness of the supports rather than assumed.
* `IsCode.offSumG_eq_zero` --- obligation (A): the off-diagonal rows.
* `IsCode.diagBotG_eq_diagTopG` --- obligation (B), general flip mask `e`.
* `IsCode.mass0_eq_one`, `IsCode.occ1_eq`, `IsCode.occ2_eq` --- obligation (B) for
  pure-`Z` Paulis, after the explicit change of basis between Walsh characters
  `(-1)^{z·x}` and occupation numbers (`charSum_zMask1`, `charSum_zMask2`).

The global prefactor that `SixQubit.diagTerm` and friends deliberately drop is
*computed* here --- it is `Complex.I ^ P.numY` --- and proved nonzero
(`SS.pauliPrefactor_ne_zero`), so vanishing of the matrix element transfers to
vanishing of the orbit sum.

No `sorry`, no `native_decide`.
-/

namespace SixQubit.MaskBridge

open SS
open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

/-! ## The three orbit-level sums over arbitrary supports -/

/-- The off-diagonal Walsh sum, over arbitrary supports.  This is character-for-
character the `offSum` that every orbit module defines at its own `S0`, `S1`. -/
def offSumG (S₀ S₁ : Finset (BitString n)) (c d : BitString n → ℂ)
    (e z : BitString n) : ℂ :=
  ∑ y ∈ S₁.filter (fun y => SS.bxor y e ∈ S₀),
      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)

/-- The bottom-fibre diagonal Walsh sum, over an arbitrary support. -/
def diagBotG (S₀ : Finset (BitString n)) (c : BitString n → ℂ)
    (e z : BitString n) : ℂ :=
  ∑ x ∈ S₀.filter (fun x => SS.bxor x e ∈ S₀),
      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)

/-- The top-fibre diagonal Walsh sum, over an arbitrary support. -/
def diagTopG (S₁ : Finset (BitString n)) (dd : BitString n → ℂ)
    (e z : BitString n) : ℂ :=
  ∑ y ∈ S₁.filter (fun y => SS.bxor y e ∈ S₁),
      SixQubit.signMul (SS.bdot z y) (star (dd (SS.bxor y e)) * dd y)

/-! ## The matrix element, with its prefactor computed -/

/-- **The matrix element of `X^e Z^z`.**  For `ψ` supported in `Sj` and `φ` in
`Sk`, the Knill--Laflamme matrix element is the orbit-level Walsh sum times the
nonzero prefactor `i^{#Y(P)}` that the orbit definitions drop. -/
theorem innerC_eq_walsh (Sj Sk : Finset (BitString n)) (ψ φ : BitString n → ℂ)
    (hψ : ∀ s, s ∉ Sj → ψ s = 0) (hφ : ∀ s, s ∉ Sk → φ s = 0) (e z : BitString n) :
    SS.innerC ψ (SS.pauliAct ⟨e, z⟩ φ)
      = Complex.I ^ (SS.PauliString.mk e z).numY *
          ∑ s ∈ Sk.filter (fun s => SS.bxor s e ∈ Sj),
            SixQubit.signMul (SS.bdot z s) (star (ψ (SS.bxor s e)) * φ s) := by
  classical
  rw [SS.innerC_pauliAct_support Sj Sk ψ φ ⟨e, z⟩ hψ hφ]
  congr 1

/-- Specialisation to the off-diagonal sum. -/
theorem innerC_eq_offSumG (S₀ S₁ : Finset (BitString n)) (c d : BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (hd : ∀ y, y ∉ S₁ → d y = 0) (e z : BitString n) :
    SS.innerC c (SS.pauliAct ⟨e, z⟩ d)
      = Complex.I ^ (SS.PauliString.mk e z).numY * offSumG S₀ S₁ c d e z :=
  innerC_eq_walsh S₀ S₁ c d hc hd e z

/-- Specialisation to the bottom diagonal sum. -/
theorem innerC_eq_diagBotG (S₀ : Finset (BitString n)) (c : BitString n → ℂ)
    (hc : ∀ x, x ∉ S₀ → c x = 0) (e z : BitString n) :
    SS.innerC c (SS.pauliAct ⟨e, z⟩ c)
      = Complex.I ^ (SS.PauliString.mk e z).numY * diagBotG S₀ c e z :=
  innerC_eq_walsh S₀ S₀ c c hc hc e z

/-- Specialisation to the top diagonal sum. -/
theorem innerC_eq_diagTopG (S₁ : Finset (BitString n)) (d : BitString n → ℂ)
    (hd : ∀ y, y ∉ S₁ → d y = 0) (e z : BitString n) :
    SS.innerC d (SS.pauliAct ⟨e, z⟩ d)
      = Complex.I ^ (SS.PauliString.mk e z).numY * diagTopG S₁ d e z :=
  innerC_eq_walsh S₁ S₁ d d hd hd e z

/-! ## `bdot` against the pure-`Z` masks -/

/-- `bdot` is symmetric. -/
lemma bdot_comm (s t : BitString n) : SS.bdot s t = SS.bdot t s := by
  unfold SS.bdot
  have hset : (Finset.univ.filter (fun i => s i && t i))
      = (Finset.univ.filter (fun i => t i && s i)) := by
    ext i
    simp [Bool.and_comm]
  rw [hset]

/-- The pure-`Z` mask of a single qubit. -/
def zMask1 (i : Fin n) : BitString n := SS.stdBasis i

/-- The pure-`Z` mask of a pair of qubits. -/
def zMask2 (i j : Fin n) : BitString n := SS.bxor (SS.stdBasis i) (SS.stdBasis j)

lemma bdot_stdBasis (i : Fin n) (x : BitString n) : SS.bdot (SS.stdBasis i) x = x i := by
  classical
  cases hx : x i with
  | true =>
      have hset : (Finset.univ.filter (fun k => SS.stdBasis i k && x k))
          = ({i} : Finset (Fin n)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          SS.stdBasis, Bool.and_eq_true, beq_iff_eq]
        constructor
        · rintro ⟨rfl, _⟩; rfl
        · rintro rfl; exact ⟨rfl, hx⟩
      unfold SS.bdot
      rw [hset]
      simp
  | false =>
      have hset : (Finset.univ.filter (fun k => SS.stdBasis i k && x k))
          = (∅ : Finset (Fin n)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, SS.stdBasis, Bool.and_eq_true, beq_iff_eq, not_and]
        rintro rfl
        simp [hx]
      unfold SS.bdot
      rw [hset]
      simp

lemma bdot_zMask1 (i : Fin n) (x : BitString n) : SS.bdot (zMask1 i) x = x i :=
  bdot_stdBasis i x

lemma bdot_zMask2 (i j : Fin n) (x : BitString n) :
    SS.bdot (zMask2 i j) x = xor (x i) (x j) := by
  rw [zMask2, bdot_comm, SS.bdot_bxor_right, bdot_comm x (SS.stdBasis i),
    bdot_comm x (SS.stdBasis j), bdot_stdBasis, bdot_stdBasis]

/-! ## Weights of the Paulis we instantiate

`HasDistance _ 3` is `Detects _ 2`, so every Pauli we feed to it must be checked
to have weight at most two --- in Lean, not on paper. -/

/-- A pure-`Z` Pauli has weight equal to the Hamming weight of its `z` mask. -/
lemma wt_pureZ (z : BitString n) :
    (SS.PauliString.mk (fun _ => false) z).wt = SS.hammingWt z := by
  classical
  unfold SS.PauliString.wt SS.hammingWt
  exact congrArg Finset.card (Finset.filter_congr (fun i _ => by simp))

lemma hammingWt_stdBasis (i : Fin n) : SS.hammingWt (SS.stdBasis i) = 1 := by
  classical
  have hset : (Finset.univ.filter (fun k => SS.stdBasis i k = true))
      = ({i} : Finset (Fin n)) := by
    ext k
    simp [SS.stdBasis]
  unfold SS.hammingWt
  rw [hset]
  exact Finset.card_singleton i

lemma hammingWt_zMask2_le (i j : Fin n) : SS.hammingWt (zMask2 i j) ≤ 2 := by
  classical
  have hsub : (Finset.univ.filter (fun k => zMask2 i j k = true))
      ⊆ ({i, j} : Finset (Fin n)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, zMask2, SS.bxor_apply,
      SS.stdBasis] at hk
    by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    rw [beq_eq_false_iff_ne.mpr hcon.1, beq_eq_false_iff_ne.mpr hcon.2] at hk
    simp at hk
  have h1 : (Finset.univ.filter (fun k => zMask2 i j k = true)).card
      ≤ ({i, j} : Finset (Fin n)).card := Finset.card_le_card hsub
  have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  exact le_trans h1 h2

lemma wt_zMask1_le_two (i : Fin n) :
    (SS.PauliString.mk (fun _ => false) (zMask1 i)).wt ≤ 2 := by
  rw [wt_pureZ, zMask1, hammingWt_stdBasis]
  norm_num

lemma wt_zMask2_le_two (i j : Fin n) :
    (SS.PauliString.mk (fun _ => false) (zMask2 i j)).wt ≤ 2 := by
  rw [wt_pureZ]
  exact hammingWt_zMask2_le i j

lemma wt_zero_le_two :
    (SS.PauliString.mk (fun _ => false) (fun _ => false) : SS.PauliString n).wt ≤ 2 := by
  rw [wt_pureZ]
  unfold SS.hammingWt
  simp

/-! ## Occupation numbers and Walsh characters -/

/-- Total probability mass carried by a fibre. -/
def mass (S : Finset (BitString n)) (c : BitString n → ℂ) : ℝ :=
  ∑ x ∈ S, Complex.normSq (c x)

/-- Single-qubit occupation number: the mass sitting on strings with `xᵢ = 1`. -/
def occ1 (S : Finset (BitString n)) (c : BitString n → ℂ) (i : Fin n) : ℝ :=
  ∑ x ∈ S.filter (fun x => x i = true), Complex.normSq (c x)

/-- Pair occupation number: the mass sitting on strings with `xᵢ = xⱼ = 1`. -/
def occ2 (S : Finset (BitString n)) (c : BitString n → ℂ) (i j : Fin n) : ℝ :=
  ∑ x ∈ S.filter (fun x => x i = true ∧ x j = true), Complex.normSq (c x)

/-- Pointwise change of basis, weight one: a single Walsh sign in terms of the
occupation indicator. -/
lemma expand1 (b : Bool) (q : ℝ) :
    (if b = true then -q else q) = q - 2 * (if b = true then q else 0) := by
  cases b
  · show q = q - 2 * (0 : ℝ)
    ring
  · show -q = q - 2 * q
    ring

/-- Pointwise change of basis, weight two. -/
lemma expand2 (b₁ b₂ : Bool) (q : ℝ) :
    (if (xor b₁ b₂) = true then -q else q)
      = q - 2 * (if b₁ = true then q else 0) - 2 * (if b₂ = true then q else 0)
        + 4 * (if b₁ = true ∧ b₂ = true then q else 0) := by
  cases b₁ <;> cases b₂
  · show q = q - 2 * (0 : ℝ) - 2 * (0 : ℝ) + 4 * (0 : ℝ)
    ring
  · show -q = q - 2 * (0 : ℝ) - 2 * q + 4 * (0 : ℝ)
    ring
  · show -q = q - 2 * q - 2 * (0 : ℝ) + 4 * (0 : ℝ)
    ring
  · show q = q - 2 * q - 2 * q + 4 * q
    ring

/-- The Walsh character sum `∑_{x ∈ S} (-1)^{z·x} |c x|²`. -/
def charSum (S : Finset (BitString n)) (c : BitString n → ℂ) (z : BitString n) : ℝ :=
  ∑ x ∈ S, (if SS.bdot z x then -Complex.normSq (c x) else Complex.normSq (c x))

/-- For the zero flip mask, both diagonal sums are the (real) Walsh character sum. -/
lemma diagBotG_zero_mask (S : Finset (BitString n)) (c : BitString n → ℂ)
    (z : BitString n) :
    diagBotG S c (fun _ => false) z = ((charSum S c z : ℝ) : ℂ) := by
  classical
  unfold diagBotG charSum
  rw [Complex.ofReal_sum]
  have hfil : S.filter (fun x => SS.bxor x (fun _ => false) ∈ S) = S := by
    refine Finset.filter_true_of_mem (fun x hx => ?_)
    simpa using hx
  rw [hfil]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [show SS.bxor x (fun _ => false) = x by simp, SixQubit.star_mul_self]
  cases SS.bdot z x <;> simp [SixQubit.signMul]

lemma diagTopG_zero_mask (S : Finset (BitString n)) (d : BitString n → ℂ)
    (z : BitString n) :
    diagTopG S d (fun _ => false) z = ((charSum S d z : ℝ) : ℂ) :=
  diagBotG_zero_mask S d z

/-- **The change of basis, weight one.**  A single-qubit Walsh character sum is the
total mass minus twice the occupation number. -/
lemma charSum_zMask1 (S : Finset (BitString n)) (c : BitString n → ℂ) (i : Fin n) :
    charSum S c (zMask1 i) = mass S c - 2 * occ1 S c i := by
  classical
  unfold charSum mass occ1
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [bdot_zMask1]
  exact expand1 (x i) (Complex.normSq (c x))

/-- **The change of basis, weight two.**  A pair Walsh character sum expands into the
mass, the two single occupation numbers and the pair occupation number. -/
lemma charSum_zMask2 (S : Finset (BitString n)) (c : BitString n → ℂ) (i j : Fin n) :
    charSum S c (zMask2 i j)
      = mass S c - 2 * occ1 S c i - 2 * occ1 S c j + 4 * occ2 S c i j := by
  classical
  unfold charSum mass occ1 occ2
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [bdot_zMask2]
  exact expand2 (x i) (x j) (Complex.normSq (c x))

/-- The Walsh character sum at the zero mask is the total mass. -/
lemma charSum_zero (S : Finset (BitString n)) (c : BitString n → ℂ) :
    charSum S c (fun _ => false) = mass S c := by
  classical
  unfold charSum mass
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hb : SS.bdot (fun _ => false) x = false := by
    unfold SS.bdot
    simp
  rw [hb]
  simp

/-! ## The code-side hypotheses -/

/-- The hypotheses a genuine two-dimensional code on the two fibres satisfies.
Nothing here mentions a Walsh sum or a moment: `dist` is literally
`SS.HasDistance` from `SS/HilbertKL.lean`. -/
structure IsCode (S₀ S₁ : Finset (BitString n)) (c d : BitString n → ℂ) : Prop where
  /-- `|0_L⟩` is supported on the residue-`0` fibre. -/
  supp0 : ∀ x, x ∉ S₀ → c x = 0
  /-- `|1_L⟩` is supported on the residue-`δ` fibre. -/
  supp1 : ∀ y, y ∉ S₁ → d y = 0
  /-- `|0_L⟩` is a unit vector. -/
  norm0 : SS.innerC c c = 1
  /-- `|1_L⟩` is a unit vector. -/
  norm1 : SS.innerC d d = 1
  /-- The code detects every Pauli error of weight `≤ 2`. -/
  dist : SS.HasDistance ![c, d] 3

variable {S₀ S₁ : Finset (BitString n)} {c d : BitString n → ℂ}

/-- Orthogonality of the two logical states is *derived* from disjointness of the
supports, not assumed. -/
theorem IsCode.orthogonal (h : IsCode S₀ S₁ c d) (hdisj : Disjoint S₀ S₁) :
    SS.innerC c d = 0 := by
  classical
  unfold SS.innerC
  refine Finset.sum_eq_zero (fun s _ => ?_)
  by_cases hs : s ∈ S₀
  · rw [h.supp1 s (Finset.disjoint_left.mp hdisj hs)]
    ring
  · rw [h.supp0 s hs]
    simp

/-- Every Pauli of weight `≤ 2` satisfies the Knill--Laflamme condition.  The
weight bound is the one distance 3 gives: `HasDistance ψ 3 = Detects ψ 2`. -/
theorem IsCode.kl (h : IsCode S₀ S₁ c d) (e z : BitString n)
    (hw : (SS.PauliString.mk e z).wt ≤ 2) : SS.KLCondition ![c, d] ⟨e, z⟩ := by
  refine h.dist ⟨e, z⟩ ?_
  simpa using hw

/-! ### Obligation (A): the off-diagonal rows -/

/-- **Obligation (A).**  A genuine distance-3 code makes every off-diagonal Walsh
sum vanish, for every flip mask `e` and dressing `z` with `wt(X^e Z^z) ≤ 2`. -/
theorem IsCode.offSumG_eq_zero (h : IsCode S₀ S₁ c d) (e z : BitString n)
    (hw : (SS.PauliString.mk e z).wt ≤ 2) : offSumG S₀ S₁ c d e z = 0 := by
  obtain ⟨t, ht⟩ := h.kl e z hw
  have h01 := ht 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h01
  rw [if_neg (by decide : ¬((0 : Fin 2) = 1))] at h01
  rw [innerC_eq_offSumG S₀ S₁ c d h.supp0 h.supp1 e z] at h01
  exact (mul_eq_zero.mp h01).resolve_left (SS.pauliPrefactor_ne_zero (SS.PauliString.mk e z))

/-! ### Obligation (B): the diagonal rows -/

/-- **Obligation (B), general flip mask.**  A genuine distance-3 code equates the two
diagonal Walsh sums, for every `e`, `z` with `wt(X^e Z^z) ≤ 2`.  The two diagonal
KL conditions share the *same* scalar `c_P`, which is what makes them equal. -/
theorem IsCode.diagBotG_eq_diagTopG (h : IsCode S₀ S₁ c d) (e z : BitString n)
    (hw : (SS.PauliString.mk e z).wt ≤ 2) : diagBotG S₀ c e z = diagTopG S₁ d e z := by
  obtain ⟨t, ht⟩ := h.kl e z hw
  have h00 := ht 0 0
  have h11 := ht 1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
  rw [innerC_eq_diagBotG S₀ c h.supp0 e z] at h00
  rw [innerC_eq_diagTopG S₁ d h.supp1 e z] at h11
  exact mul_left_cancel₀ (SS.pauliPrefactor_ne_zero (SS.PauliString.mk e z))
    (h00.trans h11.symm)

/-- **Obligation (B), pure `Z`.**  The two Walsh character sums agree, for every `z`
of Hamming weight `≤ 2`. -/
theorem IsCode.charSum_eq (h : IsCode S₀ S₁ c d) (z : BitString n)
    (hw : SS.hammingWt z ≤ 2) : charSum S₀ c z = charSum S₁ d z := by
  have hwt : (SS.PauliString.mk (fun _ => false) z).wt ≤ 2 := by
    rw [wt_pureZ]; exact hw
  have hz := h.diagBotG_eq_diagTopG (fun _ => false) z hwt
  rw [diagBotG_zero_mask, diagTopG_zero_mask] at hz
  exact_mod_cast hz

/-- The mass of each fibre is `1`: this is the normalisation, transported to the
support sum. -/
theorem mass_eq_one (S : Finset (BitString n)) (ψ : BitString n → ℂ)
    (hs : ∀ x, x ∉ S → ψ x = 0) (hn : SS.innerC ψ ψ = 1) : mass S ψ = 1 := by
  classical
  have hres : SS.innerC ψ ψ = ((mass S ψ : ℝ) : ℂ) := by
    unfold SS.innerC mass
    rw [Complex.ofReal_sum]
    rw [← Finset.sum_subset (Finset.subset_univ S) ?_]
    · exact Finset.sum_congr rfl (fun x _ => SixQubit.star_mul_self (ψ x))
    · intro x _ hx
      rw [hs x hx]
      simp
  rw [hres] at hn
  exact_mod_cast hn

theorem IsCode.mass0_eq_one (h : IsCode S₀ S₁ c d) : mass S₀ c = 1 :=
  mass_eq_one S₀ c h.supp0 h.norm0

theorem IsCode.mass1_eq_one (h : IsCode S₀ S₁ c d) : mass S₁ d = 1 :=
  mass_eq_one S₁ d h.supp1 h.norm1

/-- **The single-qubit moment rows.**
`∑_{x ∈ S₀, xᵢ = 1} |c x|² = ∑_{y ∈ S₁, yᵢ = 1} |d y|²`.
This is the `Zᵢ` diagonal condition after the change of basis `charSum_zMask1`. -/
theorem IsCode.occ1_eq (h : IsCode S₀ S₁ c d) (i : Fin n) :
    occ1 S₀ c i = occ1 S₁ d i := by
  have hz := h.charSum_eq (zMask1 i) (by rw [zMask1, hammingWt_stdBasis]; norm_num)
  rw [charSum_zMask1, charSum_zMask1, h.mass0_eq_one, h.mass1_eq_one] at hz
  linarith

/-- **The pair moment rows.**
`∑_{x ∈ S₀, xᵢ = xⱼ = 1} |c x|² = ∑_{y ∈ S₁, yᵢ = yⱼ = 1} |d y|²`.
This is the `Zᵢ Zⱼ` diagonal condition, combined with the two single-qubit rows,
after the change of basis `charSum_zMask2`. -/
theorem IsCode.occ2_eq (h : IsCode S₀ S₁ c d) (i j : Fin n) :
    occ2 S₀ c i j = occ2 S₁ d i j := by
  have hz := h.charSum_eq (zMask2 i j) (hammingWt_zMask2_le i j)
  have h1 := h.occ1_eq i
  have h2 := h.occ1_eq j
  rw [charSum_zMask2, charSum_zMask2, h.mass0_eq_one, h.mass1_eq_one] at hz
  linarith

end

end SixQubit.MaskBridge
