import Mathlib

/-!
# Kernel-facing certificates for the finite six-qubit pipeline

The numerical solver used while discovering the table in `main.tex` is not a
proof dependency.  This file defines the exact degree-at-most-two moment
polytope over `ℚ` and two small certificate formats:

* a rational primal point certifies feasibility;
* an integer strict separator certifies infeasibility.

The definitions use all 64 Boolean words.  Coordinates outside a declared
fiber are required to vanish, so generated certificates cannot silently use a
properly different fiber or change the variable ordering.
-/

namespace MainTheory.FinitePipeline

open scoped BigOperators

/-- A Boolean word on six coordinates, encoded by its value in `[0,64)`. -/
abbrev Word6 := Fin 64

/-- A labelled pair of residue fibers.  The two masks use bit `x` for the
Boolean word whose binary encoding is `x`. -/
structure FiberPair where
  q : ℕ
  m : ℕ
  mask0 : ℕ
  mask1 : ℕ
  deriving DecidableEq, Repr, Ord

/-- Membership of a word in a 64-bit fiber mask. -/
abbrev InMask (mask : ℕ) (x : Word6) : Prop := mask.testBit x.1

instance (mask : ℕ) (x : Word6) : Decidable (InMask mask x) :=
  inferInstanceAs (Decidable (mask.testBit x.1))

/-- The `j`-th Boolean coordinate, represented in `ℚ`. -/
abbrev bit (x : Word6) (j : Fin 6) : ℚ := if x.1.testBit j.1 then 1 else 0

/-- The 21 coordinates `(x_i, x_i x_j)` of the moment embedding in
`main.tex`, in lexicographic pair order. -/
abbrev feature (x : Word6) : Fin 21 → ℚ :=
  let b := bit x
  ![b 0, b 1, b 2, b 3, b 4, b 5,
    b 0 * b 1, b 0 * b 2, b 0 * b 3, b 0 * b 4, b 0 * b 5,
    b 1 * b 2, b 1 * b 3, b 1 * b 4, b 1 * b 5,
    b 2 * b 3, b 2 * b 4, b 2 * b 5,
    b 3 * b 4, b 3 * b 5,
    b 4 * b 5]

/-- Exact rational feasibility of the two-color degree-two moment system. -/
structure Feasible (pair : FiberPair) (p0 p1 : Word6 → ℚ) : Prop where
  support0 : ∀ x, ¬ InMask pair.mask0 x → p0 x = 0
  support1 : ∀ x, ¬ InMask pair.mask1 x → p1 x = 0
  nonneg0 : ∀ x, 0 ≤ p0 x
  nonneg1 : ∀ x, 0 ≤ p1 x
  norm0 : ∑ x, p0 x = 1
  norm1 : ∑ x, p1 x = 1
  moments : ∀ k, ∑ x, p0 x * feature x k = ∑ x, p1 x * feature x k

private def FeasibleConditions (pair : FiberPair) (p0 p1 : Word6 → ℚ) : Prop :=
  (∀ x, ¬ InMask pair.mask0 x → p0 x = 0) ∧
  (∀ x, ¬ InMask pair.mask1 x → p1 x = 0) ∧
  (∀ x, 0 ≤ p0 x) ∧ (∀ x, 0 ≤ p1 x) ∧
  (∑ x, p0 x) = 1 ∧ (∑ x, p1 x) = 1 ∧
  (∀ k, ∑ x, p0 x * feature x k = ∑ x, p1 x * feature x k)

private theorem feasibleConditions_iff (pair : FiberPair) (p0 p1 : Word6 → ℚ) :
    FeasibleConditions pair p0 p1 ↔ Feasible pair p0 p1 := by
  constructor
  · rintro ⟨hs0, hs1, hn0, hn1, hnorm0, hnorm1, hm⟩
    exact ⟨hs0, hs1, hn0, hn1, hnorm0, hnorm1, hm⟩
  · intro h
    exact ⟨h.support0, h.support1, h.nonneg0, h.nonneg1,
      h.norm0, h.norm1, h.moments⟩

instance (pair : FiberPair) (p0 p1 : Word6 → ℚ) :
    Decidable (Feasible pair p0 p1) := by
  letI : Decidable (FeasibleConditions pair p0 p1) := by
    unfold FeasibleConditions
    infer_instance
  exact decidable_of_iff (FeasibleConditions pair p0 p1)
    (feasibleConditions_iff pair p0 p1)

/-- A proof-carrying exact primal certificate. -/
structure PrimalCertificate (pair : FiberPair) where
  p0 : Word6 → ℚ
  p1 : Word6 → ℚ
  valid : Feasible pair p0 p1

theorem feasible_of_primal {pair : FiberPair} (cert : PrimalCertificate pair) :
    ∃ p0 p1, Feasible pair p0 p1 :=
  ⟨cert.p0, cert.p1, cert.valid⟩

/-- The mathematical finite-sum form of a rational score. -/
def scoreSum (h : Fin 21 → ℚ) (x : Word6) : ℚ :=
  ∑ k, h k * feature x k

/-- A reduction-friendly list evaluation of the 21 features.  For concrete
certificates `List.sum` reduces directly, unlike a nested abstract big sum. -/
def score (h : Fin 21 → ℚ) (x : Word6) : ℚ :=
  (List.ofFn fun k => h k * feature x k).sum

private theorem sum_list_ofFn_eq_sum_fin {n : ℕ} (f : Fin n → ℚ) :
    (List.ofFn f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      exact congrArg (f 0 + ·) (ih (fun i => f i.succ))

theorem score_eq_scoreSum (h : Fin 21 → ℚ) (x : Word6) :
    score h x = scoreSum h x := by
  exact sum_list_ofFn_eq_sum_fin (fun k => h k * feature x k)

/-- Equal feature moments imply equal expectation for every rational linear
functional of those features. -/
theorem expected_score_eq {pair : FiberPair} {p0 p1 : Word6 → ℚ}
    (hp : Feasible pair p0 p1) (h : Fin 21 → ℚ) :
    (∑ x, p0 x * score h x) = ∑ x, p1 x * score h x := by
  simp_rw [score_eq_scoreSum]
  calc
    (∑ x, p0 x * scoreSum h x) =
        ∑ k, h k * (∑ x, p0 x * feature x k) := by
      simp only [scoreSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ k, h k * (∑ x, p1 x * feature x k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hp.moments k]
    _ = ∑ x, p1 x * scoreSum h x := by
      simp only [scoreSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- A strict hyperplane separator between the two feature polytopes. -/
structure SeparatorCertificate (pair : FiberPair) where
  h : Fin 21 → ℚ
  lower : ℚ
  upper : ℚ
  gap : lower < upper
  left_bound : ∀ x, InMask pair.mask0 x → score h x ≤ lower
  right_bound : ∀ x, InMask pair.mask1 x → upper ≤ score h x

private theorem left_expectation_le {pair : FiberPair} {p0 p1 : Word6 → ℚ}
    (hp : Feasible pair p0 p1) (cert : SeparatorCertificate pair) :
    (∑ x, p0 x * score cert.h x) ≤ cert.lower := by
  calc
    (∑ x, p0 x * score cert.h x) ≤ ∑ x, p0 x * cert.lower := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : InMask pair.mask0 x
      · exact mul_le_mul_of_nonneg_left (cert.left_bound x hx) (hp.nonneg0 x)
      · rw [hp.support0 x hx]
        simp
    _ = cert.lower := by rw [← Finset.sum_mul, hp.norm0, one_mul]

private theorem right_expectation_ge {pair : FiberPair} {p0 p1 : Word6 → ℚ}
    (hp : Feasible pair p0 p1) (cert : SeparatorCertificate pair) :
    cert.upper ≤ ∑ x, p1 x * score cert.h x := by
  calc
    cert.upper = ∑ x, p1 x * cert.upper := by
      rw [← Finset.sum_mul, hp.norm1, one_mul]
    _ ≤ ∑ x, p1 x * score cert.h x := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : InMask pair.mask1 x
      · exact mul_le_mul_of_nonneg_left (cert.right_bound x hx) (hp.nonneg1 x)
      · rw [hp.support1 x hx]
        simp

/-- **A valid exact separator rules out the moment polytope.** -/
theorem not_feasible_of_separator {pair : FiberPair}
    (cert : SeparatorCertificate pair) :
    ¬ ∃ p0 p1, Feasible pair p0 p1 := by
  rintro ⟨p0, p1, hp⟩
  have hleft := left_expectation_le hp cert
  have hright := right_expectation_ge hp cert
  have heq := expected_score_eq hp cert.h
  have hgap := cert.gap
  linarith

/-! ## One dual exposing the complete active face -/

/-- Coefficients of a dual vector for the standard 23-row formulation: two
normalization rows followed by the 21 moment-equality rows. -/
structure FaceDual where
  norm0 : ℚ
  norm1 : ℚ
  moment : Fin 21 → ℚ

def FaceDual.leftCoeff (y : FaceDual) (x : Word6) : ℚ :=
  y.norm0 + score y.moment x

def FaceDual.rightCoeff (y : FaceDual) (x : Word6) : ℚ :=
  y.norm1 - score y.moment x

/-- A single exact dual which exposes a proposed pair of active submasks. -/
structure FaceCertificate (pair : FiberPair) where
  active0 : ℕ
  active1 : ℕ
  active0_subset : ∀ x, InMask active0 x → InMask pair.mask0 x
  active1_subset : ∀ x, InMask active1 x → InMask pair.mask1 x
  dual : FaceDual
  rhs_zero : dual.norm0 + dual.norm1 = 0
  left_nonpos : ∀ x, InMask pair.mask0 x → dual.leftCoeff x ≤ 0
  right_nonpos : ∀ x, InMask pair.mask1 x → dual.rightCoeff x ≤ 0
  left_strict : ∀ x, InMask pair.mask0 x → ¬ InMask active0 x → dual.leftCoeff x < 0
  right_strict : ∀ x, InMask pair.mask1 x → ¬ InMask active1 x → dual.rightCoeff x < 0

private theorem face_weighted_sum_eq_zero {pair : FiberPair}
    {p0 p1 : Word6 → ℚ} (hp : Feasible pair p0 p1) (y : FaceDual)
    (hy : y.norm0 + y.norm1 = 0) :
    (∑ x, p0 x * y.leftCoeff x) +
      (∑ x, p1 x * y.rightCoeff x) = 0 := by
  have hscore : (∑ x, p0 x * scoreSum y.moment x) =
      ∑ x, p1 x * scoreSum y.moment x := by
    simpa only [← score_eq_scoreSum] using expected_score_eq hp y.moment
  simp_rw [FaceDual.leftCoeff, FaceDual.rightCoeff, score_eq_scoreSum]
  simp only [mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hp.norm0, hp.norm1]
  linarith [hscore]

private theorem summand_eq_zero_of_sum_eq_zero_of_nonpos
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℚ)
    (hsum : ∑ i, f i = 0) (hnonpos : ∀ i, f i ≤ 0) (i : ι) : f i = 0 := by
  have hrest : ∑ j ∈ (Finset.univ.erase i), f j ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact hnonpos j
  have hi : f i + ∑ j ∈ (Finset.univ.erase i), f j = 0 := by
    calc
      f i + ∑ j ∈ (Finset.univ.erase i), f j =
          (∑ j ∈ (Finset.univ.erase i), f j) + f i := add_comm _ _
      _ = ∑ j, f j := Finset.sum_erase_add _ _ (Finset.mem_univ i)
      _ = 0 := hsum
  have hge : 0 ≤ f i := by linarith
  exact le_antisymm (hnonpos i) hge

/-- Every feasible distribution is supported on the face exposed by a valid
dual certificate. -/
theorem support_subset_face {pair : FiberPair} (cert : FaceCertificate pair)
    {p0 p1 : Word6 → ℚ} (hp : Feasible pair p0 p1) :
    (∀ x, ¬ InMask cert.active0 x → p0 x = 0) ∧
      (∀ x, ¬ InMask cert.active1 x → p1 x = 0) := by
  have hsum := face_weighted_sum_eq_zero hp cert.dual cert.rhs_zero
  let f : Sum Word6 Word6 → ℚ
    | Sum.inl x => p0 x * cert.dual.leftCoeff x
    | Sum.inr x => p1 x * cert.dual.rightCoeff x
  have hf_sum : ∑ i, f i = 0 := by
    simpa [f, Fintype.sum_sum_type] using hsum
  have hf_nonpos : ∀ i, f i ≤ 0 := by
    intro i
    cases i with
    | inl x =>
        simp only [f]
        by_cases hx : InMask pair.mask0 x
        · exact mul_nonpos_of_nonneg_of_nonpos (hp.nonneg0 x) (cert.left_nonpos x hx)
        · rw [hp.support0 x hx]
          simp
    | inr x =>
        simp only [f]
        by_cases hx : InMask pair.mask1 x
        · exact mul_nonpos_of_nonneg_of_nonpos (hp.nonneg1 x) (cert.right_nonpos x hx)
        · rw [hp.support1 x hx]
          simp
  constructor
  · intro x hxactive
    by_cases hxfiber : InMask pair.mask0 x
    · have hproduct := summand_eq_zero_of_sum_eq_zero_of_nonpos f hf_sum hf_nonpos (Sum.inl x)
      simp only [f] at hproduct
      have hcoeff := cert.left_strict x hxfiber hxactive
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hproduct with hp0 | hcoef
      · exact hp0
      · rw [hcoef] at hcoeff
        exact False.elim (lt_irrefl 0 hcoeff)
    · exact hp.support0 x hxfiber
  · intro x hxactive
    by_cases hxfiber : InMask pair.mask1 x
    · have hproduct := summand_eq_zero_of_sum_eq_zero_of_nonpos f hf_sum hf_nonpos (Sum.inr x)
      simp only [f] at hproduct
      have hcoeff := cert.right_strict x hxfiber hxactive
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hproduct with hp1 | hcoef
      · exact hp1
      · rw [hcoef] at hcoeff
        exact False.elim (lt_irrefl 0 hcoeff)
    · exact hp.support1 x hxfiber

/-! ## Compact generated-data formats

The declarations below contain no proof by themselves.  They are compact
serializable payloads; a generated module must prove their `Valid` predicates
with ordinary kernel reduction before the soundness theorems can be used. -/

/-- Interpret a sparse list of `(word,value)` pairs.  Repeated words are added,
so a malformed generator cannot change semantics by relying on lookup order.
The `List.sum` presentation is intentionally transparent: the generic
soundness lemmas below reduce sparse certificates without expanding a
64-entry dense vector. -/
def sparseDist (entries : List (ℕ × ℚ)) (x : Word6) : ℚ :=
  (entries.map fun entry => if entry.1 = x.1 then entry.2 else 0).sum

/-- Total, proof-free conversion used by sparse moment payloads.  A valid
payload separately proves that the input is below `64`, so the reduction
modulo `64` is semantically inert. -/
def wordOfNat (n : ℕ) : Word6 := ⟨n % 64, Nat.mod_lt _ (by decide)⟩

theorem wordOfNat_val {n : ℕ} (h : n < 64) : (wordOfNat n).1 = n := by
  simp [wordOfNat, Nat.mod_eq_of_lt h]

private theorem sum_indicator (n : ℕ) (a : ℚ) (hn : n < 64) :
    (∑ x : Word6, if n = x.1 then a else 0) = a := by
  let y : Word6 := ⟨n, hn⟩
  classical
  calc
    (∑ x : Word6, if n = x.1 then a else 0) =
        ∑ x : Word6, if x = y then a else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          simp only [y, Fin.ext_iff]
          aesop
    _ = a := by simp

theorem sparseDist_cons (e : ℕ × ℚ) (es : List (ℕ × ℚ)) (x : Word6) :
    sparseDist (e :: es) x = (if e.1 = x.1 then e.2 else 0) + sparseDist es x := by
  simp [sparseDist]

theorem sum_sparseDist (entries : List (ℕ × ℚ))
    (hvalid : ∀ e ∈ entries, e.1 < 64) :
    (∑ x : Word6, sparseDist entries x) = (entries.map Prod.snd).sum := by
  induction entries with
  | nil => simp [sparseDist]
  | cons e es ih =>
      have he : e.1 < 64 := hvalid e (by simp)
      have hes : ∀ z ∈ es, z.1 < 64 := by
        intro z hz
        exact hvalid z (by simp [hz])
      simp only [sparseDist_cons, Finset.sum_add_distrib, ih hes, List.map_cons,
        List.sum_cons]
      rw [sum_indicator e.1 e.2 he]

theorem sum_sparseDist_mul_feature (entries : List (ℕ × ℚ))
    (hvalid : ∀ e ∈ entries, e.1 < 64) (k : Fin 21) :
    (∑ x : Word6, sparseDist entries x * feature x k) =
      (entries.map fun e => e.2 * feature (wordOfNat e.1) k).sum := by
  induction entries with
  | nil => simp [sparseDist]
  | cons e es ih =>
      have he : e.1 < 64 := hvalid e (by simp)
      have hes : ∀ z ∈ es, z.1 < 64 := by
        intro z hz
        exact hvalid z (by simp [hz])
      let y : Word6 := ⟨e.1, he⟩
      have hy : y = wordOfNat e.1 := by
        apply Fin.ext
        simp [y, wordOfNat, Nat.mod_eq_of_lt he]
      have hhead :
          (∑ x : Word6, (if e.1 = x.1 then e.2 else 0) * feature x k) =
            e.2 * feature y k := by
        classical
        calc
          _ = ∑ x : Word6, if x = y then e.2 * feature y k else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : e.1 = x.1
            · have hxy : x = y := by
                apply Fin.ext
                simpa [y] using hx.symm
              simp [hx, hxy]
            · have hxy : x ≠ y := by
                intro h
                apply hx
                simpa [y] using (congrArg Fin.val h).symm
              simp [hx, hxy]
          _ = _ := by simp
      rw [List.map_cons, List.sum_cons]
      simp_rw [sparseDist_cons, add_mul, Finset.sum_add_distrib]
      rw [hhead, ih hes, hy]

/-- Every entry of a sparse distribution has a genuine six-bit index, lies in
the advertised fiber, and carries nonnegative mass. -/
def sparseEntriesValid (mask : ℕ) (entries : List (ℕ × ℚ)) : Prop :=
  entries.Forall fun e => e.1 < 64 ∧ mask.testBit e.1 = true ∧ 0 ≤ e.2

theorem sparseEntriesValid_of_mem {mask : ℕ} {entries : List (ℕ × ℚ)}
    (h : sparseEntriesValid mask entries) {e : ℕ × ℚ} (he : e ∈ entries) :
    e.1 < 64 ∧ mask.testBit e.1 = true ∧ 0 ≤ e.2 :=
  List.forall_iff_forall_mem.mp h e he

theorem sparseDist_eq_zero_of_not_mem (mask : ℕ) (entries : List (ℕ × ℚ))
    (hvalid : sparseEntriesValid mask entries) (x : Word6) (hx : ¬ InMask mask x) :
    sparseDist entries x = 0 := by
  induction entries with
  | nil => simp [sparseDist]
  | cons e es ih =>
      have he := sparseEntriesValid_of_mem hvalid (show e ∈ e :: es by simp)
      have hes : sparseEntriesValid mask es := by
        apply List.forall_iff_forall_mem.mpr
        intro z hz
        exact sparseEntriesValid_of_mem hvalid (by simp [hz])
      rw [sparseDist_cons, ih hes]
      simp only [add_zero]
      by_cases hex : e.1 = x.1
      · have : mask.testBit x.1 = true := by simpa [hex] using he.2.1
        exact False.elim (hx this)
      · simp [hex]

theorem sparseDist_nonneg (mask : ℕ) (entries : List (ℕ × ℚ))
    (hvalid : sparseEntriesValid mask entries) (x : Word6) :
    0 ≤ sparseDist entries x := by
  induction entries with
  | nil => simp [sparseDist]
  | cons e es ih =>
      have he := sparseEntriesValid_of_mem hvalid (show e ∈ e :: es by simp)
      have hes : sparseEntriesValid mask es := by
        apply List.forall_iff_forall_mem.mpr
        intro z hz
        exact sparseEntriesValid_of_mem hvalid (by simp [hz])
      rw [sparseDist_cons]
      by_cases hex : e.1 = x.1
      · simp [hex, add_nonneg he.2.2 (ih hes)]
      · simp [hex, ih hes]

def sparseMass (entries : List (ℕ × ℚ)) : ℚ :=
  (entries.map Prod.snd).sum

def sparseMoment (entries : List (ℕ × ℚ)) (k : Fin 21) : ℚ :=
  (entries.map fun e => e.2 * feature (wordOfNat e.1) k).sum

/-- The compact primal predicate actually checked by generated files.  Its
generic soundness theorem below expands it to the full 64-variable moment
system inside Lean. -/
structure SparsePrimalValid (pair : FiberPair)
    (p0 p1 : List (ℕ × ℚ)) : Prop where
  entries0 : sparseEntriesValid pair.mask0 p0
  entries1 : sparseEntriesValid pair.mask1 p1
  mass0 : sparseMass p0 = 1
  mass1 : sparseMass p1 = 1
  moments : ∀ k, sparseMoment p0 k = sparseMoment p1 k

private def SparsePrimalConditions (pair : FiberPair)
    (p0 p1 : List (ℕ × ℚ)) : Prop :=
  sparseEntriesValid pair.mask0 p0 ∧
  sparseEntriesValid pair.mask1 p1 ∧
  sparseMass p0 = 1 ∧ sparseMass p1 = 1 ∧
  ∀ k, sparseMoment p0 k = sparseMoment p1 k

private theorem sparsePrimalConditions_iff (pair : FiberPair)
    (p0 p1 : List (ℕ × ℚ)) :
    SparsePrimalConditions pair p0 p1 ↔ SparsePrimalValid pair p0 p1 := by
  constructor
  · rintro ⟨h0, h1, hm0, hm1, hm⟩
    exact ⟨h0, h1, hm0, hm1, hm⟩
  · intro h
    exact ⟨h.entries0, h.entries1, h.mass0, h.mass1, h.moments⟩

instance (pair : FiberPair) (p0 p1 : List (ℕ × ℚ)) :
    Decidable (SparsePrimalValid pair p0 p1) := by
  letI : Decidable (SparsePrimalConditions pair p0 p1) := by
    unfold SparsePrimalConditions sparseEntriesValid sparseMass sparseMoment
    infer_instance
  exact decidable_of_iff (SparsePrimalConditions pair p0 p1)
    (sparsePrimalConditions_iff pair p0 p1)

theorem feasible_of_sparsePrimalValid {pair : FiberPair} {p0 p1 : List (ℕ × ℚ)}
    (h : SparsePrimalValid pair p0 p1) :
    Feasible pair (sparseDist p0) (sparseDist p1) := by
  constructor
  · exact sparseDist_eq_zero_of_not_mem _ _ h.entries0
  · exact sparseDist_eq_zero_of_not_mem _ _ h.entries1
  · exact sparseDist_nonneg _ _ h.entries0
  · exact sparseDist_nonneg _ _ h.entries1
  · rw [sum_sparseDist p0 (fun _ he => (sparseEntriesValid_of_mem h.entries0 he).1)]
    exact h.mass0
  · rw [sum_sparseDist p1 (fun _ he => (sparseEntriesValid_of_mem h.entries1 he).1)]
    exact h.mass1
  · intro k
    rw [sum_sparseDist_mul_feature p0
          (fun _ he => (sparseEntriesValid_of_mem h.entries0 he).1),
      sum_sparseDist_mul_feature p1
          (fun _ he => (sparseEntriesValid_of_mem h.entries1 he).1)]
    exact h.moments k

structure PrimalData where
  p0 : List (ℕ × ℚ)
  p1 : List (ℕ × ℚ)
  deriving Repr

def PrimalData.SparseValid (pair : FiberPair) (data : PrimalData) : Prop :=
  SparsePrimalValid pair data.p0 data.p1

instance (pair : FiberPair) (data : PrimalData) : Decidable (data.SparseValid pair) := by
  unfold PrimalData.SparseValid
  infer_instance

theorem PrimalData.feasible_of_sparseValid {pair : FiberPair} {data : PrimalData}
    (h : data.SparseValid pair) :
    Feasible pair (sparseDist data.p0) (sparseDist data.p1) :=
  feasible_of_sparsePrimalValid h

def PrimalData.Valid (pair : FiberPair) (data : PrimalData) : Prop :=
  Feasible pair (sparseDist data.p0) (sparseDist data.p1)

instance (pair : FiberPair) (data : PrimalData) : Decidable (data.Valid pair) :=
  inferInstanceAs (Decidable (Feasible pair (sparseDist data.p0) (sparseDist data.p1)))

def PrimalData.certificate (pair : FiberPair) (data : PrimalData)
    (h : data.Valid pair) : PrimalCertificate pair :=
  ⟨sparseDist data.p0, sparseDist data.p1, h⟩

structure SeparatorData where
  h : List ℚ
  lower : ℚ
  upper : ℚ
  deriving Repr

abbrev listVector21 (values : List ℚ) : Fin 21 → ℚ :=
  fun k => values.getD k.1 0

def SeparatorData.Valid (pair : FiberPair) (data : SeparatorData) : Prop :=
  data.h.length = 21 ∧ data.lower < data.upper ∧
    (∀ x, InMask pair.mask0 x → score (listVector21 data.h) x ≤ data.lower) ∧
    (∀ x, InMask pair.mask1 x → data.upper ≤ score (listVector21 data.h) x)

instance (pair : FiberPair) (data : SeparatorData) : Decidable (data.Valid pair) :=
  by
    unfold SeparatorData.Valid
    infer_instance

def SeparatorData.certificate (pair : FiberPair) (data : SeparatorData)
    (h : data.Valid pair) : SeparatorCertificate pair where
  h := listVector21 data.h
  lower := data.lower
  upper := data.upper
  gap := h.2.1
  left_bound := h.2.2.1
  right_bound := h.2.2.2

theorem not_feasible_of_separatorData {pair : FiberPair} {data : SeparatorData}
    (h : data.Valid pair) : ¬ ∃ p0 p1, Feasible pair p0 p1 :=
  not_feasible_of_separator (data.certificate pair h)

structure FaceData where
  active0 : ℕ
  active1 : ℕ
  dual : List ℚ
  relativeInterior : PrimalData
  deriving Repr

abbrev listFaceDual (values : List ℚ) : FaceDual where
  norm0 := values.getD 0 0
  norm1 := values.getD 1 0
  moment := fun k => values.getD (k.1 + 2) 0

def FaceData.Valid (pair : FiberPair) (data : FaceData) : Prop :=
  data.dual.length = 23 ∧ data.relativeInterior.SparseValid pair ∧
    (∀ x, InMask data.active0 x ↔ 0 < sparseDist data.relativeInterior.p0 x) ∧
    (∀ x, InMask data.active1 x ↔ 0 < sparseDist data.relativeInterior.p1 x) ∧
    (∀ x, InMask data.active0 x → InMask pair.mask0 x) ∧
    (∀ x, InMask data.active1 x → InMask pair.mask1 x) ∧
    let y := listFaceDual data.dual
    y.norm0 + y.norm1 = 0 ∧
      (∀ x, InMask pair.mask0 x → y.leftCoeff x ≤ 0) ∧
      (∀ x, InMask pair.mask1 x → y.rightCoeff x ≤ 0) ∧
      (∀ x, InMask pair.mask0 x → ¬ InMask data.active0 x → y.leftCoeff x < 0) ∧
      (∀ x, InMask pair.mask1 x → ¬ InMask data.active1 x → y.rightCoeff x < 0)

instance (pair : FiberPair) (data : FaceData) : Decidable (data.Valid pair) :=
  by
    unfold FaceData.Valid
    infer_instance

def FaceData.certificate (pair : FiberPair) (data : FaceData)
    (h : data.Valid pair) : FaceCertificate pair where
  active0 := data.active0
  active1 := data.active1
  active0_subset := h.2.2.2.2.1
  active1_subset := h.2.2.2.2.2.1
  dual := listFaceDual data.dual
  rhs_zero := h.2.2.2.2.2.2.1
  left_nonpos := h.2.2.2.2.2.2.2.1
  right_nonpos := h.2.2.2.2.2.2.2.2.1
  left_strict := h.2.2.2.2.2.2.2.2.2.1
  right_strict := h.2.2.2.2.2.2.2.2.2.2

/-- A valid face payload proves both directions of activity: its rational
relative-interior point is positive exactly on the advertised masks, and its
dual forces every feasible point to vanish elsewhere. -/
theorem active_masks_exact {pair : FiberPair} {data : FaceData}
    (h : data.Valid pair) :
    (∀ x, InMask data.active0 x ↔
      ∃ p0 p1, Feasible pair p0 p1 ∧ 0 < p0 x) ∧
    (∀ x, InMask data.active1 x ↔
      ∃ p0 p1, Feasible pair p0 p1 ∧ 0 < p1 x) := by
  have hprimal : Feasible pair
      (sparseDist data.relativeInterior.p0) (sparseDist data.relativeInterior.p1) :=
    data.relativeInterior.feasible_of_sparseValid h.2.1
  constructor
  · intro x
    constructor
    · intro hx
      exact ⟨_, _, hprimal, (h.2.2.1 x).1 hx⟩
    · rintro ⟨p0, p1, hp, hpos⟩
      by_contra hx
      have hz := (support_subset_face (data.certificate pair h) hp).1 x hx
      rw [hz] at hpos
      exact (lt_irrefl 0) hpos
  · intro x
    constructor
    · intro hx
      exact ⟨_, _, hprimal, (h.2.2.2.1 x).1 hx⟩
    · rintro ⟨p0, p1, hp, hpos⟩
      by_contra hx
      have hz := (support_subset_face (data.certificate pair h) hp).2 x hx
      rw [hz] at hpos
      exact (lt_irrefl 0) hpos

/-- One row of the exact moment-feasibility audit. -/
inductive MomentResultData where
  | feasible (pairId : ℕ) (primal : PrimalData)
  | infeasible (pairId : ℕ) (separator : SeparatorData)
  deriving Repr

def MomentResultData.pairId : MomentResultData → ℕ
  | .feasible pairId _ => pairId
  | .infeasible pairId _ => pairId

def MomentResultData.isFeasible : MomentResultData → Bool
  | .feasible .. => true
  | .infeasible .. => false

abbrev pairAt (pairs : Array FiberPair) (pairId : ℕ) : FiberPair :=
  pairs.getD pairId ⟨0, 0, 0, 0⟩

def MomentResultData.ValidFor (pair : FiberPair) : MomentResultData → Prop
  | .feasible _ primal => primal.SparseValid pair
  | .infeasible _ separator => separator.Valid pair

def MomentResultData.Valid (pairs : Array FiberPair) (data : MomentResultData) : Prop :=
  data.ValidFor (pairAt pairs data.pairId)

instance (pair : FiberPair) (data : MomentResultData) :
    Decidable (data.ValidFor pair) := by
  cases data <;> simp only [MomentResultData.ValidFor] <;> infer_instance

instance (pairs : Array FiberPair) (data : MomentResultData) :
    Decidable (data.Valid pairs) := by
  cases data <;> simp only [MomentResultData.Valid] <;> infer_instance

/-- Every valid moment-result row has the advertised mathematical meaning. -/
theorem MomentResultData.sound {pairs : Array FiberPair}
    {data : MomentResultData} (h : data.Valid pairs) :
    if data.isFeasible then
      ∃ p0 p1, Feasible (pairAt pairs data.pairId) p0 p1
    else
      ¬ ∃ p0 p1, Feasible (pairAt pairs data.pairId) p0 p1 := by
  cases data with
  | feasible pairId primal =>
      exact ⟨_, _, primal.feasible_of_sparseValid h⟩
  | infeasible pairId separator =>
      exact not_feasible_of_separatorData h

/-- Soundness phrased directly for an explicit pair.  Generated certificates
use this form, and separately certify the correspondence between their pair
payloads and the outer-enumeration table.  This prevents table lookup cost
from obscuring the algebraic certificate check. -/
theorem MomentResultData.soundFor {pair : FiberPair}
    {data : MomentResultData} (h : data.ValidFor pair) :
    if data.isFeasible then
      ∃ p0 p1, Feasible pair p0 p1
    else
      ¬ ∃ p0 p1, Feasible pair p0 p1 := by
  cases data with
  | feasible pairId primal =>
      exact ⟨_, _, primal.feasible_of_sparseValid h⟩
  | infeasible pairId separator =>
      exact not_feasible_of_separatorData h

/-- A generated moment row together with the exact pair on which its payload
was checked.  The proof field is kernel checked; a later provenance theorem
connects `pairId` and `pair` to the exhaustive outer table. -/
structure CertifiedMomentRow where
  pairId : ℕ
  pair : FiberPair
  result : MomentResultData
  result_pairId : result.pairId = pairId
  valid : result.ValidFor pair

theorem CertifiedMomentRow.sound (row : CertifiedMomentRow) :
    if row.result.isFeasible then
      ∃ p0 p1, Feasible row.pair p0 p1
    else
      ¬ ∃ p0 p1, Feasible row.pair p0 p1 :=
  row.result.soundFor row.valid

/-- One row of the exact active-face/rank audit.  The two natural numbers are
the independently certified affine ranks of the advertised active masks. -/
structure RankResultData where
  pairId : ℕ
  face : FaceData
  rank0 : ℕ
  rank1 : ℕ
  compatible : Bool
  deriving Repr

def RankResultData.ValidFace (pairs : Array FiberPair) (data : RankResultData) : Prop :=
  data.face.Valid (pairAt pairs data.pairId)

instance (pairs : Array FiberPair) (data : RankResultData) :
    Decidable (data.ValidFace pairs) := by
  unfold RankResultData.ValidFace
  infer_instance

end MainTheory.FinitePipeline
