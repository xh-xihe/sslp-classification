import MainTheory.FiniteRankPipeline

/-!
# Compact kernel certificates for active faces

The generated rank audit used to prove four semantic facts by splitting an
arbitrary `Fin 64` word into all 64 cases.  This file proves those facts once.
Generated rows now check two exact natural-number masks and finite lists of
actual fibre words; the generic theorems recover the quantified statements.
No evaluator is added to the trusted base.
-/

namespace MainTheory.CompactFaceCertificate

open MainTheory.FinitePipeline

/-- Bitmask containing exactly the natural-number word indices in a list. -/
def wordMask : List ℕ → ℕ
  | [] => 0
  | w :: ws => 2 ^ w ||| wordMask ws

@[simp] theorem testBit_wordMask (words : List ℕ) (j : ℕ) :
    (wordMask words).testBit j = words.any (· = j) := by
  induction words with
  | nil => simp [wordMask]
  | cons w ws ih =>
      simp [wordMask, Nat.testBit_two_pow, ih]

theorem in_wordMask_iff (words : List ℕ) (x : Word6) :
    InMask (wordMask words) x ↔ x.1 ∈ words := by
  simp [InMask, testBit_wordMask, List.any_eq_true]

/-- Every stored coefficient is strictly positive. -/
def SparsePositive (entries : List (ℕ × ℚ)) : Prop :=
  ∀ e ∈ entries, 0 < e.2

theorem sparseDist_nonneg_of_positive {entries : List (ℕ × ℚ)}
    (h : SparsePositive entries) (x : Word6) : 0 ≤ sparseDist entries x := by
  induction entries with
  | nil => simp [sparseDist]
  | cons e es ih =>
      have he : 0 < e.2 := h e (by simp)
      have hs : SparsePositive es := by
        intro z hz
        exact h z (by simp [hz])
      rw [sparseDist_cons]
      by_cases hex : e.1 = x.1
      · simp only [hex, if_pos]
        exact add_nonneg (le_of_lt he) (ih hs)
      · simp [hex, ih hs]

theorem sparseDist_pos_iff {entries : List (ℕ × ℚ)}
    (h : SparsePositive entries) (x : Word6) :
    0 < sparseDist entries x ↔ x.1 ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [sparseDist]
  | cons e es ih =>
      have he : 0 < e.2 := h e (by simp)
      have hs : SparsePositive es := by
        intro z hz
        exact h z (by simp [hz])
      rw [sparseDist_cons]
      by_cases hex : e.1 = x.1
      · have hxe : x.1 = e.1 := hex.symm
        have hsum : 0 < e.2 + sparseDist es x :=
          add_pos_of_pos_of_nonneg he (sparseDist_nonneg_of_positive hs x)
        constructor
        · intro _
          simp [hxe]
        · intro _
          simpa only [hex, if_pos] using hsum
      · have hxe : x.1 ≠ e.1 := fun h => hex h.symm
        rw [if_neg hex, zero_add]
        simp only [List.map_cons, List.mem_cons, hxe, false_or]
        exact ih hs

theorem active_exact_of_mask_eq {active : ℕ} {entries : List (ℕ × ℚ)}
    (hmask : active = wordMask (entries.map Prod.fst))
    (hpos : SparsePositive entries) (x : Word6) :
    InMask active x ↔ 0 < sparseDist entries x := by
  rw [hmask, in_wordMask_iff, sparseDist_pos_iff hpos]

theorem active_subset_of_sparse {active pairMask : ℕ}
    {entries : List (ℕ × ℚ)}
    (hmask : active = wordMask (entries.map Prod.fst))
    (hpos : SparsePositive entries)
    (hvalid : sparseEntriesValid pairMask entries) (x : Word6) :
    InMask active x → InMask pairMask x := by
  intro hx
  have hp : 0 < sparseDist entries x :=
    (active_exact_of_mask_eq hmask hpos x).1 hx
  by_contra hnot
  have hz := sparseDist_eq_zero_of_not_mem pairMask entries hvalid x hnot
  linarith

/-- A finite list checks one side of an exposing dual.  `mask_eq` proves that
the list contains every and only fibre word; the two inequalities are then
checked only on this list. -/
structure SideWitness (pairMask activeMask : ℕ) (coeff : Word6 → ℚ) where
  words : List ℕ
  mask_eq : pairMask = wordMask words
  words_lt : ∀ w ∈ words, w < 64
  sign : ∀ w ∈ words,
    coeff (wordOfNat w) ≤ 0 ∧
      (¬ activeMask.testBit w = true → coeff (wordOfNat w) < 0)

theorem SideWitness.nonpos_all {pairMask activeMask : ℕ} {coeff : Word6 → ℚ}
    (h : SideWitness pairMask activeMask coeff) (x : Word6)
    (hx : InMask pairMask x) : coeff x ≤ 0 := by
  have hmem : x.1 ∈ h.words := by
    rw [h.mask_eq, in_wordMask_iff] at hx
    exact hx
  have hw := (h.sign x.1 hmem).1
  have hword : wordOfNat x.1 = x := by
    apply Fin.ext
    exact wordOfNat_val x.isLt
  simpa only [hword] using hw

theorem SideWitness.strict_all {pairMask activeMask : ℕ} {coeff : Word6 → ℚ}
    (h : SideWitness pairMask activeMask coeff) (x : Word6)
    (hx : InMask pairMask x) (ha : ¬ InMask activeMask x) : coeff x < 0 := by
  have hmem : x.1 ∈ h.words := by
    rw [h.mask_eq, in_wordMask_iff] at hx
    exact hx
  have hnot : ¬ activeMask.testBit x.1 = true := by
    simpa [InMask] using ha
  have hw := (h.sign x.1 hmem).2 hnot
  have hword : wordOfNat x.1 = x := by
    apply Fin.ext
    exact wordOfNat_val x.isLt
  simpa only [hword] using hw

/-- Complete compact payload from which `FaceData.Valid` follows. -/
structure Witness (pair : FiberPair) (data : FaceData) where
  dual_length : data.dual.length = 23
  primal_valid : data.relativeInterior.SparseValid pair
  positive0 : SparsePositive data.relativeInterior.p0
  positive1 : SparsePositive data.relativeInterior.p1
  active0_eq : data.active0 = wordMask (data.relativeInterior.p0.map Prod.fst)
  active1_eq : data.active1 = wordMask (data.relativeInterior.p1.map Prod.fst)
  rhs_zero :
    let y := listFaceDual data.dual
    y.norm0 + y.norm1 = 0
  side0 : SideWitness pair.mask0 data.active0 (listFaceDual data.dual).leftCoeff
  side1 : SideWitness pair.mask1 data.active1 (listFaceDual data.dual).rightCoeff

/-- A compact list/mask certificate has the full quantified active-face
semantics consumed by the rank pipeline. -/
theorem valid_of_witness {pair : FiberPair} {data : FaceData}
    (h : Witness pair data) : data.Valid pair := by
  unfold FaceData.Valid
  refine ⟨h.dual_length, h.primal_valid, ?_, ?_, ?_, ?_, ?_⟩
  · exact active_exact_of_mask_eq h.active0_eq h.positive0
  · exact active_exact_of_mask_eq h.active1_eq h.positive1
  · exact active_subset_of_sparse h.active0_eq h.positive0 h.primal_valid.entries0
  · exact active_subset_of_sparse h.active1_eq h.positive1 h.primal_valid.entries1
  · dsimp only
    exact ⟨h.rhs_zero, h.side0.nonpos_all, h.side1.nonpos_all,
      h.side0.strict_all, h.side1.strict_all⟩

/-- The common full-fibre case needs no per-word dual table.  When both active
masks are the complete fibres and the stored dual is identically zero, strict
inequalities are vacuous and the non-strict inequalities reduce to `0 ≤ 0`.
This covers most full-rank generated rows without expanding 64 word cases. -/
structure FullFiberZeroWitness (pair : FiberPair) (data : FaceData) where
  primal_valid : data.relativeInterior.SparseValid pair
  positive0 : SparsePositive data.relativeInterior.p0
  positive1 : SparsePositive data.relativeInterior.p1
  active0_support :
    data.active0 = wordMask (data.relativeInterior.p0.map Prod.fst)
  active1_support :
    data.active1 = wordMask (data.relativeInterior.p1.map Prod.fst)
  active0_full : data.active0 = pair.mask0
  active1_full : data.active1 = pair.mask1
  dual_zero : data.dual = List.replicate 23 0

theorem valid_of_fullFiberZeroWitness {pair : FiberPair} {data : FaceData}
    (h : FullFiberZeroWitness pair data) : data.Valid pair := by
  unfold FaceData.Valid
  refine ⟨?_, h.primal_valid, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.dual_zero]
    simp
  · exact active_exact_of_mask_eq h.active0_support h.positive0
  · exact active_exact_of_mask_eq h.active1_support h.positive1
  · intro x hx
    simpa only [h.active0_full] using hx
  · intro x hx
    simpa only [h.active1_full] using hx
  · dsimp only
    have hleft : ∀ x, (listFaceDual data.dual).leftCoeff x = 0 := by
      intro x
      rw [h.dual_zero]
      simp [FaceDual.leftCoeff, score]
    have hright : ∀ x, (listFaceDual data.dual).rightCoeff x = 0 := by
      intro x
      rw [h.dual_zero]
      simp [FaceDual.rightCoeff, score]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h.dual_zero]
      simp
    · intro x _
      rw [hleft]
    · intro x _
      rw [hright]
    · intro x hx hnot
      exact False.elim (hnot (by simpa only [h.active0_full] using hx))
    · intro x hx hnot
      exact False.elim (hnot (by simpa only [h.active1_full] using hx))

end MainTheory.CompactFaceCertificate
