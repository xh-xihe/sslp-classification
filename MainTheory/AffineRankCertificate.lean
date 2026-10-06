import MainTheory.FinitePipeline

/-!
# Exact affine-rank certificates for six-bit masks

This file turns the affine-rank data emitted by the finite-pipeline generator
into a kernel-checkable certificate.  The lower certificate consists of points
of the mask and a nonsingular coordinate minor of their differences from a
base point.  The upper certificate consists of independent normal vectors
which annihilate every such difference.

The JSON fields are represented without changing their order:
`base`, `lower_points`, `lower_coords`, `normals`, and `normal_coords`.
Raw natural-number indices are range checked before their bounded versions
are used, so reduction cannot silently accept an index modulo 64 or modulo 6.

For the empty mask the generator currently emits only one dummy normal,
irrespective of codimension.  Consequently `Valid` has an explicit empty-mask
branch: emptiness itself proves rank zero, while those unused dummy fields are
not presented as an upper-rank proof.
-/

namespace MainTheory.AffineRankCertificate

open MainTheory.FinitePipeline
open scoped BigOperators

set_option maxHeartbeats 800000

/-- Six rational coordinates, with the same bit convention as `FinitePipeline.bit`. -/
abbrev Vec6 := Fin 6 → ℚ

/-- The Boolean cube point represented by a six-bit word. -/
def point (x : Word6) : Vec6 := fun j => bit x j

/-- The point set selected by a (possibly larger than 64-bit) natural mask. -/
def maskPointSet (mask : ℕ) : Set Vec6 :=
  point '' {x : Word6 | InMask mask x}

/-- Affine rank of the points selected by `mask`, over the exact field `ℚ`. -/
noncomputable def maskAffineRank (mask : ℕ) : ℕ :=
  Module.finrank ℚ (affineSpan ℚ (maskPointSet mask)).direction

/-- Raw certificate data, matching the generator's JSON arrays exactly. -/
structure Data where
  rank : ℕ
  base : ℕ
  lowerPoints : List ℕ
  lowerCoords : List ℕ
  normals : List (List ℤ)
  normalCoords : List ℕ
  deriving DecidableEq, Repr

/-- Range-safe conversion used only after validity has checked the raw value. -/
def wordOfNat (x : ℕ) : Word6 :=
  ⟨x % 64, Nat.mod_lt _ (by decide)⟩

/-- Range-safe conversion used only after validity has checked the raw value. -/
def coordOfNat (j : ℕ) : Fin 6 :=
  ⟨j % 6, Nat.mod_lt _ (by decide)⟩

/-- Exact low-word bitmask represented by a finite list of word indices. -/
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

def Data.baseWord (d : Data) : Word6 := wordOfNat d.base

def Data.lowerWord (d : Data) (i : Fin d.rank) : Word6 :=
  wordOfNat (d.lowerPoints.getD i.1 0)

def Data.lowerCoord (d : Data) (j : Fin d.rank) : Fin 6 :=
  coordOfNat (d.lowerCoords.getD j.1 0)

def Data.normalCoord (d : Data) (j : Fin (6 - d.rank)) : Fin 6 :=
  coordOfNat (d.normalCoords.getD j.1 0)

def Data.basePoint (d : Data) : Vec6 := point d.baseWord

def Data.lowerDiff (d : Data) (i : Fin d.rank) : Vec6 :=
  point (d.lowerWord i) - d.basePoint

/-- A generator normal, padded only for totality.  Validity forbids padding. -/
def Data.normalVec (d : Data) (i : Fin (6 - d.rank)) : Vec6 := fun j =>
  ((d.normals.getD i.1 []).getD j.1 0 : ℤ)

/-- Exact dot product on six coordinates. -/
def dot (u v : Vec6) : ℚ := ∑ j, u j * v j

/-- A normal row, regarded as an exact rational linear functional. -/
def Data.normalFunctional (d : Data) (i : Fin (6 - d.rank)) : Module.Dual ℚ Vec6 where
  toFun v := dot (d.normalVec i) v
  map_add' x y := by
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [RingHom.id_apply]
    ring

/-- Coordinate restriction to the lower minor's selected columns. -/
def Data.lowerRestriction (d : Data) : Vec6 →ₗ[ℚ] (Fin d.rank → ℚ) where
  toFun v j := v (d.lowerCoord j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Standard coordinate vector. -/
def stdBasisVec (j : Fin 6) : Vec6 := fun k => if k = j then 1 else 0

/-- Restrict a dual vector to the normal minor's selected columns. -/
def Data.normalRestriction (d : Data) :
    Module.Dual ℚ Vec6 →ₗ[ℚ] (Fin (6 - d.rank) → ℚ) where
  toFun f j := f (stdBasisVec (d.normalCoord j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The square lower minor, indexed in the exact JSON order. -/
def Data.lowerMinor (d : Data) : Matrix (Fin d.rank) (Fin d.rank) ℚ := fun i j =>
  d.lowerDiff i (d.lowerCoord j)

/-- The square normal minor, indexed in the exact JSON order. -/
def Data.normalMinor (d : Data) : Matrix (Fin (6 - d.rank)) (Fin (6 - d.rank)) ℚ :=
  fun i j => d.normalFunctional i (stdBasisVec (d.normalCoord j))

/-- No six-bit word is selected.  This checks semantic emptiness of the low
64 mask bits, rather than incorrectly requiring the ambient natural to be 0. -/
def MaskEmpty (mask : ℕ) : Prop := ∀ x : Word6, ¬ InMask mask x

/-- The lower-rank half of a nonempty certificate. -/
structure LowerValid (mask : ℕ) (d : Data) : Prop where
  rank_le : d.rank ≤ 6
  base_lt : d.base < 64
  base_mem : InMask mask d.baseWord
  lower_length : d.lowerPoints.length = d.rank
  coord_length : d.lowerCoords.length = d.rank
  lower_lt : ∀ i : Fin d.rank, d.lowerPoints.getD i.1 0 < 64
  lower_mem : ∀ i : Fin d.rank, InMask mask (d.lowerWord i)
  coord_lt : ∀ j : Fin d.rank, d.lowerCoords.getD j.1 0 < 6
  minor_ne : d.lowerMinor.det ≠ 0

/-- The upper-rank half of a nonempty certificate. -/
structure UpperValid (mask : ℕ) (d : Data) : Prop where
  rank_le : d.rank ≤ 6
  normals_length : d.normals.length = 6 - d.rank
  normal_width : ∀ i : Fin (6 - d.rank), (d.normals.getD i.1 []).length = 6
  coord_length : d.normalCoords.length = 6 - d.rank
  coord_lt : ∀ j : Fin (6 - d.rank), d.normalCoords.getD j.1 0 < 6
  minor_ne : d.normalMinor.det ≠ 0
  annihilates : ∀ (x : Word6), InMask mask x →
    ∀ i : Fin (6 - d.rank), d.normalFunctional i (point x - d.basePoint) = 0

/-! ## Reduction-friendly inverse witnesses

Directly expanding a `6 × 6` Leibniz determinant creates 720 summands in every
generated proof.  The following helper formats certify the same non-singularity
claim by checking an exact rational right inverse entry by entry.  The abstract
determinant theorem is then used only once, in the generic conversion below.
-/

/-- A list-backed square rational matrix.  Missing entries are padded by zero;
the equation with the identity is the semantic check, so padding cannot make a
bad inverse pass. -/
def listMatrix (n : ℕ) (rows : List (List ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (rows.getD i.1 []).getD j.1 0

structure LowerInverseValid (mask : ℕ) (d : Data) where
  inverseRows : List (List ℚ)
  rank_le : d.rank ≤ 6
  base_lt : d.base < 64
  base_mem : InMask mask d.baseWord
  lower_length : d.lowerPoints.length = d.rank
  coord_length : d.lowerCoords.length = d.rank
  lower_lt : ∀ i : Fin d.rank, d.lowerPoints.getD i.1 0 < 64
  lower_mem : ∀ i : Fin d.rank, InMask mask (d.lowerWord i)
  coord_lt : ∀ j : Fin d.rank, d.lowerCoords.getD j.1 0 < 6
  right_inverse : d.lowerMinor * listMatrix d.rank inverseRows = 1

structure UpperInverseValid (mask : ℕ) (d : Data) where
  inverseRows : List (List ℚ)
  rank_le : d.rank ≤ 6
  normals_length : d.normals.length = 6 - d.rank
  normal_width : ∀ i : Fin (6 - d.rank), (d.normals.getD i.1 []).length = 6
  coord_length : d.normalCoords.length = 6 - d.rank
  coord_lt : ∀ j : Fin (6 - d.rank), d.normalCoords.getD j.1 0 < 6
  right_inverse : d.normalMinor * listMatrix (6 - d.rank) inverseRows = 1
  annihilates : ∀ (x : Word6), InMask mask x →
    ∀ i : Fin (6 - d.rank), d.normalFunctional i (point x - d.basePoint) = 0

/-- A compact upper-rank witness checks annihilation only on the actual mask
words.  `mask_eq` is an exact kernel-checked bridge back to the quantified
`InMask` predicate, avoiding 64 generated cases for every normal. -/
structure UpperListInverseValid (mask : ℕ) (d : Data) where
  inverseRows : List (List ℚ)
  words : List ℕ
  mask_eq : mask = wordMask words
  words_lt : ∀ w ∈ words, w < 64
  rank_le : d.rank ≤ 6
  normals_length : d.normals.length = 6 - d.rank
  normal_width : ∀ i : Fin (6 - d.rank), (d.normals.getD i.1 []).length = 6
  coord_length : d.normalCoords.length = 6 - d.rank
  coord_lt : ∀ j : Fin (6 - d.rank), d.normalCoords.getD j.1 0 < 6
  right_inverse : d.normalMinor * listMatrix (6 - d.rank) inverseRows = 1
  annihilates : ∀ w ∈ words, ∀ i : Fin (6 - d.rank),
    d.normalFunctional i (point (wordOfNat w) - d.basePoint) = 0

private theorem det_ne_zero_of_mul_eq_one {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℚ)
    (h : M * N = 1) : M.det ≠ 0 := by
  intro hz
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hdet
  norm_num at hdet

def LowerInverseValid.toLowerValid {mask : ℕ} {d : Data}
    (h : LowerInverseValid mask d) : LowerValid mask d where
  rank_le := h.rank_le
  base_lt := h.base_lt
  base_mem := h.base_mem
  lower_length := h.lower_length
  coord_length := h.coord_length
  lower_lt := h.lower_lt
  lower_mem := h.lower_mem
  coord_lt := h.coord_lt
  minor_ne := det_ne_zero_of_mul_eq_one _ _ h.right_inverse

def UpperInverseValid.toUpperValid {mask : ℕ} {d : Data}
    (h : UpperInverseValid mask d) : UpperValid mask d where
  rank_le := h.rank_le
  normals_length := h.normals_length
  normal_width := h.normal_width
  coord_length := h.coord_length
  coord_lt := h.coord_lt
  minor_ne := det_ne_zero_of_mul_eq_one _ _ h.right_inverse
  annihilates := h.annihilates

def UpperListInverseValid.toUpperInverseValid {mask : ℕ} {d : Data}
    (h : UpperListInverseValid mask d) : UpperInverseValid mask d where
  inverseRows := h.inverseRows
  rank_le := h.rank_le
  normals_length := h.normals_length
  normal_width := h.normal_width
  coord_length := h.coord_length
  coord_lt := h.coord_lt
  right_inverse := h.right_inverse
  annihilates := by
    intro x hx i
    have hmem : x.1 ∈ h.words := by
      rw [h.mask_eq, in_wordMask_iff] at hx
      exact hx
    have hw := h.annihilates x.1 hmem i
    have hword : wordOfNat x.1 = x := by
      apply Fin.ext
      exact MainTheory.FinitePipeline.wordOfNat_val x.isLt
    simpa only [hword] using hw

/-- A certificate is either an explicit proof that the mask is empty and the
claimed rank is zero, or a complete lower-and-upper nonempty certificate. -/
def Data.Valid (mask : ℕ) (d : Data) : Prop :=
  (MaskEmpty mask ∧ d.rank = 0) ∨ (LowerValid mask d ∧ UpperValid mask d)

/-- Build a complete nonempty rank certificate from two exact inverse
witnesses. -/
theorem Data.valid_of_inverse_witnesses {mask : ℕ} {d : Data}
    (hl : LowerInverseValid mask d) (hu : UpperInverseValid mask d) :
    d.Valid mask := by
  exact Or.inr ⟨hl.toLowerValid, hu.toUpperValid⟩

/-- Variant using a finite list for the upper annihilation audit. -/
theorem Data.valid_of_inverse_list_witnesses {mask : ℕ} {d : Data}
    (hl : LowerInverseValid mask d) (hu : UpperListInverseValid mask d) :
    d.Valid mask :=
  Data.valid_of_inverse_witnesses hl hu.toUpperInverseValid

instance (mask : ℕ) : Decidable (MaskEmpty mask) := by
  unfold MaskEmpty
  infer_instance

private def LowerConditions (mask : ℕ) (d : Data) : Prop :=
  d.rank ≤ 6 ∧ d.base < 64 ∧ InMask mask d.baseWord ∧
  d.lowerPoints.length = d.rank ∧ d.lowerCoords.length = d.rank ∧
  (∀ i : Fin d.rank, d.lowerPoints.getD i.1 0 < 64) ∧
  (∀ i : Fin d.rank, InMask mask (d.lowerWord i)) ∧
  (∀ j : Fin d.rank, d.lowerCoords.getD j.1 0 < 6) ∧ d.lowerMinor.det ≠ 0

private theorem lowerConditions_iff (mask : ℕ) (d : Data) :
    LowerConditions mask d ↔ LowerValid mask d := by
  constructor
  · rintro ⟨hr, hb, hbm, hl, hcl, hp, hpm, hc, hd⟩
    exact ⟨hr, hb, hbm, hl, hcl, hp, hpm, hc, hd⟩
  · intro h
    exact ⟨h.rank_le, h.base_lt, h.base_mem, h.lower_length, h.coord_length,
      h.lower_lt, h.lower_mem, h.coord_lt, h.minor_ne⟩

instance (mask : ℕ) (d : Data) : Decidable (LowerValid mask d) := by
  letI : Decidable (LowerConditions mask d) := by
    unfold LowerConditions
    infer_instance
  exact decidable_of_iff (LowerConditions mask d) (lowerConditions_iff mask d)

private def UpperConditions (mask : ℕ) (d : Data) : Prop :=
  d.rank ≤ 6 ∧ d.normals.length = 6 - d.rank ∧
  (∀ i : Fin (6 - d.rank), (d.normals.getD i.1 []).length = 6) ∧
  d.normalCoords.length = 6 - d.rank ∧
  (∀ j : Fin (6 - d.rank), d.normalCoords.getD j.1 0 < 6) ∧
  d.normalMinor.det ≠ 0 ∧
  (∀ (x : Word6), InMask mask x →
    ∀ i : Fin (6 - d.rank), d.normalFunctional i (point x - d.basePoint) = 0)

private theorem upperConditions_iff (mask : ℕ) (d : Data) :
    UpperConditions mask d ↔ UpperValid mask d := by
  constructor
  · rintro ⟨hr, hn, hw, hc, hcl, hm, ha⟩
    exact ⟨hr, hn, hw, hc, hcl, hm, ha⟩
  · intro h
    exact ⟨h.rank_le, h.normals_length, h.normal_width, h.coord_length,
      h.coord_lt, h.minor_ne, h.annihilates⟩

instance (mask : ℕ) (d : Data) : Decidable (UpperValid mask d) := by
  letI : Decidable (UpperConditions mask d) := by
    unfold UpperConditions
    infer_instance
  exact decidable_of_iff (UpperConditions mask d) (upperConditions_iff mask d)

instance (mask : ℕ) (d : Data) : Decidable (d.Valid mask) := by
  unfold Data.Valid
  infer_instance

private theorem lowerMinor_eq_restriction (d : Data) :
    d.lowerRestriction ∘ d.lowerDiff = d.lowerMinor := by
  rfl

private theorem normalMinor_eq_restriction (d : Data) :
    d.normalRestriction ∘ d.normalFunctional = d.normalMinor := by
  rfl

private theorem basePoint_mem {mask : ℕ} {d : Data} (h : LowerValid mask d) :
    d.basePoint ∈ maskPointSet mask := by
  exact ⟨d.baseWord, h.base_mem, rfl⟩

private theorem lowerPoint_mem {mask : ℕ} {d : Data} (h : LowerValid mask d)
    (i : Fin d.rank) : point (d.lowerWord i) ∈ maskPointSet mask := by
  exact ⟨d.lowerWord i, h.lower_mem i, rfl⟩

private theorem lowerDiff_mem_direction {mask : ℕ} {d : Data} (h : LowerValid mask d)
    (i : Fin d.rank) : d.lowerDiff i ∈ (affineSpan ℚ (maskPointSet mask)).direction := by
  exact AffineSubspace.vsub_mem_direction
    (mem_affineSpan ℚ (lowerPoint_mem h i)) (mem_affineSpan ℚ (basePoint_mem h))

private theorem lowerDiff_linearIndependent {mask : ℕ} {d : Data}
    (h : LowerValid mask d) : LinearIndependent ℚ d.lowerDiff := by
  apply LinearIndependent.of_comp d.lowerRestriction
  rw [lowerMinor_eq_restriction]
  exact Matrix.linearIndependent_rows_of_det_ne_zero h.minor_ne

private theorem rank_le_maskAffineRank {mask : ℕ} {d : Data}
    (h : LowerValid mask d) : d.rank ≤ maskAffineRank mask := by
  let D := (affineSpan ℚ (maskPointSet mask)).direction
  let v : Fin d.rank → D := fun i => ⟨d.lowerDiff i, lowerDiff_mem_direction h i⟩
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp D.subtype
    simpa [v] using lowerDiff_linearIndependent h
  simpa [maskAffineRank, D] using hv.fintype_card_le_finrank

private theorem maskPointSet_subset_hyperplane {mask : ℕ} {d : Data}
    (h : UpperValid mask d) (i : Fin (6 - d.rank)) :
    maskPointSet mask ⊆ AffineSubspace.mk' d.basePoint (LinearMap.ker (d.normalFunctional i)) := by
  rintro _ ⟨x, hx, rfl⟩
  change point x - d.basePoint ∈ LinearMap.ker (d.normalFunctional i)
  exact h.annihilates x hx i

private theorem direction_le_normalKer {mask : ℕ} {d : Data}
    (h : UpperValid mask d) (i : Fin (6 - d.rank)) :
    (affineSpan ℚ (maskPointSet mask)).direction ≤ LinearMap.ker (d.normalFunctional i) := by
  have hd := AffineSubspace.direction_le
    (affineSpan_le.2 (maskPointSet_subset_hyperplane h i))
  simpa only [AffineSubspace.direction_mk'] using hd

private theorem normalFunctional_linearIndependent {mask : ℕ} {d : Data}
    (h : UpperValid mask d) : LinearIndependent ℚ d.normalFunctional := by
  apply LinearIndependent.of_comp d.normalRestriction
  rw [normalMinor_eq_restriction]
  exact Matrix.linearIndependent_rows_of_det_ne_zero h.minor_ne

private theorem direction_le_normalCoannihilator {mask : ℕ} {d : Data}
    (h : UpperValid mask d) :
    (affineSpan ℚ (maskPointSet mask)).direction ≤
      (Submodule.span ℚ (Set.range d.normalFunctional)).dualCoannihilator := by
  intro v hv
  rw [Submodule.mem_dualCoannihilator]
  intro f hf
  refine Submodule.span_induction
    (p := fun f _ => f v = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨i, rfl⟩
    exact direction_le_normalKer h i hv
  · rfl
  · intro f g _ _ hf hg
    simpa using congrArg₂ (· + ·) hf hg
  · intro a f _ hf
    simp [hf]

private theorem normalSpan_finrank {mask : ℕ} {d : Data} (h : UpperValid mask d) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range d.normalFunctional)) = 6 - d.rank := by
  rw [finrank_span_eq_card (normalFunctional_linearIndependent h)]
  simp

private theorem normalCoannihilator_finrank {mask : ℕ} {d : Data}
    (h : UpperValid mask d) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range d.normalFunctional)).dualCoannihilator =
      d.rank := by
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span ℚ (Set.range d.normalFunctional))
  rw [normalSpan_finrank h] at hdim
  have hvec : Module.finrank ℚ Vec6 = 6 := by simp [Vec6]
  rw [hvec] at hdim
  have hr := h.rank_le
  omega

private theorem maskAffineRank_le_rank {mask : ℕ} {d : Data}
    (h : UpperValid mask d) : maskAffineRank mask ≤ d.rank := by
  calc
    maskAffineRank mask ≤
        Module.finrank ℚ (Submodule.span ℚ (Set.range d.normalFunctional)).dualCoannihilator := by
      exact Submodule.finrank_mono (direction_le_normalCoannihilator h)
    _ = d.rank := normalCoannihilator_finrank h

private theorem maskPointSet_eq_empty {mask : ℕ} (h : MaskEmpty mask) :
    maskPointSet mask = ∅ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x hx).elim
  · simp

private theorem maskAffineRank_eq_zero_of_empty {mask : ℕ} (h : MaskEmpty mask) :
    maskAffineRank mask = 0 := by
  rw [maskAffineRank, maskPointSet_eq_empty h]
  simp

/-- **Soundness of the exact affine-rank certificate.**  Every accepted data
object proves, in the ordinary Lean kernel, that its declared rank is exactly
the affine rank of all low-64 mask points. -/
theorem affineRank_eq_of_valid {mask : ℕ} {d : Data} (h : d.Valid mask) :
    maskAffineRank mask = d.rank := by
  rcases h with h | h
  · rw [h.2]
    exact maskAffineRank_eq_zero_of_empty h.1
  · exact Nat.le_antisymm (maskAffineRank_le_rank h.2) (rank_le_maskAffineRank h.1)

/-! ## Public one-sided bounds for threshold-only filters -/

/-- A lower inverse witness may be used without also constructing an upper
certificate.  This is the resource-efficient direction needed to certify
that a mask reaches a prescribed rank threshold. -/
theorem rank_le_maskAffineRank_of_lowerInverse {mask : ℕ} {d : Data}
    (h : LowerInverseValid mask d) : d.rank ≤ maskAffineRank mask :=
  rank_le_maskAffineRank h.toLowerValid

/-- A list-backed upper inverse witness may be used without also constructing
a lower certificate.  This is the resource-efficient direction needed to
certify that a mask lies strictly below a prescribed rank threshold. -/
theorem maskAffineRank_le_rank_of_upperListInverse {mask : ℕ} {d : Data}
    (h : UpperListInverseValid mask d) : maskAffineRank mask ≤ d.rank :=
  maskAffineRank_le_rank h.toUpperInverseValid.toUpperValid

end MainTheory.AffineRankCertificate
