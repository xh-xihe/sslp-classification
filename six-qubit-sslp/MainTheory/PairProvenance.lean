import MainTheory.OuterCompleteness
import MainTheory.FinitePipeline

/-!
# Fully kernel-checked provenance for generated finite pair tables

The finite pipeline deduplicates the residue-fiber pairs arising from
`OuterEnumeration.nonemptyFiberRecords`.  A generated table is trustworthy
only when it proves both directions of this relationship:

* every outer record points to the exact pair computed from that record;
* every table-indexed payload is realized by an outer record.

All indexing below uses `Fin`.  There is no default element and no fallback
lookup whose value could silently replace an out-of-bounds index.
-/

namespace MainTheory.PairProvenance

open MainTheory

/-- A proof-relevant index into the actual surviving outer enumeration. -/
abbrev OuterRecordIndex : Type :=
  Fin OuterEnumeration.nonemptyFiberRecords.length

/-- The indexed outer record.  `List.get` requires its bound as part of the
index, so this definition cannot fall back to a dummy record. -/
def outerRecord (i : OuterRecordIndex) : OuterEnumeration.RawRecord :=
  OuterEnumeration.nonemptyFiberRecords.get i

/-- The exact fiber pair computed from an indexed outer record. -/
def outerPair (i : OuterRecordIndex) : FinitePipeline.FiberPair :=
  OuterCompleteness.recordFiberPair (outerRecord i)

/-- Generated table data.  Both the payload and the record map are finite
functions.  In particular, the index type mentions only `pairCount`, never
the reduction of a large array literal's `.size`. -/
structure Table where
  pairCount : ℕ
  pairs : Fin pairCount → FinitePipeline.FiberPair
  recordToPair : OuterRecordIndex → Fin pairCount

/-- Exact lookup of a table entry. -/
def Table.pairAt (table : Table) (i : Fin table.pairCount) :
    FinitePipeline.FiberPair :=
  table.pairs i

/-- The complete provenance obligation for a generated table.

`exactRecord` rules out an incorrect record-to-table assignment.
`noGhostIndex` rules out table entries with no outer provenance.  It is stated
directly at the semantic payload level: image equality needs no artificial
injectivity or deduplication premise for table indices. -/
structure Table.Validity (table : Table) : Prop where
  exactRecord : ∀ i, table.pairAt (table.recordToPair i) = outerPair i
  noGhostIndex : ∀ j, ∃ i, table.pairAt j = outerPair i

/-- A table is genuinely deduplicated when its finite index is injective at
the exact payload level.  This is deliberately separate from `Validity`:
two-way image coverage alone does not rule out duplicate table positions. -/
structure Table.Deduplicated (table : Table) : Prop where
  pairAt_injective : Function.Injective table.pairAt

theorem Table.Deduplicated.pairAt_eq_iff {table : Table}
    (dedup : table.Deduplicated) (i j : Fin table.pairCount) :
    table.pairAt i = table.pairAt j ↔ i = j := by
  constructor
  · intro hpairs
    exact dedup.pairAt_injective hpairs
  · intro hij
    rw [hij]

theorem Table.Deduplicated.pairAt_ne {table : Table}
    (dedup : table.Deduplicated) {i j : Fin table.pairCount} (hij : i ≠ j) :
    table.pairAt i ≠ table.pairAt j := by
  intro hpairs
  exact hij (dedup.pairAt_injective hpairs)

/-! ## Immediate indexed consequences -/

theorem outerRecord_mem (i : OuterRecordIndex) :
    outerRecord i ∈ OuterEnumeration.nonemptyFiberRecords := by
  exact List.get_mem _ i

/-- Every outer record is covered by its declared table index. -/
theorem Table.Validity.recordCovered {table : Table}
    (valid : table.Validity) (i : OuterRecordIndex) :
    ∃ j : Fin table.pairCount, table.pairAt j = outerPair i :=
  ⟨table.recordToPair i, valid.exactRecord i⟩

/-- Every table position's payload is realized by an outer record. -/
theorem Table.Validity.entryWitness {table : Table}
    (valid : table.Validity) (j : Fin table.pairCount) :
    ∃ i : OuterRecordIndex, table.pairAt j = outerPair i :=
  valid.noGhostIndex j

/-- Value-level no-ghost statement: every generated pair is the exact image
of a genuine surviving outer record. -/
theorem Table.Validity.noGhostPair {table : Table}
    (valid : table.Validity) (j : Fin table.pairCount) :
    ∃ i : OuterRecordIndex, table.pairAt j = outerPair i :=
  valid.entryWitness j

/-! ## Equality of the two images -/

/-- Values represented by the generated table. -/
def Table.image (table : Table) : Set FinitePipeline.FiberPair :=
  Set.range table.pairAt

/-- Values computed directly from all surviving outer records. -/
def outerImage : Set FinitePipeline.FiberPair := Set.range outerPair

/-- The two validity obligations imply exact equality of images.  The forward
direction is no-ghost provenance; the reverse direction is record coverage. -/
theorem Table.Validity.image_eq_outerImage {table : Table}
    (valid : table.Validity) : table.image = outerImage := by
  ext pair
  constructor
  · rintro ⟨j, hj⟩
    rcases valid.noGhostPair j with ⟨i, hi⟩
    exact ⟨i, hi.symm.trans hj⟩
  · rintro ⟨i, hi⟩
    exact ⟨table.recordToPair i, (valid.exactRecord i).trans hi⟩

/-- Pointwise form of image equality, convenient for downstream generated
certificate statements. -/
theorem Table.Validity.pair_mem_iff_outerWitness {table : Table}
    (valid : table.Validity) (pair : FinitePipeline.FiberPair) :
    pair ∈ table.image ↔ ∃ i : OuterRecordIndex, outerPair i = pair := by
  rw [valid.image_eq_outerImage]
  rfl

/-- Conversely, an outer image value has an exact table witness. -/
theorem Table.Validity.outerPair_has_tableWitness {table : Table}
    (valid : table.Validity) (i : OuterRecordIndex) :
    ∃ j : Fin table.pairCount, table.pairAt j = outerPair i :=
  valid.recordCovered i

/-! ## Nonempty-fiber provenance -/

/-- The fixed outer index contains only records whose second residue fiber
passed the executable nonemptiness test. -/
theorem outerRecord_hasSecondFiber (i : OuterRecordIndex) :
    OuterEnumeration.HasSecondFiber (outerRecord i) = true := by
  have hmem := outerRecord_mem i
  simp only [OuterEnumeration.nonemptyFiberRecords, List.mem_flatMap,
    List.mem_map] at hmem
  rcases hmem with ⟨q, _, m, _, a0, _, a, ha, hrecord⟩
  rw [← hrecord]
  exact (List.mem_filter.mp ha).2

/-- For each record, success of `HasSecondFiber` is exactly nonemptiness of
the second mask of its mapped generated pair. -/
theorem Table.Validity.hasSecondFiber_iff_mappedMask1_nonempty
    {table : Table} (valid : table.Validity) (i : OuterRecordIndex) :
    OuterEnumeration.HasSecondFiber (outerRecord i) = true ↔
      ∃ x : FinitePipeline.Word6,
        FinitePipeline.InMask
          (table.pairAt (table.recordToPair i)).mask1 x := by
  rw [valid.exactRecord i]
  exact OuterCompleteness.hasSecondFiber_iff_recordFiberPair_mask1_nonempty
    (outerRecord i)

/-- Hence every mapped record has a nonempty second mask. -/
theorem Table.Validity.mappedMask1_nonempty {table : Table}
    (valid : table.Validity) (i : OuterRecordIndex) :
    ∃ x : FinitePipeline.Word6,
      FinitePipeline.InMask
        (table.pairAt (table.recordToPair i)).mask1 x :=
  (valid.hasSecondFiber_iff_mappedMask1_nonempty i).1
    (outerRecord_hasSecondFiber i)

/-- With the no-ghost condition, every table entry has a nonempty second
fiber, not merely every entry reached in a partial record traversal. -/
theorem Table.Validity.everyEntryMask1_nonempty {table : Table}
    (valid : table.Validity) (j : Fin table.pairCount) :
    ∃ x : FinitePipeline.Word6,
      FinitePipeline.InMask (table.pairAt j).mask1 x := by
  rcases valid.noGhostIndex j with ⟨i, hi⟩
  rw [hi]
  rw [← valid.exactRecord i]
  exact valid.mappedMask1_nonempty i

end MainTheory.PairProvenance
