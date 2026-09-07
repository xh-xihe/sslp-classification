import MainTheory.Generated.OrbitTableMultiplicities

/-!
# The paper's row order is a relabelling, not a selection

`OrbitTableRecords.paperKey : Fin 66 -> Fin 66` translates the manuscript's row
number into this repository's internal key, and every statement about the
manuscript's table is indexed through it -- notably
`Generated.OrbitTableMultiplicities.all_multiplicities`, which reads

  `multiplicity (paperKey i) = paperMultiplicity i`   for every `i : Fin 66`.

Read literally that is a statement about the *image* of `paperKey`.  If
`paperKey` were not surjective it would leave internal keys with no row at all,
and if it were not injective two rows would describe the same orbit while a
third orbit went unmentioned -- in either case the table would not be the
classification, and the theorem would still be true.

Nothing anywhere proved it was a bijection.  This file does, by kernel
evaluation, and then draws the two consequences that make the table a table:
every internal key is the image of exactly one manuscript row, and the row
multiplicities sum to the 216 surviving records.

`paperKey` is generated, so the theorems live here rather than being appended
to `MainTheory/Generated/OrbitTableRecords.lean`.
-/

namespace MainTheory.OrbitTablePaperKey

open MainTheory.OrbitRecordMultiplicity
open MainTheory.Generated

set_option maxRecDepth 40000

/-- The manuscript's row order is injective. -/
theorem paperKey_injective : Function.Injective OrbitTableRecords.paperKey := by
  decide

theorem paperKey_bijective : Function.Bijective OrbitTableRecords.paperKey :=
  Finite.injective_iff_bijective.mp paperKey_injective

theorem paperKey_surjective : Function.Surjective OrbitTableRecords.paperKey :=
  paperKey_bijective.2

/-- **Every internal key is named by exactly one manuscript row**, and that
row's multiplicity is the key's.  This is what upgrades `all_multiplicities`
from a statement about the rows to a statement about the orbits. -/
theorem exists_unique_row (k : KeyId) :
    ∃! i : Fin 66, OrbitTableRecords.paperKey i = k := by
  obtain ⟨i, hi⟩ := paperKey_surjective k
  exact ⟨i, hi, fun j hj => paperKey_injective (hj.trans hi.symm)⟩

/-- Restated on the key rather than on the row. -/
theorem multiplicity_eq_paperMultiplicity (k : KeyId) :
    ∃ i : Fin 66, OrbitTableRecords.paperKey i = k ∧
      multiplicity k = OrbitTableRecords.paperMultiplicity i := by
  obtain ⟨i, hi⟩ := paperKey_surjective k
  exact ⟨i, hi, hi ▸ OrbitTableMultiplicities.all_multiplicities i⟩

/-- The manuscript's multiplicity column sums to the number of surviving
records, so no record is counted twice and none is dropped. -/
theorem sum_paperMultiplicity :
    ∑ i : Fin 66, OrbitTableRecords.paperMultiplicity i = 216 := by
  decide

end MainTheory.OrbitTablePaperKey
