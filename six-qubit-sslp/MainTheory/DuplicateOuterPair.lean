import MainTheory.PairProvenance

namespace MainTheory.DuplicateOuterPair

def ones : MainTheory.OuterEnumeration.RawRecord := ⟨4, 2, fun _ => 1⟩
def threes : MainTheory.OuterEnumeration.RawRecord := ⟨4, 2, fun _ => 3⟩

theorem records_distinct : ones ≠ threes := by decide +kernel

theorem same_full_fibers : MainTheory.OuterCompleteness.recordFiberPair ones =
    MainTheory.OuterCompleteness.recordFiberPair threes := by decide +kernel

theorem both_primitive : MainTheory.OuterEnumeration.IsPrimitive 4 ones.a = true ∧
    MainTheory.OuterEnumeration.IsPrimitive 4 threes.a = true := by decide +kernel

end MainTheory.DuplicateOuterPair
