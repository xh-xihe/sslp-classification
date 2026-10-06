import MainTheory.OuterEnumeration

namespace MainTheory.RawOuterLoopBoundary

open MainTheory.OuterEnumeration

def zeroRecord : RawRecord := ⟨2, 2, angle6 0 0 0 0 0 0⟩

theorem zero_record_in_raw_loop : zeroRecord ∈ rawRecords := by decide

theorem zero_record_not_primitive : IsPrimitive zeroRecord.q zeroRecord.a = false := by decide

theorem zero_record_has_empty_second_fiber : HasSecondFiberByMasks zeroRecord = false := by decide

end MainTheory.RawOuterLoopBoundary
