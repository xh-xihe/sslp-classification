import SixQubit.Generated.Orbit3CollectedRows.Trace000
import SixQubit.Generated.Orbit3RowMetadata
import MainTheory.Orbit3CoefficientTrace

namespace SixQubit.Generated.Orbit3CollectedRows.Trace000

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

theorem step00 : MainTheory.DyadicCoefficientTree.accumulate state00
    (MainTheory.Orbit3CoefficientTrace.rowTerms (Orbit3RowMetadata.pauli 0) 0) = state01 := by
  decide +kernel

end SixQubit.Generated.Orbit3CollectedRows.Trace000
