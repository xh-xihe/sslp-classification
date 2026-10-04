import SixQubit.Generated.Orbit3CollectedRows.TraceH208Certified
import SixQubit.Generated.Orbit3CollectedRows.TraceH209Certified
import SixQubit.Generated.Orbit3CollectedRows.TraceH210Certified

namespace SixQubit.Generated.Orbit3CollectedHadamardRows

theorem hadamard_indices : ∀ i : Fin 211, Orbit3PauliConstraints.kind i = 2 →
    i = 208 ∨ i = 209 ∨ i = 210 := by decide +kernel

theorem all_hadamard_primitive_rows_zero
    (W : MainTheory.Orbit3ScalarCategoryRealization.Encoder)
    (i : Fin 211) (hi : Orbit3PauliConstraints.kind i = 2) :
    Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i)
      (MainTheory.Orbit3CoordinateRealization.coordinates W) = 0 := by
  rcases hadamard_indices i hi with h | h | h
  · subst i; exact Orbit3CollectedRows.TraceH208.Certified.primitive_row_zero W
  · subst i; exact Orbit3CollectedRows.TraceH209.Certified.primitive_row_zero W
  · subst i; exact Orbit3CollectedRows.TraceH210.Certified.primitive_row_zero W

end SixQubit.Generated.Orbit3CollectedHadamardRows
