import SixQubit.Generated.Orbit3CollectedRows.Spin203
import SixQubit.Generated.Orbit3CollectedRows.Spin204
import SixQubit.Generated.Orbit3CollectedRows.Spin205
import SixQubit.Generated.Orbit3CollectedRows.Spin206
import SixQubit.Generated.Orbit3CollectedRows.Spin207

namespace SixQubit.Generated.Orbit3CollectedSpinRows

theorem spin_indices : ∀ i : Fin 211, Orbit3PauliConstraints.kind i = 1 →
    i = 203 ∨ i = 204 ∨ i = 205 ∨ i = 206 ∨ i = 207 := by decide +kernel

theorem all_spin_primitive_rows_zero
    (W : MainTheory.Orbit3ScalarCategoryRealization.Encoder)
    (i : Fin 211) (hi : Orbit3PauliConstraints.kind i = 1) :
    Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i)
      (MainTheory.Orbit3CoordinateRealization.coordinates W) = 0 := by
  rcases spin_indices i hi with h | h | h | h | h
  · subst i; exact Orbit3CollectedRows.Spin203.primitive_row_zero W
  · subst i; exact Orbit3CollectedRows.Spin204.primitive_row_zero W
  · subst i; exact Orbit3CollectedRows.Spin205.primitive_row_zero W
  · subst i; exact Orbit3CollectedRows.Spin206.primitive_row_zero W
  · subst i; exact Orbit3CollectedRows.Spin207.primitive_row_zero W

end SixQubit.Generated.Orbit3CollectedSpinRows
