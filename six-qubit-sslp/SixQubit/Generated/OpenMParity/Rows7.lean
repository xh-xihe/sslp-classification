import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_56 : ∀ k < 64,
    rowCheck (⟨nbit 56, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_57 : ∀ k < 64,
    rowCheck (⟨nbit 57, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_58 : ∀ k < 64,
    rowCheck (⟨nbit 58, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_59 : ∀ k < 64,
    rowCheck (⟨nbit 59, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_60 : ∀ k < 64,
    rowCheck (⟨nbit 60, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_61 : ∀ k < 64,
    rowCheck (⟨nbit 61, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_62 : ∀ k < 64,
    rowCheck (⟨nbit 62, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_63 : ∀ k < 64,
    rowCheck (⟨nbit 63, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows7 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (56 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_56
  · exact row_57
  · exact row_58
  · exact row_59
  · exact row_60
  · exact row_61
  · exact row_62
  · exact row_63

end SixQubit.OpenMParity
