import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_8 : ∀ k < 64,
    rowCheck (⟨nbit 8, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_9 : ∀ k < 64,
    rowCheck (⟨nbit 9, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_10 : ∀ k < 64,
    rowCheck (⟨nbit 10, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_11 : ∀ k < 64,
    rowCheck (⟨nbit 11, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_12 : ∀ k < 64,
    rowCheck (⟨nbit 12, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_13 : ∀ k < 64,
    rowCheck (⟨nbit 13, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_14 : ∀ k < 64,
    rowCheck (⟨nbit 14, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_15 : ∀ k < 64,
    rowCheck (⟨nbit 15, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows1 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (8 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15

end SixQubit.OpenMParity
