import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_0 : ∀ k < 64,
    rowCheck (⟨nbit 0, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_1 : ∀ k < 64,
    rowCheck (⟨nbit 1, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_2 : ∀ k < 64,
    rowCheck (⟨nbit 2, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_3 : ∀ k < 64,
    rowCheck (⟨nbit 3, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_4 : ∀ k < 64,
    rowCheck (⟨nbit 4, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_5 : ∀ k < 64,
    rowCheck (⟨nbit 5, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_6 : ∀ k < 64,
    rowCheck (⟨nbit 6, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_7 : ∀ k < 64,
    rowCheck (⟨nbit 7, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows0 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (0 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7

end SixQubit.OpenMParity
