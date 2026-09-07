import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_24 : ∀ k < 64,
    rowCheck (⟨nbit 24, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_25 : ∀ k < 64,
    rowCheck (⟨nbit 25, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_26 : ∀ k < 64,
    rowCheck (⟨nbit 26, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_27 : ∀ k < 64,
    rowCheck (⟨nbit 27, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_28 : ∀ k < 64,
    rowCheck (⟨nbit 28, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_29 : ∀ k < 64,
    rowCheck (⟨nbit 29, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_30 : ∀ k < 64,
    rowCheck (⟨nbit 30, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_31 : ∀ k < 64,
    rowCheck (⟨nbit 31, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows3 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (24 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_24
  · exact row_25
  · exact row_26
  · exact row_27
  · exact row_28
  · exact row_29
  · exact row_30
  · exact row_31

end SixQubit.OpenMParity
