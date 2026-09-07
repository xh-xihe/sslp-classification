import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_32 : ∀ k < 64,
    rowCheck (⟨nbit 32, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_33 : ∀ k < 64,
    rowCheck (⟨nbit 33, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_34 : ∀ k < 64,
    rowCheck (⟨nbit 34, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_35 : ∀ k < 64,
    rowCheck (⟨nbit 35, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_36 : ∀ k < 64,
    rowCheck (⟨nbit 36, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_37 : ∀ k < 64,
    rowCheck (⟨nbit 37, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_38 : ∀ k < 64,
    rowCheck (⟨nbit 38, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_39 : ∀ k < 64,
    rowCheck (⟨nbit 39, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows4 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (32 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_32
  · exact row_33
  · exact row_34
  · exact row_35
  · exact row_36
  · exact row_37
  · exact row_38
  · exact row_39

end SixQubit.OpenMParity
