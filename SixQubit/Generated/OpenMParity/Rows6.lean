import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_48 : ∀ k < 64,
    rowCheck (⟨nbit 48, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_49 : ∀ k < 64,
    rowCheck (⟨nbit 49, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_50 : ∀ k < 64,
    rowCheck (⟨nbit 50, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_51 : ∀ k < 64,
    rowCheck (⟨nbit 51, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_52 : ∀ k < 64,
    rowCheck (⟨nbit 52, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_53 : ∀ k < 64,
    rowCheck (⟨nbit 53, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_54 : ∀ k < 64,
    rowCheck (⟨nbit 54, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_55 : ∀ k < 64,
    rowCheck (⟨nbit 55, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows6 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (48 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_48
  · exact row_49
  · exact row_50
  · exact row_51
  · exact row_52
  · exact row_53
  · exact row_54
  · exact row_55

end SixQubit.OpenMParity
