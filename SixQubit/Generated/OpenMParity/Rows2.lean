import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_16 : ∀ k < 64,
    rowCheck (⟨nbit 16, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_17 : ∀ k < 64,
    rowCheck (⟨nbit 17, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_18 : ∀ k < 64,
    rowCheck (⟨nbit 18, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_19 : ∀ k < 64,
    rowCheck (⟨nbit 19, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_20 : ∀ k < 64,
    rowCheck (⟨nbit 20, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_21 : ∀ k < 64,
    rowCheck (⟨nbit 21, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_22 : ∀ k < 64,
    rowCheck (⟨nbit 22, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_23 : ∀ k < 64,
    rowCheck (⟨nbit 23, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows2 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (16 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_16
  · exact row_17
  · exact row_18
  · exact row_19
  · exact row_20
  · exact row_21
  · exact row_22
  · exact row_23

end SixQubit.OpenMParity
