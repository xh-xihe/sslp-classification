import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem row_40 : ∀ k < 64,
    rowCheck (⟨nbit 40, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_41 : ∀ k < 64,
    rowCheck (⟨nbit 41, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_42 : ∀ k < 64,
    rowCheck (⟨nbit 42, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_43 : ∀ k < 64,
    rowCheck (⟨nbit 43, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_44 : ∀ k < 64,
    rowCheck (⟨nbit 44, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_45 : ∀ k < 64,
    rowCheck (⟨nbit 45, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_46 : ∀ k < 64,
    rowCheck (⟨nbit 46, nbit k⟩ : SS.PauliString 6) := by decide

theorem row_47 : ∀ k < 64,
    rowCheck (⟨nbit 47, nbit k⟩ : SS.PauliString 6) := by decide

theorem rows5 : ∀ j < 8, ∀ k < 64,
    rowCheck (⟨nbit (40 + j), nbit k⟩ : SS.PauliString 6) := by
  intro j hj
  interval_cases j
  · exact row_40
  · exact row_41
  · exact row_42
  · exact row_43
  · exact row_44
  · exact row_45
  · exact row_46
  · exact row_47

end SixQubit.OpenMParity
