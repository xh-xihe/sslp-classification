import SixQubit.Generated.OpenLFamilies.Orbit1Data

namespace SixQubit.OpenLOrbit1

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_56 : ∀ k < 64,
    (⟨nbit 56, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 56, nbit k⟩ := by decide

theorem kl_masks_fixed_57 : ∀ k < 64,
    (⟨nbit 57, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 57, nbit k⟩ := by decide

theorem kl_masks_fixed_58 : ∀ k < 64,
    (⟨nbit 58, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 58, nbit k⟩ := by decide

theorem kl_masks_fixed_59 : ∀ k < 64,
    (⟨nbit 59, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 59, nbit k⟩ := by decide

theorem kl_masks_fixed_60 : ∀ k < 64,
    (⟨nbit 60, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 60, nbit k⟩ := by decide

theorem kl_masks_fixed_61 : ∀ k < 64,
    (⟨nbit 61, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 61, nbit k⟩ := by decide

theorem kl_masks_fixed_62 : ∀ k < 64,
    (⟨nbit 62, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 62, nbit k⟩ := by decide

theorem kl_masks_fixed_63 : ∀ k < 64,
    (⟨nbit 63, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 63, nbit k⟩ := by decide

theorem kl_masks_7 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*7+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*7+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_56
  · exact kl_masks_fixed_57
  · exact kl_masks_fixed_58
  · exact kl_masks_fixed_59
  · exact kl_masks_fixed_60
  · exact kl_masks_fixed_61
  · exact kl_masks_fixed_62
  · exact kl_masks_fixed_63

theorem sparse_masks_fixed_56 : ∀ k < 64,
    sparseCheck ⟨nbit 56, nbit k⟩ := by decide

theorem sparse_masks_fixed_57 : ∀ k < 64,
    sparseCheck ⟨nbit 57, nbit k⟩ := by decide

theorem sparse_masks_fixed_58 : ∀ k < 64,
    sparseCheck ⟨nbit 58, nbit k⟩ := by decide

theorem sparse_masks_fixed_59 : ∀ k < 64,
    sparseCheck ⟨nbit 59, nbit k⟩ := by decide

theorem sparse_masks_fixed_60 : ∀ k < 64,
    sparseCheck ⟨nbit 60, nbit k⟩ := by decide

theorem sparse_masks_fixed_61 : ∀ k < 64,
    sparseCheck ⟨nbit 61, nbit k⟩ := by decide

theorem sparse_masks_fixed_62 : ∀ k < 64,
    sparseCheck ⟨nbit 62, nbit k⟩ := by decide

theorem sparse_masks_fixed_63 : ∀ k < 64,
    sparseCheck ⟨nbit 63, nbit k⟩ := by decide

theorem sparse_masks_7 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*7+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_56
  · exact sparse_masks_fixed_57
  · exact sparse_masks_fixed_58
  · exact sparse_masks_fixed_59
  · exact sparse_masks_fixed_60
  · exact sparse_masks_fixed_61
  · exact sparse_masks_fixed_62
  · exact sparse_masks_fixed_63

end SixQubit.OpenLOrbit1
