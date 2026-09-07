import SixQubit.Generated.OpenLFamilies.Orbit2Data

namespace SixQubit.OpenLOrbit2

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_48 : ∀ k < 64,
    (⟨nbit 48, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 48, nbit k⟩ := by decide

theorem kl_masks_fixed_49 : ∀ k < 64,
    (⟨nbit 49, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 49, nbit k⟩ := by decide

theorem kl_masks_fixed_50 : ∀ k < 64,
    (⟨nbit 50, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 50, nbit k⟩ := by decide

theorem kl_masks_fixed_51 : ∀ k < 64,
    (⟨nbit 51, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 51, nbit k⟩ := by decide

theorem kl_masks_fixed_52 : ∀ k < 64,
    (⟨nbit 52, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 52, nbit k⟩ := by decide

theorem kl_masks_fixed_53 : ∀ k < 64,
    (⟨nbit 53, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 53, nbit k⟩ := by decide

theorem kl_masks_fixed_54 : ∀ k < 64,
    (⟨nbit 54, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 54, nbit k⟩ := by decide

theorem kl_masks_fixed_55 : ∀ k < 64,
    (⟨nbit 55, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 55, nbit k⟩ := by decide

theorem kl_masks_6 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*6+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*6+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_48
  · exact kl_masks_fixed_49
  · exact kl_masks_fixed_50
  · exact kl_masks_fixed_51
  · exact kl_masks_fixed_52
  · exact kl_masks_fixed_53
  · exact kl_masks_fixed_54
  · exact kl_masks_fixed_55

theorem sparse_masks_fixed_48 : ∀ k < 64,
    sparseCheck ⟨nbit 48, nbit k⟩ := by decide

theorem sparse_masks_fixed_49 : ∀ k < 64,
    sparseCheck ⟨nbit 49, nbit k⟩ := by decide

theorem sparse_masks_fixed_50 : ∀ k < 64,
    sparseCheck ⟨nbit 50, nbit k⟩ := by decide

theorem sparse_masks_fixed_51 : ∀ k < 64,
    sparseCheck ⟨nbit 51, nbit k⟩ := by decide

theorem sparse_masks_fixed_52 : ∀ k < 64,
    sparseCheck ⟨nbit 52, nbit k⟩ := by decide

theorem sparse_masks_fixed_53 : ∀ k < 64,
    sparseCheck ⟨nbit 53, nbit k⟩ := by decide

theorem sparse_masks_fixed_54 : ∀ k < 64,
    sparseCheck ⟨nbit 54, nbit k⟩ := by decide

theorem sparse_masks_fixed_55 : ∀ k < 64,
    sparseCheck ⟨nbit 55, nbit k⟩ := by decide

theorem sparse_masks_6 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*6+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_48
  · exact sparse_masks_fixed_49
  · exact sparse_masks_fixed_50
  · exact sparse_masks_fixed_51
  · exact sparse_masks_fixed_52
  · exact sparse_masks_fixed_53
  · exact sparse_masks_fixed_54
  · exact sparse_masks_fixed_55

end SixQubit.OpenLOrbit2
