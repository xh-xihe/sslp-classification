import SixQubit.Generated.OpenLFamilies.Orbit2Data

namespace SixQubit.OpenLOrbit2

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_8 : ∀ k < 64,
    (⟨nbit 8, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 8, nbit k⟩ := by decide

theorem kl_masks_fixed_9 : ∀ k < 64,
    (⟨nbit 9, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 9, nbit k⟩ := by decide

theorem kl_masks_fixed_10 : ∀ k < 64,
    (⟨nbit 10, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 10, nbit k⟩ := by decide

theorem kl_masks_fixed_11 : ∀ k < 64,
    (⟨nbit 11, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 11, nbit k⟩ := by decide

theorem kl_masks_fixed_12 : ∀ k < 64,
    (⟨nbit 12, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 12, nbit k⟩ := by decide

theorem kl_masks_fixed_13 : ∀ k < 64,
    (⟨nbit 13, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 13, nbit k⟩ := by decide

theorem kl_masks_fixed_14 : ∀ k < 64,
    (⟨nbit 14, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 14, nbit k⟩ := by decide

theorem kl_masks_fixed_15 : ∀ k < 64,
    (⟨nbit 15, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 15, nbit k⟩ := by decide

theorem kl_masks_1 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*1+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*1+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_8
  · exact kl_masks_fixed_9
  · exact kl_masks_fixed_10
  · exact kl_masks_fixed_11
  · exact kl_masks_fixed_12
  · exact kl_masks_fixed_13
  · exact kl_masks_fixed_14
  · exact kl_masks_fixed_15

theorem sparse_masks_fixed_8 : ∀ k < 64,
    sparseCheck ⟨nbit 8, nbit k⟩ := by decide

theorem sparse_masks_fixed_9 : ∀ k < 64,
    sparseCheck ⟨nbit 9, nbit k⟩ := by decide

theorem sparse_masks_fixed_10 : ∀ k < 64,
    sparseCheck ⟨nbit 10, nbit k⟩ := by decide

theorem sparse_masks_fixed_11 : ∀ k < 64,
    sparseCheck ⟨nbit 11, nbit k⟩ := by decide

theorem sparse_masks_fixed_12 : ∀ k < 64,
    sparseCheck ⟨nbit 12, nbit k⟩ := by decide

theorem sparse_masks_fixed_13 : ∀ k < 64,
    sparseCheck ⟨nbit 13, nbit k⟩ := by decide

theorem sparse_masks_fixed_14 : ∀ k < 64,
    sparseCheck ⟨nbit 14, nbit k⟩ := by decide

theorem sparse_masks_fixed_15 : ∀ k < 64,
    sparseCheck ⟨nbit 15, nbit k⟩ := by decide

theorem sparse_masks_1 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*1+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_8
  · exact sparse_masks_fixed_9
  · exact sparse_masks_fixed_10
  · exact sparse_masks_fixed_11
  · exact sparse_masks_fixed_12
  · exact sparse_masks_fixed_13
  · exact sparse_masks_fixed_14
  · exact sparse_masks_fixed_15

end SixQubit.OpenLOrbit2
