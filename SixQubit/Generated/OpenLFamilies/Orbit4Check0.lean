import SixQubit.Generated.OpenLFamilies.Orbit4Data

namespace SixQubit.OpenLOrbit4

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_0 : ∀ k < 64,
    (⟨nbit 0, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 0, nbit k⟩ := by decide

theorem kl_masks_fixed_1 : ∀ k < 64,
    (⟨nbit 1, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 1, nbit k⟩ := by decide

theorem kl_masks_fixed_2 : ∀ k < 64,
    (⟨nbit 2, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 2, nbit k⟩ := by decide

theorem kl_masks_fixed_3 : ∀ k < 64,
    (⟨nbit 3, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 3, nbit k⟩ := by decide

theorem kl_masks_fixed_4 : ∀ k < 64,
    (⟨nbit 4, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 4, nbit k⟩ := by decide

theorem kl_masks_fixed_5 : ∀ k < 64,
    (⟨nbit 5, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 5, nbit k⟩ := by decide

theorem kl_masks_fixed_6 : ∀ k < 64,
    (⟨nbit 6, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 6, nbit k⟩ := by decide

theorem kl_masks_fixed_7 : ∀ k < 64,
    (⟨nbit 7, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 7, nbit k⟩ := by decide

theorem kl_masks_0 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*0+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*0+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_0
  · exact kl_masks_fixed_1
  · exact kl_masks_fixed_2
  · exact kl_masks_fixed_3
  · exact kl_masks_fixed_4
  · exact kl_masks_fixed_5
  · exact kl_masks_fixed_6
  · exact kl_masks_fixed_7

theorem sparse_masks_fixed_0 : ∀ k < 64,
    sparseCheck ⟨nbit 0, nbit k⟩ := by decide

theorem sparse_masks_fixed_1 : ∀ k < 64,
    sparseCheck ⟨nbit 1, nbit k⟩ := by decide

theorem sparse_masks_fixed_2 : ∀ k < 64,
    sparseCheck ⟨nbit 2, nbit k⟩ := by decide

theorem sparse_masks_fixed_3 : ∀ k < 64,
    sparseCheck ⟨nbit 3, nbit k⟩ := by decide

theorem sparse_masks_fixed_4 : ∀ k < 64,
    sparseCheck ⟨nbit 4, nbit k⟩ := by decide

theorem sparse_masks_fixed_5 : ∀ k < 64,
    sparseCheck ⟨nbit 5, nbit k⟩ := by decide

theorem sparse_masks_fixed_6 : ∀ k < 64,
    sparseCheck ⟨nbit 6, nbit k⟩ := by decide

theorem sparse_masks_fixed_7 : ∀ k < 64,
    sparseCheck ⟨nbit 7, nbit k⟩ := by decide

theorem sparse_masks_0 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*0+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_0
  · exact sparse_masks_fixed_1
  · exact sparse_masks_fixed_2
  · exact sparse_masks_fixed_3
  · exact sparse_masks_fixed_4
  · exact sparse_masks_fixed_5
  · exact sparse_masks_fixed_6
  · exact sparse_masks_fixed_7

end SixQubit.OpenLOrbit4
