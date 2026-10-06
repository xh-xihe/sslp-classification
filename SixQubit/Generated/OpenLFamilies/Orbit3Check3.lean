import SixQubit.Generated.OpenLFamilies.Orbit3Data

namespace SixQubit.OpenLOrbit3

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_24 : ∀ k < 64,
    (⟨nbit 24, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 24, nbit k⟩ := by decide

theorem kl_masks_fixed_25 : ∀ k < 64,
    (⟨nbit 25, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 25, nbit k⟩ := by decide

theorem kl_masks_fixed_26 : ∀ k < 64,
    (⟨nbit 26, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 26, nbit k⟩ := by decide

theorem kl_masks_fixed_27 : ∀ k < 64,
    (⟨nbit 27, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 27, nbit k⟩ := by decide

theorem kl_masks_fixed_28 : ∀ k < 64,
    (⟨nbit 28, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 28, nbit k⟩ := by decide

theorem kl_masks_fixed_29 : ∀ k < 64,
    (⟨nbit 29, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 29, nbit k⟩ := by decide

theorem kl_masks_fixed_30 : ∀ k < 64,
    (⟨nbit 30, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 30, nbit k⟩ := by decide

theorem kl_masks_fixed_31 : ∀ k < 64,
    (⟨nbit 31, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 31, nbit k⟩ := by decide

theorem kl_masks_3 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*3+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*3+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_24
  · exact kl_masks_fixed_25
  · exact kl_masks_fixed_26
  · exact kl_masks_fixed_27
  · exact kl_masks_fixed_28
  · exact kl_masks_fixed_29
  · exact kl_masks_fixed_30
  · exact kl_masks_fixed_31

theorem sparse_masks_fixed_24 : ∀ k < 64,
    sparseCheck ⟨nbit 24, nbit k⟩ := by decide

theorem sparse_masks_fixed_25 : ∀ k < 64,
    sparseCheck ⟨nbit 25, nbit k⟩ := by decide

theorem sparse_masks_fixed_26 : ∀ k < 64,
    sparseCheck ⟨nbit 26, nbit k⟩ := by decide

theorem sparse_masks_fixed_27 : ∀ k < 64,
    sparseCheck ⟨nbit 27, nbit k⟩ := by decide

theorem sparse_masks_fixed_28 : ∀ k < 64,
    sparseCheck ⟨nbit 28, nbit k⟩ := by decide

theorem sparse_masks_fixed_29 : ∀ k < 64,
    sparseCheck ⟨nbit 29, nbit k⟩ := by decide

theorem sparse_masks_fixed_30 : ∀ k < 64,
    sparseCheck ⟨nbit 30, nbit k⟩ := by decide

theorem sparse_masks_fixed_31 : ∀ k < 64,
    sparseCheck ⟨nbit 31, nbit k⟩ := by decide

theorem sparse_masks_3 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*3+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_24
  · exact sparse_masks_fixed_25
  · exact sparse_masks_fixed_26
  · exact sparse_masks_fixed_27
  · exact sparse_masks_fixed_28
  · exact sparse_masks_fixed_29
  · exact sparse_masks_fixed_30
  · exact sparse_masks_fixed_31

end SixQubit.OpenLOrbit3
