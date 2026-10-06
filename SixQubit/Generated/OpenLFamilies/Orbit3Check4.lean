import SixQubit.Generated.OpenLFamilies.Orbit3Data

namespace SixQubit.OpenLOrbit3

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_32 : ∀ k < 64,
    (⟨nbit 32, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 32, nbit k⟩ := by decide

theorem kl_masks_fixed_33 : ∀ k < 64,
    (⟨nbit 33, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 33, nbit k⟩ := by decide

theorem kl_masks_fixed_34 : ∀ k < 64,
    (⟨nbit 34, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 34, nbit k⟩ := by decide

theorem kl_masks_fixed_35 : ∀ k < 64,
    (⟨nbit 35, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 35, nbit k⟩ := by decide

theorem kl_masks_fixed_36 : ∀ k < 64,
    (⟨nbit 36, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 36, nbit k⟩ := by decide

theorem kl_masks_fixed_37 : ∀ k < 64,
    (⟨nbit 37, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 37, nbit k⟩ := by decide

theorem kl_masks_fixed_38 : ∀ k < 64,
    (⟨nbit 38, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 38, nbit k⟩ := by decide

theorem kl_masks_fixed_39 : ∀ k < 64,
    (⟨nbit 39, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 39, nbit k⟩ := by decide

theorem kl_masks_4 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*4+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*4+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_32
  · exact kl_masks_fixed_33
  · exact kl_masks_fixed_34
  · exact kl_masks_fixed_35
  · exact kl_masks_fixed_36
  · exact kl_masks_fixed_37
  · exact kl_masks_fixed_38
  · exact kl_masks_fixed_39

theorem sparse_masks_fixed_32 : ∀ k < 64,
    sparseCheck ⟨nbit 32, nbit k⟩ := by decide

theorem sparse_masks_fixed_33 : ∀ k < 64,
    sparseCheck ⟨nbit 33, nbit k⟩ := by decide

theorem sparse_masks_fixed_34 : ∀ k < 64,
    sparseCheck ⟨nbit 34, nbit k⟩ := by decide

theorem sparse_masks_fixed_35 : ∀ k < 64,
    sparseCheck ⟨nbit 35, nbit k⟩ := by decide

theorem sparse_masks_fixed_36 : ∀ k < 64,
    sparseCheck ⟨nbit 36, nbit k⟩ := by decide

theorem sparse_masks_fixed_37 : ∀ k < 64,
    sparseCheck ⟨nbit 37, nbit k⟩ := by decide

theorem sparse_masks_fixed_38 : ∀ k < 64,
    sparseCheck ⟨nbit 38, nbit k⟩ := by decide

theorem sparse_masks_fixed_39 : ∀ k < 64,
    sparseCheck ⟨nbit 39, nbit k⟩ := by decide

theorem sparse_masks_4 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*4+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_32
  · exact sparse_masks_fixed_33
  · exact sparse_masks_fixed_34
  · exact sparse_masks_fixed_35
  · exact sparse_masks_fixed_36
  · exact sparse_masks_fixed_37
  · exact sparse_masks_fixed_38
  · exact sparse_masks_fixed_39

end SixQubit.OpenLOrbit3
