import SixQubit.Generated.OpenLFamilies.Orbit1Data

namespace SixQubit.OpenLOrbit1

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_16 : ∀ k < 64,
    (⟨nbit 16, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 16, nbit k⟩ := by decide

theorem kl_masks_fixed_17 : ∀ k < 64,
    (⟨nbit 17, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 17, nbit k⟩ := by decide

theorem kl_masks_fixed_18 : ∀ k < 64,
    (⟨nbit 18, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 18, nbit k⟩ := by decide

theorem kl_masks_fixed_19 : ∀ k < 64,
    (⟨nbit 19, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 19, nbit k⟩ := by decide

theorem kl_masks_fixed_20 : ∀ k < 64,
    (⟨nbit 20, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 20, nbit k⟩ := by decide

theorem kl_masks_fixed_21 : ∀ k < 64,
    (⟨nbit 21, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 21, nbit k⟩ := by decide

theorem kl_masks_fixed_22 : ∀ k < 64,
    (⟨nbit 22, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 22, nbit k⟩ := by decide

theorem kl_masks_fixed_23 : ∀ k < 64,
    (⟨nbit 23, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 23, nbit k⟩ := by decide

theorem kl_masks_2 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*2+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*2+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_16
  · exact kl_masks_fixed_17
  · exact kl_masks_fixed_18
  · exact kl_masks_fixed_19
  · exact kl_masks_fixed_20
  · exact kl_masks_fixed_21
  · exact kl_masks_fixed_22
  · exact kl_masks_fixed_23

theorem sparse_masks_fixed_16 : ∀ k < 64,
    sparseCheck ⟨nbit 16, nbit k⟩ := by decide

theorem sparse_masks_fixed_17 : ∀ k < 64,
    sparseCheck ⟨nbit 17, nbit k⟩ := by decide

theorem sparse_masks_fixed_18 : ∀ k < 64,
    sparseCheck ⟨nbit 18, nbit k⟩ := by decide

theorem sparse_masks_fixed_19 : ∀ k < 64,
    sparseCheck ⟨nbit 19, nbit k⟩ := by decide

theorem sparse_masks_fixed_20 : ∀ k < 64,
    sparseCheck ⟨nbit 20, nbit k⟩ := by decide

theorem sparse_masks_fixed_21 : ∀ k < 64,
    sparseCheck ⟨nbit 21, nbit k⟩ := by decide

theorem sparse_masks_fixed_22 : ∀ k < 64,
    sparseCheck ⟨nbit 22, nbit k⟩ := by decide

theorem sparse_masks_fixed_23 : ∀ k < 64,
    sparseCheck ⟨nbit 23, nbit k⟩ := by decide

theorem sparse_masks_2 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*2+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_16
  · exact sparse_masks_fixed_17
  · exact sparse_masks_fixed_18
  · exact sparse_masks_fixed_19
  · exact sparse_masks_fixed_20
  · exact sparse_masks_fixed_21
  · exact sparse_masks_fixed_22
  · exact sparse_masks_fixed_23

end SixQubit.OpenLOrbit1
