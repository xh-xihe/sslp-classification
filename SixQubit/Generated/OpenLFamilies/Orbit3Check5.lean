import SixQubit.Generated.OpenLFamilies.Orbit3Data

namespace SixQubit.OpenLOrbit3

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_masks_fixed_40 : ∀ k < 64,
    (⟨nbit 40, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 40, nbit k⟩ := by decide

theorem kl_masks_fixed_41 : ∀ k < 64,
    (⟨nbit 41, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 41, nbit k⟩ := by decide

theorem kl_masks_fixed_42 : ∀ k < 64,
    (⟨nbit 42, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 42, nbit k⟩ := by decide

theorem kl_masks_fixed_43 : ∀ k < 64,
    (⟨nbit 43, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 43, nbit k⟩ := by decide

theorem kl_masks_fixed_44 : ∀ k < 64,
    (⟨nbit 44, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 44, nbit k⟩ := by decide

theorem kl_masks_fixed_45 : ∀ k < 64,
    (⟨nbit 45, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 45, nbit k⟩ := by decide

theorem kl_masks_fixed_46 : ∀ k < 64,
    (⟨nbit 46, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 46, nbit k⟩ := by decide

theorem kl_masks_fixed_47 : ∀ k < 64,
    (⟨nbit 47, nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit 47, nbit k⟩ := by decide

theorem kl_masks_5 : ∀ m < 8, ∀ k < 64,
    (⟨nbit (8*5+m), nbit k⟩ : SS.PauliString 6).wt ≤ 2 → klCheck ⟨nbit (8*5+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact kl_masks_fixed_40
  · exact kl_masks_fixed_41
  · exact kl_masks_fixed_42
  · exact kl_masks_fixed_43
  · exact kl_masks_fixed_44
  · exact kl_masks_fixed_45
  · exact kl_masks_fixed_46
  · exact kl_masks_fixed_47

theorem sparse_masks_fixed_40 : ∀ k < 64,
    sparseCheck ⟨nbit 40, nbit k⟩ := by decide

theorem sparse_masks_fixed_41 : ∀ k < 64,
    sparseCheck ⟨nbit 41, nbit k⟩ := by decide

theorem sparse_masks_fixed_42 : ∀ k < 64,
    sparseCheck ⟨nbit 42, nbit k⟩ := by decide

theorem sparse_masks_fixed_43 : ∀ k < 64,
    sparseCheck ⟨nbit 43, nbit k⟩ := by decide

theorem sparse_masks_fixed_44 : ∀ k < 64,
    sparseCheck ⟨nbit 44, nbit k⟩ := by decide

theorem sparse_masks_fixed_45 : ∀ k < 64,
    sparseCheck ⟨nbit 45, nbit k⟩ := by decide

theorem sparse_masks_fixed_46 : ∀ k < 64,
    sparseCheck ⟨nbit 46, nbit k⟩ := by decide

theorem sparse_masks_fixed_47 : ∀ k < 64,
    sparseCheck ⟨nbit 47, nbit k⟩ := by decide

theorem sparse_masks_5 : ∀ m < 8, ∀ k < 64,
    sparseCheck ⟨nbit (8*5+m), nbit k⟩ := by
  intro m hm
  interval_cases m
  · exact sparse_masks_fixed_40
  · exact sparse_masks_fixed_41
  · exact sparse_masks_fixed_42
  · exact sparse_masks_fixed_43
  · exact sparse_masks_fixed_44
  · exact sparse_masks_fixed_45
  · exact sparse_masks_fixed_46
  · exact sparse_masks_fixed_47

end SixQubit.OpenLOrbit3
