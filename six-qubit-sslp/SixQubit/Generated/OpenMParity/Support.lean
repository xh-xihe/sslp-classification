import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize SixQubit.Orbit8Family

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem traceList1_support_masks : ∀ m < 64, ∀ k < 64,
    let P : SS.PauliString 6 := ⟨nbit m, nbit k⟩
    P.wt = 1 → P ∉ traceList1 → traceModel P = QuadZ.zero := by
  intro m hm
  interval_cases m <;> decide

theorem traceList1_support (P : SS.PauliString 6) (hw : P.wt = 1)
    (hn : P ∉ traceList1) : traceModel P = QuadZ.zero := by
  have he : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
    cases P; simp only [nbit_num]
  have h := traceList1_support_masks (num P.x) (num_lt _) (num P.z) (num_lt _)
  dsimp only at h
  rw [he] at h
  exact h hw hn

theorem traceList2_support_masks : ∀ m < 64, ∀ k < 64,
    let P : SS.PauliString 6 := ⟨nbit m, nbit k⟩
    P.wt = 2 → P ∉ traceList2 → traceModel P = QuadZ.zero := by
  intro m hm
  interval_cases m <;> decide

theorem traceList2_support (P : SS.PauliString 6) (hw : P.wt = 2)
    (hn : P ∉ traceList2) : traceModel P = QuadZ.zero := by
  have he : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
    cases P; simp only [nbit_num]
  have h := traceList2_support_masks (num P.x) (num_lt _) (num P.z) (num_lt _)
  dsimp only at h
  rw [he] at h
  exact h hw hn

theorem traceList3_support_masks : ∀ m < 64, ∀ k < 64,
    let P : SS.PauliString 6 := ⟨nbit m, nbit k⟩
    P.wt = 3 → P ∉ traceList3 → traceModel P = QuadZ.zero := by
  intro m hm
  interval_cases m <;> decide

theorem traceList3_support (P : SS.PauliString 6) (hw : P.wt = 3)
    (hn : P ∉ traceList3) : traceModel P = QuadZ.zero := by
  have he : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
    cases P; simp only [nbit_num]
  have h := traceList3_support_masks (num P.x) (num_lt _) (num P.z) (num_lt _)
  dsimp only at h
  rw [he] at h
  exact h hw hn

end SixQubit.OpenMParity
