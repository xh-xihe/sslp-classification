import SixQubit.Generated.OpenLFamilies.Orbit2Check0
import SixQubit.Generated.OpenLFamilies.Orbit2Check1
import SixQubit.Generated.OpenLFamilies.Orbit2Check2
import SixQubit.Generated.OpenLFamilies.Orbit2Check3
import SixQubit.Generated.OpenLFamilies.Orbit2Check4
import SixQubit.Generated.OpenLFamilies.Orbit2Check5
import SixQubit.Generated.OpenLFamilies.Orbit2Check6
import SixQubit.Generated.OpenLFamilies.Orbit2Check7

namespace SixQubit.OpenLOrbit2

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem kl_all (P : SS.PauliString 6) (hP : P.wt ≤ 2) : klCheck P := by
  have hb := num_lt P.x
  have hcases : num P.x / 8 = 0 ∨ num P.x / 8 = 1 ∨ num P.x / 8 = 2 ∨ num P.x / 8 = 3 ∨ num P.x / 8 = 4 ∨ num P.x / 8 = 5 ∨ num P.x / 8 = 6 ∨ num P.x / 8 = 7 := by omega
  rcases hcases with h | h | h | h | h | h | h | h
  · have he : 8*0 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*0+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_0 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP
  · have he : 8*1 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*1+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_1 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP
  · have he : 8*2 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*2+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_2 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP
  · have he : 8*3 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*3+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_3 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP
  · have he : 8*4 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*4+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_4 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP
  · have he : 8*5 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*5+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_5 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP
  · have he : 8*6 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*6+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_6 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP
  · have he : 8*7 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*7+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := kl_masks_7 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP

theorem sparse_all (P : SS.PauliString 6) (hP : P.wt ≤ 2)
    (hi : P ≠ identityPauli) (h1 : P ≠ onePauli) (h2 : P ≠ twoPauli) :
    CircleZero (qtrace c0 c1 L0 L1 P) := by
  have hb := num_lt P.x
  have hcases : num P.x / 8 = 0 ∨ num P.x / 8 = 1 ∨ num P.x / 8 = 2 ∨ num P.x / 8 = 3 ∨ num P.x / 8 = 4 ∨ num P.x / 8 = 5 ∨ num P.x / 8 = 6 ∨ num P.x / 8 = 7 := by omega
  rcases hcases with h | h | h | h | h | h | h | h
  · have he : 8*0 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*0+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_0 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))
  · have he : 8*1 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*1+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_1 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))
  · have he : 8*2 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*2+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_2 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))
  · have he : 8*3 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*3+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_3 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))
  · have he : 8*4 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*4+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_4 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))
  · have he : 8*5 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*5+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_5 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))
  · have he : 8*6 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*6+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_6 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))
  · have he : 8*7 + num P.x % 8 = num P.x := by omega
    have hp : (⟨nbit (8*7+num P.x%8), nbit (num P.z)⟩ : SS.PauliString 6) = P := by
      rw [he, nbit_num, nbit_num]
    have hg := sparse_masks_7 (num P.x%8) (Nat.mod_lt _ (by decide))
      (num P.z) (num_lt _)
    rw [hp] at hg
    exact hg hP (fun h => hi (sameMasks_eq h)) (fun h => h1 (sameMasks_eq h)) (fun h => h2 (sameMasks_eq h))

def certificate : Certificate where
  angle := angle
  c0 := c0
  c1 := c1
  L0 := L0
  L1 := L1
  denominator := 8
  denominator_pos := by decide
  L0_nodup := by decide
  L1_nodup := by decide
  vanishes0 := by decide
  vanishes1 := by decide
  fiber0 := by decide
  fiber1 := by decide
  kl := kl_all
  norm0 := by decide
  norm1 := by decide
  onePauli := onePauli
  twoPauli := twoPauli
  oneWeight := by decide
  twoWeight := by decide
  oneNumY := by decide
  twoNumY := by decide
  trace1 := by decide
  trace2 := by decide
  sparse := sparse_all

end SixQubit.OpenLOrbit2
