import MainTheory.DirectoryEnumeratorImages
import SixQubit.ParityPauliScalars

/-! # The chosen orbit-2/3 gates imply the actual scalar label relations

No LP realization is assumed here. The parity hypotheses are derived from
the actual encoder support, and shadow zeros from the involution's odd active
length and the physical Pauli weight.
-/

namespace MainTheory.OrderTwoScalarBridge

open MainTheory.CubeCompletionTransport MainTheory.DirectoryEnumeratorImages
open SixQubit.ParityPauliScalars SS.MacWilliams SS.Shadow SS.ShadowTwisted

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem parity_of_completion (a : Fin 6 → ZMod 2) (mask : SS.BitString 6)
    (hpar : ∀ k : Fin 2, ∀ s : SS.BitString 6,
      s ∈ angleFibers a (finColor k) → SS.bdot mask s = (k == 1))
    (W : Completion (angleFibers a)) : ParityPair mask W.states := by
  intro k s hs
  apply W.supported k s
  intro hm
  have h := chi_bdot mask s
  rw [hpar k s hm] at h
  have he : (if k == 1 then (-1 : ℝ) else 1) = logicalSign k := by
    fin_cases k <;> norm_num [logicalSign]
  exact hs (h.trans he)

def orbit2Mask : SS.BitString 6 := SixQubit.Realize.nbit 60
def orbit3Mask : SS.BitString 6 := SixQubit.Realize.nbit 62

theorem orbit2_parity (W : Completion (angleFibers SixQubit.OpenLOrbit2.angle)) :
    ParityPair orbit2Mask W.states := by
  apply parity_of_completion
  decide +kernel

theorem orbit3_parity (W : Completion (angleFibers SixQubit.OpenLOrbit3.angle)) :
    ParityPair orbit3Mask W.states := by
  apply parity_of_completion
  decide +kernel

theorem orbit2_diagonal_relation
    (W : Completion (angleFibers SixQubit.OpenLOrbit2.angle))
    (P : SS.PauliString 6) (hc : SS.bdot orbit2Mask P.x = false) :
    2 * frob W.states P = Complex.normSq (trProj W.states P) +
      Complex.normSq (trProj W.states ⟨P.x, SS.bxor P.z orbit2Mask⟩) := by
  apply diagonal_relation (orbit2_parity W)
  rw [chi_bdot, hc]
  rfl

theorem orbit3_diagonal_relation
    (W : Completion (angleFibers SixQubit.OpenLOrbit3.angle))
    (P : SS.PauliString 6) (hc : SS.bdot orbit3Mask P.x = false) :
    2 * frob W.states P = Complex.normSq (trProj W.states P) +
      Complex.normSq (trProj W.states ⟨P.x, SS.bxor P.z orbit3Mask⟩) := by
  apply diagonal_relation (orbit3_parity W)
  rw [chi_bdot, hc]
  rfl

theorem orbit3_complement_parity : ∀ x : SS.BitString 6,
    SS.bdot orbit3Mask (SS.complement x) = !SS.bdot orbit3Mask x := by decide +kernel

theorem six_spin_parity : ∀ E : SS.PauliString 6,
    SS.bdot (SS.bxor (SS.ones 6) E.z) (SS.complement E.x) = (E.wt % 2 == 1) := by
  decide +kernel

theorem orbit3_shadow_zero
    (W : Completion (angleFibers SixQubit.OpenLOrbit3.angle))
    (E : SS.PauliString 6) (htrans : SS.bdot orbit3Mask E.x = true)
    (hodd : E.wt % 2 = 1) :
    (∑ P : SS.PauliString 6,
      (-1 : ℝ) ^ P.wt * pairSign E P * Complex.normSq (trProj W.states P)) = 0 := by
  apply shadow_zero (orbit3_parity W)
  · rw [chi_bdot, orbit3_complement_parity, htrans]
    rfl
  · unfold psignT
    rw [chi_comm, chi_bdot, six_spin_parity, hodd]
    rfl

end
end MainTheory.OrderTwoScalarBridge
