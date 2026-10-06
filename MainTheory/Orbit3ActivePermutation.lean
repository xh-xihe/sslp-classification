import MainTheory.Orbit3PhasePreservation

/-! # Actual active permutations preserve the chosen orbit-3 completion -/

namespace MainTheory.Orbit3ActivePermutation

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.CubeCompletionTransport
open MainTheory.DirectoryEnumeratorImages MainTheory.OrderTwoScalarBridge
open SixQubit.CodeEquiv SixQubit.ParityLogicalState

noncomputable section

theorem fiber_parity : ∀ k : Fin 2, ∀ s : SS.BitString 6,
    s ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) ↔ SS.bdot orbit3Mask s = (k == 1) := by
  decide +kernel

theorem parity_permutation (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ j, orbit3Mask (σ j) = orbit3Mask j) (s : SS.BitString 6) :
    SS.bdot orbit3Mask (permStr σ s) = SS.bdot orbit3Mask s := by
  have hm : permStr σ orbit3Mask = orbit3Mask := funext hσ
  have h := bdot_permStr σ orbit3Mask s
  rw [hm] at h
  exact h

theorem fiber_permutation (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ j, orbit3Mask (σ j) = orbit3Mask j) (k : Fin 2) (s : SS.BitString 6) :
    permStr σ s ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) ↔
      s ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) := by
  rw [fiber_parity, fiber_parity, parity_permutation σ hσ]

def transform (W : Encoder) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ j, orbit3Mask (σ j) = orbit3Mask j) : Encoder where
  states k := permAct σ (W.states k)
  supported := by
    intro k s hs
    change W.states k (permStr σ s) = 0
    apply W.supported
    exact fun ht => hs ((fiber_permutation σ hσ k s).mp ht)
  normalized := by
    intro k
    calc
      _ = SS.innerC (W.states k) (W.states k) := by
        unfold SS.innerC permAct
        exact Equiv.sum_comp (permStrEquiv σ) (fun s => star (W.states k s) * W.states k s)
      _ = 1 := W.normalized k
  hasDistance := (hasDistance_iff _).mpr
    (detectsRaw_permAct σ ((hasDistance_iff W.states).mp W.hasDistance))

theorem permuted_superposition (W : Encoder) (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ j, orbit3Mask (σ j) = orbit3Mask j) :
    superposition (transform W σ hσ).states = permAct σ (superposition W.states) := rfl

end
end MainTheory.Orbit3ActivePermutation
