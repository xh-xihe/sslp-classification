import MainTheory.Orbit3PhasePreservation

/-! # Actual bit translations preserve the chosen orbit-3 completion

An active-odd translation interchanges the two logical columns. The actual
superposition is therefore pulled back by XOR for every translation, while
norms and the full Knill--Laflamme distance remain valid.
-/

namespace MainTheory.Orbit3Translation

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.CubeCompletionTransport
open MainTheory.DirectoryEnumeratorImages MainTheory.OrderTwoScalarBridge
open SixQubit.CodeEquiv SixQubit.ParityLogicalState

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def swaps (f : SS.BitString 6) : Bool := SS.bdot orbit3Mask f

theorem fiber_translation : ∀ f s : SS.BitString 6, ∀ k : Fin 2,
    SS.bxor s f ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor (swapIdx (swaps f) k)) ↔
      s ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) := by
  decide +kernel

theorem inner_flip (f : SS.BitString 6) (u v : SS.State 6 ℂ) :
    SS.innerC (flipAct f u) (flipAct f v) = SS.innerC u v := by
  unfold SS.innerC flipAct
  exact Equiv.sum_comp (SS.bxorEquiv f) (fun s => star (u s) * v s)

def transform (W : Encoder) (f : SS.BitString 6) : Encoder where
  states k := flipAct f (W.states (swapIdx (swaps f) k))
  supported := by
    intro k s hs
    change W.states (swapIdx (swaps f) k) (SS.bxor s f) = 0
    apply W.supported
    exact fun ht => hs ((fiber_translation f s k).mp ht)
  normalized := by
    intro k
    rw [inner_flip]
    exact W.normalized _
  hasDistance := by
    have hswap := detectsRaw_swap (swaps f) ((hasDistance_iff W.states).mp W.hasDistance)
    exact (hasDistance_iff _).mpr (detectsRaw_flipAct f hswap)

theorem translated_superposition (W : Encoder) (f : SS.BitString 6) :
    superposition (transform W f).states = flipAct f (superposition W.states) := by
  funext s
  change W.states (swapIdx (swaps f) 0) (SS.bxor s f) +
    W.states (swapIdx (swaps f) 1) (SS.bxor s f) =
      W.states 0 (SS.bxor s f) + W.states 1 (SS.bxor s f)
  cases swaps f <;> simp [swapIdx, add_comm]

end
end MainTheory.Orbit3Translation
