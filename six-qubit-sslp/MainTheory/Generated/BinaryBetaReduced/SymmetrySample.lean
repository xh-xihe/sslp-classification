-- Generated-shape sample for the S₃ top-row/column transport.
import MainTheory.BinaryDetSymmetry
import MainTheory.Generated.BinaryBetaReduced.Shard000

namespace MainTheory.Generated.BinaryBetaReduced.SymmetrySample

open MainTheory.BinaryDetSymmetry
open MainTheory.Generated.BinaryBetaReduced.Shard000

/-- Swap columns three and four to restore `(0,0,0,1,2,4)` after swapping
the first two top rows. -/
def columnSwap34 : Equiv.Perm (Fin 6) :=
  Equiv.swap (3 : Fin 6) (4 : Fin 6)

/-- A symmetry transport changes the proof source but returns exactly the
same literal top block in this stabilizer example. -/
theorem stabilizerTransport (h : BottomDetBound explicitTop 9) :
    BottomDetBound explicitTop 9 := by
  have hrows := h.swapTopRows (0 : Fin 3) (1 : Fin 3)
  have hcols := hrows.permuteColumns columnSwap34
  have htop :
      permuteTopColumns
          (swapTopRows explicitTop (0 : Fin 3) (1 : Fin 3)) columnSwap34 =
        explicitTop := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [explicitTop, swapTopRows, permuteTopColumns, columnSwap34,
        Equiv.swap_apply_def]
  rw [htop] at hcols
  exact hcols

end MainTheory.Generated.BinaryBetaReduced.SymmetrySample
