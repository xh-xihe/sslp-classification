import Orbit2.Encoder
import Orbit2.PhysicalB

namespace Orbit2
open scoped BigOperators
open SS.MacWilliams
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Exact distance three follows from the genuine B transform; no separate
Singleton-bound assumption is needed for the enumerator line. -/
theorem Encoder.not_distance_four_of_line (V : Encoder) (α : ℝ) (hα : 0 ≤ α)
    (hline : (fun w : Fin 7 => V.A w.val) = enumeratorLine α) :
    ¬ SS.HasDistance V.psi 4 := by
  have he : ∀ w : Fin 7, Aco V.psi w.val = 4 * enumeratorLine α w := by
    intro w
    have hw := congrFun hline w
    unfold Encoder.A at hw
    linarith
  have hB := (bco_transform_six V.psi).2.2.2.1
  have he' (w : ℕ) (hw : w < 7) : Aco V.psi w =
      4 * enumeratorLine α ⟨w,hw⟩ := he ⟨w,hw⟩
  rw [he' 0 (by omega),he' 1 (by omega),he' 2 (by omega),he' 3 (by omega),
    he' 4 (by omega),he' 5 (by omega),he' 6 (by omega)] at hB
  norm_num [enumeratorLine] at hB
  have hz : Aco V.psi 3 = 0 := by simpa [enumeratorLine] using he' 3 (by omega)
  intro hd
  have hBA : Bco V.psi 3 = Aco V.psi 3 := by
    unfold Bco Aco
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hwt := (Finset.mem_filter.mp hp).2
    exact frob_of_KL V.psi p (hd p (by omega))
  linarith

end Orbit2
