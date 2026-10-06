import MainTheory.WithinSectorCodeAction
import MainTheory.FiveQubitRationalization

set_option autoImplicit false

namespace MainTheory.CurrentMainDisplays

open MainTheory.PhaseSectorFull MainTheory.FiniteLift MainTheory.RealGate

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

theorem all_real_colors_preserved (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (u : Sum (Fin n) (Color D) → ℝ)
    (hu : ((coloredMatrix D).map (algebraMap ℚ ℝ)).mulVec u=
      fun r => (coloredRhsQ D r : ℝ)) (g : Color D) :
    u (.inr g)=realUnknown D (.inr g) := by
  have hk : ((coloredMatrix D).map (algebraMap ℚ ℝ)).mulVec (u-realUnknown D)=0 := by
    rw [Matrix.mulVec_sub,hu,coloredMatrix_realSolution]
    simp only [MainTheory.WithinSectorRationalization.rational_algebra_map,sub_self]
  have h := coloredMatrix_kernel_color_zero D hZ (u-realUnknown D) hk g
  exact sub_eq_zero.mp h

theorem normalized_real_phases_preserved (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (hbase : D.phase (baseSector D)=0)
    (v : Fin n → ℝ) (s : Color D → ℝ)
    (hu : ((coloredMatrix D).map (algebraMap ℚ ℝ)).mulVec
      (Sum.elim v (fun g => -s g))=fun r => (coloredRhsQ D r : ℝ)) (g : Color D) :
    s g=D.phase g.val := by
  have h := all_real_colors_preserved D hZ _ hu g
  simpa [realUnknown,hbase] using h

theorem first_sector_equation (D : SectorDecomposition n t theta)
    (hbase : D.phase (baseSector D)=0) (x : SupportIndex D (baseSector D)) :
    angle theta x.val=(phaseInteger D (baseSector D) x : ℝ) := by
  simpa [hbase] using phaseInteger_spec D (baseSector D) x

theorem within_rows_ternary (D : SectorDecomposition n t theta)
    (r : Sigma (SupportIndex D)) (j : Fin n) :
    MainTheory.WithinSectorRationalization.rows D r j ∈ ({-1,0,1} : Set ℚ) := by
  unfold MainTheory.WithinSectorRationalization.rows bitQ
  split_ifs <;> norm_num

theorem difference_need_not_be_binary :
    bitQ (![false] : SS.BitString 1) 0-bitQ (![true] : SS.BitString 1) 0=-1 ∧
    bitQ (![false] : SS.BitString 1) 0-bitQ (![true] : SS.BitString 1) 0 ∉ ({0,1} : Set ℚ) := by
  norm_num [bitQ]

theorem example_theta_zero : MainTheory.FiveQubitRationalization.theta 0=
    (1/3 : ℝ) • (![0,1,1,1,0] : Fin 5 → ℝ) := by
  ext j
  fin_cases j <;> norm_num [MainTheory.FiveQubitRationalization.theta]

theorem example_theta_sixth : MainTheory.FiveQubitRationalization.theta (1/6)=
    (![1/6,1/6,1/6,1/2,-1/6] : Fin 5 → ℝ) := by
  ext j
  fin_cases j <;> norm_num [MainTheory.FiveQubitRationalization.theta]

theorem strict_divisibility_example : 3 ∣ (6 : ℕ) ∧ 3<6 := by decide

end

end MainTheory.CurrentMainDisplays
