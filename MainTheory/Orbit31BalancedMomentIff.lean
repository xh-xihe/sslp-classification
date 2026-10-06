import MainTheory.Orbit31SupportBase
import SixQubit.Orbit31MomentNormal

/-! The seven balanced real moments are exactly the complete diagonal
moment system after complementary probability equality. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit31BalancedMomentIff
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.Orbit31SupportBase
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

def nativeQ (p : Fin 16 → ℝ) : Fin 16 → ℝ := ![p ⟨0,by decide⟩,p ⟨1,by decide⟩,p ⟨2,by decide⟩,p ⟨3,by decide⟩,p ⟨7,by decide⟩,p ⟨6,by decide⟩,p ⟨5,by decide⟩,p ⟨4,by decide⟩,p ⟨11,by decide⟩,p ⟨10,by decide⟩,p ⟨9,by decide⟩,p ⟨8,by decide⟩,p ⟨15,by decide⟩,p ⟨14,by decide⟩,p ⟨13,by decide⟩,p ⟨12,by decide⟩]
def nativeR (p : Fin 16 → ℝ) : Fin 16 → ℝ := ![p ⟨12,by decide⟩,p ⟨13,by decide⟩,p ⟨14,by decide⟩,p ⟨15,by decide⟩,p ⟨8,by decide⟩,p ⟨9,by decide⟩,p ⟨10,by decide⟩,p ⟨11,by decide⟩,p ⟨4,by decide⟩,p ⟨5,by decide⟩,p ⟨6,by decide⟩,p ⟨7,by decide⟩,p ⟨3,by decide⟩,p ⟨2,by decide⟩,p ⟨1,by decide⟩,p ⟨0,by decide⟩]

theorem q_table (p : Fin 16 → ℝ) (j : Fin 16) : nativeQ p (nativeIndex j) = p j := by
  fin_cases j <;> rfl
theorem r_complement (p : Fin 16 → ℝ) : nativeR p =
    ![(nativeQ p) 15,(nativeQ p) 14,(nativeQ p) 13,(nativeQ p) 12,
      (nativeQ p) 11,(nativeQ p) 10,(nativeQ p) 9,(nativeQ p) 8,
      (nativeQ p) 7,(nativeQ p) 6,(nativeQ p) 5,(nativeQ p) 4,
      (nativeQ p) 3,(nativeQ p) 2,(nativeQ p) 1,(nativeQ p) 0] := by
  funext j
  fin_cases j <;> rfl

theorem full_moments_of_feasible (p : Fin 16 → ℝ) (hp : Feasible M b p) :
    VectorMomentSystem (nativeQ p) (nativeR p) := by
  have h0 := congrFun hp.equations ⟨0,by decide⟩
  have h1 := congrFun hp.equations ⟨1,by decide⟩
  have h2 := congrFun hp.equations ⟨2,by decide⟩
  have h3 := congrFun hp.equations ⟨3,by decide⟩
  have h4 := congrFun hp.equations ⟨4,by decide⟩
  have h5 := congrFun hp.equations ⟨5,by decide⟩
  have h6 := congrFun hp.equations ⟨6,by decide⟩
  norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5 h6
  change MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨7,by decide⟩) (p ⟨6,by decide⟩) (p ⟨5,by decide⟩) (p ⟨4,by decide⟩) (p ⟨11,by decide⟩) (p ⟨10,by decide⟩) (p ⟨9,by decide⟩) (p ⟨8,by decide⟩) (p ⟨15,by decide⟩) (p ⟨14,by decide⟩) (p ⟨13,by decide⟩) (p ⟨12,by decide⟩) (p ⟨12,by decide⟩) (p ⟨13,by decide⟩) (p ⟨14,by decide⟩) (p ⟨15,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (p ⟨10,by decide⟩) (p ⟨11,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨3,by decide⟩) (p ⟨2,by decide⟩) (p ⟨1,by decide⟩) (p ⟨0,by decide⟩)
  constructor
  · norm_num
    linear_combination 1 * h0
  · norm_num
    linear_combination 1 * h0
  · norm_num
    linear_combination -1 * h0 + 2 * h1
  · norm_num
    linear_combination -1 * h0 + 2 * h2
  · norm_num
    linear_combination -1 * h0 + 2 * h3
  · norm_num
    linear_combination -1 * h0 + 2 * h4
  · norm_num
    linear_combination -1 * h0 + 2 * h5
  · norm_num
    linear_combination -1 * h0 + 2 * h6
  · norm_num
    linear_combination -1 * h0 + 1 * h1 + 1 * h2
  · norm_num
    linear_combination -1 * h0 + 1 * h1 + 1 * h3
  · norm_num
    linear_combination -1 * h0 + 1 * h1 + 1 * h4
  · norm_num
    linear_combination -1 * h0 + 1 * h1 + 1 * h5
  · norm_num
    linear_combination -1 * h0 + 1 * h1 + 1 * h6
  · norm_num
    linear_combination -1 * h0 + 1 * h2 + 1 * h3
  · norm_num
    linear_combination -1 * h0 + 1 * h2 + 1 * h4
  · norm_num
    linear_combination -1 * h0 + 1 * h2 + 1 * h5
  · norm_num
    linear_combination -1 * h0 + 1 * h2 + 1 * h6
  · norm_num
    linear_combination -1 * h0 + 1 * h3 + 1 * h4
  · norm_num
    linear_combination -1 * h0 + 1 * h3 + 1 * h5
  · norm_num
    linear_combination -1 * h0 + 1 * h3 + 1 * h6
  · norm_num
    linear_combination -1 * h0 + 1 * h4 + 1 * h5
  · norm_num
    linear_combination -1 * h0 + 1 * h4 + 1 * h6
  · norm_num
    linear_combination -1 * h0 + 1 * h5 + 1 * h6
  · exact hp.nonneg ⟨0,by decide⟩
  · exact hp.nonneg ⟨1,by decide⟩
  · exact hp.nonneg ⟨2,by decide⟩
  · exact hp.nonneg ⟨3,by decide⟩
  · exact hp.nonneg ⟨7,by decide⟩
  · exact hp.nonneg ⟨6,by decide⟩
  · exact hp.nonneg ⟨5,by decide⟩
  · exact hp.nonneg ⟨4,by decide⟩
  · exact hp.nonneg ⟨11,by decide⟩
  · exact hp.nonneg ⟨10,by decide⟩
  · exact hp.nonneg ⟨9,by decide⟩
  · exact hp.nonneg ⟨8,by decide⟩
  · exact hp.nonneg ⟨15,by decide⟩
  · exact hp.nonneg ⟨14,by decide⟩
  · exact hp.nonneg ⟨13,by decide⟩
  · exact hp.nonneg ⟨12,by decide⟩
  · exact hp.nonneg ⟨12,by decide⟩
  · exact hp.nonneg ⟨13,by decide⟩
  · exact hp.nonneg ⟨14,by decide⟩
  · exact hp.nonneg ⟨15,by decide⟩
  · exact hp.nonneg ⟨8,by decide⟩
  · exact hp.nonneg ⟨9,by decide⟩
  · exact hp.nonneg ⟨10,by decide⟩
  · exact hp.nonneg ⟨11,by decide⟩
  · exact hp.nonneg ⟨4,by decide⟩
  · exact hp.nonneg ⟨5,by decide⟩
  · exact hp.nonneg ⟨6,by decide⟩
  · exact hp.nonneg ⟨7,by decide⟩
  · exact hp.nonneg ⟨3,by decide⟩
  · exact hp.nonneg ⟨2,by decide⟩
  · exact hp.nonneg ⟨1,by decide⟩
  · exact hp.nonneg ⟨0,by decide⟩

theorem feasible_of_full_moments (p : Fin 16 → ℝ)
    (hm : VectorMomentSystem (nativeQ p) (nativeR p)) : Feasible M b p := by
  change MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨7,by decide⟩) (p ⟨6,by decide⟩) (p ⟨5,by decide⟩) (p ⟨4,by decide⟩) (p ⟨11,by decide⟩) (p ⟨10,by decide⟩) (p ⟨9,by decide⟩) (p ⟨8,by decide⟩) (p ⟨15,by decide⟩) (p ⟨14,by decide⟩) (p ⟨13,by decide⟩) (p ⟨12,by decide⟩) (p ⟨12,by decide⟩) (p ⟨13,by decide⟩) (p ⟨14,by decide⟩) (p ⟨15,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (p ⟨10,by decide⟩) (p ⟨11,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨3,by decide⟩) (p ⟨2,by decide⟩) (p ⟨1,by decide⟩) (p ⟨0,by decide⟩) at hm
  constructor
  · intro j
    fin_cases j
    · exact hm.nq0
    · exact hm.nq1
    · exact hm.nq2
    · exact hm.nq3
    · exact hm.nq7
    · exact hm.nq6
    · exact hm.nq5
    · exact hm.nq4
    · exact hm.nq11
    · exact hm.nq10
    · exact hm.nq9
    · exact hm.nq8
    · exact hm.nq15
    · exact hm.nq14
    · exact hm.nq13
    · exact hm.nq12
  ·
    have g0 := hm.n0
    have g2 := hm.m1
    have g3 := hm.m2
    have g4 := hm.m3
    have g5 := hm.m4
    have g6 := hm.m5
    have g7 := hm.m6
    norm_num at g0 g2 g3 g4 g5 g6 g7
    ext i
    fin_cases i
    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
      linear_combination 1 * g0
    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
      linear_combination (1/2) * g0 + (1/2) * g2
    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
      linear_combination (1/2) * g0 + (1/2) * g3
    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
      linear_combination (1/2) * g0 + (1/2) * g4
    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
      linear_combination (1/2) * g0 + (1/2) * g5
    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
      linear_combination (1/2) * g0 + (1/2) * g6
    · norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
      linear_combination (1/2) * g0 + (1/2) * g7

theorem feasible_iff_full_moments (p : Fin 16 → ℝ) :
    Feasible M b p ↔ VectorMomentSystem (nativeQ p) (nativeR p) :=
  ⟨full_moments_of_feasible p,feasible_of_full_moments p⟩

end
end MainTheory.Orbit31BalancedMomentIff
