import MainTheory.Generated.Orbit31SupportArithmetic

/-! Real semantics of the explicitly checked orbit-31 support certificates.
All-mask coverage and the subsequent phase classification remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace MainTheory.Orbit31SupportSemantics
noncomputable section
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.Orbit31SupportBase
open MainTheory.Generated.Orbit31SupportArithmetic
open scoped BigOperators Matrix

def maskSet (mask : ℕ) : Finset (Fin 16) :=
  Finset.univ.filter fun j => mask.testBit j.val = true

theorem mem_maskSet (mask : ℕ) (j : Fin 16) : j ∈ maskSet mask ↔ mask.testBit j.val = true := by
  simp [maskSet]

def primal (v : Fin 204) (j : Fin 16) : ℝ := (primalNumerators v j : ℝ)/8
def dual (v : Fin 68) (i : Fin 7) : ℝ := dualMultipliers v i

theorem rhs_real (i : Fin 7) : b i = (rhsTwice i : ℝ)/2 := by
  fin_cases i <;> norm_num [b,rhsTwice,Fin.succ]

theorem primal_feasible (v : Fin 204) : Feasible M b (primal v) := by
  constructor
  · intro j
    exact div_nonneg (by exact_mod_cast (primal_valid v).1 j) (by norm_num)
  · ext i
    have hi : 2 * (∑ j, (integerRows i j : ℝ)*(primalNumerators v j : ℝ)) =
        8*(rhsTwice i : ℝ) := by exact_mod_cast (primal_valid v).2.1 i
    have hs : (∑ j, (integerRows i j : ℝ)*(primalNumerators v j : ℝ)) =
        4*(rhsTwice i : ℝ) := by linarith
    simp only [Matrix.mulVec,dotProduct,M,primal,← mul_div_assoc]
    rw [← Finset.sum_div,hs,rhs_real]
    ring

theorem primal_support (v : Fin 204) : ExactSupport (maskSet (primalMasks v)) (primal v) := by
  intro j
  rw [mem_maskSet]
  change 0 < (primalNumerators v j : ℝ)/8 ↔ _
  rw [div_pos_iff_of_pos_right (by norm_num : (0 : ℝ)<8)]
  exact_mod_cast ((primal_valid v).2.2 j).symm

theorem dual_coefficients (v : Fin 68) (j : Fin 16) :
    M.vecMul (dual v) j = (dualCoefficients v j : ℝ) := by
  change (∑ i, (dualMultipliers v i : ℝ)*(integerRows i j : ℝ)) = _
  exact_mod_cast ((dual_valid v).1 j).symm

theorem dual_rhs (v : Fin 68) : dual v ⬝ᵥ b = (dualRhsTwice v : ℝ)/2 := by
  simp only [dotProduct,rhs_real,dual,← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast (dual_valid v).2.1.symm

theorem subset_bit {a b : ℕ} (h : a &&& b = a) {j : ℕ}
    (ha : a.testBit j = true) : b.testBit j = true := by
  have he := congrArg (fun n : ℕ => n.testBit j) h
  simpa only [Nat.testBit_and,ha,Bool.true_and] using he

def PrimalWitness (mask : ℕ) (w : Fin 16 → Fin 204) : Prop :=
  ∀ j, (primalMasks (w j) &&& mask = primalMasks (w j)) ∧
    (mask.testBit j.val = true → (primalMasks (w j)).testBit j.val = true)

theorem support_exists_of_primal {mask : ℕ} {w : Fin 16 → Fin 204}
    (hw : PrimalWitness mask w) : ∃ p, Feasible M b p ∧ ExactSupport (maskSet mask) p := by
  refine ⟨average (fun j => primal (w j)),average_feasible M b _ (fun j => primal_feasible (w j)),?_⟩
  apply average_exact_support
  · intro i j
    exact (primal_feasible (w i)).nonneg j
  · intro i j hj
    apply zero_off_support (primal_feasible (w i)).nonneg (primal_support (w i))
    intro hmem
    apply hj
    rw [mem_maskSet] at hmem ⊢
    exact subset_bit (hw i).1 hmem
  · intro j hj
    apply (primal_support (w j) j).mpr
    rw [mem_maskSet] at hj ⊢
    exact (hw j).2 hj

def DualWitness (mask : ℕ) (v : Fin 68) (j : Fin 16) : Prop :=
  dualNegativeMasks v &&& mask = 0 ∧
    (dualRhsTwice v < 0 ∨
     (dualRhsTwice v = 0 ∧ mask.testBit j.val = true ∧ 0 < dualCoefficients v j))

theorem dual_nonneg_on_mask {mask : ℕ} {v : Fin 68}
    (hv : dualNegativeMasks v &&& mask = 0) :
    ∀ j ∈ maskSet mask, 0 ≤ M.vecMul (dual v) j := by
  intro j hj
  rw [mem_maskSet] at hj
  have he := congrArg (fun n : ℕ => n.testBit j.val) hv
  have hz : (dualNegativeMasks v).testBit j.val = false := by
    simpa only [Nat.testBit_and,hj,Bool.and_true,Nat.zero_testBit] using he
  rw [dual_coefficients]
  have hn : ¬ dualCoefficients v j < 0 := by
    intro hneg
    have ht := ((dual_valid v).2.2.1 j).mpr hneg
    rw [hz] at ht
    contradiction
  exact_mod_cast le_of_not_gt hn

theorem support_excluded_of_dual {mask : ℕ} {v : Fin 68} {j : Fin 16}
    (hv : DualWitness mask v j) : ¬ ∃ p, Feasible M b p ∧ ExactSupport (maskSet mask) p := by
  rcases hv with ⟨hn,hb|⟨hb,hj,hpos⟩⟩
  · apply negative_dual_excludes (dual_nonneg_on_mask hn)
    rw [dual_rhs]
    exact div_neg_of_neg_of_pos (by exact_mod_cast hb) (by norm_num)
  · apply zero_dual_excludes (dual_nonneg_on_mask hn)
    · rw [dual_rhs,hb]
      norm_num
    · refine ⟨j,(mem_maskSet mask j).mpr hj,?_⟩
      rw [dual_coefficients]
      exact_mod_cast hpos

end
end MainTheory.Orbit31SupportSemantics
