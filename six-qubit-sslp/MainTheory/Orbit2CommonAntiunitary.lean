import Mathlib

/-! # The common orbit-2 antiunitary from block compression equations

The same skew unitary works for every compression whose four blocks are
complex symmetric and whose diagonal blocks sum to twice the common mean.
The physical magic-basis and mixed-KL derivation of these block hypotheses is
a separate encoder bridge, not an assumption-free consequence of this lemma.
-/

namespace MainTheory.Orbit2CommonAntiunitary

open Matrix

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def J : Matrix (I ⊕ I) (I ⊕ I) ℂ := fromBlocks 0 1 (-1) 0

theorem J_transpose : (J (I := I)).transpose = -J := by
  simp [J, fromBlocks_transpose, fromBlocks_neg]

theorem J_square : J (I := I) * J = -1 := by
  simp [J, fromBlocks_multiply, fromBlocks_neg, ← fromBlocks_one]

theorem common_equation (R C B S : Matrix I I ℂ) (μ : ℂ)
    (hR : R.transpose = R) (hC : C.transpose = C)
    (hB : B.transpose = B) (hS : S.transpose = S)
    (hmean : R + S = (2 * μ) • (1 : Matrix I I ℂ)) :
    fromBlocks R C B S * J + J * (fromBlocks R C B S).transpose =
      (2 * μ) • J := by
  simp only [J, fromBlocks_transpose, fromBlocks_multiply, hR, hC, hB, hS,
    mul_zero, zero_mul, mul_one, one_mul, mul_neg, neg_mul,
    zero_add, add_zero, fromBlocks_add, fromBlocks_smul, smul_zero]
  congr 1
  · abel
  · rw [← neg_add, add_comm S R, hmean, smul_neg]
  · abel

theorem common_equation_of_compression (h : Matrix (I ⊕ I) (I ⊕ I) ℂ) (μ : ℂ)
    (h00 : h.toBlocks₁₁.transpose = h.toBlocks₁₁)
    (h01 : h.toBlocks₁₂.transpose = h.toBlocks₁₂)
    (h10 : h.toBlocks₂₁.transpose = h.toBlocks₂₁)
    (h11 : h.toBlocks₂₂.transpose = h.toBlocks₂₂)
    (hmean : h.toBlocks₁₁ + h.toBlocks₂₂ = (2 * μ) • (1 : Matrix I I ℂ)) :
    h * J + J * h.transpose = (2 * μ) • J := by
  have hc := common_equation h.toBlocks₁₁ h.toBlocks₁₂ h.toBlocks₂₁ h.toBlocks₂₂
    μ h00 h01 h10 h11 hmean
  simpa only [fromBlocks_toBlocks] using hc

end
end MainTheory.Orbit2CommonAntiunitary
