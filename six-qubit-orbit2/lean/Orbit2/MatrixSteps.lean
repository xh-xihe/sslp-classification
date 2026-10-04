import Orbit2.Certificate

/-! Direct algebra for two matrix steps in the TeX. -/
namespace Orbit2
open Matrix

/-- The common-J equation follows from symmetric blocks and their fixed sum.
These are explicit hypotheses: their derivation from mixed KL is not formalized here. -/
theorem commonJ_block_identity {n : ℕ}
    (R C : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hR : R.transpose = R) (hC : C.transpose = C) :
    let h := Matrix.fromBlocks R C (C.map star) ((2 * μ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R)
    let J := Matrix.fromBlocks 0 (1 : Matrix (Fin n) (Fin n) ℂ) (-1) 0
    h * J + J * h.transpose = (2 * μ) • J := by
  have hCc : (C.map star).transpose = C.map star := by
    ext i j
    simpa [Matrix.transpose_apply, Matrix.map_apply] using congrArg star (congrFun (congrFun hC i) j)
  dsimp
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add, Matrix.fromBlocks_smul, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_one, hR, hC,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_smul,
    smul_zero, smul_neg]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · module
  · module
  · module
  · change C.map star + 0 + (-(C.map star).transpose + (0-0)) = 0
    rw [hCc]
    module

/-- The split-qubit isometry in computational order 00,01,10,11. -/
def splitW (a b : ℝ) : Matrix (Fin 4) (Fin 2) ℂ :=
  ![![(a : ℂ), 0], ![0, (a : ℂ)], ![0, (b : ℂ)], ![(b : ℂ), 0]]

def zTwo : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]
def zzFour : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, -1, -1, 1]
def ziFour : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, -1, -1]
def xxFour : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,0,0,1], ![0,0,1,0], ![0,1,0,0], ![1,0,0,0]]

theorem split_isometry (a b : ℝ) (hab : a^2+b^2 = 1) :
    (splitW a b).conjTranspose * splitW a b = 1 := by
  have hc : (a : ℂ)^2 + (b : ℂ)^2 = 1 := by exact_mod_cast hab
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitW, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.conj_ofReal] <;> linear_combination hc

theorem split_logical_lift (a b : ℝ) :
    zzFour * splitW a b = splitW a b * zTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zzFour, zTwo, splitW, Matrix.mul_apply, Matrix.diagonal]

/-- Trigonometry is unnecessary: the projection identity depends only on a²+b²=1. -/
theorem split_projection (a b : ℝ) (hab : a^2+b^2 = 1) :
    splitW a b * (splitW a b).conjTranspose =
      (1/2 : ℂ) • (1 + ((a^2-b^2 : ℝ) : ℂ) • ziFour +
        ((2*a*b : ℝ) : ℂ) • xxFour) := by
  have hc : (a : ℂ)^2 + (b : ℂ)^2 = 1 := by exact_mod_cast hab
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitW, ziFour, xxFour, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Complex.conj_ofReal,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    first | linear_combination hc / 2 | linear_combination -hc / 2 | ring

end Orbit2
