import Orbit2.Global

/-! Strict positivity of every physical M-4I block, including invertibility of its LDL factor. -/

namespace MainTheory.Orbit2StrictBlocks

noncomputable section

open Matrix
open scoped BigOperators

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

theorem unit_lower (b : Fin 111) :
    (∀ i j : Fin (Orbit2.checkedBlocks b).n,i<j → (Orbit2.checkedBlocks b).certificate.L i j=0) ∧
      (∀ i : Fin (Orbit2.checkedBlocks b).n,(Orbit2.checkedBlocks b).certificate.L i i=1) := by
  have h : ∀ b : Fin 111,
      (∀ i j : Fin (Orbit2.checkedBlocks b).n,i<j → (Orbit2.checkedBlocks b).certificate.L i j=0) ∧
        (∀ i : Fin (Orbit2.checkedBlocks b).n,(Orbit2.checkedBlocks b).certificate.L i i=1) := by
    decide +kernel
  exact h b

theorem certificate_strict {n : ℕ} (C : Orbit2.LDLCertificate n n)
    (htri : ∀ i j : Fin n,i<j → C.L i j=0) (hdiag : ∀ i : Fin n,C.L i i=1) :
    (Orbit2.realMatrix C.A).PosDef := by
  let L : Matrix (Fin n) (Fin n) ℝ := fun i j => C.L i j
  let d : Fin n → ℝ := fun k => C.d k
  have hd : ∀ k,0<d k := by intro k; change (0 : ℝ)<(C.d k : ℝ); exact_mod_cast C.positive k
  have hlt : L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change (C.L i j : ℝ)=0
    exact_mod_cast htri i j hij
  have hdet : L.det=1 := by
    rw [Matrix.det_of_lowerTriangular L hlt]
    have hh : ∀ i,L i i=1 := by intro i; change (C.L i i : ℝ)=1; exact_mod_cast hdiag i
    simp [hh]
  have hunit : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (by rw [hdet]; exact isUnit_one)
  have heq : Orbit2.realMatrix C.A=L*Matrix.diagonal d*L.conjTranspose := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,star_trivial]
    change (C.A i j : ℝ)=∑ k,(C.L i k : ℝ)*(C.d k : ℝ)*(C.L j k : ℝ)
    exact_mod_cast C.factorization i j
  rw [heq]
  exact (Matrix.PosDef.diagonal hd).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr hunit)

theorem physical_strict (b : Fin 111) :
    (Orbit2.realMatrix (Orbit2.checkedBlocks b).M-
      (4 : ℝ) • (1 : Matrix (Fin (Orbit2.checkedBlocks b).n) (Fin (Orbit2.checkedBlocks b).n) ℝ)).PosDef := by
  have h := certificate_strict (Orbit2.checkedBlocks b).certificate (unit_lower b).1 (unit_lower b).2
  have he : Orbit2.realMatrix (Orbit2.checkedBlocks b).certificate.A =
      Orbit2.realMatrix (Orbit2.checkedBlocks b).M-
        (4 : ℝ) • (1 : Matrix (Fin (Orbit2.checkedBlocks b).n) (Fin (Orbit2.checkedBlocks b).n) ℝ) := by
    ext i j
    have hij := (Orbit2.checkedBlocks b).shifted i j
    simp only [Orbit2.realMatrix,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs at * <;> exact_mod_cast hij
  exact he ▸ h

end

end MainTheory.Orbit2StrictBlocks
