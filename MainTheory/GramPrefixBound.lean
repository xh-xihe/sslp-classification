import Mathlib

/-! # Exact Gram-prefix determinant bounds for verified pruning

The inequality is a real-matrix theorem. No numerical matrix or enumeration
result is an assumption. Singular positive semidefinite matrices are included.
-/

namespace MainTheory.GramPrefixBound

open Matrix

noncomputable section

theorem posDef_submatrix {m n : Type*} {G : Matrix n n ℝ} (hG : G.PosDef)
    (e : m → n) (he : Function.Injective e) : (G.submatrix e e).PosDef := by
  refine ⟨hG.1.submatrix _, fun x hx => ?_⟩
  have hne : x.mapDomain e ≠ 0 := by
    intro h
    exact hx ((Finsupp.mapDomain_injective he) (by simpa using h))
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hG.2 hne

theorem det_fromBlocks_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosDef) (B : Matrix n (Fin 1) ℝ) (c : ℝ) :
    (Matrix.fromBlocks A B B.conjTranspose (fun _ _ => c)).det ≤ A.det * c := by
  letI := hA.isUnit.invertible
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one]
  have hn : 0 ≤ (B.conjTranspose * A⁻¹ * B) 0 0 :=
    (hA.inv.posSemidef.conjTranspose_mul_mul_same B).diag_nonneg
  change A.det * (c - (B.conjTranspose * A⁻¹ * B) 0 0) ≤ A.det * c
  exact mul_le_mul_of_nonneg_left (sub_le_self _ hn) hA.det_pos.le

theorem det_succ_le {n : ℕ} (G : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hG : G.PosDef) :
    G.det ≤ (G.submatrix Fin.castSucc Fin.castSucc).det * G (Fin.last n) (Fin.last n) := by
  let A := G.submatrix Fin.castSucc Fin.castSucc
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => G i.castSucc (Fin.last n)
  let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
  have he : G.submatrix e e =
      Matrix.fromBlocks A B B.conjTranspose (fun _ _ => G (Fin.last n) (Fin.last n)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · fin_cases j; rfl
    · fin_cases i
      simpa [e, B, Matrix.conjTranspose_apply] using
        (hG.isHermitian.apply (Fin.last n) j.castSucc).symm
    · fin_cases i; fin_cases j; rfl
  have hA := posDef_submatrix hG Fin.castSucc (Fin.castSucc_injective n)
  have hb := det_fromBlocks_le A hA B (G (Fin.last n) (Fin.last n))
  rw [← he, Matrix.det_submatrix_equiv_self] at hb
  exact hb

def principalPrefix {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (hk : k ≤ N) :
    Matrix (Fin k) (Fin k) ℝ := G.submatrix (Fin.castLE hk) (Fin.castLE hk)

theorem det_le_prefix_mul_pow_posDef {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : G.PosDef) (R : ℝ) (hR : 0 ≤ R) (hdiag : ∀ i, G i i ≤ R)
    {k : ℕ} (hk : k ≤ N) :
    G.det ≤ (principalPrefix G hk).det * R^(N-k) := by
  induction N with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp [principalPrefix]
  | succ n ih =>
    by_cases heq : k = n+1
    · subst k
      simp [principalPrefix]
    · have hkn : k ≤ n := by omega
      let A := G.submatrix Fin.castSucc Fin.castSucc
      have hA : A.PosDef := posDef_submatrix hG Fin.castSucc (Fin.castSucc_injective n)
      have hdiagA : ∀ i, A i i ≤ R := fun i => hdiag i.castSucc
      have hi := ih A hA hdiagA hkn
      have hp : principalPrefix A hkn = principalPrefix G hk := by
        ext i j
        rfl
      have hexp : n+1-k = (n-k)+1 := by omega
      calc
        G.det ≤ A.det * G (Fin.last n) (Fin.last n) := det_succ_le G hG
        _ ≤ A.det * R := mul_le_mul_of_nonneg_left (hdiag _) hA.det_pos.le
        _ ≤ (principalPrefix A hkn).det * R^(n-k) * R := mul_le_mul_of_nonneg_right hi hR
        _ = (principalPrefix G hk).det * R^(n+1-k) := by rw [hp, hexp, pow_succ, mul_assoc]

/-- Every PSD Gram prefix bounds the determinant of every completion with
the same diagonal bound. This is the inequality used by the pruning checker. -/
theorem det_le_prefix_mul_pow {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : G.PosSemidef) (R : ℝ) (hR : 0 ≤ R) (hdiag : ∀ i, G i i ≤ R)
    {k : ℕ} (hk : k ≤ N) :
    G.det ≤ (principalPrefix G hk).det * R^(N-k) := by
  by_cases hd : G.det = 0
  · rw [hd]
    exact mul_nonneg (hG.submatrix _).det_nonneg (pow_nonneg hR _)
  · exact det_le_prefix_mul_pow_posDef G
      (hG.posDef_iff_isUnit.mpr (G.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd)))
      R hR hdiag hk

theorem int_det_le_prefix_mul_pow {N : ℕ} (G : Matrix (Fin N) (Fin N) ℤ)
    (hG : (G.map (Int.castRingHom ℝ)).PosSemidef) (R : ℤ) (hR : 0 ≤ R)
    (hdiag : ∀ i, G i i ≤ R) {k : ℕ} (hk : k ≤ N) :
    G.det ≤ (G.submatrix (Fin.castLE hk) (Fin.castLE hk)).det * R^(N-k) := by
  have hd : ∀ i, (G.map (Int.castRingHom ℝ)) i i ≤ (R : ℝ) := by
    intro i
    change (G i i : ℝ) ≤ (R : ℝ)
    exact_mod_cast hdiag i
  have h := det_le_prefix_mul_pow (G.map (Int.castRingHom ℝ)) hG (R : ℝ)
    (by exact_mod_cast hR) hd hk
  have hp : principalPrefix (G.map (Int.castRingHom ℝ)) hk =
      (G.submatrix (Fin.castLE hk) (Fin.castLE hk)).map (Int.castRingHom ℝ) := rfl
  rw [hp] at h
  change (G.map (fun z : ℤ => (z : ℝ))).det ≤
    ((G.submatrix (Fin.castLE hk) (Fin.castLE hk)).map (fun z : ℤ => (z : ℝ))).det *
      (R : ℝ)^(N-k) at h
  rw [← Int.cast_det, ← Int.cast_det] at h
  exact_mod_cast h

def intGram {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) := A * A.transpose

theorem intGram_posSemidef {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    ((intGram A).map (Int.castRingHom ℝ)).PosSemidef := by
  have he : (intGram A).map (Int.castRingHom ℝ) =
      (A.map (Int.castRingHom ℝ)) * (A.map (Int.castRingHom ℝ)).conjTranspose := by
    rw [intGram, Matrix.map_mul]
    congr 1
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem sign_gram_diagonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = 1 ∨ A i j = -1) (i : Fin N) : intGram A i i = N := by
  have hs : ∀ j, A i j * A i j = 1 := by
    intro j
    rcases hA i j with h | h <;> rw [h] <;> norm_num
  simp [intGram, Matrix.mul_apply, Matrix.transpose_apply, hs]

/-- Integer form used for every proposed high-determinant sign-matrix branch. -/
theorem sign_det_sq_le_prefix {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = 1 ∨ A i j = -1) {k : ℕ} (hk : k ≤ N) :
    A.det^2 ≤ ((intGram A).submatrix (Fin.castLE hk) (Fin.castLE hk)).det * (N : ℤ)^(N-k) := by
  have h := int_det_le_prefix_mul_pow (intGram A) (intGram_posSemidef A) (N : ℤ)
    (by positivity) (fun i => le_of_eq (sign_gram_diagonal A hA i)) hk
  simpa only [intGram, Matrix.det_mul, Matrix.det_transpose, pow_two] using h

/-- A strict integer pruning threshold excludes every completion of a prefix. -/
theorem sign_prune {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = 1 ∨ A i j = -1) {k : ℕ} (hk : k ≤ N)
    (T : ℤ) (hT : 0 ≤ T)
    (hp : ((intGram A).submatrix (Fin.castLE hk) (Fin.castLE hk)).det * (N : ℤ)^(N-k) < T^2) :
    |A.det| < T := by
  have h := sign_det_sq_le_prefix A hA hk
  have ha := abs_nonneg A.det
  have he := sq_abs A.det
  nlinarith

end
end MainTheory.GramPrefixBound
