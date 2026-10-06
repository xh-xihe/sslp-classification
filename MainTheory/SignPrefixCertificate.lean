import MainTheory.SignMatrixCertificate

/-! Sound rules for an exhaustive DAG of sign-matrix prefixes. -/

namespace MainTheory.SignPrefixCertificate

open Matrix SignMatrixCertificate GramPrefixBound
open scoped BigOperators

def IsSign {r c : Type*} (P : Matrix r c ℤ) : Prop :=
  ∀ i j, P i j = 1 ∨ P i j = -1

def PrefixGood {N k : ℕ} (T : ℤ) (B : ℕ) (hk : k ≤ N)
    (P : Matrix (Fin k) (Fin N) ℤ) : Prop :=
  ∀ A : Matrix (Fin N) (Fin N) ℤ, IsSign A →
    (∀ i j, A (Fin.castLE hk i) j = P i j) → Good T B A

theorem prefixGood_leaf {N : ℕ} {T : ℤ} {B : ℕ}
    {P : Matrix (Fin N) (Fin N) ℤ} (hP : Good T B P) :
    PrefixGood T B (Nat.le_refl N) P := by
  intro A _ hA
  have : A = P := by ext i j; exact hA i j
  rwa [this]

theorem prefixGood_prune {N k : ℕ} {T : ℤ} {B : ℕ} (hk : k ≤ N)
    (P : Matrix (Fin k) (Fin N) ℤ) (hT : 0 ≤ T)
    (hp : (P * P.transpose).det * (N : ℤ)^(N-k) < T^2) :
    PrefixGood T B hk P := by
  intro A hA hP
  apply Or.inl
  apply sign_prune A hA hk T hT
  have he : (intGram A).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      P * P.transpose := by
    ext i j
    simp only [intGram, Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.transpose_apply, hP]
  rwa [he]

theorem prefixGood_step {N k : ℕ} {T : ℤ} {B : ℕ} (hk : k+1 ≤ N)
    (P : Matrix (Fin k) (Fin N) ℤ)
    (h : ∀ v : Fin N → ℤ, (∀ j, v j = 1 ∨ v j = -1) →
      PrefixGood T B hk (Fin.snoc P v)) :
    PrefixGood T B (by omega : k ≤ N) P := by
  intro A hA hP
  apply h (A ⟨k, by omega⟩) (hA _) A hA
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last]
    rfl
  · simpa only [Fin.snoc_castSucc] using hP i j

theorem sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a*b = 1 ∨ a*b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem prefixGood_signed {N k : ℕ} {T : ℤ} {B : ℕ} (hk : k ≤ N)
    {P Q : Matrix (Fin k) (Fin N) ℤ} (hQ : PrefixGood T B hk Q)
    (rp : Equiv.Perm (Fin k)) (cp : Equiv.Perm (Fin N))
    (u : Fin k → ℤ) (v : Fin N → ℤ)
    (hu : ∀ i, u i = 1 ∨ u i = -1) (hv : ∀ j, v j = 1 ∨ v j = -1)
    (he : ∀ i j, P i j = u i * Q (rp i) (cp j) * v j) :
    PrefixGood T B hk P := by
  intro A hA hP
  let e : Fin k ↪ Fin N := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  let R := rp.viaFintypeEmbedding e
  have hR : ∀ i, R (e i) = e (rp i) :=
    fun i => Equiv.Perm.viaFintypeEmbedding_apply_image rp e i
  have hRi : ∀ i, R.symm (e i) = e (rp.symm i) := by
    intro i
    apply R.injective
    rw [R.apply_symm_apply, hR, rp.apply_symm_apply]
  let U : Fin N → ℤ := fun i => if h : i.val < k then u ⟨i.val, h⟩ else 1
  have hU : ∀ i, U i = 1 ∨ U i = -1 := by
    intro i
    dsimp only [U]
    split <;> simp_all only [true_or]
  have hUe : ∀ i, U (e i) = u i := by
    intro i
    simp only [U, e, Function.Embedding.coeFn_mk, Fin.val_castLE, i.isLt, ↓reduceDIte]
  let A' : Matrix (Fin N) (Fin N) ℤ :=
    fun i j => U (R.symm i) * A (R.symm i) (cp.symm j) * v (cp.symm j)
  have hA' : IsSign A' := fun i j =>
    sign_mul (sign_mul (hU _) (hA _ _)) (hv _)
  have hP' : ∀ i j, A' (Fin.castLE hk i) j = Q i j := by
    intro i j
    change U (R.symm (e i)) * A (R.symm (e i)) (cp.symm j) * v (cp.symm j) = _
    rw [hRi, hUe]
    change u (rp.symm i) * A (Fin.castLE hk (rp.symm i)) (cp.symm j) * v (cp.symm j) = _
    rw [hP, he, rp.apply_symm_apply, cp.apply_symm_apply]
    rcases hu (rp.symm i) with h | h <;>
      rcases hv (cp.symm j) with h' | h' <;> rw [h, h'] <;> ring
  have hg := good_signed (hQ A' hA' hP') R cp U v hU hv
  have hback : (fun i j => U i * A' (R i) (cp j) * v j) = A := by
    ext i j
    dsimp only [A']
    rw [R.symm_apply_apply, cp.symm_apply_apply]
    rcases hU i with h | h <;> rcases hv j with h' | h' <;> rw [h, h'] <;> ring
  rwa [hback] at hg

end MainTheory.SignPrefixCertificate
