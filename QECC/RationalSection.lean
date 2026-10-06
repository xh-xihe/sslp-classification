import Mathlib

open Matrix

namespace QECC

/-- Every rational square matrix has a generalized inverse in the sense `B * G * B = B`.

This finite-dimensional form is enough for clearing denominators in
`integerMatrix_uniform_rational_lift`. -/
theorem matrix_exists_generalizedInverse
    {c : Type*} [Fintype c] [DecidableEq c]
    (B : Matrix c c ℚ) : ∃ G : Matrix c c ℚ, B * G * B = B := by
  let f : (c → ℚ) →ₗ[ℚ] (c → ℚ) := Matrix.toLin' B
  obtain ⟨s, hs⟩ :=
    f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let p : (c → ℚ) →ₗ[ℚ] f.range := f.range.subtype.leftInverse
  let g : (c → ℚ) →ₗ[ℚ] (c → ℚ) := s.comp p
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  change (f.comp g).comp f = f
  apply LinearMap.ext
  intro x
  change f (s (p (f x))) = f x
  have hp : p (f x) = ⟨f x, ⟨x, rfl⟩⟩ := by
    exact f.range.subtype.leftInverse_apply_of_inj f.range.ker_subtype
      ⟨f x, ⟨x, rfl⟩⟩
  rw [hp]
  have hsx := LinearMap.congr_fun hs ⟨f x, ⟨x, rfl⟩⟩
  exact congr_arg Subtype.val hsx

private theorem cast_num_mulVec_div_den
    {c : Type*} [Fintype c]
    (G : Matrix c c ℚ) (d : c → ℤ) :
    (fun i ↦ ((G.num *ᵥ d) i : ℝ) / (G.den : ℝ)) =
      G.map ((Rat.castHom ℝ) : ℚ → ℝ) *ᵥ (fun j ↦ (d j : ℝ)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have he : ((G.num i j : ℤ) : ℝ) / (G.den : ℝ) = ((G i j : ℚ) : ℝ) := by
    exact_mod_cast G.num_div_den i j
  rw [← div_mul_eq_mul_div, he]
  rfl

/-- A uniform denominator for lifting integral values of an integer matrix.

For an integer matrix `A`, this produces one positive integer `Q`, depending only on
`A`. Whenever the real vector `t` has integral image `A *ᵥ t = b`, there is an
integer vector `a` such that subtracting `a / Q` from `t` does not change its image
under `A`.

The proof applies a rational generalized inverse to the Gram matrix `Aᵀ * A` and
uses `Matrix.num` and `Matrix.den` to clear all its denominators at once. -/
theorem integerMatrix_uniform_rational_lift
    {r c : Type*} [Fintype r] [Fintype c] [DecidableEq c]
    (A : Matrix r c ℤ) :
    ∃ Q : ℕ, 0 < Q ∧
      ∀ (t : c → ℝ) (b : r → ℤ),
        A.map ((Int.castRingHom ℝ) : ℤ → ℝ) *ᵥ t = (fun i ↦ (b i : ℝ)) →
        ∃ a : c → ℤ,
          A.map ((Int.castRingHom ℝ) : ℤ → ℝ) *ᵥ
            (t - fun j ↦ (a j : ℝ) / (Q : ℝ)) = 0 := by
  classical
  let Aq : Matrix r c ℚ := A.map ((Int.castRingHom ℚ) : ℤ → ℚ)
  let B : Matrix c c ℚ := Aqᵀ * Aq
  obtain ⟨G, hG⟩ := matrix_exists_generalizedInverse B
  refine ⟨G.den, Nat.pos_of_ne_zero G.den_ne_zero, ?_⟩
  intro t b hAt
  let Ar : Matrix r c ℝ := A.map ((Int.castRingHom ℝ) : ℤ → ℝ)
  let Br : Matrix c c ℝ := Arᵀ * Ar
  let Gr : Matrix c c ℝ := G.map ((Rat.castHom ℝ) : ℚ → ℝ)
  let d : c → ℤ := Aᵀ *ᵥ b
  let a : c → ℤ := G.num *ᵥ d
  refine ⟨a, ?_⟩
  change Ar *ᵥ (t - fun j ↦ (a j : ℝ) / (G.den : ℝ)) = 0

  have hBcast : B.map ((Rat.castHom ℝ) : ℚ → ℝ) = Br := by
    ext i j
    simp [B, Aq, Br, Ar, Matrix.mul_apply]
  have hGreal : Br * Gr * Br = Br := by
    have h := congrArg (fun M : Matrix c c ℚ ↦
      M.map ((Rat.castHom ℝ) : ℚ → ℝ)) hG
    change (B * G * B).map ((Rat.castHom ℝ) : ℚ → ℝ) =
      B.map ((Rat.castHom ℝ) : ℚ → ℝ) at h
    rw [Matrix.map_mul, Matrix.map_mul, hBcast] at h
    exact h

  have hdcast : (fun j ↦ (d j : ℝ)) = Arᵀ *ᵥ (fun i ↦ (b i : ℝ)) := by
    funext j
    simpa [d, Ar] using
      (RingHom.map_mulVec (Int.castRingHom ℝ) Aᵀ b j)
  have hBr_t : Br *ᵥ t = (fun j ↦ (d j : ℝ)) := by
    calc
      Br *ᵥ t = Arᵀ *ᵥ (Ar *ᵥ t) := by
        exact (Matrix.mulVec_mulVec t Arᵀ Ar).symm
      _ = Arᵀ *ᵥ (fun i ↦ (b i : ℝ)) := by
        change Ar *ᵥ t = (fun i ↦ (b i : ℝ)) at hAt
        rw [hAt]
      _ = (fun j ↦ (d j : ℝ)) := hdcast.symm

  have ha_div : (fun j ↦ (a j : ℝ) / (G.den : ℝ)) =
      Gr *ᵥ (fun j ↦ (d j : ℝ)) := by
    simpa [a, Gr] using cast_num_mulVec_div_den G d
  have hB_a : Br *ᵥ (fun j ↦ (a j : ℝ) / (G.den : ℝ)) = Br *ᵥ t := by
    calc
      Br *ᵥ (fun j ↦ (a j : ℝ) / (G.den : ℝ)) =
          Br *ᵥ (Gr *ᵥ (fun j ↦ (d j : ℝ))) := by rw [ha_div]
      _ = (Br * Gr) *ᵥ (fun j ↦ (d j : ℝ)) :=
        Matrix.mulVec_mulVec _ Br Gr
      _ = (Br * Gr) *ᵥ (Br *ᵥ t) := by rw [hBr_t]
      _ = (Br * Gr * Br) *ᵥ t := Matrix.mulVec_mulVec _ _ _
      _ = Br *ᵥ t := by rw [hGreal]
  have hBr_zero : Br *ᵥ (t - fun j ↦ (a j : ℝ) / (G.den : ℝ)) = 0 := by
    rw [Matrix.mulVec_sub, hB_a, sub_self]

  have hvBr : (t - fun j ↦ (a j : ℝ) / (G.den : ℝ)) ∈
      LinearMap.ker Br.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hBr_zero
  have hker : LinearMap.ker Br.mulVecLin = LinearMap.ker Ar.mulVecLin := by
    simpa [Br] using Matrix.ker_mulVecLin_transpose_mul_self Ar
  have hvAr : (t - fun j ↦ (a j : ℝ) / (G.den : ℝ)) ∈
      LinearMap.ker Ar.mulVecLin := by
    rw [← hker]
    exact hvBr
  simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hvAr

end QECC
