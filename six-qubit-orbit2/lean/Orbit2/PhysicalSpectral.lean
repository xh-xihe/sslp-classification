import Orbit2.SpectralGeometry

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem frame_transpose_projection_omega {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Matrix α Frames.LogicalFrame ℂ) (hQ : Q.conjTranspose * Q=1) :
    (Frames.pi Q).transpose * (Frames.omega Q).conjTranspose = (Frames.omega Q).conjTranspose := by
  have ht := Frames.transpose_isometry Q hQ
  unfold Frames.pi Frames.omega
  simp only [Matrix.transpose_mul,Matrix.transpose_conjTranspose,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_transpose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q.transpose (Q.map star),ht,Matrix.one_mul]

theorem Encoder.physicalOmega_moment (V : Encoder) (i : Fin 4) :
    V.activeProjector * operator (single i 3) * V.activeProjector +
      V.physicalOmega * operator (single i 3) * V.physicalOmega.conjTranspose =
        (2 * V.activeMu (single i 3)) • V.activeProjector := by
  have h := Frames.lift_commonJ V.magicFrames V.magicFrames_isometry _ _ (V.physical_commonJ i 3 (by decide))
  have hm := congrArg (fun M => M * (Frames.omega V.magicFrames).conjTranspose) h
  dsimp only at hm
  simp only [Matrix.add_mul,Matrix.smul_mul] at hm
  have hl : Frames.pi V.magicFrames * operator (single i 3) * Frames.omega V.magicFrames *
      (Frames.omega V.magicFrames).conjTranspose =
      Frames.pi V.magicFrames * operator (single i 3) * Frames.pi V.magicFrames := by
    rw [Matrix.mul_assoc _ (Frames.omega V.magicFrames),Frames.omega_left V.magicFrames V.magicFrames_isometry]
  have hr : Frames.omega V.magicFrames * (operator (single i 3)).transpose * (Frames.pi V.magicFrames).transpose *
      (Frames.omega V.magicFrames).conjTranspose =
      Frames.omega V.magicFrames * operator (single i 3) * (Frames.omega V.magicFrames).conjTranspose := by
    rw [Matrix.mul_assoc _ (Frames.pi V.magicFrames).transpose,
      frame_transpose_projection_omega V.magicFrames V.magicFrames_isometry,
      single_Z_diagonal,Matrix.diagonal_transpose]
  rw [hl,hr,Frames.omega_left V.magicFrames V.magicFrames_isometry] at hm
  exact hm

theorem field_weighted_sum (M : Defects.ActiveMatrix) (x : ActiveBits) :
    (∑ y, (rowField x y : ℂ) * (Complex.normSq (M x y) : ℂ)) =
      ∑ i : Fin 4, (zSign i x : ℂ) * ∑ y, (zSign i y : ℂ) * (Complex.normSq (M x y) : ℂ) := by
  simp only [rowField,Int.cast_sum,Int.cast_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem Encoder.projector_field_expectation (V : Encoder) (x : ActiveBits) :
    (∑ y, (rowField x y : ℂ) * (Complex.normSq (V.activeProjector x y) : ℂ)) =
      4 * (V.activeProjector x x)^2 := by
  have hs : star (V.activeProjector x x)=V.activeProjector x x := by
    have h := congrFun (congrFun (Frames.pi_hermitian V.magicFrames V.magicFrames_isometry) x) x
    exact h
  have hn : (Complex.normSq (V.activeProjector x x) : ℂ) = (V.activeProjector x x)^2 := by
    rw [Complex.normSq_eq_conj_mul_self,← Complex.star_def,hs,pow_two]
  have ht (y : ActiveBits) : (rowField x y : ℂ) * (Complex.normSq (V.activeProjector x y) : ℂ) =
      if y=x then 4 * (V.activeProjector x x)^2 else 0 := by
    by_cases hy : y=x
    · subst y
      simp [rowField_self,hn]
    · simp only [hy,if_false]
      by_cases hp : evenBits x ↔ evenBits y
      · by_cases hc : y=complementBits x
        · subst y
          rw [V.activeProjector_complement_zero]
          simp
        · rw [rowField_middle x y hp hy hc]
          simp
      · rw [V.activeProjector_parity_zero x y hp]
        simp
  simp_rw [ht]
  simp

/-- The physical spectral saturation step: Omega cannot connect rows at
Hamming distance one, including when the row norm is zero. -/
theorem Encoder.physicalOmega_distance_one_zero (V : Encoder) (x y : ActiveBits)
    (hxy : hamming x y=1) : V.physicalOmega x y=0 := by
  have hP : V.activeProjector.conjTranspose=V.activeProjector :=
    Frames.pi_hermitian V.magicFrames V.magicFrames_isometry
  have hm (i : Fin 4) :
      (∑ z, (zSign i z : ℂ) * (Complex.normSq (V.activeProjector x z) : ℂ)) +
      (∑ z, (zSign i z : ℂ) * (Complex.normSq (V.physicalOmega x z) : ℂ)) =
      2 * V.activeMu (single i 3) * V.activeProjector x x := by
    have h := congrFun (congrFun (V.physicalOmega_moment i) x) x
    have hp := diagonal_norm_compression V.activeProjector (fun z => (zSign i z : ℂ)) x
    rw [hP] at hp
    simp only [single_Z_diagonal,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at h
    rw [hp,diagonal_norm_compression] at h
    exact h
  have hfield : 4 * (V.activeProjector x x)^2 +
      (∑ z, (rowField x z : ℂ) * (Complex.normSq (V.physicalOmega x z) : ℂ)) =
      2 * (∑ i, V.activeMu (single i 3) * (zSign i x : ℂ)) * V.activeProjector x x := by
    rw [← V.projector_field_expectation,field_weighted_sum,field_weighted_sum,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ i : Fin 4, (zSign i x : ℂ) * (2 * V.activeMu (single i 3) * V.activeProjector x x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_add,hm]
      _ = _ := by
        simp only [Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hnorm : (∑ z, (Complex.normSq (V.physicalOmega x z) : ℂ))=V.activeProjector x x := by
    have h := congrFun (congrFun (Frames.omega_left V.magicFrames V.magicFrames_isometry) x) x
    simpa [Encoder.physicalOmega,Encoder.activeProjector,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Complex.star_def,Complex.mul_conj] using h
  have hzero : (∑ z, ((rowField x z : ℂ)+2) * (Complex.normSq (V.physicalOmega x z) : ℂ))=0 := by
    simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [hnorm]
    have hd := V.activeProjector_diagonal_mu x
    linear_combination hfield - 4 * V.activeProjector x x * hd
  have ht (z : ActiveBits) : ((rowField x z : ℂ)+2) * (Complex.normSq (V.physicalOmega x z) : ℂ) =
      if hamming x z=1 then 4 * (Complex.normSq (V.physicalOmega x z) : ℂ) else 0 := by
    by_cases hp : evenBits x ↔ evenBits z
    · rw [V.physicalOmega_parity_zero x z hp]
      simp
    · have hf := congrArg (fun a : ℤ => (a : ℂ)) (rowField_opposite x z hp)
      simp only [Int.cast_add,Int.cast_ofNat] at hf
      by_cases hd : hamming x z=1
      · norm_num [hd] at hf
        simp only [hd,if_true]
        rw [hf]
      · norm_num [hd] at hf
        simp [hd,hf]
  simp_rw [ht] at hzero
  have hr : (∑ z : ActiveBits, if hamming x z=1 then 4 * Complex.normSq (V.physicalOmega x z) else 0)=0 := by
    have he := congrArg Complex.re hzero
    simpa [apply_ite,Complex.mul_re] using he
  have hn (z : ActiveBits) : 0≤ (if hamming x z=1 then 4 * Complex.normSq (V.physicalOmega x z) else 0 : ℝ) := by
    split_ifs
    · exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
    · exact le_rfl
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hn z)).mp hr y (Finset.mem_univ y)
  simp only [hxy,if_true] at hz
  apply Complex.normSq_eq_zero.mp
  linarith

end Orbit2
