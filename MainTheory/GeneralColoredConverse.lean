import MainTheory.ColoredResidueArithmetic
import MainTheory.GeneralFrameTransport
import MainTheory.GeneralLiftOrder

/-!
# The converse of the general colored SSLP theorem

The finite data here retain every multiplicity and the actual orthonormal
frame.  A complete KL solution on that frame defines a code, and the
displayed finite gate has exactly the logical order prescribed by its colors.
-/

namespace MainTheory.GeneralColoredConverse

open ClassificationLevels GlobalClassificationBridge ColoredResidueArithmetic

noncomputable section

variable {n K d q m t : ℕ}

theorem exists_frame_amplitude_ne_zero (F : CodeSpec.OrthonormalFrame n K)
    (k : Fin K) : ∃ x, F.vec k x ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : F.vec k = 0 := funext h
  have hs := F.orthonormal k k
  rw [hz] at hs
  simp [SS.innerC] at hs

/-- A normalized eigenframe removes the common projective scalar. -/
theorem intrinsicClass_pow_eq_one_iff (F : CodeSpec.OrthonormalFrame n K)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame F))
    (lambda : Fin K → ℂ)
    (heigen : ∀ j, diagonalAction (u : LocalPhase n) (F.vec j) = lambda j • F.vec j)
    (j0 : Fin K) (hzero : lambda j0 = 1) (k : ℕ) :
    intrinsicClass (CodeProjector.ofFrame F) u ^ k = 1 ↔
      ∀ j, lambda j ^ k = 1 := by
  have hclass : intrinsicClass (CodeProjector.ofFrame F) u ^ k
      = intrinsicClass (CodeProjector.ofFrame F) (u ^ k) := by
    change (QuotientGroup.mk u) ^ k = QuotientGroup.mk (u ^ k)
    simp
  rw [hclass, ClassificationLevels.intrinsicClass_eq_one_iff,
    isProjectivelyTrivial_iff_sameProjectiveOnCode,
    CodeSpec.sameProjectiveOnCode_iff_frame]
  have hp (j : Fin K) :
      diagonalEnd ((u ^ k : diagonalSymmetryGroup (CodeProjector.ofFrame F)) : LocalPhase n)
        (F.vec j) = lambda j ^ k • F.vec j :=
    diagonalAction_pow_eigen (u : LocalPhase n) _ _ (heigen j) k
  constructor
  · rintro ⟨c, _, hc⟩
    have heq (j : Fin K) : lambda j ^ k = c := by
      obtain ⟨x, hx⟩ := exists_frame_amplitude_ne_zero F j
      have hs := (hp j).symm.trans (hc j)
      exact mul_right_cancel₀ hx (congrFun hs x)
    have hc1 : c = 1 := by simpa [hzero] using (heq j0).symm
    intro j
    exact (heq j).trans hc1
  · intro h
    exact ⟨1, one_ne_zero, fun j => by simpa [h j] using hp j⟩

/-- The unnormalized version, retaining the chosen representative's scalar. -/
theorem sameProjective_power_iff_ratios (F : CodeSpec.OrthonormalFrame n K)
    (u : LocalPhase n) (lambda : Fin K → ℂ)
    (heigen : ∀ j, diagonalAction u (F.vec j) = lambda j • F.vec j)
    (j0 : Fin K) (hzero : lambda j0 ≠ 0) (k : ℕ) :
    CodeSpec.SameProjectiveOnCode F (diagonalEnd (u ^ k)) LinearMap.id ↔
      ∀ j, (lambda j / lambda j0) ^ k = 1 := by
  rw [CodeSpec.sameProjectiveOnCode_iff_frame]
  have hp (j : Fin K) : diagonalEnd (u ^ k) (F.vec j) = lambda j ^ k • F.vec j :=
    diagonalAction_pow_eigen u _ _ (heigen j) k
  constructor
  · rintro ⟨c, hc0, hc⟩
    have heq (j : Fin K) : lambda j ^ k = c := by
      obtain ⟨x, hx⟩ := exists_frame_amplitude_ne_zero F j
      exact mul_right_cancel₀ hx (congrFun ((hp j).symm.trans (hc j)) x)
    intro j
    rw [div_pow, heq j, heq j0, div_self hc0]
  · intro h
    refine ⟨lambda j0 ^ k, pow_ne_zero _ hzero, fun j => ?_⟩
    have heq : lambda j ^ k = lambda j0 ^ k := by
      exact (div_eq_one_iff_eq (pow_ne_zero _ hzero)).1 (by simpa [div_pow] using h j)
    simpa [heq] using hp j

/-- General colored SSLP outer data and the actual vectors in every fiber. -/
structure ColoredFrame (n K q m t : ℕ) [NeZero q] [NeZero m] where
  modulus_dvd : m ∣ q
  angle : Fin n → ZMod q
  primitive : Gate.Primitive q angle
  sorted : Monotone fun j => (angle j).val
  rank : Fin t → ℕ
  rank_pos : ∀ alpha, 0 < rank alpha
  reindex : Fin K ≃ (Σ alpha, Fin (rank alpha))
  frame : CodeSpec.OrthonormalFrame n K
  base : Fin t
  color : Fin t → ZMod m
  color_zero : color base = 0
  color_distinct : Function.Injective color
  color_primitive : Gate.Primitive m color
  fiber : ∀ j, SS.SSConditionState angle
    (scaledColor q (color (reindex j).1)) (frame.vec j)

namespace ColoredFrame

variable [NeZero q] [NeZero m] (S : ColoredFrame n K q m t)

theorem sum_rank : ∑ alpha, S.rank alpha = K := by
  have h := Fintype.card_congr S.reindex
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h.symm

include S in
theorem positiveRank : 0 < K := by
  have hi : Nonempty (Fin K) :=
    ⟨S.reindex.symm ⟨S.base, ⟨0, S.rank_pos S.base⟩⟩⟩
  simpa only [Fintype.card_fin] using Fintype.card_pos_iff.2 hi

theorem colors_gcd : Nat.gcd m (Finset.univ.gcd fun alpha => (S.color alpha).val) = 1 :=
  (primitive_iff_gcd_eq_one S.color).1 S.color_primitive

include S in
theorem sectorCount_le_rank : t ≤ K := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (f := fun _ : Fin t => 1) (g := S.rank) (fun alpha _ => S.rank_pos alpha)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, S.sum_rank] using h

include S in
theorem sectorCount_le_order : t ≤ m := by
  simpa only [Fintype.card_fin, ZMod.card] using Fintype.card_le_of_injective S.color S.color_distinct

include S in
theorem two_le_sectorCount (hm : 2 ≤ m) : 2 ≤ t := by
  by_contra ht
  have hsame : ∀ alpha : Fin t, alpha = S.base := by
    intro alpha
    apply Fin.ext
    have ha := alpha.isLt
    have hb := S.base.isLt
    omega
  have hall : ∀ alpha, S.color alpha = 0 := fun alpha => by rw [hsame alpha, S.color_zero]
  have hm1 := S.color_primitive m dvd_rfl (fun alpha => by simp [hall alpha])
  omega

def exactCode (hdist : SS.HasDistance S.frame.vec d) : CodeSpec.ExactCode n K d where
  positiveRank := S.positiveRank
  frame := S.frame
  hasDistance := hdist

def eigenvalue (zeta : ℂ) (j : Fin K) : ℂ :=
  Cyclic.chi zeta (scaledColor q (S.color (S.reindex j).1))

theorem eigen (zeta : ℂ) (j : Fin K) :
    Gate.gate zeta S.angle (S.frame.vec j) = S.eigenvalue zeta j • S.frame.vec j :=
  PhaseSector.eigen_of_ssCondition zeta S.angle (S.frame.vec j) _ (S.fiber j)

def symmetry (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    diagonalSymmetryGroup (CodeProjector.ofFrame S.frame) := by
  refine finiteOrderSymmetryOfCodePreserving S.frame
    (finiteLocalPhase zeta hzeta S.angle) (Nat.pos_of_ne_zero (NeZero.ne q))
    (finiteLocalPhase_pow_order zeta hzeta S.angle) ?_
  apply (CodeSpec.codePreserving_iff_frame S.frame _).2
  intro j
  rw [diagonalEnd_apply, diagonalAction_finiteLocalPhase, S.eigen]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

@[simp] theorem symmetry_coe (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    (S.symmetry zeta hzeta : LocalPhase n) = finiteLocalPhase zeta hzeta S.angle := rfl

theorem class_pow_iff (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) (k : ℕ) :
    intrinsicClass (CodeProjector.ofFrame S.frame) (S.symmetry zeta hzeta) ^ k = 1
      ↔ m ∣ k := by
  let j0 := S.reindex.symm ⟨S.base, ⟨0, S.rank_pos S.base⟩⟩
  have hj0 : S.eigenvalue zeta j0 = 1 := by
    simp [eigenvalue, j0, S.color_zero]
  have heigen (j : Fin K) :
      diagonalAction (S.symmetry zeta hzeta : LocalPhase n) (S.frame.vec j)
        = S.eigenvalue zeta j • S.frame.vec j := by
    rw [S.symmetry_coe, diagonalAction_finiteLocalPhase]
    exact S.eigen zeta j
  rw [intrinsicClass_pow_eq_one_iff S.frame (S.symmetry zeta hzeta)
    (S.eigenvalue zeta) heigen j0 hj0 k]
  have hpow (j : Fin K) : S.eigenvalue zeta j ^ k = 1 ↔
      (k : ZMod q) * scaledColor q (S.color (S.reindex j).1) = 0 := by
    rw [eigenvalue, Cyclic.chi_pow zeta hzeta, Cyclic.chi_eq_one_iff zeta hzeta,
      nsmul_eq_mul]
  simp only [hpow]
  rw [← scaled_exact_joint_order S.modulus_dvd S.color S.color_primitive k]
  constructor
  · intro h alpha
    simpa using h (S.reindex.symm ⟨alpha, ⟨0, S.rank_pos alpha⟩⟩)
  · intro h j
    exact h (S.reindex j).1

theorem orderOf_class (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q) :
    orderOf (intrinsicClass (CodeProjector.ofFrame S.frame) (S.symmetry zeta hzeta)) = m := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((S.class_pow_iff zeta hzeta m).2 dvd_rfl)
  · exact (S.class_pow_iff zeta hzeta _).1 (pow_orderOf_eq_one _)

/-- Full KL completion gives the asserted rank, distance, and exact logical order. -/
theorem sslp_converse (hdist : SS.HasDistance S.frame.vec d) (hm : 2 ≤ m) :
    ∃ (C : CodeSpec.ExactCode n K d)
      (u : diagonalSymmetryGroup (exactCodeProjector C)),
      C.frame = S.frame ∧
      (u : LocalPhase n) = finiteLocalPhase
        (D3NormalizedFiniteToReal.canonicalRoot q)
        (D3NormalizedFiniteToReal.canonicalRoot_primitive q) S.angle ∧
      orderOf (intrinsicClass (exactCodeProjector C) u) = m ∧
      intrinsicClass (exactCodeProjector C) u ≠ 1 := by
  let zeta := D3NormalizedFiniteToReal.canonicalRoot q
  let hzeta := D3NormalizedFiniteToReal.canonicalRoot_primitive q
  refine ⟨S.exactCode hdist, S.symmetry zeta hzeta, rfl, rfl,
    S.orderOf_class zeta hzeta, ?_⟩
  intro h
  change intrinsicClass (CodeProjector.ofFrame S.frame) (S.symmetry zeta hzeta) = 1 at h
  have heq := S.orderOf_class zeta hzeta
  rw [h, orderOf_one] at heq
  omega

end ColoredFrame

end

end MainTheory.GeneralColoredConverse
