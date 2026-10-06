import MainTheory.GeneralColoredConverse
import MainTheory.SortedNormalForm

/-! # Normalizing a primitive finite gate with arbitrarily many phase sectors -/

namespace MainTheory.GeneralColoredNormalForm

open ClassificationLevels GlobalClassificationBridge GeneralColoredConverse
open ColoredResidueArithmetic PermutationSemanticTransport

noncomputable section

variable {n K d q m t : ℕ} [NeZero q]

/-- A finite spectral decomposition tied to the actual code, before normalization. -/
structure FiniteSectors (C : CodeSpec.ExactCode n K d) (q t : ℕ) [NeZero q] where
  angle : Fin n → ZMod q
  primitive : Gate.Primitive q angle
  rank : Fin t → ℕ
  rank_pos : ∀ alpha, 0 < rank alpha
  reindex : Fin K ≃ (Σ alpha, Fin (rank alpha))
  frame : CodeSpec.OrthonormalFrame n K
  span_eq : CodeSpec.codeSpan C.frame = CodeSpec.codeSpan frame
  base : Fin t
  residue : Fin t → ZMod q
  residue_distinct : Function.Injective residue
  fiber : ∀ j, SS.SSConditionState angle (residue (reindex j).1) (frame.vec j)

namespace FiniteSectors

variable {C : CodeSpec.ExactCode n K d} (R : FiniteSectors C q t)

def root (_R : FiniteSectors C q t) : ℂ := D3NormalizedFiniteToReal.canonicalRoot q

theorem root_primitive : IsPrimitiveRoot R.root q :=
  D3NormalizedFiniteToReal.canonicalRoot_primitive q

def localPhase : LocalPhase n := finiteLocalPhase R.root R.root_primitive R.angle

def eigenvalue (j : Fin K) : ℂ := Cyclic.chi R.root (R.residue (R.reindex j).1)

theorem eigen (j : Fin K) :
    diagonalAction R.localPhase (R.frame.vec j) = R.eigenvalue j • R.frame.vec j := by
  rw [localPhase, diagonalAction_finiteLocalPhase]
  exact PhaseSector.eigen_of_ssCondition R.root R.angle (R.frame.vec j) _ (R.fiber j)

def symmetry : diagonalSymmetryGroup (exactCodeProjector C) := by
  refine finiteOrderSymmetryOfCodePreserving C.frame R.localPhase
    (Nat.pos_of_ne_zero (NeZero.ne q)) (finiteLocalPhase_pow_order _ _ _) ?_
  intro phi hphi
  rw [R.span_eq] at hphi ⊢
  apply ((CodeSpec.codePreserving_iff_frame R.frame (diagonalEnd R.localPhase)).2 ?_) phi hphi
  intro j
  rw [diagonalEnd_apply, R.eigen]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

@[simp] theorem symmetry_coe : (R.symmetry : LocalPhase n) = R.localPhase := rfl

def intrinsic : IntrinsicGroup C := intrinsicClass (exactCodeProjector C) R.symmetry

def delta (alpha : Fin t) : ZMod q := R.residue alpha - R.residue R.base

theorem class_pow_iff (k : ℕ) :
    R.intrinsic ^ k = 1 ↔ ∀ alpha, (k : ZMod q) * R.delta alpha = 0 := by
  have hclass : R.intrinsic ^ k
      = intrinsicClass (exactCodeProjector C) (R.symmetry ^ k) := by
    change (QuotientGroup.mk R.symmetry) ^ k = QuotientGroup.mk (R.symmetry ^ k)
    simp
  rw [hclass, intrinsicClass_eq_one_iff,
    isProjectivelyTrivial_iff_sameProjectiveOnCode,
    sameProjectiveOnCode_congr_span C.frame R.frame R.span_eq]
  let j0 := R.reindex.symm ⟨R.base, ⟨0, R.rank_pos R.base⟩⟩
  have hz : R.eigenvalue j0 ≠ 0 := Cyclic.chi_ne_zero R.root R.root_primitive _
  change CodeSpec.SameProjectiveOnCode R.frame (diagonalEnd (R.localPhase ^ k))
    LinearMap.id ↔ _
  rw [sameProjective_power_iff_ratios R.frame R.localPhase R.eigenvalue R.eigen j0 hz]
  have hratio (j : Fin K) : R.eigenvalue j / R.eigenvalue j0
      = Cyclic.chi R.root (R.delta (R.reindex j).1) := by
    simp only [eigenvalue, j0, Equiv.apply_symm_apply, delta]
    exact (Cyclic.chi_sub R.root R.root_primitive _ _).symm
  simp only [hratio, Cyclic.chi_pow R.root R.root_primitive,
    Cyclic.chi_eq_one_iff R.root R.root_primitive, nsmul_eq_mul]
  constructor
  · intro h alpha
    simpa only [Equiv.apply_symm_apply] using
      h (R.reindex.symm ⟨alpha, ⟨0, R.rank_pos alpha⟩⟩)
  · intro h j
    exact h (R.reindex j).1

theorem order_dvd : orderOf R.intrinsic ∣ q := by
  apply orderOf_dvd_of_pow_eq_one
  apply (R.class_pow_iff q).2
  intro alpha
  simp

theorem order_pos : 0 < orderOf R.intrinsic :=
  Nat.pos_of_dvd_of_pos R.order_dvd (Nat.pos_of_ne_zero (NeZero.ne q))

theorem exists_normalized [NeZero m] (hm : orderOf R.intrinsic = m) :
    ∃ (S : ColoredFrame n K q m t) (x0 : SS.BitString n) (sigma : Equiv.Perm (Fin n)),
      S.rank = R.rank ∧ HEq S.reindex R.reindex ∧ S.base = R.base ∧
      S.angle = permAngle sigma (Normalize.flip R.angle x0) ∧
      (∀ j s, S.frame.vec j s =
        R.frame.vec j (SS.bxor (SixQubit.CodeEquiv.permStr sigma s) x0)) ∧
      (∀ alpha, scaledColor q (S.color alpha) = R.delta alpha) ∧
      SS.HasDistance S.frame.vec d := by
  have hmq : m ∣ q := by simpa only [hm] using R.order_dvd
  have hkill : ∀ alpha, (m : ZMod q) * R.delta alpha = 0 := by
    apply (R.class_pow_iff m).1
    rw [← hm]
    exact pow_orderOf_eq_one _
  choose gamma hgamma huniq using fun alpha => existsUnique_scaledColor hmq (R.delta alpha) (hkill alpha)
  have hg0 : gamma R.base = 0 := by
    apply scaledColor_injective hmq
    simp [hgamma, delta]
  have hginj : Function.Injective gamma := by
    intro a b h
    apply R.residue_distinct
    have heq : R.delta a = R.delta b := by rw [← hgamma a, ← hgamma b, h]
    simpa only [delta, sub_left_inj] using heq
  have hgprim : Gate.Primitive m gamma := by
    apply (primitive_iff_exact_joint_order gamma).2
    intro k
    constructor
    · intro hk
      have hp : R.intrinsic ^ k = 1 := by
        apply (R.class_pow_iff k).2
        intro alpha
        rw [← hgamma alpha]
        exact (mul_scaledColor_eq_zero_iff hmq _ _).2 (hk alpha)
      simpa only [← hm] using orderOf_dvd_of_pow_eq_one hp
    · intro hk alpha
      rw [(ZMod.natCast_eq_zero_iff _ _).2 hk, zero_mul]
  let j0 := R.reindex.symm ⟨R.base, ⟨0, R.rank_pos R.base⟩⟩
  obtain ⟨x0, hx0⟩ := exists_frame_amplitude_ne_zero R.frame j0
  have hbase : SS.weight R.angle x0 = R.residue R.base := by
    simpa only [j0, Equiv.apply_symm_apply] using R.fiber j0 x0 hx0
  let sigma := SortedForm.sortingPerm (Normalize.flip R.angle x0)
  let F := PermutationFrameBridge.permFrame (IntrinsicTransport.shiftFrame R.frame x0) sigma
  let S : ColoredFrame n K q m t := {
    modulus_dvd := hmq
    angle := permAngle sigma (Normalize.flip R.angle x0)
    primitive := primitive_permAngle sigma _ (Normalize.primitive_flip _ _ R.primitive)
    sorted := SortedForm.monotone_permAngle_sortingPerm _
    rank := R.rank
    rank_pos := R.rank_pos
    reindex := R.reindex
    frame := F
    base := R.base
    color := gamma
    color_zero := hg0
    color_distinct := hginj
    color_primitive := hgprim
    fiber := by
      intro j
      rw [hgamma]
      change SS.SSConditionState _ _ (SixQubit.CodeEquiv.permAct sigma
        (fun s => R.frame.vec j (SS.bxor s x0)))
      apply ssConditionState_permAct sigma
      have h := Normalize.ssCondition_bxor R.angle x0 _ (R.frame.vec j) (R.fiber j)
      simpa only [hbase, delta] using h }
  refine ⟨S, x0, sigma, rfl, HEq.rfl, rfl, rfl, fun _ _ => rfl, hgamma, ?_⟩
  exact GeneralFrameTransport.hasDistance_permAct sigma _
    (GeneralFrameTransport.hasDistance_bxor R.frame.vec x0
      (CodeSpec.hasDistance_of_codeSpan_eq C.frame R.frame R.span_eq C.hasDistance))

end FiniteSectors

end

end MainTheory.GeneralColoredNormalForm
