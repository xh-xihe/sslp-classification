import MainTheory.RankTwo
import MainTheory.PhaseSectorBridge
import SixQubit.CodeEquiv

/-!
# Honest bridges to the global rank-two normal form

`RankTwo.normal_form_core` proves the arithmetic/geometric part of the
two-fibre theorem for a *supplied* finite gate and two supplied eigenvectors.
This file connects that result to `CodeSpec.ExactCode` without pretending that
the two genuinely global inputs already follow from the current library.

There are two such inputs.

* `PhaseSectorBridge.LogicalSectorResolution` is the output of the missing
  finite-dimensional spectral extraction theorem.  Once it is supplied,
  distance at least two really is used: Knill--Laflamme gives `ZDetects`, and
  `FiniteLift.qualitative_finite_lift` constructs a primitive rational lift.
* `FiniteGeneratorResolution` is the discrete finite-gate version of that
  output.  It records a primitive physical lift, an orthonormal eigenframe
  spanning the actual code, and distinct logical eigenvalues.  These are
  semantic data, not the desired two-fibre conclusion.  From them the kernel
  proves code preservation, local-`X` two-fibre reduction, the exact logical
  order, its divisibility by the physical order, coprime-power normalization
  to the `q / m` fibre, and preservation of the exact physical order.

What is intentionally *not* proved here is finiteness of the full intrinsic
projective diagonal group, spectral extraction from an arbitrary preserving
unitary, or conversion of the rational lift into the discrete structure below.
Consequently this module does not claim the full group is cyclic.  Once a
faithful character of a finite group is available, that last algebraic step is
already `Cyclic.isCyclic_of_faithful`.
-/

namespace MainTheory.RankTwoGlobal

open SS
open MainTheory
open MainTheory.PhaseSectorFull

noncomputable section

/-! ## Exact-code to qualitative finite-lift bridge -/

/-- A supplied complete logical sector resolution of an exact rank-two code
really enters the finite-lift theorem through its Knill--Laflamme equations.
The extra hypothesis `2 <= sectorCount` is the semantic nontriviality condition
that the restriction has at least two distinct logical eigenvalues. -/
theorem finiteLift_of_rankTwo_resolution {n d : ℕ} {θ : Fin n → ℝ}
    {C : CodeSpec.ExactCode n 2 d}
    (R : PhaseSectorBridge.LogicalSectorResolution C θ)
    (hd : 2 ≤ d) (hnontrivial : 2 ≤ R.sectorCount) :
    ∃ L : FiniteLift.RationalColoredLift R.sectors,
      2 ≤ L.order ∧
      FiniteLift.SameProjectiveSectorAction R.sectors
        (fun j ↦ (L.physical j : ℝ)) := by
  obtain ⟨L, hq, hprojective, _⟩ :=
    FiniteLift.qualitative_finite_lift R.sectors
      (R.zDetects hd) hnontrivial
  exact ⟨L, hq, hprojective⟩

/-! ## A discrete primitive generator spanning the actual code -/

/-- The finite-gate spectral data which the unfinished global arguments must
produce from an arbitrary nontrivial projective diagonal symmetry.

Unlike an assumption named "normal form", these fields are pre-normalization
semantic facts: the displayed pair is merely an arbitrary orthonormal
eigenbasis of the actual code, and its two residues have not been prescribed. -/
structure FiniteGeneratorResolution {n d : ℕ}
    (C : CodeSpec.ExactCode n 2 d) (q : ℕ) [NeZero q] where
  zeta : ℂ
  primitiveRoot : IsPrimitiveRoot zeta q
  angle : Fin n → ZMod q
  primitive : Gate.Primitive q angle
  eigenFrame : CodeSpec.OrthonormalFrame n 2
  span_eq : CodeSpec.codeSpan C.frame = CodeSpec.codeSpan eigenFrame
  eigenvalue : Fin 2 → ℂ
  eigen : ∀ k, Gate.gate zeta angle (eigenFrame.vec k) =
    fun x ↦ eigenvalue k * eigenFrame.vec k x
  projectively_nontrivial : eigenvalue 0 ≠ eigenvalue 1

/-- The finite diagonal gate as a complex-linear endomorphism. -/
def finiteGateEnd {n q : ℕ} (zeta : ℂ)
    (a : Fin n → ZMod q) : Module.End ℂ (SS.State n ℂ) where
  toFun := Gate.gate zeta a
  map_add' := by
    intro phi chi
    funext x
    simp [Gate.gate]
    ring
  map_smul' := by
    intro c phi
    funext x
    simp [Gate.gate]
    ring

@[simp] theorem finiteGateEnd_apply {n q : ℕ} [NeZero q]
    (zeta : ℂ) (a : Fin n → ZMod q) (phi : SS.State n ℂ) :
    finiteGateEnd zeta a phi = Gate.gate zeta a phi := rfl

/-- The supplied eigenframe and span equality are sufficient to prove, in the
standard `CodeSpec` sense, that the finite gate preserves the actual code. -/
theorem FiniteGeneratorResolution.codePreserving {n d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    (G : FiniteGeneratorResolution C q) :
    CodeSpec.CodePreserving C.frame (finiteGateEnd G.zeta G.angle) := by
  intro phi hphi
  rw [G.span_eq] at hphi ⊢
  refine Submodule.span_induction
    (p := fun psi _ ↦ finiteGateEnd G.zeta G.angle psi ∈
      CodeSpec.codeSpan G.eigenFrame) ?_ ?_ ?_ ?_ hphi
  · rintro _ ⟨k, rfl⟩
    rw [finiteGateEnd_apply, G.eigen k]
    exact (CodeSpec.codeSpan G.eigenFrame).smul_mem (G.eigenvalue k)
      (Submodule.subset_span (Set.mem_range_self k))
  · change finiteGateEnd G.zeta G.angle 0 ∈ _
    rw [map_zero]
    exact (CodeSpec.codeSpan G.eigenFrame).zero_mem
  · intro x y _ _ hx hy
    change finiteGateEnd G.zeta G.angle (x + y) ∈ _
    rw [map_add]
    exact (CodeSpec.codeSpan G.eigenFrame).add_mem hx hy
  · intro c x _ hx
    change finiteGateEnd G.zeta G.angle (c • x) ∈ _
    rw [map_smul]
    exact (CodeSpec.codeSpan G.eigenFrame).smul_mem c hx

private theorem exists_amplitude_ne_zero {n : ℕ}
    (F : CodeSpec.OrthonormalFrame n 2) (k : Fin 2) :
    ∃ x, F.vec k x ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : F.vec k = 0 := funext h
  have hself := F.orthonormal k k
  rw [hz] at hself
  simp [SS.innerC] at hself

/-- Local `X` conjugation is a permutation of computational basis
coordinates, hence preserves every logical inner product. -/
theorem innerC_bxor {n : ℕ} (x0 : SS.BitString n)
    (c e : SS.State n ℂ) :
    SS.innerC (fun s ↦ c (SS.bxor s x0))
        (fun s ↦ e (SS.bxor s x0)) = SS.innerC c e := by
  change (∑ s : SS.BitString n,
      star (c (SS.bxor s x0)) * e (SS.bxor s x0)) =
    ∑ s : SS.BitString n, star (c s) * e s
  exact SS.MacWilliams.sum_bxor_reindex x0
    (fun s ↦ star (c s) * e s)

/-- Bridge-form error detection is equivalent to the repository's genuine KL
predicate at every weight cutoff, not only at the distance-three specialization
used elsewhere in `CodeEquiv`. -/
theorem detects_iff_raw {n : ℕ} (p : Fin 2 → SS.State n ℂ) (w : ℕ) :
    SS.Detects p w ↔ SixQubit.CodeEquiv.DetectsRaw p w := by
  constructor
  · intro h x z hw
    exact (SixQubit.CodeEquiv.klCondition_iff p ⟨x, z⟩).mp
      (h ⟨x, z⟩ hw)
  · intro h P hw
    exact (SixQubit.CodeEquiv.klCondition_iff p P).mpr
      (h P.x P.z hw)

/-- Local `X` conjugation preserves the full Knill--Laflamme predicate at an
arbitrary requested distance. -/
theorem hasDistance_bxor {n d : ℕ} (p : Fin 2 → SS.State n ℂ)
    (x0 : SS.BitString n) (h : SS.HasDistance p d) :
    SS.HasDistance (fun k s ↦ p k (SS.bxor s x0)) d := by
  apply (detects_iff_raw _ _).mpr
  exact SixQubit.CodeEquiv.detectsRaw_flipAct x0
    ((detects_iff_raw _ _).mp h)

/-! ## Scaling by a coprime power -/

theorem weight_unit_mul {n q : ℕ}
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q) (x : SS.BitString n) :
    SS.weight (fun j ↦ (u : ZMod q) * a j) x =
      (u : ZMod q) * SS.weight a x := by
  rw [SS.weight, SS.weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ssConditionState_unit_mul {n q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q) (r : ZMod q)
    (c : SS.State n ℂ) (h : SS.SSConditionState a r c) :
    SS.SSConditionState (fun j ↦ (u : ZMod q) * a j)
      ((u : ZMod q) * r) c := by
  intro x hx
  rw [weight_unit_mul, h x hx]

/-- Multiplication of the angle vector by a unit leaves the exact physical
order equal to `q`.  This proves the operational content needed when replacing
the generator by a coprime power, without silently assuming that the new gate
is still primitive. -/
theorem scaledGate_pow_eq_one_iff {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hz : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (hprim : Gate.Primitive q a)
    (u : (ZMod q)ˣ) (k : ℕ) :
    (∀ s : SS.BitString n,
      Gate.diag zeta (fun j ↦ (u : ZMod q) * a j) s ^ k = 1) ↔ q ∣ k := by
  constructor
  · intro hk
    apply Gate.dvd_of_forall_mul_eq_zero a hprim k
    intro j
    have hj := hk (SS.stdBasis j)
    rw [Gate.diag_pow] at hj
    have hdvd : q ∣ k *
        (SS.weight (fun i ↦ (u : ZMod q) * a i) (SS.stdBasis j)).val :=
      (hz.pow_eq_one_iff_dvd _).1 hj
    have hscaled : (k : ZMod q) * ((u : ZMod q) * a j) = 0 := by
      have hzero : ((k *
          (SS.weight (fun i ↦ (u : ZMod q) * a i)
            (SS.stdBasis j)).val : ℕ) : ZMod q) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      push_cast at hzero
      rw [ZMod.natCast_val, ZMod.cast_id, Gate.weight_stdBasis] at hzero
      exact hzero
    have hu : ((↑(u⁻¹) : ZMod q) * (u : ZMod q)) = 1 := by simp
    calc
      (k : ZMod q) * a j = 1 * ((k : ZMod q) * a j) := by simp
      _ = ((↑(u⁻¹) : ZMod q) * (u : ZMod q)) *
          ((k : ZMod q) * a j) := by rw [hu]
      _ = (↑(u⁻¹) : ZMod q) *
          ((k : ZMod q) * ((u : ZMod q) * a j)) := by ring
      _ = 0 := by rw [hscaled, mul_zero]
  · intro hk s
    rw [Gate.diag_pow]
    exact (hz.pow_eq_one_iff_dvd _).2 (Dvd.dvd.mul_right hk _)

/-! ## The derived two-fibre certificate -/

/-- Every field is a derived conclusion.  In particular `unit` is not a
normal-form hypothesis: it is constructed by
`RankTwo.exists_unit_mul_eq_div`. -/
structure TwoFiberCertificate {n d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    (G : FiniteGeneratorResolution C q) where
  x0 : SS.BitString n
  y0 : SS.BitString n
  /-- The shift is by a point of the first logical word's own support.  This is
  how `finiteGenerator_twoFiber` chooses it, and recording it is what lets a
  later argument say that the *zero* word lies in the normalized support --
  which is where a normalized support's affine and linear ranks agree. -/
  base_supported : G.eigenFrame.vec 0 x0 ≠ 0
  gap : ZMod q
  leftFiber : SS.SSConditionState (Normalize.flip G.angle x0) 0
    (fun s ↦ G.eigenFrame.vec 0 (SS.bxor s x0))
  rightFiber : SS.SSConditionState (Normalize.flip G.angle x0) gap
    (fun s ↦ G.eigenFrame.vec 1 (SS.bxor s x0))
  ratio_eq : G.eigenvalue 1 / G.eigenvalue 0 = Cyclic.chi G.zeta gap
  ratio_order : ∀ k : ℕ,
    (G.eigenvalue 1 / G.eigenvalue 0) ^ k = 1 ↔ addOrderOf gap ∣ k
  gap_ne_zero : gap ≠ 0
  logicalOrder : ℕ
  logicalOrder_eq : logicalOrder = addOrderOf gap
  two_le_logicalOrder : 2 ≤ logicalOrder
  logicalOrder_dvd_physical : logicalOrder ∣ q
  two_le_physicalOrder : 2 ≤ q
  normalizedOrthonormal : ∀ i j : Fin 2,
    SS.innerC
        (fun s ↦ G.eigenFrame.vec i (SS.bxor s x0))
        (fun s ↦ G.eigenFrame.vec j (SS.bxor s x0)) =
      if i = j then 1 else 0
  normalizedHasDistance :
    SS.HasDistance
      (fun i s ↦ G.eigenFrame.vec i (SS.bxor s x0)) d
  unit : (ZMod q)ˣ
  unit_normalizes_gap :
    (unit : ZMod q) * gap = (((q / logicalOrder : ℕ) : ZMod q))
  normalizedLeft :
    SS.SSConditionState
      (fun j ↦ (unit : ZMod q) * Normalize.flip G.angle x0 j) 0
      (fun s ↦ G.eigenFrame.vec 0 (SS.bxor s x0))
  normalizedRight :
    SS.SSConditionState
      (fun j ↦ (unit : ZMod q) * Normalize.flip G.angle x0 j)
      (((q / logicalOrder : ℕ) : ZMod q))
      (fun s ↦ G.eigenFrame.vec 1 (SS.bxor s x0))
  normalizedLeftEigen :
    Gate.gate G.zeta
      (fun j ↦ (unit : ZMod q) * Normalize.flip G.angle x0 j)
      (fun s ↦ G.eigenFrame.vec 0 (SS.bxor s x0)) =
      fun s ↦ (1 : ℂ) * G.eigenFrame.vec 0 (SS.bxor s x0)
  normalizedRightEigen :
    Gate.gate G.zeta
      (fun j ↦ (unit : ZMod q) * Normalize.flip G.angle x0 j)
      (fun s ↦ G.eigenFrame.vec 1 (SS.bxor s x0)) =
      fun s ↦ Cyclic.chi G.zeta
        (((q / logicalOrder : ℕ) : ZMod q)) *
          G.eigenFrame.vec 1 (SS.bxor s x0)
  normalizedProjectiveOrder : ∀ k : ℕ,
    Cyclic.chi G.zeta (((q / logicalOrder : ℕ) : ZMod q)) ^ k = 1 ↔
      logicalOrder ∣ k
  normalizedPhysicalOrder : ∀ k : ℕ,
    (∀ s : SS.BitString n,
      Gate.diag G.zeta
        (fun j ↦ (unit : ZMod q) * Normalize.flip G.angle x0 j) s ^ k = 1) ↔
      q ∣ k

/-- The code-level, normalized two-fibre conclusion for a supplied primitive
finite generator resolution. -/
theorem finiteGenerator_twoFiber {n d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    (G : FiniteGeneratorResolution C q) : Nonempty (TwoFiberCertificate G) := by
  obtain ⟨x0, hx0⟩ := exists_amplitude_ne_zero G.eigenFrame 0
  obtain ⟨y0, hy0⟩ := exists_amplitude_ne_zero G.eigenFrame 1
  obtain ⟨delta, hdeltaEq, hleft, hright, hratio, hratioOrder⟩ :=
    RankTwo.normal_form_core G.zeta G.primitiveRoot G.angle
      (G.eigenFrame.vec 0) (G.eigenFrame.vec 1)
      (G.eigenvalue 0) (G.eigenvalue 1)
      (G.eigen 0) (G.eigen 1) x0 y0 hx0 hy0
  have hgap : SS.weight G.angle y0 - SS.weight G.angle x0 ≠ 0 :=
    RankTwo.gap_ne_zero G.zeta G.angle
      (G.eigenFrame.vec 0) (G.eigenFrame.vec 1)
      (G.eigenvalue 0) (G.eigenvalue 1)
      (G.eigen 0) (G.eigen 1) x0 y0 hx0 hy0
      G.projectively_nontrivial
  have hdelta : delta ≠ 0 := by
    rw [hdeltaEq]
    exact hgap
  let m := addOrderOf delta
  have hmne : m ≠ 1 := by
    intro hm
    exact hdelta (AddMonoid.addOrderOf_eq_one_iff.mp hm)
  have hmpos : 0 < m := addOrderOf_pos delta
  have hm2 : 2 ≤ m := by omega
  have hmq : m ∣ q := Cyclic.addOrderOf_dvd_card delta
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : 2 ≤ q := hm2.trans (Nat.le_of_dvd hqpos hmq)
  have heigenDistance : SS.HasDistance G.eigenFrame.vec d :=
    CodeSpec.hasDistance_of_codeSpan_eq C.frame G.eigenFrame
      G.span_eq C.hasDistance
  obtain ⟨u, hu⟩ := RankTwo.exists_unit_mul_eq_div delta m rfl
  have hnleft := ssConditionState_unit_mul u _ _ _ hleft
  have hnright := ssConditionState_unit_mul u _ _ _ hright
  have hnleft' : SS.SSConditionState
      (fun j ↦ (u : ZMod q) * Normalize.flip G.angle x0 j) 0
      (fun s ↦ G.eigenFrame.vec 0 (SS.bxor s x0)) := by
    simpa using hnleft
  have hnright' : SS.SSConditionState
      (fun j ↦ (u : ZMod q) * Normalize.flip G.angle x0 j)
      (((q / m : ℕ) : ZMod q))
      (fun s ↦ G.eigenFrame.vec 1 (SS.bxor s x0)) := by
    simpa [hu] using hnright
  obtain ⟨hneigen0, hneigen1, hnorder⟩ :=
    RankTwo.order_of_two_fiber G.zeta G.primitiveRoot m hmq
      (fun j ↦ (u : ZMod q) * Normalize.flip G.angle x0 j)
      (fun s ↦ G.eigenFrame.vec 0 (SS.bxor s x0))
      (fun s ↦ G.eigenFrame.vec 1 (SS.bxor s x0))
      hnleft' hnright'
  have hflipPrimitive : Gate.Primitive q (Normalize.flip G.angle x0) :=
    Normalize.primitive_flip G.angle x0 G.primitive
  exact ⟨{
    x0 := x0
    y0 := y0
    base_supported := hx0
    gap := delta
    leftFiber := hleft
    rightFiber := hright
    ratio_eq := hratio
    ratio_order := hratioOrder
    gap_ne_zero := hdelta
    logicalOrder := m
    logicalOrder_eq := rfl
    two_le_logicalOrder := hm2
    logicalOrder_dvd_physical := hmq
    two_le_physicalOrder := hq2
    normalizedOrthonormal := by
      intro i j
      rw [innerC_bxor]
      exact G.eigenFrame.orthonormal i j
    normalizedHasDistance :=
      hasDistance_bxor G.eigenFrame.vec x0 heigenDistance
    unit := u
    unit_normalizes_gap := hu
    normalizedLeft := hnleft'
    normalizedRight := hnright'
    normalizedLeftEigen := hneigen0
    normalizedRightEigen := hneigen1
    normalizedProjectiveOrder := hnorder
    normalizedPhysicalOrder :=
      scaledGate_pow_eq_one_iff G.zeta G.primitiveRoot
        (Normalize.flip G.angle x0) hflipPrimitive u }⟩

end

end MainTheory.RankTwoGlobal
