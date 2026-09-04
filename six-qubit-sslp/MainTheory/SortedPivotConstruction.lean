import MainTheory.SortedPivot
import MainTheory.D3BoundedNormalForm

/-!
# Building the pivot where the normal form is built

`SortedPivot` reduced the coarse-filter entry to one statement about a sorted
normal form: its left support, restricted to the coordinates its angle
touches, spans.  `SortedPivot.span_rqpoint_of_shifted_nonsingular` transports
that across the cube shift separating the normal form from the fresh sparse
pivot.  What is left, and what this file does, is name the two sides.

* The **fresh** side is `frameFreshSparsePhase T`, whose `data.minor` is by
  definition `data.row i (data.coordinate j)` and whose `data_row` field says
  `data.row = bitRows basis.vertex`.  So the minor *is* the bit matrix of
  `basis.vertex` on `data.coordinate`, which is the shape the transport wants.
* The **normal form** side is `S.frame.vec 0`, and `S.frame_eq` says exactly
  how it factors: a coordinate permutation `S.perm`, then a shift by `S.x0`,
  applied to `S.source`.

`exists_sortedNormalForm_of_generator'` keeps `S.source` and the fact that the
shift is by a supported point, which is the hypothesis the transport needs on
that side; `TwoFiberCertificate.base_supported` supplies the same on the fresh
side.
-/

namespace MainTheory.SortedPivotConstruction

open MainTheory
open MainTheory.SortedForm
open MainTheory.SixQubitSemanticEntrance
open MainTheory.D3NormalizedFreshPhase
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.D3BoundedNormalForm
open MainTheory.SectionTwoGeneral

noncomputable section

variable {n : ℕ}

/-! ## The fresh side is a bit matrix -/

/-- The sparse pivot's minor is the bit matrix of its own supported basis on
its own selected coordinates.  Both halves are definitional; this records the
composite in the shape the transport consumes. -/
theorem freshMinor_eq {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : D3FreshSparseAssembly.FreshSparsePhase c d theta) (i j : Fin F.basis.rank) :
    F.data.minor i j =
      if F.basis.vertex i (F.data.coordinate j) then 1 else 0 := by
  rw [D3SparseRationalization.Data.minor, F.data_row,
    D3SparseRationalization.bitRows]

/-- Hence the minor is the matrix the transport expects, verbatim. -/
theorem freshMinor_det_ne_zero {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : D3FreshSparseAssembly.FreshSparsePhase c d theta) :
    (Matrix.of fun i j =>
      if F.basis.vertex i (F.data.coordinate j) then (1 : ℤ) else 0).det ≠ 0 := by
  have hEq : (Matrix.of fun i j =>
      if F.basis.vertex i (F.data.coordinate j) then (1 : ℤ) else 0)
      = F.data.minor := by
    funext i j
    exact (freshMinor_eq F i j).symm
  rw [hEq]
  exact F.data.minor_nonsingular

/-! ## The two supports -/

/-- The zero word lies in the normalized support: the shift is by a point of
the first logical word's own support. -/
theorem zero_mem_normalizedSupport {d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    (normalizedFrame T).vec 0 (fun _ => false) ≠ 0 := by
  have hval : (normalizedFrame T).vec 0 (fun _ => false)
      = G.eigenFrame.vec 0 T.x0 := by
    simp [normalizedFrame, normalizedState]
  rw [hval]
  exact T.base_supported

/-- The same on the normal form's own side.  Permuting the all-false string
leaves it alone, and shifting it by `x0` gives `x0`. -/
theorem zero_mem_sortedSupport {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedNormalForm C) (hbase : S.source.vec 0 S.x0 ≠ 0) :
    S.frame.vec 0 (fun _ => false) ≠ 0 := by
  rw [S.frame_eq]
  have hperm : SixQubit.CodeEquiv.permStr S.perm (fun _ => false)
      = (fun _ : Fin n => false) := by
    funext i
    simp [SixQubit.CodeEquiv.permStr]
  rw [hperm]
  have hb : SS.bxor (fun _ : Fin n => false) S.x0 = S.x0 := by
    funext i
    simp [SS.bxor]
  rw [hb]
  exact hbase

/-! ## The sparse angle vanishes off its selected coordinates

`Data.angle` is the residue of `Denominator.liftNum` applied to
`Data.fullSolution`, which is `extendByZero coordinate selectedSolution`.  Off
the selected coordinates the solution is zero, so the numerator is zero, so
the angle is.  This is what makes the `sparse` field of a pivot available. -/

theorem sparseAngle_eq_zero {r : ℕ} (P : D3SparseRationalization.Data n r)
    {j : Fin n} (h : ∀ i, P.coordinate i ≠ j) : P.angle j = 0 := by
  have hfull : P.fullSolution j = 0 := by
    rw [D3SparseRationalization.Data.fullSolution, FiniteLift.extendByZero]
    exact Finset.sum_eq_zero fun i _ => by simp [h i]
  have hnum : P.numerator j = 0 := by
    rw [D3SparseRationalization.Data.numerator, Denominator.liftNum, hfull]
    simp
  rw [D3SparseRationalization.Data.angle, hnum]
  simp

/-- The bounded generator's eigenframe is the normalized one, shifted back.
This is `rfl` once the modulus instance is in scope. -/
theorem boundedGenerator_eigenFrame {q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 3}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G)
    [NeZero (frameFreshSparsePhase T).data.order]
    (k : Fin 2) (u : SS.BitString n) :
    (boundedGenerator T).eigenFrame.vec k u
      = (normalizedFrame T).vec k (SS.bxor u T.x0) := rfl

/-! ## The assembly

Everything above, joined at the one place where the fresh sparse pivot and the
sorted normal form are both in scope. -/

/-- **The normal form comes with a pivot.**

Same statement as `exists_sortedNormalForm_le_betaN`, plus the pivot data that
`SortedPivot.Pivot.s0Clause` turns into the coarse filter's `S_0` clause.  The
proof is the original one with the fresh sparse phase kept rather than
discarded, and the transports of `SortedPivot` carrying its nonsingular minor
onto the normal form's own support. -/
theorem exists_sortedNormalForm_pivot {B : ℕ}
    (beta : BinaryBeta.BetaBound 6 B)
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C, S.q ≤ B ∧
      S.frame.vec 0 (fun _ => false) ≠ 0 ∧
      Nonempty (SortedPivot.Pivot S) := by
  classical
  letI : NeZero (rationalLift C GeneralFiniteness.two_le_three theta hpres).order :=
    ⟨(rationalLift C GeneralFiniteness.two_le_three theta hpres).order_pos.ne'⟩
  set G := finiteGenerator C GeneralFiniteness.two_le_three theta hpres hnt with hG
  set T := canonicalTwoFiber G with hT
  letI : NeZero (frameFreshSparsePhase T).data.order := frameFreshOrderNeZero T
  obtain ⟨S, hq, hsrc, hbase, hzero⟩ :=
    SortedForm.exists_sortedNormalForm_of_generator' C (boundedGenerator T)
  refine ⟨S, ?_, zero_mem_sortedSupport S (by rw [hsrc]; exact hbase), ?_⟩
  · rw [hq]
    exact automaticFreshGenerator_order_le beta T
  · set F := frameFreshSparsePhase T with hF
    set K : Fin F.basis.rank ↪ Fin 6 := F.data.coordinate with hK
    set δ : SS.BitString 6 := SS.bxor S.x0 T.x0 with hd
    set Tset : Set (SS.BitString 6) :=
      {u | (normalizedFrame T).vec 0 u ≠ 0} with hTs
    set U : Set (SS.BitString 6) :=
      {u | (normalizedFrame T).vec 0 (SS.bxor u δ) ≠ 0} with hU
    have hshift : Tset = (fun u => SS.bxor u δ) '' U := by
      ext u
      constructor
      · intro hu
        refine ⟨SS.bxor u δ, ?_, SS.bxor_bxor_cancel u δ⟩
        show (normalizedFrame T).vec 0 (SS.bxor (SS.bxor u δ) δ) ≠ 0
        rwa [SS.bxor_bxor_cancel]
      · rintro ⟨w, hw, rfl⟩
        exact hw
    have hzT : (fun _ => false) ∈ Tset := zero_mem_normalizedSupport T
    have hzU : (fun _ => false) ∈ U := by
      show (normalizedFrame T).vec 0 (SS.bxor (fun _ => false) δ) ≠ 0
      have hb : SS.bxor (fun _ : Fin 6 => false) δ = δ := by
        funext i; simp [SS.bxor]
      rw [hb]
      have := hbase
      rw [boundedGenerator_eigenFrame T 0 S.x0] at this
      exact this
    have hv : ∀ i, F.basis.vertex i ∈ Tset := fun i => F.basis.vertex_supported i
    have hspanU : Submodule.span ℚ
        (MaskRankBridge.rqpoint K '' U) = ⊤ :=
      SortedPivot.span_rqpoint_of_shifted_nonsingular K δ Tset U hshift hzT hzU
        F.basis.vertex hv (freshMinor_det_ne_zero F)
    -- the normal form's support is `U` pulled back along its own permutation
    have hsupp : {s : SS.BitString 6 | S.frame.vec 0 s ≠ 0}
        = (fun s => SixQubit.CodeEquiv.permStr S.perm s) ⁻¹' U := by
      ext s
      show S.frame.vec 0 s ≠ 0 ↔
        (normalizedFrame T).vec 0
          (SS.bxor (SixQubit.CodeEquiv.permStr S.perm s) δ) ≠ 0
      rw [S.frame_eq, hsrc, boundedGenerator_eigenFrame T 0]
      have hb : SS.bxor (SS.bxor (SixQubit.CodeEquiv.permStr S.perm s) S.x0)
          T.x0 = SS.bxor (SixQubit.CodeEquiv.permStr S.perm s) δ := by
        funext i
        cases hxi : S.x0 i <;> cases hti : T.x0 i <;>
          simp [SS.bxor, hd, hxi, hti]
      rw [hb]
    -- transport across the permutation
    set K₂ : Fin F.basis.rank ↪ Fin 6 := K.trans S.perm.toEmbedding with hK₂
    have hspanS : Submodule.span ℚ
        (MaskRankBridge.rqpoint K₂ ''
          {s : SS.BitString 6 | S.frame.vec 0 s ≠ 0}) = ⊤ := by
      rw [hsupp]
      refine SortedPivot.span_rqpoint_permStr K₂ S.perm U ?_
      have hid : K₂.trans S.perm.symm.toEmbedding = K := by
        ext i
        simp only [hK₂, Function.Embedding.trans_apply,
          Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
      rw [hid]
      exact hspanU
    -- the angle vanishes off the selected coordinates, so the pivot is sparse
    have hsparse : ∀ j, (∀ i, K₂ i ≠ j) → S.angle j = 0 := by
      intro j hj
      refine hzero j ?_
      have hnot : ∀ i, F.data.coordinate i ≠ S.perm.symm j := by
        intro i hi
        exact hj i (by simpa [hK₂, hK] using congrArg S.perm hi)
      have hfresh : (automaticFreshGenerator T).angle (S.perm.symm j) = 0 :=
        sparseAngle_eq_zero F.data hnot
      show Normalize.flip (automaticFreshGenerator T).angle T.x0
        (S.perm.symm j) = 0
      rw [Normalize.flip]
      by_cases hx : T.x0 (S.perm.symm j) <;> simp [hx, hfresh]
    exact SortedPivot.nonempty_pivot_of_spanning_at S K₂ F.rank_pos
      F.rank_le_six hsparse hspanS

/-- **The six-qubit cutoff, with the pivot.**  `beta_6 = 9` is a kernel
theorem, so this has no hypothesis beyond the code and its symmetry. -/
theorem exists_sortedNormalForm_pivot_nine
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C, S.q ≤ 9 ∧
      S.frame.vec 0 (fun _ => false) ≠ 0 ∧
      Nonempty (SortedPivot.Pivot S) :=
  exists_sortedNormalForm_pivot
    MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper C theta hpres hnt

/-- **Every exact `((6,2,3))` code with a projectively nontrivial diagonal
symmetry satisfies the coarse filter's `S_0` clause.**

This is the last link of the coarse-filter entry: `CoarseFilterUnconditional`
already showed that a row satisfying this clause and admitting a common moment
point is kept, and a code supplies the moment point itself.  So the coarse
filter provably never discards a code -- with no appeal to `q <= beta_r` at
the affine rank.  The paper does prove that bound: `thm:d3-bound` normalizes
by a local `X` conjugation that puts `0^n` in `T_0`, so the common affine span
is linear and `r` is the affine and the linear rank at once.  What this
development lacked was that normalization at its own entrance, which
`RankTwoGlobal.TwoFiberCertificate.base_supported` now records. -/
theorem exists_normalForm_s0Clause
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C, S.q ≤ 9 ∧
      CoarseFilterSound.S0Clause
        (OuterCompleteness.recordFiberPair (CodeFiberBridge.recordOf S)) := by
  obtain ⟨S, hq, _, ⟨P⟩⟩ := exists_sortedNormalForm_pivot_nine C theta hpres hnt
  exact ⟨S, hq, P.s0Clause⟩

/-- **The same, keeping the pivot and the zero-word fact.**

`exists_normalForm_s0Clause` discards both, because the coarse filter needs
neither.  The *rank* filter needs both: the pivot to bound the active affine
rank, and `S.frame.vec 0 0 != 0` to put the zero word on the active face. -/
theorem exists_normalForm_pivot_full
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : SortedNormalForm C) (_ : SortedPivot.Pivot S), S.q ≤ 9 ∧
      S.frame.vec 0 (fun _ => false) ≠ 0 ∧
      CoarseFilterSound.S0Clause
        (OuterCompleteness.recordFiberPair (CodeFiberBridge.recordOf S)) := by
  obtain ⟨S, hq, hz, ⟨P⟩⟩ := exists_sortedNormalForm_pivot_nine C theta hpres hnt
  exact ⟨S, P, hq, hz, P.s0Clause⟩

end

end MainTheory.SortedPivotConstruction
