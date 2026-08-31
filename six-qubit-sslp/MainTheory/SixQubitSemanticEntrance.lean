import MainTheory.CodeAffineSpanBridge
import MainTheory.RankTwoGlobal
import MainTheory.BinaryBeta
import MainTheory.OuterCompleteness
import MainTheory.D3SparseRationalization

/-!
# Honest semantic entrance to the six-qubit finite classification

This file isolates the still-missing entrance from an arbitrary exact
`((6,2,3))` code with a nontrivial diagonal product symmetry to the finite
outer enumeration.

There are two facts which must not be conflated.

* Once a primitive finite generator spanning the actual code is supplied,
  `RankTwoGlobal.finiteGenerator_twoFiber` gives the genuine, normalized
  two-fibre SSLP states and preserves the complete Knill--Laflamme predicate.
* To obtain the sharp cutoff for a finite generator already supplied at order
  `q`, one must additionally know that its normalized modular angle is realized
  by the freshly rationalized binary-simplex phase.  Merely knowing that the
  two supports have the same affine span does not identify an old modulus with
  the least denominator of that new phase.

`D3FiniteResolution` is therefore a *resolved sparse-generator* interface, not
a constructor from an arbitrary earlier finite generator.  Its pivot rows are
actual supported vertices and `angle_spec` ties the zero-extended sparse phase
to that very generator's normalized modular angle.  Under this stronger link,
and the universal theorem `BetaBound 6 9`, the kernel proves `2 <= q <= 9`,
`1 < m | q`, and occurrence of a canonical primitive angle record in
`OuterEnumeration.primitiveRecords`.  The separate downstream module
`D3FreshSparseAssembly` constructs a fresh rational phase and its own order;
turning that output into a new `FiniteGeneratorResolution` remains a distinct
semantic packaging step.

The final `D3ExtractionPrinciple` is an explicit name for what remains to be
proved in order to start from an arbitrary real diagonal symmetry.  No
inhabitant of that principle is declared here.  Consequently none of the
theorems below silently assumes spectral extraction, finite-generator
construction, or the sharp distance-three pivot.
-/

namespace MainTheory.SixQubitSemanticEntrance

open MainTheory
open scoped BigOperators

noncomputable section

abbrev ExactSixQubitCode := CodeSpec.ExactCode 6 2 3

/-! ## A supported Boolean basis chosen without certificate data -/

/-- A basis of the linear span of the Boolean vertices in the *actual*
nonzero support of a state.  The vertices and their support proofs are part of
the result, but no coordinate minor is: `D3SparseRationalization.Data.ofBitRows`
constructs that minor from `independent`.

This is a linear-span basis, rather than an affine basis.  That is the form
needed by the homogeneous phase equations in `main.tex`. -/
structure SupportedBitBasis (psi : SS.State 6 ℂ) where
  rank : ℕ
  vertex : Fin rank → SS.BitString 6
  vertex_supported : ∀ i, psi (vertex i) ≠ 0
  independent : LinearIndependent ℝ
    (fun i => CodeAffineSpanBridge.bitPoint (vertex i))
  span_eq :
    Submodule.span ℝ
        (Set.range (fun i => CodeAffineSpanBridge.bitPoint (vertex i))) =
      Submodule.span ℝ
        (CodeAffineSpanBridge.bitPoint ''
          CodeAffineSpanBridge.actualSupport psi)

/-- Every actual support admits a supported Boolean basis.  This is a direct
application of finite-dimensional basis extraction to the span of the actual
support image; the preimages returned below are therefore genuine supported
bit strings, not arbitrary real vectors. -/
noncomputable def supportedBitBasis (psi : SS.State 6 ℂ) :
    SupportedBitBasis psi := by
  let S : Set (Fin 6 → ℝ) :=
    CodeAffineSpanBridge.bitPoint ''
      CodeAffineSpanBridge.actualSupport psi
  let hexists := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  let f := Classical.choose hexists
  have hf_spec := Classical.choose_spec hexists
  have hf_mem : ∀ i, f i ∈ S := hf_spec.1
  have hf_span : Submodule.span ℝ (Set.range f) =
      Submodule.span ℝ S := hf_spec.2.1
  have hf_independent : LinearIndependent ℝ f := hf_spec.2.2
  let vertex : Fin (Module.finrank ℝ (Submodule.span ℝ S)) →
      SS.BitString 6 := fun i => Classical.choose (hf_mem i)
  have hvertex_supported : ∀ i,
      vertex i ∈ CodeAffineSpanBridge.actualSupport psi := fun i =>
    (Classical.choose_spec (hf_mem i)).1
  have hvertex_eq : ∀ i,
      CodeAffineSpanBridge.bitPoint (vertex i) = f i := fun i =>
    (Classical.choose_spec (hf_mem i)).2
  refine
    { rank := Module.finrank ℝ (Submodule.span ℝ S)
      vertex := vertex
      vertex_supported := hvertex_supported
      independent := ?_
      span_eq := ?_ }
  · have hfun :
        (fun i => CodeAffineSpanBridge.bitPoint (vertex i)) = f := by
      funext i
      exact hvertex_eq i
    rw [hfun]
    exact hf_independent
  · have hfun :
        (fun i => CodeAffineSpanBridge.bitPoint (vertex i)) = f := by
      funext i
      exact hvertex_eq i
    rw [hfun, hf_span]

/-- At most six supported Boolean rows are ever needed. -/
theorem SupportedBitBasis.rank_le_six {psi : SS.State 6 ℂ}
    (B : SupportedBitBasis psi) : B.rank ≤ 6 := by
  simpa using B.independent.fintype_card_le_finrank

/-- Coordinatewise real embedding of bit strings is injective. -/
theorem bitPoint_injective :
    Function.Injective
      (CodeAffineSpanBridge.bitPoint : SS.BitString 6 → Fin 6 → ℝ) := by
  intro x y hxy
  funext j
  have hj := congrFun hxy j
  cases hx : x j <;> cases hy : y j <;>
    simp [CodeAffineSpanBridge.bitPoint, hx, hy] at hj ⊢

/-- The all-zero Boolean vertex. -/
def zeroBitString : SS.BitString 6 := fun _ => false

@[simp] theorem bitPoint_zeroBitString :
    CodeAffineSpanBridge.bitPoint zeroBitString = 0 := by
  funext j
  simp [zeroBitString, CodeAffineSpanBridge.bitPoint]

/-- A common-affine-span pair in two distinct subset-sum fibres cannot have a
zero-dimensional supported linear span on the left.

This is the precise nondegeneracy argument used in the distance-three proof.
If the left span were zero, every point in the common affine span would be the
zero cube vertex.  A supported point of the right state would then have both
zero subset-sum and the stipulated nonzero right residue. -/
theorem SupportedBitBasis.rank_pos_of_commonAffineSpan
    {q : ℕ} [NeZero q]
    {c d : SS.State 6 ℂ}
    (B : SupportedBitBasis c)
    (H : CodeAffineSpanBridge.CommonAffineSpanCertificate c d)
    (a : Fin 6 → ZMod q) (residue : ZMod q)
    (hright : SS.SSConditionState a residue d)
    (hresidue : residue ≠ 0) :
    1 ≤ B.rank := by
  by_contra hnot
  have hrank : B.rank = 0 := by omega
  have hrange :
      Set.range (fun i => CodeAffineSpanBridge.bitPoint (B.vertex i)) =
        (∅ : Set (Fin 6 → ℝ)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      have i0 : Fin 0 := hrank ▸ i
      exact Fin.elim0 i0
    · simp
  have hspan :
      Submodule.span ℝ
          (CodeAffineSpanBridge.bitPoint ''
            CodeAffineSpanBridge.actualSupport c) = ⊥ := by
    calc
      Submodule.span ℝ
          (CodeAffineSpanBridge.bitPoint ''
            CodeAffineSpanBridge.actualSupport c) =
          Submodule.span ℝ
            (Set.range
              (fun i => CodeAffineSpanBridge.bitPoint (B.vertex i))) :=
        B.span_eq.symm
      _ = ⊥ := by rw [hrange]; simp
  obtain ⟨y, hy⟩ := H.support1_nonempty
  have hy_affine_right :
      CodeAffineSpanBridge.bitPoint y ∈
        affineSpan ℝ
          (CodeAffineSpanBridge.bitPoint ''
            CodeAffineSpanBridge.actualSupport d) :=
    mem_affineSpan ℝ ⟨y, hy, rfl⟩
  have hy_affine_left :
      CodeAffineSpanBridge.bitPoint y ∈
        affineSpan ℝ
          (CodeAffineSpanBridge.bitPoint ''
            CodeAffineSpanBridge.actualSupport c) := by
    rw [H.affineSpan_eq]
    exact hy_affine_right
  have hy_span :
      CodeAffineSpanBridge.bitPoint y ∈
        Submodule.span ℝ
          (CodeAffineSpanBridge.bitPoint ''
            CodeAffineSpanBridge.actualSupport c) :=
    affineSpan_subset_span hy_affine_left
  rw [hspan] at hy_span
  have hy_point_zero : CodeAffineSpanBridge.bitPoint y = 0 := by
    simpa using hy_span
  have hy_zero : y = zeroBitString := by
    apply bitPoint_injective
    rw [hy_point_zero, bitPoint_zeroBitString]
  have hweight := hright y hy
  rw [hy_zero] at hweight
  have hzero_residue : (0 : ZMod q) = residue := by
    simpa [SS.weight, SS.bit, zeroBitString] using hweight
  exact hresidue hzero_residue.symm

/-! ## The missing sharp distance-three pivot, stated semantically -/

/-- The finite angle after the local-`X` and coprime-power normalizations in
the rank-two theorem. -/
def normalizedFiniteAngle {q : ℕ} [NeZero q]
    {C : ExactSixQubitCode}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (T : RankTwoGlobal.TwoFiberCertificate G) : Fin 6 → ZMod q :=
  fun j ↦ (T.unit : ZMod q) * Normalize.flip G.angle T.x0 j

/-- A square binary simplex cut out of actual supported vertices of the
normalized left logical word.

The last two fields expose the selected rational phase and its exact
connection to the normalized finite angle.  The integral pivot equation is
derived below from the genuine left-fibre support equation.  In particular
`q ∣ inverseDenominator matrix` is *not* a field: it is derived below from
the derived integral pivot solution, denominator minimality, and
primitivity. -/
structure BinarySimplexPivot {q : ℕ} [NeZero q]
    {C : ExactSixQubitCode}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (T : RankTwoGlobal.TwoFiberCertificate G) where
  rank : ℕ
  rank_pos : 1 ≤ rank
  rank_le_six : rank ≤ 6
  base_supported : G.eigenFrame.vec 0 T.x0 ≠ 0
  vertex : Fin rank → SS.BitString 6
  vertex_supported : ∀ i,
    G.eigenFrame.vec 0 (SS.bxor (vertex i) T.x0) ≠ 0
  coordinate : Fin rank ↪ Fin 6
  matrix : Matrix (Fin rank) (Fin rank) ℤ
  matrix_eq : ∀ i j,
    matrix i j = if vertex i (coordinate j) then 1 else 0
  nonsingular : matrix.det ≠ 0
  selectedPhase : Fin rank → ℚ
  angle_spec : ∀ j,
    ∃ z : ℤ,
      (q : ℚ) *
          FiniteLift.extendByZero coordinate selectedPhase j = (z : ℚ) ∧
      (z : ZMod q) = normalizedFiniteAngle G T j

/-!
`angle_spec` states the congruence in `main.tex` literally: `q * theta'_j` is
an integer whose residue is the normalized finite angle.  It does not impose
the stronger and unnecessary equality with the canonical `.val`
representative.  Outside the selected coordinate image the angle residue is
still forced to zero.  The field therefore applies to the *new sparse lift*
constructed by rationalization, not to an unrelated pre-existing generator.
-/

/-- The matrix displayed by a `BinarySimplexPivot` is genuinely entrywise
zero--one; this is derived from its connection to supported bit strings and
is not another trusted field. -/
theorem BinarySimplexPivot.isZeroOne {q : ℕ} [NeZero q]
    {C : ExactSixQubitCode}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    {T : RankTwoGlobal.TwoFiberCertificate G}
    (P : BinarySimplexPivot G T) :
    BinaryBeta.IsZeroOne P.matrix := by
  intro i j
  rw [P.matrix_eq]
  split <;> simp

/-- The six-coordinate rational phase obtained by keeping the selected pivot
coordinates and setting all other coordinates to zero, exactly as in the
distance-three proof. -/
def BinarySimplexPivot.physicalPhase {q : ℕ} [NeZero q]
    {C : ExactSixQubitCode}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    {T : RankTwoGlobal.TwoFiberCertificate G}
    (P : BinarySimplexPivot G T) : Fin 6 → ℚ :=
  FiniteLift.extendByZero P.coordinate P.selectedPhase

/-- Extending the selected solution by zero cannot introduce a new
denominator. -/
theorem BinarySimplexPivot.lcmDen_physical_dvd_selected
    {q : ℕ} [NeZero q]
    {C : ExactSixQubitCode}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    {T : RankTwoGlobal.TwoFiberCertificate G}
    (P : BinarySimplexPivot G T) :
    Denominator.lcmDen P.physicalPhase ∣
      Denominator.lcmDen P.selectedPhase := by
  apply Denominator.lcmDen_dvd_of_clears
  intro j
  by_cases hj : ∃ i, P.coordinate i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [BinarySimplexPivot.physicalPhase,
      FiniteLift.extendByZero_apply_column]
    exact Denominator.lcmDen_clears P.selectedPhase i
  · have hzero : P.physicalPhase j = 0 := by
      rw [BinarySimplexPivot.physicalPhase]
      apply Finset.sum_eq_zero
      intro i _
      have hne : P.coordinate i ≠ j := by
        intro hi
        exact hj ⟨i, hi⟩
      simp [hne]
    rw [hzero]
    simp

/-! ## The integral right-hand side comes from the phase equation -/

/-- A support point in the zero residue fibre has integral rational phase.
This is the exact bridge from the `ZMod q` subset-sum equation to the integral
right-hand side used in the binary pivot system. -/
theorem exists_integral_support_phase {q : ℕ} [NeZero q]
    (a : Fin 6 → ZMod q) (theta : Fin 6 → ℚ)
    (hspec : ∀ j, ∃ z : ℤ,
      (q : ℚ) * theta j = (z : ℚ) ∧ (z : ZMod q) = a j)
    (x : SS.BitString 6) (hweight : SS.weight a x = 0) :
    ∃ h : ℤ,
      (∑ j : Fin 6, (if x j then 1 else 0 : ℚ) * theta j) = h := by
  choose z hz hza using hspec
  let numerator : ℤ := ∑ j : Fin 6, if x j then z j else 0
  have hcast : (numerator : ZMod q) = SS.weight a x := by
    simp only [numerator, Int.cast_sum, SS.weight]
    apply Finset.sum_congr rfl
    intro j _
    cases x j <;> simp [SS.bit, hza j]
  have hqdvd : (q : ℤ) ∣ numerator := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd numerator q).1
    rw [hcast, hweight]
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have hcleared :
      (q : ℚ) *
          (∑ j : Fin 6, (if x j then 1 else 0 : ℚ) * theta j) =
        (numerator : ℚ) := by
    rw [Finset.mul_sum]
    simp only [numerator, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    cases x j <;> simp [hz j]
  obtain ⟨h, hnum⟩ := hqdvd
  refine ⟨h, ?_⟩
  apply mul_left_cancel₀ hqne
  calc
    (q : ℚ) *
        (∑ j : Fin 6, (if x j then 1 else 0 : ℚ) * theta j) =
      (numerator : ℚ) := hcleared
    _ = (q : ℚ) * (h : ℚ) := by
      rw [hnum]
      push_cast
      rfl

/-- For every displayed pivot row, the genuine left-fibre phase equation
constructs an integral right-hand side.  Thus `C x = h` is a theorem from the
support semantics and `angle_spec`, not a certificate field. -/
theorem BinarySimplexPivot.exists_integral_rhs
    {q : ℕ} [NeZero q]
    {C : ExactSixQubitCode}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    {T : RankTwoGlobal.TwoFiberCertificate G}
    (P : BinarySimplexPivot G T) :
    ∃ rhs : Fin P.rank → ℤ,
      (SharpClearing.ratMatrix P.matrix).mulVec P.selectedPhase =
        fun i ↦ (rhs i : ℚ) := by
  have hrow : ∀ i : Fin P.rank, ∃ h : ℤ,
      (∑ j : Fin 6,
          (if P.vertex i j then 1 else 0 : ℚ) * P.physicalPhase j) = h := by
    intro i
    apply exists_integral_support_phase
      (normalizedFiniteAngle G T) P.physicalPhase P.angle_spec
      (P.vertex i)
    exact T.normalizedLeft (P.vertex i) (P.vertex_supported i)
  choose rhs hrhs using hrow
  refine ⟨rhs, funext fun i ↦ ?_⟩
  calc
    ((SharpClearing.ratMatrix P.matrix).mulVec P.selectedPhase) i =
        ∑ k : Fin P.rank,
          (if P.vertex i (P.coordinate k) then 1 else 0 : ℚ) *
            P.selectedPhase k := by
      simp only [Matrix.mulVec, dotProduct, SharpClearing.ratMatrix,
        Matrix.map_apply, P.matrix_eq]
      apply Finset.sum_congr rfl
      intro k _
      split <;> simp
    _ = dotProduct
        (fun j : Fin 6 ↦ (if P.vertex i j then 1 else 0 : ℚ))
        P.physicalPhase := by
      exact (FiniteLift.dotProduct_extendByZero P.coordinate
        (fun j : Fin 6 ↦ (if P.vertex i j then 1 else 0 : ℚ))
        P.selectedPhase).symm
    _ = (rhs i : ℚ) := hrhs i

/-! ## Least denominator from a primitive residue vector -/

/-- If `q * theta_j` has an integral representative congruent to the
primitive residue `a_j`, then the least common denominator of `theta` is
exactly `q`.  Integer shifts of a phase coordinate are allowed, as in the
literal congruence in `main.tex`; canonical `.val` representatives are not
assumed. -/
theorem lcmDen_eq_of_primitive_residues {q : ℕ} [NeZero q]
    (theta : Fin 6 → ℚ) (a : Fin 6 → ZMod q)
    (hprimitive : Gate.Primitive q a)
    (hspec : ∀ j, ∃ z : ℤ,
      (q : ℚ) * theta j = (z : ℚ) ∧ (z : ZMod q) = a j) :
    Denominator.lcmDen theta = q := by
  choose z hz hza using hspec
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdq : Denominator.lcmDen theta ∣ q :=
    Denominator.lcmDen_dvd_of_clears theta q (fun j ↦
      (Denominator.clears_iff q hq (theta j)).2
        ⟨z j, hz j⟩)
  let d := Denominator.lcmDen theta
  let g := q / d
  have hdpos : 0 < d := Denominator.lcmDen_pos theta
  have hqeq : q = d * g := by
    simpa [d, g] using (Nat.mul_div_cancel' hdq).symm
  have hgdvdq : g ∣ q := by
    exact ⟨d, by simpa [mul_comm] using hqeq⟩
  have hgdvdz : ∀ j, (g : ℤ) ∣ z j := by
    intro j
    obtain ⟨b, hb⟩ :=
      (Denominator.clears_iff d hdpos (theta j)).1
        (Denominator.lcmDen_clears theta j)
    have hrat : (z j : ℚ) = (g : ℚ) * (b : ℚ) := by
      calc
        (z j : ℚ) = (q : ℚ) * theta j := (hz j).symm
        _ = ((d * g : ℕ) : ℚ) * theta j := by rw [hqeq]
        _ = (g : ℚ) * ((d : ℚ) * theta j) := by
          push_cast
          ring
        _ = (g : ℚ) * (b : ℚ) := by rw [hb]
    have hint : z j = (g : ℤ) * b := by
      exact_mod_cast hrat
    exact ⟨b, hint⟩
  have hgdvda : ∀ j, g ∣ (a j).val := by
    intro j
    have hcast : (z j : ZMod q) =
        (((a j).val : ℤ) : ZMod q) := by
      simpa using hza j
    have hqsub : (q : ℤ) ∣ ((a j).val : ℤ) - z j :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub
        (z j) ((a j).val : ℤ) q).1 hcast
    have hgsub : (g : ℤ) ∣ ((a j).val : ℤ) - z j :=
      (Int.natCast_dvd_natCast.mpr hgdvdq).trans hqsub
    have hgval : (g : ℤ) ∣ ((a j).val : ℤ) := by
      convert Int.dvd_add (hgdvdz j) hgsub using 1
      ring
    exact Int.natCast_dvd_natCast.mp hgval
  have hg : g = 1 := hprimitive g hgdvdq hgdvda
  have hqd : q = d := by simpa [hg] using hqeq
  simpa [d] using hqd.symm

/-- The desired sharp divisibility is now a theorem from the displayed pivot
equation and the exact primitive-residue transcription. -/
theorem BinarySimplexPivot.q_dvd_inverseDenominator
    {q : ℕ} [NeZero q]
    {C : ExactSixQubitCode}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    {T : RankTwoGlobal.TwoFiberCertificate G}
    (P : BinarySimplexPivot G T)
    (hprimitive : Gate.Primitive q (normalizedFiniteAngle G T)) :
    q ∣ SharpClearing.inverseDenominator P.matrix := by
  obtain ⟨rhs, hsolves⟩ := P.exists_integral_rhs
  have hqeq : Denominator.lcmDen P.physicalPhase = q :=
    lcmDen_eq_of_primitive_residues P.physicalPhase
      (normalizedFiniteAngle G T) hprimitive P.angle_spec
  have hdiv : Denominator.lcmDen P.physicalPhase ∣
      SharpClearing.inverseDenominator P.matrix :=
    dvd_trans P.lcmDen_physical_dvd_selected
    (SharpClearing.solution_lcmDen_dvd_inverseDenominator
      P.matrix rhs P.selectedPhase P.nonsingular hsolves)
  rcases hdiv with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    SharpClearing.inverseDenominator P.matrix =
        Denominator.lcmDen P.physicalPhase * k := hk
    _ = q * k := congrArg (fun d : ℕ ↦ d * k) hqeq

/-- Complete finite semantic data extracted from one exact six-qubit code.

The normalized primitive clause is kept explicit.  It is elementary under
local `X`, coordinate permutation, and multiplication by a unit, but recording
it here ensures that the outer enumerator can never accept an imprimitive
angle vector through an implicit normalization claim. -/
structure D3FiniteResolution (C : ExactSixQubitCode) (q : ℕ) [NeZero q] where
  generator : RankTwoGlobal.FiniteGeneratorResolution C q
  normalForm : RankTwoGlobal.TwoFiberCertificate generator
  pivot : BinarySimplexPivot generator normalForm
  normalizedPrimitive : Gate.Primitive q
    (fun j ↦ (normalForm.unit : ZMod q) *
      Normalize.flip generator.angle normalForm.x0 j)

/-- The normalized finite angle vector occurring in the two-fibre theorem. -/
def D3FiniteResolution.normalizedAngle {C : ExactSixQubitCode}
    {q : ℕ} [NeZero q] (R : D3FiniteResolution C q) :
    Fin 6 → ZMod q :=
  normalizedFiniteAngle R.generator R.normalForm

/-- Natural representatives of the normalized finite angles. -/
def D3FiniteResolution.natAngle {C : ExactSixQubitCode}
    {q : ℕ} [NeZero q] (R : D3FiniteResolution C q) :
    OuterEnumeration.Angle6 :=
  fun j ↦ (R.normalizedAngle j).val

/-- The two logical states after the local-`X` normalization recorded by the
two-fibre certificate. -/
def D3FiniteResolution.normalizedState {C : ExactSixQubitCode}
    {q : ℕ} [NeZero q] (R : D3FiniteResolution C q)
    (k : Fin 2) : SS.State 6 ℂ :=
  fun s ↦ R.generator.eigenFrame.vec k (SS.bxor s R.normalForm.x0)

/-- The finite diagonal action carried by a resolved generator.  Packaging the
`ZMod q`-dependent projections under the explicit `NeZero q` argument lets
later structures install that instance from their stored positivity proof. -/
def D3FiniteResolution.finiteGate {C : ExactSixQubitCode}
    {q : ℕ} [NeZero q] (R : D3FiniteResolution C q) :=
  RankTwoGlobal.finiteGateEnd R.generator.zeta R.generator.angle

theorem D3FiniteResolution.natAngle_lt {C : ExactSixQubitCode}
    {q : ℕ} [NeZero q] (R : D3FiniteResolution C q) (j : Fin 6) :
    R.natAngle j < q :=
  ZMod.val_lt _

/-! ## Kernel consequences of a resolved entrance -/

/-- The already-formalized code semantics force the two *actual* logical
supports of the supplied eigenframe to have one affine span. -/
theorem D3FiniteResolution.commonAffineSpan {C : ExactSixQubitCode}
    {q : ℕ} [NeZero q] (R : D3FiniteResolution C q) :
    CodeAffineSpanBridge.CommonAffineSpanCertificate
      (R.generator.eigenFrame.vec 0) (R.generator.eigenFrame.vec 1) := by
  exact CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame
    C R.generator.eigenFrame R.generator.span_eq (by decide)

/-- The common-affine-span theorem also applies after the exact local-`X`
normalization used by the sparse pivot.  This is the geometry relevant to
`BinarySimplexPivot.vertex`; it is derived from the normalized KL and
orthonormality fields, not asserted by the pivot. -/
theorem D3FiniteResolution.normalizedCommonAffineSpan
    {C : ExactSixQubitCode} {q : ℕ} [NeZero q]
    (R : D3FiniteResolution C q) :
    CodeAffineSpanBridge.CommonAffineSpanCertificate
      (R.normalizedState 0) (R.normalizedState 1) := by
  have hn0 : SS.innerC (R.normalizedState 0) (R.normalizedState 0) = 1 := by
    simpa [D3FiniteResolution.normalizedState] using
      R.normalForm.normalizedOrthonormal 0 0
  have hn1 : SS.innerC (R.normalizedState 1) (R.normalizedState 1) = 1 := by
    simpa [D3FiniteResolution.normalizedState] using
      R.normalForm.normalizedOrthonormal 1 1
  have hdist := R.normalForm.normalizedHasDistance
  have hframe :
      (fun i s ↦ R.generator.eigenFrame.vec i
        (SS.bxor s R.normalForm.x0)) =
        ![R.normalizedState 0, R.normalizedState 1] := by
    funext i s
    fin_cases i <;> rfl
  rw [hframe] at hdist
  exact CodeAffineSpanBridge.certificate_of_hasDistance
    (R.normalizedState 0) (R.normalizedState 1) hn0 hn1 hdist

/-- The physical order is bounded by nine from the semantic beta theorem,
not from a numerical lookup table. -/
theorem D3FiniteResolution.q_le_nine
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : ExactSixQubitCode} {q : ℕ} [NeZero q]
    (R : D3FiniteResolution C q) : q ≤ 9 := by
  have hden : SharpClearing.inverseDenominator R.pivot.matrix ≤ 9 :=
    betaSix R.pivot.rank R.pivot.rank_pos R.pivot.rank_le_six
      R.pivot.matrix R.pivot.isZeroOne R.pivot.nonsingular
  have hqden : q ≤ SharpClearing.inverseDenominator R.pivot.matrix :=
    Nat.le_of_dvd (SharpClearing.inverseDenominator_pos R.pivot.matrix)
      (R.pivot.q_dvd_inverseDenominator R.normalizedPrimitive)
  exact hqden.trans hden

/-- The normalized two-fibre certificate gives all elementary order
conditions used by the finite outer index. -/
theorem D3FiniteResolution.order_bounds
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : ExactSixQubitCode} {q : ℕ} [NeZero q]
    (R : D3FiniteResolution C q) :
    2 ≤ q ∧ 2 ≤ R.normalForm.logicalOrder ∧
      R.normalForm.logicalOrder ∣ q ∧ q ≤ 9 :=
  ⟨R.normalForm.two_le_physicalOrder,
    R.normalForm.two_le_logicalOrder,
    R.normalForm.logicalOrder_dvd_physical,
    R.q_le_nine betaSix⟩

/-! ## Canonical occurrence in the executable outer enumeration -/

theorem primitive_comp_perm {q : ℕ} [NeZero q]
    (a : Fin 6 → ZMod q) (h : Gate.Primitive q a)
    (σ : Equiv.Perm (Fin 6)) : Gate.Primitive q (a ∘ σ) := by
  intro d hdq hda
  apply h d hdq
  intro j
  simpa using hda (σ.symm j)

/-- `primitiveAngles6` is exactly the primitive sublist of `weakAngles6`.
This small bridge prevents later proofs from treating membership in the two
lists as interchangeable without checking the Boolean primitive predicate. -/
theorem mem_primitiveAngles6_iff {q : ℕ}
    {a : OuterEnumeration.Angle6} :
    a ∈ OuterEnumeration.primitiveAngles6 q ↔
      a ∈ OuterEnumeration.weakAngles6 q ∧
        OuterEnumeration.IsPrimitive q a = true := by
  simp only [OuterEnumeration.primitiveAngles6,
    OuterEnumeration.primitiveAngles6FromFirst,
    OuterEnumeration.weakAngles6,
    List.mem_flatMap, List.mem_filter]
  aesop

/-- Sorting the natural representatives of the normalized primitive angle
vector produces an angle which the executable primitive enumerator contains.
The permutation is returned explicitly, so no coordinate relabeling is hidden.
-/
theorem D3FiniteResolution.exists_canonical_primitive_angle
    {C : ExactSixQubitCode} {q : ℕ} [NeZero q]
    (R : D3FiniteResolution C q) :
    ∃ (σ : Equiv.Perm (Fin 6)) (a : OuterEnumeration.Angle6),
      a ∈ OuterEnumeration.primitiveAngles6 q ∧
      a = R.natAngle ∘ σ ∧
      (fun j ↦ (a j : ZMod q)) = R.normalizedAngle ∘ σ := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨σ, hweak⟩ :=
    OuterCompleteness.exists_permutation_mem_weakAngles6
      R.natAngle R.natAngle_lt
  let a : OuterEnumeration.Angle6 := R.natAngle ∘ σ
  have hcast : (fun j ↦ (a j : ZMod q)) = R.normalizedAngle ∘ σ := by
    funext j
    simp only [a, D3FiniteResolution.natAngle, Function.comp_apply,
      D3FiniteResolution.normalizedAngle]
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hprimitive : Gate.Primitive q (fun j ↦ (a j : ZMod q)) := by
    rw [hcast]
    exact primitive_comp_perm R.normalizedAngle R.normalizedPrimitive σ
  have hrange : ∀ j, a j < q := by
    intro j
    exact R.natAngle_lt (σ j)
  have hbool : OuterEnumeration.IsPrimitive q a = true :=
    (OuterCompleteness.isPrimitive_iff_gatePrimitive hq a hrange).2 hprimitive
  refine ⟨σ, a, (mem_primitiveAngles6_iff).2 ⟨hweak, hbool⟩, rfl, hcast⟩

theorem mem_sixQubitModuli_of_bounds {q : ℕ}
    (hq2 : 2 ≤ q) (hq9 : q ≤ 9) :
    q ∈ OuterEnumeration.sixQubitModuli := by
  interval_cases q <;> simp [OuterEnumeration.sixQubitModuli]

theorem mem_logicalOrders_of_order_data {q m : ℕ}
    (hq : 0 < q) (hm2 : 2 ≤ m) (hmq : m ∣ q) :
    m ∈ OuterEnumeration.logicalOrders q := by
  have hmq' : m ≤ q := Nat.le_of_dvd hq hmq
  have hq2 : 2 ≤ q := hm2.trans hmq'
  rw [OuterEnumeration.logicalOrders, List.mem_filter]
  constructor
  · exact (OuterCompleteness.mem_range'_one_iff).2
      ⟨hm2, by omega⟩
  · simp [Nat.dvd_iff_mod_eq_zero.mp hmq]

/-- A resolved exact code produces a literal record in the checked finite
outer list whose angle vector is an explicit coordinate permutation of the
normalized finite angle.  This theorem does not yet transport the two logical
states along that permutation, so its formal conclusion is record-index
coverage, not membership of the code in a record's fibre pair.  In particular
it also does not claim that the later
`11,422 -> 508 -> 291 -> 215 -> 66` directories have already been
semantically connected to this code. -/
theorem D3FiniteResolution.exists_record_in_primitiveRecords
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : ExactSixQubitCode} {q : ℕ} [NeZero q]
    (R : D3FiniteResolution C q) :
    ∃ record : OuterEnumeration.RawRecord,
      record ∈ OuterEnumeration.primitiveRecords ∧
      record.q = q ∧
      record.m = R.normalForm.logicalOrder ∧
      ∃ σ : Equiv.Perm (Fin 6),
        record.a = R.natAngle ∘ σ := by
  obtain ⟨σ, a, ha, haeq, _⟩ := R.exists_canonical_primitive_angle
  have hqmem : q ∈ OuterEnumeration.sixQubitModuli :=
    mem_sixQubitModuli_of_bounds
      R.normalForm.two_le_physicalOrder (R.q_le_nine betaSix)
  have hm : R.normalForm.logicalOrder ∈
      OuterEnumeration.logicalOrders q :=
    mem_logicalOrders_of_order_data
      (Nat.pos_of_ne_zero (NeZero.ne q))
      R.normalForm.two_le_logicalOrder
      R.normalForm.logicalOrder_dvd_physical
  let record : OuterEnumeration.RawRecord :=
    { q := q, m := R.normalForm.logicalOrder, a := a }
  have hrecord : record ∈ OuterEnumeration.primitiveRecords := by
    simp only [OuterEnumeration.primitiveRecords, List.mem_flatMap,
      List.mem_map]
    exact ⟨q, hqmem, R.normalForm.logicalOrder, hm, a, ha, rfl⟩
  exact ⟨record, hrecord, rfl, rfl, σ, haeq⟩

/-! ## The precise arbitrary-code obligation -/

/-- Projective nontriviality of a real diagonal gate on the actual code: its
restriction is not a nonzero scalar multiple of the identity. -/
def ProjectivelyNontrivialReal (C : ExactSixQubitCode)
    (theta : Fin 6 → ℝ) : Prop :=
  ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id

/-- An exact six-qubit code lies in the paper's nontrivial diagonal sector
when at least one real diagonal product gate preserves it nontrivially. -/
def HasNontrivialDiagonalSymmetry (C : ExactSixQubitCode) : Prop :=
  ∃ theta : Fin 6 → ℝ,
    CodeSpec.CodePreserving C.frame
        (PhaseSectorBridge.realGateEnd theta) ∧
    ProjectivelyNontrivialReal C theta

/-- One extracted finite resolution, with positivity stored before installing
the `NeZero` instance required by `ZMod`.  The final field prevents a finite
generator for some unrelated action on the same code from being substituted:
the displayed finite and real gates induce the same projective action on the
actual code span. -/
structure ExtractedD3Resolution (C : ExactSixQubitCode)
    (theta : Fin 6 → ℝ) where
  q : ℕ
  q_pos : 0 < q
  resolution :
    @D3FiniteResolution C q ⟨Nat.ne_of_gt q_pos⟩
  sameProjectiveAction :
    CodeSpec.SameProjectiveOnCode C.frame
      (@D3FiniteResolution.finiteGate C q ⟨Nat.ne_of_gt q_pos⟩ resolution)
      (PhaseSectorBridge.realGateEnd theta)

/-- The resolved logical order, exposed without requiring callers to
reconstruct the stored `NeZero q` instance in a theorem statement. -/
def ExtractedD3Resolution.logicalOrder
    {C : ExactSixQubitCode} {theta : Fin 6 → ℝ}
    (E : ExtractedD3Resolution C theta) : ℕ := by
  letI : NeZero E.q := ⟨Nat.ne_of_gt E.q_pos⟩
  exact E.resolution.normalForm.logicalOrder

/-- The resolved normalized natural angle, with the same instance-free
interface for dependent existential conclusions. -/
def ExtractedD3Resolution.natAngle
    {C : ExactSixQubitCode} {theta : Fin 6 → ℝ}
    (E : ExtractedD3Resolution C theta) : OuterEnumeration.Angle6 := by
  letI : NeZero E.q := ⟨Nat.ne_of_gt E.q_pos⟩
  exact E.resolution.natAngle

/-- The exact missing entrance theorem.

An inhabitant must be constructed from an arbitrary preserving,
projectively nontrivial real diagonal gate.  In particular it must perform
spectral extraction and normalization, derive the integral phase equations on
the actual support, construct the fresh sparse rational phase, and package
that fresh phase (with its own least denominator) as a primitive finite
generator spanning the actual code.  Only then may its supported binary minor
be used to bound that same denominator.  This file does not postulate such an
inhabitant. -/
def D3ExtractionPrinciple : Prop :=
  ∀ (C : ExactSixQubitCode) (theta : Fin 6 → ℝ),
    CodeSpec.CodePreserving C.frame
        (PhaseSectorBridge.realGateEnd theta) →
    ProjectivelyNontrivialReal C theta →
    Nonempty (ExtractedD3Resolution C theta)

/-- Conditional end-to-end entrance theorem for an arbitrary exact
`((6,2,3))` code and one nontrivial preserving diagonal operation.

Every mathematical premise which is not yet derived in the repository is
visible: `extraction` is the missing semantic construction, while `betaSix`
is the universal binary-matrix bound.  Under precisely those premises the
resulting code-linked finite generator has `2 <= q <= 9`, and its normalized
angle has a literal index in the primitive outer enumeration.  The record's
modulus, logical order, and angle (up to the returned coordinate permutation)
are retained in the conclusion.  What is still absent is transport of the two
logical states and their actual fibres along that permutation. -/
theorem arbitrary_code_enters_primitive_outer_index
    (extraction : D3ExtractionPrinciple)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : ExactSixQubitCode) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnontrivial : ProjectivelyNontrivialReal C theta) :
    ∃ E : ExtractedD3Resolution C theta,
      2 ≤ E.q ∧ E.q ≤ 9 ∧
      ∃ record : OuterEnumeration.RawRecord,
        record ∈ OuterEnumeration.primitiveRecords ∧
        record.q = E.q ∧
        record.m = E.logicalOrder ∧
        ∃ σ : Equiv.Perm (Fin 6),
          record.a = E.natAngle ∘ σ := by
  obtain ⟨E⟩ := extraction C theta hpres hnontrivial
  letI : NeZero E.q := ⟨Nat.ne_of_gt E.q_pos⟩
  have hq2 : 2 ≤ E.q := E.resolution.normalForm.two_le_physicalOrder
  have hq9 : E.q ≤ 9 := E.resolution.q_le_nine betaSix
  obtain ⟨record, hrecord, hq, hm, σ, ha⟩ :=
    E.resolution.exists_record_in_primitiveRecords betaSix
  have hm' : record.m = E.logicalOrder := by
    simpa [ExtractedD3Resolution.logicalOrder] using hm
  have ha' : record.a = E.natAngle ∘ σ := by
    simpa [ExtractedD3Resolution.natAngle] using ha
  exact ⟨E, hq2, hq9, record, hrecord, hq, hm', σ, ha'⟩

/-- Code-only form of the conditional entrance theorem.  The witness gate is
unpacked from `HasNontrivialDiagonalSymmetry`; no preferred gate is assumed. -/
theorem code_with_nontrivial_diagonal_symmetry_has_outer_index
    (extraction : D3ExtractionPrinciple)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : ExactSixQubitCode)
    (hsymmetry : HasNontrivialDiagonalSymmetry C) :
    ∃ (theta : Fin 6 → ℝ) (E : ExtractedD3Resolution C theta),
      2 ≤ E.q ∧ E.q ≤ 9 ∧
      ∃ record : OuterEnumeration.RawRecord,
        record ∈ OuterEnumeration.primitiveRecords ∧
        record.q = E.q ∧
        record.m = E.logicalOrder ∧
        ∃ σ : Equiv.Perm (Fin 6),
          record.a = E.natAngle ∘ σ := by
  rcases hsymmetry with ⟨theta, hpres, hnontrivial⟩
  obtain ⟨E, hq2, hq9, record, hrecord, hq, hm, σ, ha⟩ :=
    arbitrary_code_enters_primitive_outer_index
      extraction betaSix C theta hpres hnontrivial
  exact ⟨theta, E, hq2, hq9, record, hrecord, hq, hm, σ, ha⟩

end

end MainTheory.SixQubitSemanticEntrance
