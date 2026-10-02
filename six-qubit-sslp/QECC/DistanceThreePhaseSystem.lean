import QECC.SectorPhaseSystem
import QECC.RankTwoSSLP
import QECC.RationalDenominator
import QECC.SmithOrderBound

namespace QECC

open scoped BigOperators
open Matrix

noncomputable section

/-- A real linear functional whose value on a zero-one vector is the physical
support weight. -/
def realSupportWeightLinear {n : ℕ} (theta : Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (dotProductBilin ℝ ℝ) theta

@[simp] theorem realSupportWeightLinear_bitVector {n : ℕ}
    (theta : Fin n → ℝ) (x : BitString n) :
    realSupportWeightLinear theta (bitVector x) =
      realSupportWeight theta x := by
  simp [realSupportWeightLinear, dotProduct, realSupportWeight, bitVector]

/-- The real zero-one embedding remembers the underlying bit string. -/
theorem bitVector_injective {n : ℕ} :
    Function.Injective (bitVector : BitString n → Fin n → ℝ) := by
  intro x y hxy
  funext j
  have hj := congrFun hxy j
  cases hx : x j <;> cases hy : y j <;>
    simp [bitVector, bitReal, hx, hy] at hj ⊢

namespace BinaryPivotSolution

variable {rows : Type*} [Fintype rows] {N : ℕ}
  {A : Matrix rows (Fin N) ℤ} {h : rows → ℤ}

/-- The rational rank recorded by an integral pivot solution is unchanged
after casting the matrix to the reals.  The nonsingular integral pivot minor
gives real independence, while `rows_span` casts rational spanning
coefficients to real ones. -/
theorem realRank_eq_size (S : BinaryPivotSolution N A h) :
    (A.map (Int.castRingHom ℝ)).rank = S.size := by
  classical
  let Aq : Matrix rows (Fin N) ℚ := A.map (Int.castRingHom ℚ)
  let Ar : Matrix rows (Fin N) ℝ := A.map (Int.castRingHom ℝ)
  let selectedQ : Fin S.size → (Fin N → ℚ) :=
    fun i => Aq.row (S.row i)
  let selectedR : Fin S.size → (Fin N → ℝ) :=
    fun i => Ar.row (S.row i)
  let minorR : Matrix (Fin S.size) (Fin S.size) ℝ :=
    (A.submatrix S.row S.column).map (Int.castRingHom ℝ)
  have hminorDet : minorR.det ≠ 0 := by
    intro hzero
    apply S.minor_det_ne_zero
    have hcast :
        (((A.submatrix S.row S.column).det : ℤ) : ℝ) = 0 := by
      exact (RingHom.map_det (Int.castRingHom ℝ)
        (A.submatrix S.row S.column)).trans hzero
    exact_mod_cast hcast
  have hminorLI : LinearIndependent ℝ minorR.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hminorDet
  let restrict : (Fin N → ℝ) →ₗ[ℝ] (Fin S.size → ℝ) :=
    LinearMap.funLeft ℝ ℝ S.column
  have hselectedLI : LinearIndependent ℝ selectedR := by
    apply LinearIndependent.of_comp restrict
    simpa [restrict, selectedR, minorR, Ar, Function.comp_def] using hminorLI
  have htransfer (v : Fin N → ℚ)
      (hv : v ∈ Submodule.span ℚ (Set.range selectedQ)) :
      (fun j => (v j : ℝ)) ∈
        Submodule.span ℝ (Set.range selectedR) := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        apply Submodule.subset_span
        refine ⟨i, ?_⟩
        funext j
        rfl
    | zero =>
        convert Submodule.zero_mem
          (Submodule.span ℝ (Set.range selectedR)) using 1
        funext j
        norm_num
    | add x y hx hy ihx ihy =>
        simpa using
          (Submodule.add_mem (Submodule.span ℝ (Set.range selectedR))
            ihx ihy)
    | smul c x hx ih =>
        have hsmul := Submodule.smul_mem
          (Submodule.span ℝ (Set.range selectedR)) (c : ℝ) ih
        simpa using hsmul
  have hallRows : Submodule.span ℝ (Set.range Ar.row) ≤
      Submodule.span ℝ (Set.range selectedR) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hqmem : Aq.row i ∈
        Submodule.span ℚ (Set.range selectedQ) := by
      change Aq.row i ∈ Submodule.span ℚ
        (Set.range fun k => Aq.row (S.row k))
      rw [S.rows_span]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hcast := htransfer (Aq.row i) hqmem
    simpa [Aq, Ar] using hcast
  have hselectedRows : Submodule.span ℝ (Set.range selectedR) ≤
      Submodule.span ℝ (Set.range Ar.row) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨S.row i, rfl⟩
  have hspans : Submodule.span ℝ (Set.range Ar.row) =
      Submodule.span ℝ (Set.range selectedR) :=
    le_antisymm hallRows hselectedRows
  rw [show A.map (Int.castRingHom ℝ) = Ar by rfl,
    Matrix.rank_eq_finrank_span_row, hspans]
  exact (linearIndependent_iff_card_eq_finrank_span.mp hselectedLI).symm.trans
    (Fintype.card_fin S.size)

end BinaryPivotSolution

/-- The zero-one matrix whose rows are precisely the actual support strings
of one chosen active sector. -/
def CodeProjector.anchorActualSupportMatrix {n K q : ℕ}
    (C : CodeProjector n K) (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) :
    Matrix (C.actualSectorSupport a b0) (Fin n) ℤ :=
  fun x j ↦ bitInt (x.1 j)

namespace CodeProjector

variable {n K q d : ℕ} (C : CodeProjector n K)

/-- The anchor actual-support matrix is binary. -/
theorem anchorActualSupportMatrix_isZeroOne
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    Matrix.IsZeroOne (C.anchorActualSupportMatrix a b0) := by
  intro x j
  cases hx : x.1 j <;> simp [anchorActualSupportMatrix, bitInt, hx]

/-- The rational row span of the normalized anchor support.  When the zero
string lies in the support, this is its rational affine direction. -/
def anchorActualSupportSpan (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) : Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ (Set.range
    ((C.anchorActualSupportMatrix a b0).map (Int.castRingHom ℚ)).row)

/-- The formal common affine dimension used by the normalized distance-three
system.  It is computed over `ℚ` from the zero-one anchor rows; the anchor-at-
zero hypothesis identifies this row span with the affine direction. -/
def normalizedActualSupportDimension (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) : ℕ :=
  Module.finrank ℚ (C.anchorActualSupportSpan a b0)

/-- The rank of the binary support matrix is the normalized affine dimension. -/
theorem rank_anchorActualSupportMatrix
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    ((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℚ)).rank =
      C.normalizedActualSupportDimension a b0 := by
  rw [Matrix.rank_eq_finrank_span_row]
  rfl

@[simp] theorem anchorActualSupportMatrix_row_real
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (x : C.actualSectorSupport a b0) :
    (((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℝ)).row x) = bitVector x.1 := by
  funext j
  cases hx : x.1 j <;> simp [anchorActualSupportMatrix, bitVector,
    bitInt, bitReal, hx]

/-- With the zero string in the anchor support, the direction of its real
affine span is exactly the real row span of the anchor support matrix. -/
theorem direction_actualSectorAffineSpan_eq_anchorRowSpan
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0) :
    (C.actualSectorAffineSpan a b0).direction =
      Submodule.span ℝ (Set.range
        (((C.anchorActualSupportMatrix a b0).map
          (Int.castRingHom ℝ)).row)) := by
  have hzeroImage : (0 : Fin n → ℝ) ∈
      bitVector '' C.actualSectorSupport a b0 := by
    refine ⟨0, hzero, ?_⟩
    funext j
    rfl
  rw [actualSectorAffineSpan, direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ hzeroImage]
  simp only [vsub_eq_sub, sub_zero, Set.image_id']
  congr 1
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩,
      C.anchorActualSupportMatrix_row_real a b0 ⟨x, hx⟩⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2,
      (C.anchorActualSupportMatrix_row_real a b0 x).symm⟩

/-- Integral right-hand side for the anchor-only system. -/
def anchorActualSupportRHS [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    C.actualSectorSupport a b0 → ℤ :=
  fun x ↦ C.actualSectorPhaseRHS hq a b0 x.1

/-- Multiplication by the real anchor matrix computes support weight. -/
theorem anchorActualSupportMatrix_mulVec_real
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (theta : Fin n → ℝ) (x : C.actualSectorSupport a b0) :
    ((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℝ)).mulVec theta x =
      realSupportWeight theta x.1 := by
  simp only [anchorActualSupportMatrix, Matrix.mulVec, dotProduct,
    Matrix.map_apply, realSupportWeight]
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x.1 j <;> simp [bitInt, bitReal]

/-- The original lifted modular phase is a real solution of the anchor-only
integer system once the anchor residue has been normalized to zero. -/
theorem phaseLift_solves_anchorActualSupportSystem [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) (hb0 : b0.1 = 0) :
    ((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℝ)).mulVec
        (phaseLift (phaseHom n q hq a)) =
      fun x ↦ (C.anchorActualSupportRHS hq a b0 x : ℝ) := by
  funext x
  rw [C.anchorActualSupportMatrix_mulVec_real]
  have hspec := C.actualSectorPhaseRHS_spec hq a b0 x.1 x.2
  rw [hb0, zmodPhaseLift_zero, sub_zero] at hspec
  exact hspec

/-- The size of an anchor pivot system is the real affine dimension when the
anchor support contains zero. -/
theorem anchorBinaryPivotSolution_size_eq_realAffineDimension [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0)
    (S : BinaryPivotSolution n
      (C.anchorActualSupportMatrix a b0)
      (C.anchorActualSupportRHS hq a b0)) :
    S.size = Module.finrank ℝ
      (C.actualSectorAffineSpan a b0).direction := by
  calc
    S.size = ((C.anchorActualSupportMatrix a b0).map
        (Int.castRingHom ℝ)).rank := S.realRank_eq_size.symm
    _ = Module.finrank ℝ
        (Submodule.span ℝ (Set.range
          (((C.anchorActualSupportMatrix a b0).map
            (Int.castRingHom ℝ)).row))) :=
      Matrix.rank_eq_finrank_span_row _
    _ = Module.finrank ℝ
        (C.actualSectorAffineSpan a b0).direction := by
      rw [C.direction_actualSectorAffineSpan_eq_anchorRowSpan
        a b0 hzero]

/-- The normalized anchor support equations have a binary pivot solution
with only the `n` physical phase coordinates. -/
theorem exists_anchorBinaryPivotSolution [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) (hb0 : b0.1 = 0) :
    Nonempty (BinaryPivotSolution n
      (C.anchorActualSupportMatrix a b0)
      (C.anchorActualSupportRHS hq a b0)) := by
  apply exists_binaryPivotSolution
  · exact C.anchorActualSupportMatrix_isZeroOne a b0
  · exact ⟨phaseLift (phaseHom n q hq a),
      C.phaseLift_solves_anchorActualSupportSystem hq a b0 hb0⟩

/-- Casting the rational anchor matrix equation to the reals recovers the
support weight of the cast rational vector. -/
theorem cast_anchorActualSupportMatrix_mulVec
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (theta : Fin n → ℚ) (x : C.actualSectorSupport a b0) :
    (((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℚ)).mulVec theta x : ℝ) =
      realSupportWeight (fun j ↦ (theta j : ℝ)) x.1 := by
  simp only [anchorActualSupportMatrix, Matrix.mulVec, dotProduct,
    Matrix.map_apply, realSupportWeight]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x.1 j <;> simp [bitInt, bitReal]

/-- A pivot solution of the normalized anchor system agrees with the original
lifted modular phase on every actual anchor-support string. -/
theorem anchorBinaryPivotSolution_agrees_on_anchor [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) (hb0 : b0.1 = 0)
    (S : BinaryPivotSolution n
      (C.anchorActualSupportMatrix a b0)
      (C.anchorActualSupportRHS hq a b0))
    (x : BitString n) (hx : x ∈ C.actualSectorSupport a b0) :
    realSupportWeight (fun j ↦ (S.solution j : ℝ)) x =
      realSupportWeight (phaseLift (phaseHom n q hq a)) x := by
  let X : C.actualSectorSupport a b0 := ⟨x, hx⟩
  have hsolve := congrFun S.solves X
  have hcast := congrArg (fun z : ℚ ↦ (z : ℝ)) hsolve
  change (((((C.anchorActualSupportMatrix a b0).map
    (Int.castRingHom ℚ)).mulVec S.solution X : ℚ) : ℝ)) =
      (C.anchorActualSupportRHS hq a b0 X : ℝ) at hcast
  rw [C.cast_anchorActualSupportMatrix_mulVec a b0 S.solution X] at hcast
  have hspec := C.actualSectorPhaseRHS_spec hq a b0 x hx
  rw [hb0, zmodPhaseLift_zero, sub_zero] at hspec
  exact hcast.trans hspec.symm

/-- Equality of the real affine spans transports agreement of two physical
linear phase vectors from one actual support to the other. -/
theorem supportWeights_agree_on_second_of_affineSpan_eq
    (a : Fin n → ZMod q) (b c : C.ActiveResidue a)
    (physical physical' : Fin n → ℝ)
    (hspan : C.actualSectorAffineSpan a b =
      C.actualSectorAffineSpan a c)
    (hagree : ∀ x ∈ C.actualSectorSupport a b,
      realSupportWeight physical' x = realSupportWeight physical x) :
    ∀ y ∈ C.actualSectorSupport a c,
      realSupportWeight physical' y = realSupportWeight physical y := by
  let delta : Fin n → ℝ := physical' - physical
  let f : (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
    (realSupportWeightLinear delta).toAffineMap
  let z : (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (Fin n → ℝ) 0
  have heq : Set.EqOn f z
      (bitVector '' C.actualSectorSupport a b) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxagree := hagree x hx
    change realSupportWeight delta x = 0
    rw [realSupportWeight_sub]
    exact sub_eq_zero.mpr hxagree
  have heqSpan := AffineMap.eqOn_affineSpan heq
  intro y hy
  have hySpan : bitVector y ∈
      affineSpan ℝ (bitVector '' C.actualSectorSupport a b) := by
    change bitVector y ∈ C.actualSectorAffineSpan a b
    rw [hspan]
    exact subset_affineSpan ℝ _ ⟨y, hy, rfl⟩
  have hyzero := heqSpan hySpan
  change realSupportWeight delta y = 0 at hyzero
  rw [realSupportWeight_sub] at hyzero
  exact sub_eq_zero.mp hyzero

/-- At distance at least three, every pivot solution of the normalized anchor
system agrees with the original lifted phase on a second active sector. -/
theorem anchorBinaryPivotSolution_agrees_on_sector_of_hasDistanceAtLeast
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (b0 b1 : C.ActiveResidue a) (hb0 : b0.1 = 0)
    (S : BinaryPivotSolution n
      (C.anchorActualSupportMatrix a b0)
      (C.anchorActualSupportRHS hq a b0))
    (x : BitString n) (hx : x ∈ C.actualSectorSupport a b1) :
    realSupportWeight (fun j ↦ (S.solution j : ℝ)) x =
      realSupportWeight (phaseLift (phaseHom n q hq a)) x := by
  apply C.supportWeights_agree_on_second_of_affineSpan_eq a b0 b1
    (phaseLift (phaseHom n q hq a))
    (fun j ↦ (S.solution j : ℝ))
  · exact C.actualSectorAffineSpan_eq_of_hasDistanceAtLeast
      hq a hpres hd hd3 b0 b1
  · exact C.anchorBinaryPivotSolution_agrees_on_anchor hq a b0 hb0 S
  · exact hx

/-- If two distinct actual supports have the same affine span and the first
contains zero, then the first support also contains a nonzero string. -/
theorem exists_ne_zero_mem_actualSectorSupport_of_affineSpan_eq
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b0 b1 : C.ActiveResidue a) (hb01 : b0 ≠ b1)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0)
    (hspan : C.actualSectorAffineSpan a b0 =
      C.actualSectorAffineSpan a b1) :
    ∃ x ∈ C.actualSectorSupport a b0, x ≠ 0 := by
  by_contra hnonzero
  push_neg at hnonzero
  obtain ⟨y, hy⟩ := C.actualSectorSupport_nonempty hq a hpres b1
  let f : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
    AffineMap.id ℝ (Fin n → ℝ)
  let z : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
    AffineMap.const ℝ (Fin n → ℝ) 0
  have heq : Set.EqOn f z
      (bitVector '' C.actualSectorSupport a b0) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hnonzero x hx]
    rfl
  have hySpan : bitVector y ∈
      affineSpan ℝ (bitVector '' C.actualSectorSupport a b0) := by
    change bitVector y ∈ C.actualSectorAffineSpan a b0
    rw [hspan]
    exact subset_affineSpan ℝ _ ⟨y, hy, rfl⟩
  have hyzero := AffineMap.eqOn_affineSpan heq hySpan
  have hyvec : bitVector y = 0 := by
    exact hyzero
  have hy0 : y = 0 := by
    apply bitVector_injective
    simpa [bitVector] using hyvec
  have hdisjoint := C.actualSectorSupport_disjoint a hb01
  rw [Set.disjoint_left] at hdisjoint
  exact hdisjoint hzero (hy0 ▸ hy)

/-- The normalized common affine dimension is positive for two distinct
active sectors. -/
theorem normalizedActualSupportDimension_pos [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b0 b1 : C.ActiveResidue a) (hb01 : b0 ≠ b1)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0)
    (hspan : C.actualSectorAffineSpan a b0 =
      C.actualSectorAffineSpan a b1) :
    1 ≤ C.normalizedActualSupportDimension a b0 := by
  obtain ⟨x, hx, hx0⟩ :=
    C.exists_ne_zero_mem_actualSectorSupport_of_affineSpan_eq
      hq a hpres b0 b1 hb01 hzero hspan
  rw [Nat.one_le_iff_ne_zero]
  intro hdim
  let A := (C.anchorActualSupportMatrix a b0).map (Int.castRingHom ℚ)
  have hrank : A.rank = 0 := by
    rw [C.rank_anchorActualSupportMatrix a b0]
    exact hdim
  have hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.row)) = 0 := by
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hrank
  have hbot : Submodule.span ℚ (Set.range A.row) = ⊥ :=
    Submodule.finrank_eq_zero.mp hfinrank
  let X : C.actualSectorSupport a b0 := ⟨x, hx⟩
  have hrowmem : A.row X ∈ Submodule.span ℚ (Set.range A.row) :=
    Submodule.subset_span (Set.mem_range_self X)
  have hrowzero : A.row X = 0 := by
    rw [hbot] at hrowmem
    exact hrowmem
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
  have hjtrue : x j = true := by
    cases hbit : x j
    · exact (hj hbit).elim
    · rfl
  have hentry := congrFun hrowzero j
  norm_num [A, X, anchorActualSupportMatrix, bitInt, hjtrue] at hentry

/-- The normalized common affine dimension is bounded by the number of
physical qubits. -/
theorem normalizedActualSupportDimension_le
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    C.normalizedActualSupportDimension a b0 ≤ n := by
  rw [← C.rank_anchorActualSupportMatrix a b0]
  simpa using
    ((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℚ)).rank_le_card_width

-- Port to Lean 4.27: generating the constructor injectivity theorems
-- (`mk.inj`, `mk.injEq`) for this dependent structure exceeds twice the
-- default heartbeats there; Lean 4.28 does it quickly. Nothing in this
-- development uses them, and any use would fail to compile.
set_option genInjectivity false in
/-- Complete anchor-only binary-system certificate in local-`X` normalized
form.  The rational solution has only physical coordinates, agrees with the
original lifted modular phase on both actual supports, and comes with its
Smith-cleared integral numerator. -/
structure NormalizedDistanceThreePhaseSystem [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (b0 b1 : C.ActiveResidue a) where
  affineSpan_eq : C.actualSectorAffineSpan a b0 =
    C.actualSectorAffineSpan a b1
  r : ℕ
  r_eq_dimension : r = C.normalizedActualSupportDimension a b0
  r_eq_realAffineDimension : r = Module.finrank ℝ
    (C.actualSectorAffineSpan a b0).direction
  r_pos : 1 ≤ r
  r_le : r ≤ n
  pivot : BinaryPivotSolution n
    (C.anchorActualSupportMatrix a b0)
    (C.anchorActualSupportRHS hq a b0)
  pivot_size_eq : pivot.size = r
  agreesOnAnchor : ∀ x ∈ C.actualSectorSupport a b0,
    realSupportWeight (fun j ↦ (pivot.solution j : ℝ)) x =
      realSupportWeight (phaseLift (phaseHom n q hq a)) x
  agreesOnSecond : ∀ x ∈ C.actualSectorSupport a b1,
    realSupportWeight (fun j ↦ (pivot.solution j : ℝ)) x =
      realSupportWeight (phaseLift (phaseHom n q hq a)) x
  smithNumerator : Fin n → ℤ
  smithNumerator_spec :
    (fun j ↦ (smithNumerator j : ℚ)) =
      pivot.pivotMinor.finalSmithInvariant • pivot.solution

namespace NormalizedDistanceThreePhaseSystem

variable {C : CodeProjector n K} [NeZero q] {hq : 0 < q}
  {a : Fin n → ZMod q} {b0 b1 : C.ActiveResidue a}

/-- The selected nonsingular binary square minor.  Its size is `r` by
`binaryPivotMinor_size`. -/
def binaryPivotMinor
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    NonsingularBinaryMatrix D.pivot.size :=
  D.pivot.pivotMinor

/-- The displayed pivot minor is `r × r`. -/
theorem binaryPivotMinor_size
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    D.pivot.size = D.r :=
  D.pivot_size_eq

/-- The rank of the anchor binary matrix is exactly the common affine
dimension `r`. -/
theorem binaryMatrix_rank_eq_r
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    ((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℚ)).rank = D.r := by
  exact D.pivot.size_eq_rank.symm.trans D.pivot_size_eq

/-- Explicitly, the rational matrix rank equals the real affine dimension
of the anchor support. -/
theorem binaryMatrix_rank_eq_realAffineDimension
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    ((C.anchorActualSupportMatrix a b0).map
      (Int.castRingHom ℚ)).rank =
      Module.finrank ℝ (C.actualSectorAffineSpan a b0).direction := by
  rw [D.binaryMatrix_rank_eq_r, D.r_eq_realAffineDimension]

/-- The same `r` is the real affine dimension of the second support because
the two affine spans are equal. -/
theorem r_eq_secondRealAffineDimension
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    D.r = Module.finrank ℝ
      (C.actualSectorAffineSpan a b1).direction := by
  rw [← D.affineSpan_eq]
  exact D.r_eq_realAffineDimension

/-- The stored integral vector clears the denominator of the full rational
physical solution by the final Smith invariant of the displayed pivot minor. -/
theorem smithNumerator_spec_binaryPivotMinor
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    (fun j ↦ (D.smithNumerator j : ℚ)) =
      D.binaryPivotMinor.finalSmithInvariant • D.pivot.solution :=
  D.smithNumerator_spec

/-- The anchor-only certificate supplies the reduced physical representative
and Smith bound for the same nontrivial rank-two projective action. -/
theorem exists_smithBoundedPhysicalRepresentative
    {C : CodeProjector n 2} {hq : 0 < q}
    {a : Fin n → ZMod q} {b0 b1 : C.ActiveResidue a}
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap
      ⟨phaseHom n q hq a, hpres⟩ ≠ 0)
    (hexhaust : ∀ b : C.ActiveResidue a, b = b0 ∨ b = b1) :
    Nonempty (C.SmithBoundedPhysicalRepresentative
      (C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩) D.r) := by
  let thetaRat : Fin n → ℚ := D.pivot.solution
  let thetaRatReal : Fin n → ℝ := fun j ↦ (thetaRat j : ℝ)
  let thetaOld : Fin n → ℝ := phaseLift (phaseHom n q hq a)
  have hphaseOld : realVectorPhase thetaOld = phaseHom n q hq a := by
    funext j
    exact coe_phaseLift _ _
  have hagree (b : C.ActiveResidue a) (x : BitString n)
      (hx : x ∈ C.actualSectorSupport a b) :
      realSupportWeight thetaRatReal x = realSupportWeight thetaOld x := by
    rcases hexhaust b with rfl | rfl
    · exact D.agreesOnAnchor x hx
    · exact D.agreesOnSecond x hx
  have hscalar : C.ActsAsScalar
      (rationalVectorPhase thetaRat - phaseHom n q hq a) := by
    rw [← hphaseOld]
    change C.ActsAsScalar
      (realVectorPhase thetaRatReal - realVectorPhase thetaOld)
    rw [← realVectorPhase_sub]
    apply C.actsAsScalar_of_constant_on_actualSectorSupports
      hq a hpres (realVectorPhase (thetaRatReal - thetaOld)) 0
    intro b x hx
    rw [supportPhase_realVectorPhase, realSupportWeight_sub,
      hagree b x hx, sub_self]
    rfl
  have hdiffPres : C.Preserves
      (rationalVectorPhase thetaRat - phaseHom n q hq a) :=
    C.preserves_of_actsAsScalar hscalar
  have hrat : C.Preserves (rationalVectorPhase thetaRat) := by
    have hadd := C.preserves_add hdiffPres hpres
    simpa only [sub_add_cancel] using hadd
  have hclass : C.projectiveClassMap
      ⟨rationalVectorPhase thetaRat, hrat⟩ =
      C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact hscalar
  let M := D.binaryPivotMinor
  have hphaseRat : rationalVectorPhase thetaRat =
      rationalPhase M.finalSmithInvariant D.smithNumerator := by
    apply rationalVectorPhase_eq_rationalPhase_of_smul_eq
      M.finalSmithInvariant_pos thetaRat D.smithNumerator
    exact D.smithNumerator_spec_binaryPivotMinor
  have hrat' : C.Preserves
      (rationalPhase M.finalSmithInvariant D.smithNumerator) := by
    rw [← hphaseRat]
    exact hrat
  have hclass' : C.projectiveClassMap
      ⟨rationalPhase M.finalSmithInvariant D.smithNumerator, hrat'⟩ =
      C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ := by
    rw [← hclass]
    apply congrArg C.projectiveClassMap
    apply Subtype.ext
    exact hphaseRat.symm
  have hspos : 1 ≤ D.pivot.size := by
    rw [D.binaryPivotMinor_size]
    exact D.r_pos
  have hsle : D.pivot.size ≤ D.r := D.binaryPivotMinor_size.le
  exact C.exists_smithBoundedPhysicalRepresentative
    (C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩) hne
    hspos hsle M D.smithNumerator hrat' hclass'

end NormalizedDistanceThreePhaseSystem

/-- Construct the anchor-only distance-three phase system from two distinct
active sectors in local-`X` normalized form. -/
theorem exists_normalizedDistanceThreePhaseSystem [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (b0 b1 : C.ActiveResidue a) (hb01 : b0 ≠ b1)
    (hb0 : b0.1 = 0)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0) :
    Nonempty (C.NormalizedDistanceThreePhaseSystem hq a b0 b1) := by
  let r := C.normalizedActualSupportDimension a b0
  have hspan : C.actualSectorAffineSpan a b0 =
      C.actualSectorAffineSpan a b1 :=
    C.actualSectorAffineSpan_eq_of_hasDistanceAtLeast
      hq a hpres hd hd3 b0 b1
  obtain ⟨S⟩ := C.exists_anchorBinaryPivotSolution hq a b0 hb0
  have hsize : S.size = r := by
    exact S.size_eq_rank.trans (C.rank_anchorActualSupportMatrix a b0)
  have hrpos : 1 ≤ r :=
    C.normalizedActualSupportDimension_pos
      hq a hpres b0 b1 hb01 hzero hspan
  have hrle : r ≤ n := C.normalizedActualSupportDimension_le a b0
  have hrreal : r = Module.finrank ℝ
      (C.actualSectorAffineSpan a b0).direction := by
    rw [← hsize]
    exact C.anchorBinaryPivotSolution_size_eq_realAffineDimension
      hq a b0 hzero S
  obtain ⟨numerator, hnumerator⟩ :=
    S.exists_integral_finalSmithInvariant_smul_solution
  exact ⟨{
    affineSpan_eq := hspan
    r := r
    r_eq_dimension := rfl
    r_eq_realAffineDimension := hrreal
    r_pos := hrpos
    r_le := hrle
    pivot := S
    pivot_size_eq := hsize
    agreesOnAnchor :=
      C.anchorBinaryPivotSolution_agrees_on_anchor hq a b0 hb0 S
    agreesOnSecond :=
      C.anchorBinaryPivotSolution_agrees_on_sector_of_hasDistanceAtLeast
        hq a hpres hd hd3 b0 b1 hb0 S
    smithNumerator := numerator
    smithNumerator_spec := hnumerator }⟩

/-- A nontrivial modular action on a rank-two code has a second active
sector, so the preceding normalized construction applies without separately
supplying that sector. -/
theorem exists_normalizedDistanceThreePhaseSystem_of_rankTwo_nontrivial
    [NeZero q] (C : CodeProjector n 2)
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ ≠ 0)
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (b0 : C.ActiveResidue a) (hb0 : b0.1 = 0)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0) :
    ∃ b1 : C.ActiveResidue a,
      b0 ≠ b1 ∧
      (∀ b : C.ActiveResidue a, b = b0 ∨ b = b1) ∧
      Nonempty (C.NormalizedDistanceThreePhaseSystem hq a b0 b1) := by
  have hcard :=
    C.card_activeResidue_eq_two_of_projectiveClass_ne_zero
      hq a hpres hne
  obtain ⟨c0, c1, hc01, hexhaust⟩ :=
    C.exists_activeResidue_pair_of_card_eq_two a hcard
  rcases hexhaust b0 with hb0c0 | hb0c1
  · refine ⟨c1, ?_, ?_, ?_⟩
    · intro hb0c1
      apply hc01
      exact hb0c0.symm.trans hb0c1
    · intro b
      rcases hexhaust b with hbc0 | hbc1
      · exact Or.inl (hbc0.trans hb0c0.symm)
      · exact Or.inr hbc1
    · apply C.exists_normalizedDistanceThreePhaseSystem
        hq a hpres hd hd3 b0 c1
      · intro hb0c1
        apply hc01
        exact hb0c0.symm.trans hb0c1
      · exact hb0
      · exact hzero
  · refine ⟨c0, ?_, ?_, ?_⟩
    · intro hb0c0
      apply hc01
      exact hb0c0.symm.trans hb0c1
    · intro b
      rcases hexhaust b with hbc0 | hbc1
      · exact Or.inr hbc0
      · exact Or.inl (hbc1.trans hb0c1.symm)
    · apply C.exists_normalizedDistanceThreePhaseSystem
        hq a hpres hd hd3 b0 c0
      · intro hb0c0
        apply hc01
        exact hb0c0.symm.trans hb0c1
      · exact hb0
      · exact hzero

end CodeProjector

end

end QECC
