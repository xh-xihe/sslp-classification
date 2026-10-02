import QECC.GeneralRationalReplacement

namespace QECC

open scoped BigOperators
open Matrix

noncomputable section

/-- The canonical real lift in `[0,1)` of a modular residue phase. -/
def zmodPhaseLift (q : ℕ) (hq : 0 < q) (b : ZMod q) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 (zmodPhase q hq b)).1

@[simp] theorem coe_zmodPhaseLift (q : ℕ) (hq : 0 < q) (b : ZMod q) :
    ((zmodPhaseLift q hq b : ℝ) : LocalPhase) = zmodPhase q hq b := by
  change (AddCircle.equivIco (1 : ℝ) 0).symm
    (AddCircle.equivIco (1 : ℝ) 0 (zmodPhase q hq b)) = _
  exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply _

@[simp] theorem zmodPhaseLift_zero (q : ℕ) (hq : 0 < q) :
    zmodPhaseLift q hq 0 = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Ico 0 (0 + 1) := by norm_num
  have heq := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0) hmem
  simpa [zmodPhaseLift] using congrArg Subtype.val heq

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- An active residue other than the chosen anchor. -/
def NonAnchorActiveResidue (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) :=
  {b : C.ActiveResidue a // b ≠ b0}

noncomputable instance nonAnchorActiveResidueFintype [NeZero q]
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    Fintype (C.NonAnchorActiveResidue a b0) := by
  classical
  unfold NonAnchorActiveResidue
  infer_instance

/-- A row of the actual-support phase system: an active sector together with
one basis string in its actual support. -/
def ActualSectorPoint (a : Fin n → ZMod q) :=
  (b : C.ActiveResidue a) × C.actualSectorSupport a b

noncomputable instance actualSectorPointFintype [NeZero q]
    (a : Fin n → ZMod q) : Fintype (C.ActualSectorPoint a) := by
  classical
  unfold ActualSectorPoint
  infer_instance

/-- Number of auxiliary phase coordinates after omitting the anchor sector. -/
def sectorPhaseAuxCount [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) : ℕ :=
  Fintype.card (C.NonAnchorActiveResidue a b0)

/-- Omitting the anchor removes exactly one active-sector coordinate. -/
theorem sectorPhaseAuxCount_eq [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) :
    C.sectorPhaseAuxCount a b0 =
      Fintype.card (C.ActiveResidue a) - 1 := by
  classical
  unfold sectorPhaseAuxCount NonAnchorActiveResidue
  rw [Fintype.card_subtype_compl]
  simp

/-- Total number of columns in the normalized phase system. -/
def sectorPhaseSystemWidth [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) : ℕ :=
  n + C.sectorPhaseAuxCount a b0

theorem sectorPhaseSystemWidth_eq [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) :
    C.sectorPhaseSystemWidth a b0 =
      n + (Fintype.card (C.ActiveResidue a) - 1) := by
  rw [sectorPhaseSystemWidth, C.sectorPhaseAuxCount_eq]

/-- The requested `Fintype.equivFin` encoding of the non-anchor sectors. -/
def nonAnchorEquivFin [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) :
    C.NonAnchorActiveResidue a b0 ≃ Fin (C.sectorPhaseAuxCount a b0) :=
  Fintype.equivFin _

/-- Column occupied by a physical phase coordinate. -/
def physicalPhaseColumn [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) (j : Fin n) :
    Fin (C.sectorPhaseSystemWidth a b0) :=
  Fin.castAdd (C.sectorPhaseAuxCount a b0) j

/-- Column occupied by one non-anchor sector phase. -/
def auxiliaryPhaseColumn [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) (b : C.NonAnchorActiveResidue a b0) :
    Fin (C.sectorPhaseSystemWidth a b0) :=
  Fin.natAdd n (C.nonAnchorEquivFin a b0 b)

/-- The normalized zero-one phase matrix.  Its first `n` columns are the
physical incidence vector of a support point.  The remaining columns contain
one indicator for its non-anchor sector. -/
def sectorPhaseMatrix [NeZero q] (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) :
    Matrix (C.ActualSectorPoint a) (Fin (C.sectorPhaseSystemWidth a b0)) ℤ := by
  classical
  exact fun r ↦ Fin.addCases
    (fun j ↦ bitInt (r.2.1 j))
    (fun k ↦ if r.1 = ((C.nonAnchorEquivFin a b0).symm k).1 then 1 else 0)

/-- The normalized phase matrix is binary over the integers. -/
theorem sectorPhaseMatrix_isZeroOne [NeZero q]
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    Matrix.IsZeroOne (C.sectorPhaseMatrix a b0) := by
  classical
  intro r
  apply Fin.addCases
  · intro j
    cases hbit : r.2.1 j <;> simp [sectorPhaseMatrix, bitInt, hbit]
  · intro k
    by_cases hsector : r.1 = ((C.nonAnchorEquivFin a b0).symm k).1 <;>
      simp [sectorPhaseMatrix, hsector]

/-- The real vector consisting of the lifted physical phases followed by the
negatives of the non-anchor sector-phase lifts. -/
def sectorPhaseRealSolution [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    Fin (C.sectorPhaseSystemWidth a b0) → ℝ :=
  Fin.addCases
    (phaseLift (phaseHom n q hq a))
    (fun k ↦ -zmodPhaseLift q hq ((C.nonAnchorEquivFin a b0).symm k).1.1)

private theorem exists_integral_actualSectorEquation [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q) (b : C.ActiveResidue a)
    (x : BitString n) (hx : x ∈ C.actualSectorSupport a b) :
    ∃ z : ℤ,
      realSupportWeight (phaseLift (phaseHom n q hq a)) x -
          zmodPhaseLift q hq b.1 = (z : ℝ) := by
  have hfiber := C.actualSectorSupport_subset_fiber a b hx
  have hphase :
      ((realSupportWeight (phaseLift (phaseHom n q hq a)) x : ℝ) :
          LocalPhase) = ((zmodPhaseLift q hq b.1 : ℝ) : LocalPhase) := by
    calc
      ((realSupportWeight (phaseLift (phaseHom n q hq a)) x : ℝ) :
          LocalPhase) = supportPhase (phaseHom n q hq a) x :=
        supportPhase_lift _ _
      _ = zmodPhase q hq (subsetSum a x) := supportPhase_phaseHom hq a x
      _ = zmodPhase q hq b.1 := by rw [hfiber]
      _ = ((zmodPhaseLift q hq b.1 : ℝ) : LocalPhase) :=
        (coe_zmodPhaseLift q hq b.1).symm
  have hzero :
      (((realSupportWeight (phaseLift (phaseHom n q hq a)) x -
          zmodPhaseLift q hq b.1 : ℝ) : LocalPhase)) = 0 := by
    rw [AddCircle.coe_sub, hphase, sub_self]
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  exact ⟨z, by simpa using hz.symm⟩

/-- Integral right-hand side of the actual-support phase equations.  Its value
away from the actual support is immaterial and is set to zero. -/
def actualSectorPhaseRHS [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q) (b : C.ActiveResidue a) (x : BitString n) : ℤ := by
  classical
  exact if hx : x ∈ C.actualSectorSupport a b then
    Classical.choose (C.exists_integral_actualSectorEquation hq a b x hx)
  else 0

/-- Defining property of `actualSectorPhaseRHS` on the actual support. -/
theorem actualSectorPhaseRHS_spec [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q) (b : C.ActiveResidue a)
    (x : BitString n) (hx : x ∈ C.actualSectorSupport a b) :
    realSupportWeight (phaseLift (phaseHom n q hq a)) x -
        zmodPhaseLift q hq b.1 =
      (C.actualSectorPhaseRHS hq a b x : ℝ) := by
  rw [actualSectorPhaseRHS, dif_pos hx]
  simpa using Classical.choose_spec
    (C.exists_integral_actualSectorEquation hq a b x hx)

/-- Right-hand side indexed by the rows of the normalized binary system. -/
def sectorPhaseSystemRHS [NeZero q] (hq : 0 < q)
    (a : Fin n → ZMod q) : C.ActualSectorPoint a → ℤ :=
  fun r ↦ C.actualSectorPhaseRHS hq a r.1 r.2.1

/-- Decode the physical coordinates of a normalized phase-system vector. -/
def sectorPhasePhysicalPart {R : Type*} [NeZero q]
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (u : Fin (C.sectorPhaseSystemWidth a b0) → R) : Fin n → R :=
  fun j ↦ u (C.physicalPhaseColumn a b0 j)

/-- Decode sector phases, fixing the anchor phase to zero.  The stored
auxiliary coordinate is the negative of the decoded phase. -/
def sectorPhaseSectorPart {R : Type*} [Zero R] [Neg R] [NeZero q]
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (u : Fin (C.sectorPhaseSystemWidth a b0) → R) :
    C.ActiveResidue a → R := by
  classical
  exact fun b ↦ if hb : b = b0 then 0
    else -u (C.auxiliaryPhaseColumn a b0 ⟨b, hb⟩)

/-- Matrix multiplication is precisely physical support weight minus the
decoded sector phase. -/
theorem sectorPhaseMatrix_mulVec_real [NeZero q]
    (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (u : Fin (C.sectorPhaseSystemWidth a b0) → ℝ)
    (r : C.ActualSectorPoint a) :
    ((C.sectorPhaseMatrix a b0).map (Int.castRingHom ℝ)).mulVec u r =
      realSupportWeight (C.sectorPhasePhysicalPart a b0 u) r.2.1 -
        C.sectorPhaseSectorPart a b0 u r.1 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  change (∑ x : Fin (n + C.sectorPhaseAuxCount a b0),
    (C.sectorPhaseMatrix a b0).map (Int.castRingHom ℝ) r x * u x) = _
  rw [Fin.sum_univ_add]
  have hphysical :
      (∑ j : Fin n,
        (C.sectorPhaseMatrix a b0).map (Int.castRingHom ℝ) r
            (Fin.castAdd (C.sectorPhaseAuxCount a b0) j) *
          u (Fin.castAdd (C.sectorPhaseAuxCount a b0) j)) =
        realSupportWeight (C.sectorPhasePhysicalPart a b0 u) r.2.1 := by
    apply Finset.sum_congr rfl
    intro j _
    cases hbit : r.2.1 j <;>
      simp [sectorPhaseMatrix, sectorPhasePhysicalPart, physicalPhaseColumn,
        bitInt, bitReal, hbit]
  rw [hphysical]
  by_cases hb : r.1 = b0
  · have hsector : C.sectorPhaseSectorPart a b0 u r.1 = 0 := by
      simp [sectorPhaseSectorPart, hb]
    rw [hsector, sub_zero, add_eq_left]
    apply Finset.sum_eq_zero
    intro k _
    have hne : r.1 ≠ ((C.nonAnchorEquivFin a b0).symm k).1 :=
      fun h => ((C.nonAnchorEquivFin a b0).symm k).2 (h.symm.trans hb)
    simp [sectorPhaseMatrix, sectorPhaseSystemWidth, hne]
  · let b : C.NonAnchorActiveResidue a b0 := ⟨r.1, hb⟩
    have heq (k : Fin (C.sectorPhaseAuxCount a b0)) :
        (r.1 = ((C.nonAnchorEquivFin a b0).symm k).1) ↔
          C.nonAnchorEquivFin a b0 b = k := by
      constructor
      · intro h
        apply (C.nonAnchorEquivFin a b0).symm.injective
        apply Subtype.ext
        simpa [b] using h
      · intro h
        rw [← h]
        simp [b]
    have hsector : C.sectorPhaseSectorPart a b0 u r.1 =
        -u (C.auxiliaryPhaseColumn a b0 b) := by
      simp [sectorPhaseSectorPart, hb, b]
    rw [hsector, sub_neg_eq_add, add_right_inj]
    simp only [sectorPhaseMatrix, sectorPhaseSystemWidth, Matrix.map_apply,
      Fin.addCases_right]
    change (∑ k : Fin (C.sectorPhaseAuxCount a b0),
      ((if r.1 = ((C.nonAnchorEquivFin a b0).symm k).1
          then (1 : ℤ) else 0 : ℤ) : ℝ) * u (Fin.natAdd n k)) =
        u (C.auxiliaryPhaseColumn a b0 b)
    simp_rw [heq]
    simp [auxiliaryPhaseColumn]

@[simp] theorem sectorPhasePhysicalPart_realSolution [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) :
    C.sectorPhasePhysicalPart a b0 (C.sectorPhaseRealSolution hq a b0) =
      phaseLift (phaseHom n q hq a) := by
  funext j
  simp [sectorPhasePhysicalPart, sectorPhaseRealSolution,
    physicalPhaseColumn]

@[simp] theorem sectorPhaseSectorPart_realSolution [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (hb0 : b0.1 = 0) (b : C.ActiveResidue a) :
    C.sectorPhaseSectorPart a b0 (C.sectorPhaseRealSolution hq a b0) b =
      zmodPhaseLift q hq b.1 := by
  classical
  by_cases hb : b = b0
  · subst b
    simp [sectorPhaseSectorPart, hb0]
  · let b' : C.NonAnchorActiveResidue a b0 := ⟨b, hb⟩
    simp [sectorPhaseSectorPart, sectorPhaseRealSolution,
      auxiliaryPhaseColumn, hb]

/-- The phase lifts solve the normalized binary system over the reals. -/
theorem sectorPhaseRealSolution_solves [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (hb0 : b0.1 = 0) :
    ((C.sectorPhaseMatrix a b0).map (Int.castRingHom ℝ)).mulVec
        (C.sectorPhaseRealSolution hq a b0) =
      fun r ↦ (C.sectorPhaseSystemRHS hq a r : ℝ) := by
  funext r
  rw [C.sectorPhaseMatrix_mulVec_real]
  rw [C.sectorPhasePhysicalPart_realSolution,
    C.sectorPhaseSectorPart_realSolution hq a b0 hb0]
  exact C.actualSectorPhaseRHS_spec hq a r.1 r.2.1 r.2.2

/-- The anchor equation at the zero bit string has zero right-hand side. -/
theorem actualSectorPhaseRHS_anchor_zero [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q) (b0 : C.ActiveResidue a)
    (hb0 : b0.1 = 0)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0) :
    C.actualSectorPhaseRHS hq a b0 0 = 0 := by
  have hspec := C.actualSectorPhaseRHS_spec hq a b0 0 hzero
  rw [hb0, zmodPhaseLift_zero] at hspec
  have hweight :
      realSupportWeight (phaseLift (phaseHom n q hq a)) (0 : BitString n) = 0 := by
    simp [realSupportWeight, bitReal]
  rw [hweight, zero_sub] at hspec
  norm_num at hspec
  exact_mod_cast hspec.symm

/-- The normalized actual-support system has a rational pivot solution. -/
theorem exists_sectorPhasePivot [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (b0 : C.ActiveResidue a) (hb0 : b0.1 = 0) :
    Nonempty (BinaryPivotSolution
      (C.sectorPhaseSystemWidth a b0)
      (C.sectorPhaseMatrix a b0)
      (C.sectorPhaseSystemRHS hq a)) := by
  apply exists_binaryPivotSolution
    (C.sectorPhaseMatrix a b0) (C.sectorPhaseSystemRHS hq a)
    (C.sectorPhaseMatrix_isZeroOne a b0)
  exact ⟨C.sectorPhaseRealSolution hq a b0,
    C.sectorPhaseRealSolution_solves hq a b0 hb0⟩

/-- The normalized system together with the hypotheses that identify it with
the normalized phase-sector situation in Section III.C. -/
structure NormalizedSectorPhasePivot [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q) (b0 : C.ActiveResidue a) where
  preserves : C.Preserves (phaseHom n q hq a)
  anchor_eq_zero : b0.1 = 0
  zero_mem_anchor : (0 : BitString n) ∈ C.actualSectorSupport a b0
  pivot : BinaryPivotSolution
    (C.sectorPhaseSystemWidth a b0)
    (C.sectorPhaseMatrix a b0)
    (C.sectorPhaseSystemRHS hq a)

theorem exists_normalizedSectorPhasePivot [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b0 : C.ActiveResidue a) (hb0 : b0.1 = 0)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0) :
    Nonempty (C.NormalizedSectorPhasePivot hq a b0) := by
  obtain ⟨S⟩ := C.exists_sectorPhasePivot hq a b0 hb0
  exact ⟨{
    preserves := hpres
    anchor_eq_zero := hb0
    zero_mem_anchor := hzero
    pivot := S }⟩

namespace SectorPhasePivot

variable [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
  (b0 : C.ActiveResidue a)
  (S : BinaryPivotSolution
    (C.sectorPhaseSystemWidth a b0)
    (C.sectorPhaseMatrix a b0)
    (C.sectorPhaseSystemRHS hq a))

/-- Rational physical coordinates extracted from the pivot solution. -/
def physical : Fin n → ℚ :=
  C.sectorPhasePhysicalPart a b0 S.solution

/-- Rational sector phases extracted from the pivot solution, with anchor
phase fixed to zero. -/
def sector : C.ActiveResidue a → ℚ :=
  C.sectorPhaseSectorPart a b0 S.solution

/-- Cast the complete rational pivot solution to a real vector. -/
def realSolution : Fin (C.sectorPhaseSystemWidth a b0) → ℝ :=
  fun k ↦ (S.solution k : ℝ)

@[simp] theorem physical_realSolution :
    C.sectorPhasePhysicalPart a b0 (realSolution C hq a b0 S) =
      fun j ↦ (physical C hq a b0 S j : ℝ) := by
  rfl

@[simp] theorem sector_realSolution :
    C.sectorPhaseSectorPart a b0 (realSolution C hq a b0 S) =
      fun b ↦ (sector C hq a b0 S b : ℝ) := by
  classical
  funext b
  by_cases hb : b = b0 <;>
    simp [sector, realSolution, sectorPhaseSectorPart, hb]

/-- The extracted rational physical and sector coordinates solve all actual
support equations after casting to the reals. -/
theorem solvesActualSectorEquations :
    C.SolvesActualSectorEquations a (C.actualSectorPhaseRHS hq a)
      (fun j ↦ (physical C hq a b0 S j : ℝ))
      (fun b ↦ (sector C hq a b0 S b : ℝ)) := by
  intro b x hx
  let r : C.ActualSectorPoint a := ⟨b, ⟨x, hx⟩⟩
  have hs := congrFun S.solves r
  have hsReal :
      ((C.sectorPhaseMatrix a b0).map (Int.castRingHom ℝ)).mulVec
          (realSolution C hq a b0 S) r =
        (C.sectorPhaseSystemRHS hq a r : ℝ) := by
    have hsCast := congrArg (fun t : ℚ ↦ (t : ℝ)) hs
    simp only [Matrix.mulVec, dotProduct] at hsCast ⊢
    push_cast at hsCast
    simpa [Matrix.map_apply, realSolution] using hsCast
  rw [C.sectorPhaseMatrix_mulVec_real] at hsReal
  simpa [r] using hsReal

/-- The difference between the rational physical solution and the original
phase lift is constant on each actual sector.  The displayed right-hand side
is the constant for sector `b`. -/
theorem difference_constant_on_actualSector
    (b : C.ActiveResidue a)
    (x : BitString n) (hx : x ∈ C.actualSectorSupport a b) :
    realSupportWeight
        ((fun j ↦ (physical C hq a b0 S j : ℝ)) -
          phaseLift (phaseHom n q hq a)) x =
      (sector C hq a b0 S b : ℝ) - zmodPhaseLift q hq b.1 := by
  have horiginal :
      C.SolvesActualSectorEquations a (C.actualSectorPhaseRHS hq a)
        (phaseLift (phaseHom n q hq a))
        (fun c ↦ zmodPhaseLift q hq c.1) := by
    intro c y hy
    exact C.actualSectorPhaseRHS_spec hq a c y hy
  have hrational := solvesActualSectorEquations C hq a b0 S
  exact C.supportWeight_sub_eq_sectorPhase_sub_of_solvesActualSectorEquations
    a (C.actualSectorPhaseRHS hq a) horiginal hrational b x hx

/-- Equivalent pairwise form of sectorwise constancy. -/
theorem difference_eq_on_actualSector
    (b : C.ActiveResidue a)
    {x y : BitString n} (hx : x ∈ C.actualSectorSupport a b)
    (hy : y ∈ C.actualSectorSupport a b) :
    realSupportWeight
        ((fun j ↦ (physical C hq a b0 S j : ℝ)) -
          phaseLift (phaseHom n q hq a)) x =
      realSupportWeight
        ((fun j ↦ (physical C hq a b0 S j : ℝ)) -
          phaseLift (phaseHom n q hq a)) y := by
  rw [difference_constant_on_actualSector C hq a b0 S b x hx,
    difference_constant_on_actualSector C hq a b0 S b y hy]

end SectorPhasePivot

namespace NormalizedSectorPhasePivot

variable [NeZero q] {hq : 0 < q} {a : Fin n → ZMod q}
  {b0 : C.ActiveResidue a}

/-- Rational physical coordinates supplied by the normalized pivot. -/
def rationalPhysical (P : C.NormalizedSectorPhasePivot hq a b0) : Fin n → ℚ :=
  SectorPhasePivot.physical C hq a b0 P.pivot

/-- Rational auxiliary sector phases supplied by the normalized pivot. -/
def rationalSector (P : C.NormalizedSectorPhasePivot hq a b0) :
    C.ActiveResidue a → ℚ :=
  SectorPhasePivot.sector C hq a b0 P.pivot

/-- The rational physical coordinates differ from the original lifted phase
by a real support weight that is constant on each actual sector. -/
theorem rationalPhysical_difference_constant
    (P : C.NormalizedSectorPhasePivot hq a b0)
    (b : C.ActiveResidue a) (x : BitString n)
    (hx : x ∈ C.actualSectorSupport a b) :
    realSupportWeight
        ((fun j ↦ (rationalPhysical C P j : ℝ)) -
          phaseLift (phaseHom n q hq a)) x =
      (rationalSector C P b : ℝ) - zmodPhaseLift q hq b.1 := by
  exact SectorPhasePivot.difference_constant_on_actualSector
    C hq a b0 P.pivot b x hx

/-- Pairwise form of `rationalPhysical_difference_constant`. -/
theorem rationalPhysical_difference_eq
    (P : C.NormalizedSectorPhasePivot hq a b0)
    (b : C.ActiveResidue a) {x y : BitString n}
    (hx : x ∈ C.actualSectorSupport a b)
    (hy : y ∈ C.actualSectorSupport a b) :
    realSupportWeight
        ((fun j ↦ (rationalPhysical C P j : ℝ)) -
          phaseLift (phaseHom n q hq a)) x =
      realSupportWeight
        ((fun j ↦ (rationalPhysical C P j : ℝ)) -
          phaseLift (phaseHom n q hq a)) y := by
  exact SectorPhasePivot.difference_eq_on_actualSector
    C hq a b0 P.pivot b hx hy

end NormalizedSectorPhasePivot

end CodeProjector

end

end QECC
