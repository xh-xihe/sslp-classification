import Mathlib
import MainTheory.CodeSpec
import MainTheory.PhaseSectorFull
import MainTheory.ColoredSystem
import MainTheory.Rationalize
import MainTheory.Denominator
import MainTheory.SharpClearing

/-!
# Coloured rationalization to a primitive finite lift

This file connects the phase-sector theorem to the algebraic finite-lift
construction in Theorems 2.4 and 3.2 of `documents/20260822/main.tex`.

For a supplied `SectorDecomposition`, every row is indexed by an *actual*
support point.  To avoid hiding the local-`X` normalization in an assumption,
the physical part of a row is `x - x₀`, where `x₀` is chosen from the
reference sector.  Its entries are integral (`-1, 0, 1`).  The colour part is
zero on the reference sector and a distinct basis vector on every other
sector.  Phase congruence supplies the integral right-hand side.

The common first moment proves, rather than assumes, that rationalization fixes
all relative logical phases.  We then clear only the physical coordinates by
their least common denominator and prove primitivity.  Finally an explicitly
connected square pivot system carrying a `SharpClearing.SmithWitness` gives
the sharp divisibility by its final Smith factor.
-/

namespace MainTheory.FiniteLift

open scoped BigOperators
open MainTheory.PhaseSectorFull

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

/-- The flattened sector eigenbasis, reindexed by the logical-frame index. -/
def reindexedSectorFrame {K : ℕ} (D : SectorDecomposition n t theta)
    (e : Fin K ≃ D.Index) : CodeSpec.OrthonormalFrame n K where
  vec k := D.vec (e k)
  orthonormal i j := by
    rw [D.orthonormal]
    simp only [e.injective.eq_iff]

/-- Explicit identification between an exact code and the flattened logical
frame carried by a sector decomposition.  The sector eigenvectors may be any
orthonormal basis of the actual code space; they need not be a permutation of
the distinguished frame stored in `C`. -/
structure ExactCodeSectorLink {K d : ℕ}
    (C : CodeSpec.ExactCode n K d)
    (D : SectorDecomposition n t theta) where
  reindex : Fin K ≃ D.Index
  span_eq : CodeSpec.codeSpan C.frame =
    CodeSpec.codeSpan (reindexedSectorFrame D reindex)

/-- Compatibility constructor for the former, stronger interface in which
the sector frame was literally a reindexing of `C.frame`. -/
def ExactCodeSectorLink.ofFrameEq {K d : ℕ}
    {C : CodeSpec.ExactCode n K d} {D : SectorDecomposition n t theta}
    (e : Fin K ≃ D.Index) (frame_eq : ∀ k, C.frame.vec k = D.vec (e k)) :
    ExactCodeSectorLink C D where
  reindex := e
  span_eq := by
    apply congrArg (Submodule.span ℂ)
    ext phi
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (frame_eq k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, frame_eq k⟩

/-- Distance at least two on the actual exact code supplies the `Z` equations
used by the coloured construction, through the explicit frame link. -/
theorem ExactCodeSectorLink.zDetects {K d : ℕ}
    {C : CodeSpec.ExactCode n K d} {D : SectorDecomposition n t theta}
    (link : ExactCodeSectorLink C D) (hd : 2 ≤ d) : ZDetects D := by
  apply zDetects_of_hasDistance_reindex D link.reindex
  · exact CodeSpec.hasDistance_of_codeSpan_eq C.frame
      (reindexedSectorFrame D link.reindex) link.span_eq C.hasDistance
  · exact hd

/-- The canonical reference sector.  `sectorCount_pos` makes index zero valid. -/
def baseSector (D : SectorDecomposition n t theta) : Fin t :=
  ⟨0, D.sectorCount_pos⟩

/-- All nonreference sectors, used as colour coordinates. -/
abbrev Color (D : SectorDecomposition n t theta) :=
  {alpha : Fin t // alpha ≠ baseSector D}

/-- An index is exactly one computational-basis point in one sector support. -/
abbrev SupportIndex (D : SectorDecomposition n t theta) (alpha : Fin t) :=
  {x : SS.BitString n // x ∈ sectorSupport D alpha}

/-- Fix one coherent finite enumeration of each support subtype.  Without this
named instance, unrelated generic `Finite → Fintype` bridges can make two
extensionally equal finite sums use definitionally different enumerations. -/
noncomputable instance supportIndexFintype
    (D : SectorDecomposition n t theta) (alpha : Fin t) :
    Fintype (SupportIndex D alpha) :=
  Fintype.ofFinite (SupportIndex D alpha)

/-- A chosen point of the nonempty reference support. -/
noncomputable def basePoint (D : SectorDecomposition n t theta) : SS.BitString n :=
  Classical.choose (sectorSupport_nonempty D (baseSector D))

theorem basePoint_mem (D : SectorDecomposition n t theta) :
    basePoint D ∈ sectorSupport D (baseSector D) :=
  Classical.choose_spec (sectorSupport_nonempty D (baseSector D))

/-- Boolean occupation as a rational number. -/
def bitQ (x : SS.BitString n) (j : Fin n) : ℚ :=
  if x j then 1 else 0

/-- Physical row `x - x₀`; this is the normalization-free version of the
paper's locally-X-normalized binary row. -/
def physicalRow (D : SectorDecomposition n t theta) (alpha : Fin t)
    (x : SupportIndex D alpha) (j : Fin n) : ℚ :=
  bitQ x.1 j - bitQ (basePoint D) j

/-- Reference colour is zero; every nonreference sector owns one basis colour. -/
def colorRow (D : SectorDecomposition n t theta) (alpha : Fin t)
    (g : Color D) : ℚ :=
  if alpha = g.1 then 1 else 0

/-- The augmented rational matrix generated by all and only sector-support
points. -/
def coloredMatrix (D : SectorDecomposition n t theta) :
    Matrix (Sigma (SupportIndex D)) (Sum (Fin n) (Color D)) ℚ :=
  ColoredSystem.augmentedMatrix (physicalRow D) (colorRow D)

/-- Sector-projector probabilities restricted to their actual supports. -/
def supportWeight (D : SectorDecomposition n t theta) (alpha : Fin t)
    (x : SupportIndex D alpha) : ℝ :=
  sectorProbability D alpha x.1

theorem sectorProbability_eq_zero_of_not_mem
    (D : SectorDecomposition n t theta) (alpha : Fin t) (x : SS.BitString n)
    (hx : x ∉ sectorSupport D alpha) : sectorProbability D alpha x = 0 := by
  apply le_antisymm
  · exact not_lt.mp hx
  · exact sectorProbability_nonneg D alpha x

theorem supportWeight_sum_eq_one (D : SectorDecomposition n t theta)
    (alpha : Fin t) : ∑ x, supportWeight D alpha x = 1 := by
  classical
  let s : Finset (SS.BitString n) :=
    Finset.univ.filter (fun x ↦ x ∈ sectorSupport D alpha)
  calc
    (∑ x, supportWeight D alpha x) =
        (∑ x ∈ s, sectorProbability D alpha x) := by
      exact (Finset.sum_subtype s (by simp [s])
        (fun x ↦ sectorProbability D alpha x)).symm
    _ = (∑ x : SS.BitString n, sectorProbability D alpha x) := by
      simp only [s, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ sectorSupport D alpha
      · simp [hx]
      · simp [hx, sectorProbability_eq_zero_of_not_mem D alpha x hx]
    _ = 1 := sectorProbability_sum_eq_one D alpha

theorem sum_support_eq_sum (D : SectorDecomposition n t theta)
    (alpha : Fin t) (f : SS.BitString n → ℝ) :
    (∑ x : SupportIndex D alpha, sectorProbability D alpha x.1 * f x.1) =
      ∑ x : SS.BitString n, sectorProbability D alpha x * f x := by
  classical
  let s : Finset (SS.BitString n) :=
    Finset.univ.filter (fun x ↦ x ∈ sectorSupport D alpha)
  calc
    (∑ x : SupportIndex D alpha,
        sectorProbability D alpha x.1 * f x.1) =
        (∑ x ∈ s, sectorProbability D alpha x * f x) := by
      exact (Finset.sum_subtype s (by simp [s])
        (fun x ↦ sectorProbability D alpha x * f x)).symm
    _ = ∑ x : SS.BitString n, sectorProbability D alpha x * f x := by
      simp only [s, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ sectorSupport D alpha
      · simp [hx]
      · simp [hx, sectorProbability_eq_zero_of_not_mem D alpha x hx]

@[simp] theorem bitQ_cast (x : SS.BitString n) (j : Fin n) :
    (bitQ x j : ℝ) = coordinate x j := by
  by_cases h : x j <;> simp [bitQ, coordinate, h]

theorem supportWeight_physical_mean (D : SectorDecomposition n t theta)
    (alpha : Fin t) (j : Fin n) :
    (∑ x, supportWeight D alpha x * (physicalRow D alpha x j : ℝ)) =
      sectorMean D alpha j - coordinate (basePoint D) j := by
  rw [show (∑ x, supportWeight D alpha x *
      (physicalRow D alpha x j : ℝ)) =
      ∑ x : SS.BitString n, sectorProbability D alpha x *
        (coordinate x j - coordinate (basePoint D) j) by
    rw [← sum_support_eq_sum D alpha
      (fun x ↦ coordinate x j - coordinate (basePoint D) j)]
    apply Finset.sum_congr rfl
    intro x _
    simp [supportWeight, physicalRow]]
  simp only [mul_sub, Finset.sum_sub_distrib, sectorMean]
  rw [← Finset.sum_mul, sectorProbability_sum_eq_one]
  ring

theorem physical_mean_eq_base (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (alpha : Fin t) (j : Fin n) :
    (∑ x, supportWeight D alpha x * (physicalRow D alpha x j : ℝ)) =
      ∑ x, supportWeight D (baseSector D) x *
        (physicalRow D (baseSector D) x j : ℝ) := by
  rw [supportWeight_physical_mean, supportWeight_physical_mean,
    sectorMean_eq_of_ZDetects D hZ alpha (baseSector D) j]

theorem colorRow_base (D : SectorDecomposition n t theta) (g : Color D) :
    colorRow D (baseSector D) g = 0 := by
  have hne : baseSector D ≠ g.1 := Ne.symm g.property
  simp [colorRow, hne]

theorem colorRow_owner (D : SectorDecomposition n t theta) (g h : Color D) :
    colorRow D g.1 h = if h = g then 1 else 0 := by
  by_cases hh : h = g
  · subst h
    simp [colorRow]
  · have hv : g.1 ≠ h.1 := by
      intro heq
      exact hh (Subtype.ext heq.symm)
    simp [colorRow, hh, hv]

/-- The original real unknown: physical angles followed by negative relative
sector phases. -/
def realUnknown (D : SectorDecomposition n t theta) :
    Sum (Fin n) (Color D) → ℝ
  | Sum.inl j => theta j
  | Sum.inr g => -(D.phase g.1 - D.phase (baseSector D))

theorem color_dot_realUnknown (D : SectorDecomposition n t theta)
    (alpha : Fin t) :
    (∑ g : Color D, (colorRow D alpha g : ℝ) *
      realUnknown D (Sum.inr g)) =
      -(D.phase alpha - D.phase (baseSector D)) := by
  classical
  by_cases ha : alpha = baseSector D
  · subst alpha
    simp [colorRow_base, realUnknown]
  · let g0 : Color D := ⟨alpha, ha⟩
    rw [Fintype.sum_eq_single g0]
    · simp [colorRow, realUnknown, g0]
    · intro g hg
      have hv : alpha ≠ g.1 := by
        intro hval
        apply hg
        exact Subtype.ext hval.symm
      simp [colorRow, hv]

theorem physicalRow_dot_theta (D : SectorDecomposition n t theta)
    (eta : Fin n → ℝ) (alpha : Fin t) (x : SupportIndex D alpha) :
    (∑ j, (physicalRow D alpha x j : ℝ) * eta j) =
      MainTheory.RealGate.angle eta x.1 -
        MainTheory.RealGate.angle eta (basePoint D) := by
  rw [MainTheory.RealGate.angle, MainTheory.RealGate.angle,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : x.1 j <;> by_cases hb : basePoint D j <;>
    simp [physicalRow, bitQ, hx, hb]

/-- Integer chosen from the phase congruence at one actual support row. -/
noncomputable def phaseInteger (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SupportIndex D alpha) : ℤ :=
  Classical.choose (phase_congruence D alpha x.1 x.2)

theorem phaseInteger_spec (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SupportIndex D alpha) :
    MainTheory.RealGate.angle theta x.1 - D.phase alpha =
      (phaseInteger D alpha x : ℝ) :=
  Classical.choose_spec (phase_congruence D alpha x.1 x.2)

/-- The actual reference support row, as a support-index element. -/
noncomputable def baseSupportIndex (D : SectorDecomposition n t theta) :
    SupportIndex D (baseSector D) :=
  ⟨basePoint D, basePoint_mem D⟩

/-- Integral right-hand side obtained by subtracting the reference phase
congruence from every support-row congruence. -/
noncomputable def coloredRhs (D : SectorDecomposition n t theta) :
    Sigma (SupportIndex D) → ℤ :=
  fun r ↦ phaseInteger D r.1 r.2 -
    phaseInteger D (baseSector D) (baseSupportIndex D)

/-- Rational view of the integral right-hand side. -/
noncomputable def coloredRhsQ (D : SectorDecomposition n t theta) :
    Sigma (SupportIndex D) → ℚ :=
  fun r ↦ (coloredRhs D r : ℚ)

/-- The original real angles and relative phases solve the concrete matrix
generated by every support point. -/
theorem coloredMatrix_realSolution (D : SectorDecomposition n t theta) :
    ((coloredMatrix D).map (algebraMap ℚ ℝ)).mulVec (realUnknown D) =
      fun r ↦ algebraMap ℚ ℝ (coloredRhsQ D r) := by
  funext r
  rcases r with ⟨alpha, x⟩
  simp only [coloredMatrix, ColoredSystem.augmentedMatrix,
    ColoredSystem.augmentedRow, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Fintype.sum_sum_type, realUnknown]
  change (∑ j, (physicalRow D alpha x j : ℝ) * theta j) +
      (∑ g : Color D, (colorRow D alpha g : ℝ) *
        -(D.phase g.1 - D.phase (baseSector D))) =
    (coloredRhsQ D ⟨alpha, x⟩ : ℝ)
  have hc : (∑ g : Color D, (colorRow D alpha g : ℝ) *
      -(D.phase g.1 - D.phase (baseSector D))) =
      -(D.phase alpha - D.phase (baseSector D)) := by
    simpa [realUnknown] using color_dot_realUnknown D alpha
  rw [physicalRow_dot_theta D theta, hc]
  have hx := phaseInteger_spec D alpha x
  have hb := phaseInteger_spec D (baseSector D) (baseSupportIndex D)
  change MainTheory.RealGate.angle theta (basePoint D) -
      D.phase (baseSector D) =
    (phaseInteger D (baseSector D) (baseSupportIndex D) : ℝ) at hb
  change (MainTheory.RealGate.angle theta x.1 -
      MainTheory.RealGate.angle theta (basePoint D)) +
      -(D.phase alpha - D.phase (baseSector D)) =
    (((phaseInteger D alpha x -
      phaseInteger D (baseSector D) (baseSupportIndex D) : ℤ) : ℚ) : ℝ)
  push_cast
  linear_combination hx - hb

/-! ## Protected rationalization -/

/-- A rational solution of the concrete all-support coloured system, together
with the kernel-protected equality of every relative-phase coordinate. -/
structure RationalColoredLift (D : SectorDecomposition n t theta) where
  augmented : Sum (Fin n) (Color D) → ℚ
  solves : (coloredMatrix D).mulVec augmented = coloredRhsQ D
  color_preserved : ∀ g,
    (augmented (Sum.inr g) : ℝ) = realUnknown D (Sum.inr g)

/-- The rational physical angle coordinates extracted from a coloured lift. -/
def RationalColoredLift.physical {D : SectorDecomposition n t theta}
    (L : RationalColoredLift D) : Fin n → ℚ :=
  fun j ↦ L.augmented (Sum.inl j)

/-- **Protected rationalization headline.**  Exact one-qubit `Z` detection and
the complete sector decomposition produce a rational solution of the concrete
all-support system, with every relative logical phase unchanged. -/
theorem exists_rationalColoredLift (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) : Nonempty (RationalColoredLift D) := by
  let owner : Color D → Fin t := fun g ↦ g.1
  obtain ⟨uQ, huQ, hcolor⟩ :=
    ColoredSystem.exists_rational_solution_preserving_colors
      (pt := physicalRow D) (col := colorRow D) (p := supportWeight D)
      (base := baseSector D) (owner := owner)
      (supportWeight_sum_eq_one D)
      (physical_mean_eq_base D hZ)
      (colorRow_base D) (colorRow_owner D)
      (rhs := coloredRhsQ D) (u := realUnknown D)
      (coloredMatrix_realSolution D)
  exact ⟨⟨uQ, huQ, hcolor⟩⟩

/-- The rational physical angles realize exactly the same relative sector
phases as the original real gate.  This is an explicit congruence statement,
not a name attached to the system-solving field. -/
theorem RationalColoredLift.same_relative_sector_phases
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (alpha : Fin t) (x : SupportIndex D alpha) :
    ∃ k : ℤ,
      MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ)) x.1 -
        MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ))
          (basePoint D) -
        (D.phase alpha - D.phase (baseSector D)) = (k : ℝ) := by
  classical
  refine ⟨coloredRhs D ⟨alpha, x⟩, ?_⟩
  have hrow := congrFun L.solves ⟨alpha, x⟩
  have hrowR := congrArg (algebraMap ℚ ℝ) hrow
  have hcolors :
      (∑ g : Color D, (colorRow D alpha g : ℝ) *
        (L.augmented (Sum.inr g) : ℝ)) =
        -(D.phase alpha - D.phase (baseSector D)) := by
    calc
      (∑ g : Color D, (colorRow D alpha g : ℝ) *
          (L.augmented (Sum.inr g) : ℝ)) =
          ∑ g : Color D, (colorRow D alpha g : ℝ) *
            realUnknown D (Sum.inr g) := by
              apply Finset.sum_congr rfl
              intro g _
              rw [L.color_preserved]
      _ = -(D.phase alpha - D.phase (baseSector D)) :=
        color_dot_realUnknown D alpha
  have hphysical :
      (∑ j, (physicalRow D alpha x j : ℝ) *
        (L.physical j : ℝ)) =
        MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ)) x.1 -
          MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ))
            (basePoint D) :=
    physicalRow_dot_theta D (fun j ↦ (L.physical j : ℝ)) alpha x
  have hrowR' :
      (∑ j, (physicalRow D alpha x j : ℝ) *
        (L.augmented (Sum.inl j) : ℝ)) +
      (∑ g : Color D, (colorRow D alpha g : ℝ) *
        (L.augmented (Sum.inr g) : ℝ)) =
      (coloredRhs D ⟨alpha, x⟩ : ℝ) := by
    simpa [coloredMatrix, ColoredSystem.augmentedMatrix,
      ColoredSystem.augmentedRow, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, coloredRhsQ] using hrowR
  change MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ)) x.1 -
      MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ))
        (basePoint D) -
      (D.phase alpha - D.phase (baseSector D)) =
    (coloredRhs D ⟨alpha, x⟩ : ℝ)
  rw [← hphysical]
  calc
    (∑ j, (physicalRow D alpha x j : ℝ) * (L.physical j : ℝ)) -
        (D.phase alpha - D.phase (baseSector D)) =
        (∑ j, (physicalRow D alpha x j : ℝ) * (L.physical j : ℝ)) +
          (∑ g : Color D, (colorRow D alpha g : ℝ) *
            (L.augmented (Sum.inr g) : ℝ)) := by rw [hcolors]; ring
    _ = (coloredRhs D ⟨alpha, x⟩ : ℝ) := hrowR'

/-! ## Least-denominator primitive lift -/

/-- The least positive denominator clearing all physical angle coordinates. -/
def RationalColoredLift.order {D : SectorDecomposition n t theta}
    (L : RationalColoredLift D) : ℕ :=
  Denominator.lcmDen L.physical

/-- Integral physical angle numerators at the least denominator. -/
noncomputable def RationalColoredLift.numerator
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D) :
    Fin n → ℤ :=
  Denominator.liftNum L.physical

theorem RationalColoredLift.order_pos
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D) :
    0 < L.order :=
  Denominator.lcmDen_pos L.physical

theorem RationalColoredLift.numerator_spec
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (j : Fin n) :
    (L.order : ℚ) * L.physical j = (L.numerator j : ℚ) :=
  Denominator.liftNum_spec L.physical j

/-- Minimal denominator implies the exact gcd-style primitivity condition:
no natural `d > 1` divides both the modulus and every integer numerator. -/
theorem RationalColoredLift.primitive
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (d : ℕ) (hdq : d ∣ L.order)
    (hda : ∀ j, (d : ℤ) ∣ L.numerator j) : d = 1 :=
  Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum
    L.physical d hdq hda

/-- Integer subset sum of the cleared physical numerators. -/
def RationalColoredLift.angleNumerator
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (x : SS.BitString n) : ℤ :=
  ∑ j, L.numerator j * if x j then 1 else 0

theorem RationalColoredLift.order_mul_angle
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (x : SS.BitString n) :
    (L.order : ℝ) *
        MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ)) x =
      (L.angleNumerator x : ℝ) := by
  change (L.order : ℝ) *
      (∑ j, (L.physical j : ℝ) * if x j then 1 else 0) =
    ((∑ j, L.numerator j * if x j then 1 else 0 : ℤ) : ℝ)
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have hjQ := L.numerator_spec j
  have hjR : (L.order : ℝ) * (L.physical j : ℝ) =
      (L.numerator j : ℝ) := by
    exact_mod_cast hjQ
  by_cases hx : x j <;> simp [hx, hjR]

/-- Every relative logical phase is cleared by the *same physical* least
denominator.  This is the precise content behind `m ∣ q`: all projective
logical eigenvalue ratios are `q`-th roots of unity. -/
theorem RationalColoredLift.relative_phase_cleared
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (alpha : Fin t) :
    ∃ b : ℤ,
      (L.order : ℝ) * (D.phase alpha - D.phase (baseSector D)) =
        (b : ℝ) := by
  let x : SupportIndex D alpha :=
    ⟨Classical.choose (sectorSupport_nonempty D alpha),
      Classical.choose_spec (sectorSupport_nonempty D alpha)⟩
  obtain ⟨k, hk⟩ := L.same_relative_sector_phases alpha x
  refine ⟨L.angleNumerator x.1 - L.angleNumerator (basePoint D) -
    (L.order : ℤ) * k, ?_⟩
  have hx := L.order_mul_angle x.1
  have hb := L.order_mul_angle (basePoint D)
  push_cast
  linear_combination hx - hb - (L.order : ℝ) * hk

/-- A new real diagonal angle vector induces the same projective action on all
displayed logical sector vectors when it differs from the original gate by one
common nonzero scalar. -/
def SameProjectiveSectorAction (D : SectorDecomposition n t theta)
    (eta : Fin n → ℝ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ u : D.Index,
    MainTheory.RealGate.realGate eta (D.vec u) =
      fun x ↦ c * MainTheory.RealGate.realGate theta (D.vec u) x

theorem vec_ne_zero_mem_sectorSupport (D : SectorDecomposition n t theta)
    (u : D.Index) (x : SS.BitString n) (hx : D.vec u x ≠ 0) :
    x ∈ sectorSupport D u.1 := by
  change 0 < sectorProjectorDiag D u.1 x / (D.rank u.1 : ℝ)
  apply div_pos
  · apply Finset.sum_pos'
    · intro r _
      exact Complex.normSq_nonneg _
    · exact ⟨u.2, Finset.mem_univ _, Complex.normSq_pos.mpr hx⟩
  · exact_mod_cast D.rank_pos u.1

private theorem exp_angle_eq_common_mul_phase
    (etaAngle baseAngle phase basePhase : ℝ) (k : ℤ)
    (h : etaAngle - baseAngle - (phase - basePhase) = (k : ℝ)) :
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (etaAngle : ℂ)) =
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
            ((baseAngle - basePhase : ℝ) : ℂ)) *
        phaseExp phase := by
  rw [phaseExp, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  have hc : (etaAngle : ℂ) - (baseAngle : ℂ) -
      ((phase : ℂ) - (basePhase : ℂ)) = (k : ℂ) := by
    exact_mod_cast h
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hc

/-- The support congruences are promoted to equality of the actual logical
actions, up to one common nonzero scalar. -/
theorem RationalColoredLift.same_projective_sector_action
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D) :
    SameProjectiveSectorAction D (fun j ↦ (L.physical j : ℝ)) := by
  let eta : Fin n → ℝ := fun j ↦ (L.physical j : ℝ)
  let c : ℂ := Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I *
      ((MainTheory.RealGate.angle eta (basePoint D) -
        D.phase (baseSector D) : ℝ) : ℂ))
  refine ⟨c, Complex.exp_ne_zero _, ?_⟩
  intro u
  funext x
  by_cases hx : D.vec u x = 0
  · simp [MainTheory.RealGate.realGate, hx]
  · let sx : SupportIndex D u.1 :=
      ⟨x, vec_ne_zero_mem_sectorSupport D u x hx⟩
    obtain ⟨k, hk⟩ := L.same_relative_sector_phases u.1 sx
    have hexp := exp_angle_eq_common_mul_phase
      (MainTheory.RealGate.angle eta x)
      (MainTheory.RealGate.angle eta (basePoint D))
      (D.phase u.1) (D.phase (baseSector D)) k (by simpa [eta, sx] using hk)
    change Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (MainTheory.RealGate.angle eta x : ℂ)) * D.vec u x =
      c * MainTheory.RealGate.realGate theta (D.vec u) x
    rw [congrFun (D.eigen u) x, hexp]
    simp only [c]
    ring

theorem phaseExp_eq_of_sub_int (a b : ℝ) (k : ℤ)
    (h : a - b = (k : ℝ)) : phaseExp a = phaseExp b := by
  rw [phaseExp, phaseExp, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  have hc : (a : ℂ) - (b : ℂ) = (k : ℂ) := by
    exact_mod_cast h
  linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hc

/-- Two genuinely distinct logical sectors force the least physical
denominator to be nontrivial. -/
theorem RationalColoredLift.two_le_order
    {D : SectorDecomposition n t theta} (L : RationalColoredLift D)
    (ht : 2 ≤ t) : 2 ≤ L.order := by
  have hne : L.order ≠ 1 := by
    intro hq
    let alpha : Fin t := ⟨1, by omega⟩
    have hab : alpha ≠ baseSector D := by
      intro h
      have hv := congrArg Fin.val h
      simp [alpha, baseSector] at hv
    obtain ⟨b, hb⟩ := L.relative_phase_cleared alpha
    have hsub : D.phase alpha - D.phase (baseSector D) = (b : ℝ) := by
      simpa [hq] using hb
    have heq := phaseExp_eq_of_sub_int
      (D.phase alpha) (D.phase (baseSector D)) b hsub
    exact hab (D.phaseDistinct heq)
  have hpos := L.order_pos
  omega

/-- **Theorem 2.4, finite-lift core.**

Given the complete sector decomposition and its genuine `Z`-detection
consequence, all support equations have a rational solution inducing the same
relative sector phases.  Its least physical denominator is at least two,
clears every physical angle, is primitive, and clears every relative logical
phase.  Thus it is a primitive finite root-of-unity physical representative
of the same projective sector action; the last clause is the algebraic form of
the projective logical order dividing `q`. -/
theorem qualitative_finite_lift
    (D : SectorDecomposition n t theta) (hZ : ZDetects D) (ht : 2 ≤ t) :
    ∃ L : RationalColoredLift D,
      2 ≤ L.order ∧
      SameProjectiveSectorAction D (fun j ↦ (L.physical j : ℝ)) ∧
      (∀ j, (L.order : ℚ) * L.physical j = (L.numerator j : ℚ)) ∧
      (∀ d : ℕ, d ∣ L.order →
        (∀ j, (d : ℤ) ∣ L.numerator j) → d = 1) ∧
      (∀ (alpha : Fin t) (x : SupportIndex D alpha), ∃ k : ℤ,
        MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ)) x.1 -
          MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ))
            (basePoint D) -
          (D.phase alpha - D.phase (baseSector D)) = (k : ℝ)) ∧
      (∀ alpha, ∃ b : ℤ,
        (L.order : ℝ) * (D.phase alpha - D.phase (baseSector D)) =
          (b : ℝ)) := by
  obtain ⟨L⟩ := exists_rationalColoredLift D hZ
  refine ⟨L, L.two_le_order ht, L.same_projective_sector_action,
    L.numerator_spec, ?_, ?_, L.relative_phase_cleared⟩
  · intro d hdq hda
    exact L.primitive d hdq hda
  · intro alpha x
    exact L.same_relative_sector_phases alpha x

/-! ## Explicit square pivots and the sharp Smith divisor -/

/-- Integer version of a physical difference row. -/
def physicalRowZ (D : SectorDecomposition n t theta) (alpha : Fin t)
    (x : SupportIndex D alpha) (j : Fin n) : ℤ :=
  (if x.1 j then 1 else 0) - (if basePoint D j then 1 else 0)

/-- Integer version of a colour row. -/
def colorRowZ (D : SectorDecomposition n t theta) (alpha : Fin t)
    (g : Color D) : ℤ :=
  if alpha = g.1 then 1 else 0

/-- The all-support augmented integer matrix. -/
def coloredMatrixZ (D : SectorDecomposition n t theta) :
    Matrix (Sigma (SupportIndex D)) (Sum (Fin n) (Color D)) ℤ :=
  ColoredSystem.augmentedMatrix (physicalRowZ D) (colorRowZ D)

@[simp] theorem physicalRowZ_cast (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SupportIndex D alpha) (j : Fin n) :
    (physicalRowZ D alpha x j : ℚ) = physicalRow D alpha x j := by
  by_cases hx : x.1 j <;> by_cases hb : basePoint D j <;>
    simp [physicalRowZ, physicalRow, bitQ, hx, hb]

@[simp] theorem colorRowZ_cast (D : SectorDecomposition n t theta)
    (alpha : Fin t) (g : Color D) :
    (colorRowZ D alpha g : ℚ) = colorRow D alpha g := by
  by_cases h : alpha = g.1 <;> simp [colorRowZ, colorRow, h]

theorem coloredMatrixZ_cast (D : SectorDecomposition n t theta) :
    (coloredMatrixZ D).map (Int.castRingHom ℚ) = coloredMatrix D := by
  ext r c
  rcases r with ⟨alpha, x⟩
  cases c with
  | inl j => exact physicalRowZ_cast D alpha x j
  | inr g => exact colorRowZ_cast D alpha g

/-- Explicit data connecting a square pivot to the complete coloured system.
`spans` is a proof-producing row-span certificate; compatibility of the right
hand side is derived below from the already-proved real solution and is not a
field of this structure. -/
structure PivotData (D : SectorDecomposition n t theta) (s : Type*)
    [Fintype s] where
  row : s → Sigma (SupportIndex D)
  column : s ↪ Sum (Fin n) (Color D)
  rowCoeff : Sigma (SupportIndex D) → s → ℚ
  spans : ∀ r c, coloredMatrix D r c =
    ∑ i, rowCoeff r i * coloredMatrix D (row i) c

/-- The integer square matrix cut out by the displayed rows and columns. -/
def PivotData.matrix {s : Type*} [Fintype s]
    {D : SectorDecomposition n t theta} (P : PivotData D s) : Matrix s s ℤ :=
  fun i j ↦ coloredMatrixZ D (P.row i) (P.column j)

/-- The selected integral right-hand side. -/
noncomputable def PivotData.rhs {s : Type*} [Fintype s]
    {D : SectorDecomposition n t theta} (P : PivotData D s) : s → ℤ :=
  fun i ↦ coloredRhs D (P.row i)

/-- Extend selected coordinates by zero on every nonselected column. -/
def extendByZero {s c : Type*} [Fintype s] [DecidableEq c]
    (column : s ↪ c) (x : s → ℚ) : c → ℚ :=
  fun a ↦ ∑ i, if column i = a then x i else 0

theorem extendByZero_apply_column {s c : Type*} [Fintype s] [DecidableEq c]
    (column : s ↪ c) (x : s → ℚ) (i : s) :
    extendByZero column x (column i) = x i := by
  classical
  simp [extendByZero, column.injective.eq_iff]

theorem dotProduct_extendByZero {s c : Type*} [Fintype s] [Fintype c]
    [DecidableEq c] (column : s ↪ c) (row : c → ℚ) (x : s → ℚ) :
    dotProduct row (extendByZero column x) =
      ∑ i, row (column i) * x i := by
  classical
  simp only [dotProduct, extendByZero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem PivotData.rhs_spans {s : Type*} [Fintype s]
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (r : Sigma (SupportIndex D)) :
    coloredRhsQ D r = ∑ i, P.rowCoeff r i * coloredRhsQ D (P.row i) := by
  apply (algebraMap ℚ ℝ).injective
  have hr := congrFun (coloredMatrix_realSolution D) r
  have hri (i : s) := congrFun (coloredMatrix_realSolution D) (P.row i)
  have hri' (i : s) :
      (∑ c, (coloredMatrix D (P.row i) c : ℝ) * realUnknown D c) =
        (coloredRhsQ D (P.row i) : ℝ) := by
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hri i
  push_cast
  rw [← hr]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  calc
    (∑ c, (coloredMatrix D r c : ℝ) * realUnknown D c) =
        ∑ c, (∑ i, (P.rowCoeff r i : ℝ) *
          (coloredMatrix D (P.row i) c : ℝ)) * realUnknown D c := by
            apply Finset.sum_congr rfl
            intro c _
            have hs := P.spans r c
            have hsR : (coloredMatrix D r c : ℝ) =
                ∑ i, (P.rowCoeff r i : ℝ) *
                  (coloredMatrix D (P.row i) c : ℝ) := by
              exact_mod_cast hs
            rw [hsR]
    _ = ∑ i, (P.rowCoeff r i : ℝ) *
        (∑ c, (coloredMatrix D (P.row i) c : ℝ) *
          realUnknown D c) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ = ∑ i, (P.rowCoeff r i : ℝ) *
        (coloredRhsQ D (P.row i) : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hri']

section Pivot

variable {s : Type*} [Fintype s] [DecidableEq s] [LinearOrder s] [Nonempty s]

omit [DecidableEq s] [LinearOrder s] [Nonempty s] in
theorem PivotData.matrix_cast {D : SectorDecomposition n t theta}
    (P : PivotData D s) (i j : s) :
    SharpClearing.ratMatrix P.matrix i j =
      coloredMatrix D (P.row i) (P.column j) := by
  have h := congrArg (fun M : Matrix (Sigma (SupportIndex D))
      (Sum (Fin n) (Color D)) ℚ ↦ M (P.row i) (P.column j))
    (coloredMatrixZ_cast D)
  simpa [PivotData.matrix, SharpClearing.ratMatrix] using h

/-- Selected pivot coordinates, computed from the exact rational inverse. -/
noncomputable def PivotData.selectedSolution
    {D : SectorDecomposition n t theta} (P : PivotData D s) : s → ℚ :=
  (SharpClearing.ratMatrix P.matrix)⁻¹.mulVec (fun i ↦ (P.rhs i : ℚ))

omit [Nonempty s] in
theorem PivotData.selectedSolution_solves
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (W : SharpClearing.SmithWitness P.matrix) :
    (SharpClearing.ratMatrix P.matrix).mulVec P.selectedSolution =
      fun i ↦ (P.rhs i : ℚ) := by
  have hdetQ : (SharpClearing.ratMatrix P.matrix).det ≠ 0 := by
    have hm : (SharpClearing.ratMatrix P.matrix).det =
        (P.matrix.det : ℚ) :=
      ((Int.castRingHom ℚ).map_det P.matrix).symm
    rw [hm]
    exact_mod_cast W.det_ne_zero
  have hu : IsUnit (SharpClearing.ratMatrix P.matrix).det :=
    isUnit_iff_ne_zero.mpr hdetQ
  change (SharpClearing.ratMatrix P.matrix).mulVec
    ((SharpClearing.ratMatrix P.matrix)⁻¹.mulVec
      (fun i ↦ (P.rhs i : ℚ))) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]

/-- Full augmented solution: selected pivot coordinates, zero elsewhere. -/
noncomputable def PivotData.fullSolution
    {D : SectorDecomposition n t theta} (P : PivotData D s) :
    Sum (Fin n) (Color D) → ℚ :=
  extendByZero P.column P.selectedSolution

omit [Nonempty s] in
theorem PivotData.selectedRow_solves
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (W : SharpClearing.SmithWitness P.matrix) (i : s) :
    dotProduct (coloredMatrix D (P.row i)) P.fullSolution =
      coloredRhsQ D (P.row i) := by
  rw [PivotData.fullSolution, dotProduct_extendByZero]
  have hi := congrFun (P.selectedSolution_solves W) i
  simpa [Matrix.mulVec, dotProduct, P.matrix_cast, PivotData.rhs,
    coloredRhsQ] using hi

omit [Nonempty s] in
theorem PivotData.fullSolution_solves
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (W : SharpClearing.SmithWitness P.matrix) :
    (coloredMatrix D).mulVec P.fullSolution = coloredRhsQ D := by
  funext r
  simp only [Matrix.mulVec]
  calc
    dotProduct (coloredMatrix D r) P.fullSolution =
        dotProduct
          (fun c ↦ ∑ i, P.rowCoeff r i * coloredMatrix D (P.row i) c)
          P.fullSolution := by
            congr 1
            funext c
            exact P.spans r c
    _ = ∑ i, P.rowCoeff r i *
        dotProduct (coloredMatrix D (P.row i)) P.fullSolution := by
          simp only [dotProduct, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro c _
          ring
    _ = ∑ i, P.rowCoeff r i * coloredRhsQ D (P.row i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [P.selectedRow_solves W]
    _ = coloredRhsQ D r := (P.rhs_spans r).symm

theorem coloredMatrix_kernel_color_zero
    (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (v : Sum (Fin n) (Color D) → ℝ)
    (hv : ((coloredMatrix D).map (algebraMap ℚ ℝ)).mulVec v = 0)
    (g : Color D) : v (Sum.inr g) = 0 := by
  have hbaseR : ∀ g : Color D,
      (colorRow D (baseSector D) g : ℝ) = 0 := by
    intro g
    exact_mod_cast colorRow_base D g
  have hownerR : ∀ g h : Color D,
      (colorRow D g.1 h : ℝ) = if h = g then 1 else 0 := by
    intro g h
    rw [colorRow_owner]
    split <;> simp
  apply ColoredSystem.kernel_color_zero
    (pt := fun alpha x j ↦ (physicalRow D alpha x j : ℝ))
    (col := fun alpha g ↦ (colorRow D alpha g : ℝ))
    (p := supportWeight D) (base := baseSector D)
    (owner := fun g : Color D ↦ g.1)
    (supportWeight_sum_eq_one D) (physical_mean_eq_base D hZ)
    hbaseR hownerR v
  have hmatrix :
      ColoredSystem.augmentedMatrix
          (fun alpha x j ↦ (physicalRow D alpha x j : ℝ))
          (fun alpha g ↦ (colorRow D alpha g : ℝ)) =
        (coloredMatrix D).map (algebraMap ℚ ℝ) := by
    ext r c
    cases c <;> rfl
  rw [hmatrix]
  exact hv

/-- The pivot-constructed rational solution has the protected colour
coordinates, hence is a genuine rational finite lift rather than merely a
solution of an unrelated square subsystem. -/
noncomputable def PivotData.rationalLift
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (W : SharpClearing.SmithWitness P.matrix) (hZ : ZDetects D) :
    RationalColoredLift D where
  augmented := P.fullSolution
  solves := P.fullSolution_solves W
  color_preserved := by
    intro g
    let uR : Sum (Fin n) (Color D) → ℝ :=
      fun c ↦ (P.fullSolution c : ℝ)
    have hsolveR :
        ((coloredMatrix D).map (algebraMap ℚ ℝ)).mulVec uR =
          fun r ↦ algebraMap ℚ ℝ (coloredRhsQ D r) := by
      funext r
      have hr := congrArg (algebraMap ℚ ℝ)
        (congrFun (P.fullSolution_solves W) r)
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, uR,
        map_sum, map_mul] using hr
    have hker :
        ((coloredMatrix D).map (algebraMap ℚ ℝ)).mulVec
          (uR - realUnknown D) = 0 := by
      rw [Matrix.mulVec_sub, hsolveR, coloredMatrix_realSolution, sub_self]
    have hg := coloredMatrix_kernel_color_zero D hZ
      (uR - realUnknown D) hker g
    simpa [uR, sub_eq_zero] using hg

omit [Nonempty s] in
theorem lcmDen_physical_dvd_selected
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (W : SharpClearing.SmithWitness P.matrix) (hZ : ZDetects D) :
    Denominator.lcmDen (P.rationalLift W hZ).physical ∣
      Denominator.lcmDen P.selectedSolution := by
  apply Denominator.lcmDen_dvd_of_clears
  intro j
  by_cases hj : ∃ i, P.column i = Sum.inl j
  · obtain ⟨i, hi⟩ := hj
    have heq : (P.rationalLift W hZ).physical j = P.selectedSolution i := by
      change extendByZero P.column P.selectedSolution (Sum.inl j) = _
      rw [← hi, extendByZero_apply_column]
    rw [heq]
    exact Denominator.lcmDen_clears P.selectedSolution i
  · have heq : (P.rationalLift W hZ).physical j = 0 := by
      change extendByZero P.column P.selectedSolution (Sum.inl j) = 0
      apply Finset.sum_eq_zero
      intro i _
      have hne : P.column i ≠ Sum.inl j := by
        intro hi
        exact hj ⟨i, hi⟩
      simp [hne]
    rw [heq]
    simp

/-- **Theorem 3.2, sharp pivot divisor.**  For the explicitly connected
square pivot, the least denominator of the primitive physical lift divides
the final factor certified by its Smith witness. -/
theorem sharp_pivot_divisibility
    {D : SectorDecomposition n t theta} (P : PivotData D s)
    (W : SharpClearing.SmithWitness P.matrix) (hZ : ZDetects D) :
    (P.rationalLift W hZ).order ∣ W.lastFactor := by
  apply dvd_trans (lcmDen_physical_dvd_selected P W hZ)
  exact SharpClearing.solution_lcmDen_dvd_smithLastFactor
    W P.rhs P.selectedSolution (P.selectedSolution_solves W)

/-- Combined qualitative-and-sharp headline for a supplied proof-producing
pivot.  Every clause is derived from the sector decomposition, row-span
certificate, and Smith witness. -/
theorem quantitative_colored_finite_lift
    (D : SectorDecomposition n t theta) (hZ : ZDetects D) (ht : 2 ≤ t)
    (P : PivotData D s) (W : SharpClearing.SmithWitness P.matrix) :
    let L := P.rationalLift W hZ
    2 ≤ L.order ∧
      SameProjectiveSectorAction D (fun j ↦ (L.physical j : ℝ)) ∧
      (∀ j, (L.order : ℚ) * L.physical j = (L.numerator j : ℚ)) ∧
      (∀ d : ℕ, d ∣ L.order →
        (∀ j, (d : ℤ) ∣ L.numerator j) → d = 1) ∧
      (∀ (alpha : Fin t) (x : SupportIndex D alpha), ∃ k : ℤ,
        MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ)) x.1 -
          MainTheory.RealGate.angle (fun j ↦ (L.physical j : ℝ))
            (basePoint D) -
          (D.phase alpha - D.phase (baseSector D)) = (k : ℝ)) ∧
      (∀ alpha, ∃ b : ℤ,
        (L.order : ℝ) * (D.phase alpha - D.phase (baseSector D)) =
          (b : ℝ)) ∧
      L.order ∣ W.lastFactor := by
  dsimp only
  let L := P.rationalLift W hZ
  exact ⟨L.two_le_order ht, L.same_projective_sector_action,
    L.numerator_spec, L.primitive,
    L.same_relative_sector_phases, L.relative_phase_cleared,
    sharp_pivot_divisibility P W hZ⟩

end Pivot

end

end MainTheory.FiniteLift
