import QECC.GeneralSSLP
import QECC.SectorTransport

namespace QECC

open scoped BigOperators

noncomputable section

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- The coefficient vector obtained by translating an anchor sector to zero
with local `X` operators and then sorting the physical coordinates. -/
def generalCanonicalCoefficient (R : ReducedDiagonalRepresentative n)
    (t : BitString n) (sigma : Equiv.Perm (Fin n)) : Fin n → ZMod R.q :=
  permuteCoefficient sigma (xorCoefficient t R.a)

/-- The code projector in the corresponding translated and sorted
computational basis. -/
def generalCanonicalCode (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) : CodeProjector n K :=
  (C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)

/-- The canonical normalization gives an actual linear equivalence from each
original logical phase sector to the sector on the displayed colored fiber. -/
def canonicalColoredPhaseSectorEquiv
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma)
    (t : BitString n) (sigma : Equiv.Perm (Fin n))
    (ht : subsetSum R.a t = b0.1) (b : C.ActiveResidue R.a) :
    C.phaseSector R.a b.1 ≃ₗ[ℂ]
      (C.generalCanonicalCode t sigma).phaseSector
        (generalCanonicalCoefficient R t sigma)
        (colorEmbed (addOrderOf U) R.q
          H.intrinsic.logicalOrder_dvd_physical (gamma b)) := by
  have hlabel : b.1 - subsetSum R.a t =
      colorEmbed (addOrderOf U) R.q
        H.intrinsic.logicalOrder_dvd_physical (gamma b) := by
    rw [ht]
    exact (H.residueFormula b).symm
  rw [← hlabel]
  exact C.canonicalPhaseSectorEquiv R.a t sigma b.1

/-- The active residue bijection underlying the canonical normalization. -/
def generalCanonicalActiveResidueEquiv
    (R : ReducedDiagonalRepresentative n)
    (t : BitString n) (sigma : Equiv.Perm (Fin n)) :
    C.ActiveResidue R.a ≃
      (C.generalCanonicalCode t sigma).ActiveResidue
        (generalCanonicalCoefficient R t sigma) :=
  C.canonicalActiveResidueEquiv R.a t sigma

/-- Under the active-sector bijection, the new residue label is exactly the
embedded logical color `(q / m) * gamma`. -/
@[simp] theorem generalCanonicalActiveResidueEquiv_apply_val
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma)
    (t : BitString n) (sigma : Equiv.Perm (Fin n))
    (ht : subsetSum R.a t = b0.1) (b : C.ActiveResidue R.a) :
    (C.generalCanonicalActiveResidueEquiv R t sigma b).1 =
      colorEmbed (addOrderOf U) R.q
        H.intrinsic.logicalOrder_dvd_physical (gamma b) := by
  change b.1 - subsetSum R.a t = _
  rw [ht]
  exact (H.residueFormula b).symm

/-- Logical colors transported to the active sectors of the canonical code. -/
def generalCanonicalColors
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (t : BitString n) (sigma : Equiv.Perm (Fin n))
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U)) :
    (C.generalCanonicalCode t sigma).ActiveResidue
        (generalCanonicalCoefficient R t sigma) → ZMod (addOrderOf U) :=
  fun b ↦ gamma ((C.generalCanonicalActiveResidueEquiv R t sigma).symm b)

/-- Every active label of the canonical code is an embedded transported
logical color; hence the displayed colored fibers are exhaustive. -/
theorem generalCanonicalActiveResidue_value
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma)
    (t : BitString n) (sigma : Equiv.Perm (Fin n))
    (ht : subsetSum R.a t = b0.1)
    (b : (C.generalCanonicalCode t sigma).ActiveResidue
      (generalCanonicalCoefficient R t sigma)) :
    b.1 = colorEmbed (addOrderOf U) R.q
      H.intrinsic.logicalOrder_dvd_physical
      (C.generalCanonicalColors U R t sigma gamma b) := by
  let E := C.generalCanonicalActiveResidueEquiv R t sigma
  have h := C.generalCanonicalActiveResidueEquiv_apply_val
    U R hpres b0 gamma H t sigma ht (E.symm b)
  simpa [E, generalCanonicalColors] using h

/-- Reindexing the finite family of colors by the active-sector equivalence
preserves primitivity. -/
theorem generalCanonicalColors_primitive
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma)
    (t : BitString n) (sigma : Equiv.Perm (Fin n)) :
    letI : NeZero R.q :=
      ⟨(lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two).ne'⟩
    ColorPrimitive (addOrderOf U)
      (C.generalCanonicalColors U R t sigma gamma) := by
  letI : NeZero R.q :=
    ⟨(lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two).ne'⟩
  let E := C.generalCanonicalActiveResidueEquiv R t sigma
  let F : (C.ActiveResidue R.a → ZMod (addOrderOf U)) ≃+
      ((C.generalCanonicalCode t sigma).ActiveResidue
        (generalCanonicalCoefficient R t sigma) → ZMod (addOrderOf U)) :=
    AddEquiv.arrowCongr E (AddEquiv.refl (ZMod (addOrderOf U)))
  change addOrderOf (C.generalCanonicalColors U R t sigma gamma) =
    addOrderOf U
  have horder : addOrderOf (F gamma) = addOrderOf gamma :=
    addOrderOf_injective F.toAddMonoidHom F.injective gamma
  have hF : F gamma = C.generalCanonicalColors U R t sigma gamma := rfl
  rw [← hF, horder]
  exact H.colorsPrimitive

/-- Complete canonical-coordinate conclusion attached to one concrete general
SSLP witness.  The named definitions above supply the sector linear
equivalences and the active-residue equivalence; the clauses below record
their dimensions and exact colored labels. -/
def HasCanonicalGeneralSSLPData
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma) : Prop :=
  letI : NeZero R.q :=
    ⟨(lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two).ne'⟩
  ∃ (t : BitString n) (sigma : Equiv.Perm (Fin n)),
    let aCanonical := generalCanonicalCoefficient R t sigma
    let CCanonical := C.generalCanonicalCode t sigma
    subsetSum R.a t = b0.1 ∧
    Monotone (fun j ↦ (aCanonical j).val) ∧
    addOrderOf aCanonical = R.q ∧
    Nat.gcd R.q (Finset.univ.gcd fun j : Fin n ↦ (aCanonical j).val) = 1 ∧
    CCanonical.Preserves
      (phaseHom n R.q
        (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) aCanonical) ∧
    orderOf
      (diagonalGate
        (phaseHom n R.q
          (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) aCanonical)) = R.q ∧
    (∀ b : C.ActiveResidue R.a,
      Module.finrank ℂ (C.phaseSector R.a b.1) =
        Module.finrank ℂ
          (CCanonical.phaseSector aCanonical
            (colorEmbed (addOrderOf U) R.q
              H.intrinsic.logicalOrder_dvd_physical (gamma b)))) ∧
    (∀ b : C.ActiveResidue R.a,
      (C.generalCanonicalActiveResidueEquiv R t sigma b).1 =
        colorEmbed (addOrderOf U) R.q
          H.intrinsic.logicalOrder_dvd_physical (gamma b)) ∧
    (∀ b : CCanonical.ActiveResidue aCanonical,
      b.1 = colorEmbed (addOrderOf U) R.q
        H.intrinsic.logicalOrder_dvd_physical
        (C.generalCanonicalColors U R t sigma gamma b)) ∧
    ColorPrimitive (addOrderOf U)
      (C.generalCanonicalColors U R t sigma gamma) ∧
    (∀ hpresCanonical : CCanonical.Preserves
        (phaseHom n R.q
          (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) aCanonical),
      addOrderOf
        (CCanonical.projectiveClassMap
          ⟨phaseHom n R.q
            (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) aCanonical,
            hpresCanonical⟩) = addOrderOf U) ∧
    ∀ d : ℕ, C.HasDistanceAtLeast d → CCanonical.HasDistanceAtLeast d

/-- Put a concrete general SSLP witness into the full displayed canonical
form, including the transported sector decomposition and exact projective
order. -/
theorem exists_canonical_general_sslp_data
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma) :
    C.HasCanonicalGeneralSSLPData U R hpres b0 gamma H := by
  classical
  obtain ⟨t, sigma, ht, hmono, hprimitive, hpresCanonical, _hfibers⟩ :=
    C.exists_canonical_colored_normalization U R hpres b0 gamma H
  let aCanonical := generalCanonicalCoefficient R t sigma
  let CCanonical := C.generalCanonicalCode t sigma
  have hq : 0 < R.q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  have hgcd :
      Nat.gcd R.q
        (Finset.univ.gcd fun j : Fin n ↦ (aCanonical j).val) = 1 := by
    simpa [aCanonical, generalCanonicalCoefficient,
      ReducedDiagonalRepresentative.commonGCD] using
      canonical_commonGCD_eq_one R t sigma
  have hphysical :
      orderOf (diagonalGate (phaseHom n R.q hq aCanonical)) = R.q := by
    calc
      orderOf (diagonalGate (phaseHom n R.q hq aCanonical)) =
          addOrderOf (phaseHom n R.q hq aCanonical) := diagonalGate_order _
      _ = addOrderOf aCanonical :=
        addOrderOf_injective (phaseHom n R.q hq)
          (phaseHom_injective n R.q hq) aCanonical
      _ = R.q := hprimitive
  have hfinrank (b : C.ActiveResidue R.a) :
      Module.finrank ℂ (C.phaseSector R.a b.1) =
        Module.finrank ℂ
          (CCanonical.phaseSector aCanonical
            (colorEmbed (addOrderOf U) R.q
              H.intrinsic.logicalOrder_dvd_physical (gamma b))) := by
    exact LinearEquiv.finrank_eq
      (C.canonicalColoredPhaseSectorEquiv U R hpres b0 gamma H
        t sigma ht b)
  have hactive (b : C.ActiveResidue R.a) :
      (C.generalCanonicalActiveResidueEquiv R t sigma b).1 =
        colorEmbed (addOrderOf U) R.q
          H.intrinsic.logicalOrder_dvd_physical (gamma b) :=
    C.generalCanonicalActiveResidueEquiv_apply_val
      U R hpres b0 gamma H t sigma ht b
  have hexhaust (b : CCanonical.ActiveResidue aCanonical) :
      b.1 = colorEmbed (addOrderOf U) R.q
        H.intrinsic.logicalOrder_dvd_physical
        (C.generalCanonicalColors U R t sigma gamma b) :=
    C.generalCanonicalActiveResidue_value
      U R hpres b0 gamma H t sigma ht b
  have hcolors : ColorPrimitive (addOrderOf U)
      (C.generalCanonicalColors U R t sigma gamma) :=
    C.generalCanonicalColors_primitive U R hpres b0 gamma H t sigma
  let E := C.generalCanonicalActiveResidueEquiv R t sigma
  let B0 : CCanonical.ActiveResidue aCanonical := E b0
  let gammaCanonical : CCanonical.ActiveResidue aCanonical →
      ZMod (addOrderOf U) :=
    C.generalCanonicalColors U R t sigma gamma
  have hB0 : B0.1 = 0 := by
    change (E b0).1 = 0
    rw [hactive b0, H.anchorColor]
    simp
  have hresidue (b : CCanonical.ActiveResidue aCanonical) :
      colorEmbed (addOrderOf U) R.q
          H.intrinsic.logicalOrder_dvd_physical (gammaCanonical b) =
        CCanonical.relativeResidues aCanonical B0 b := by
    rw [relativeResidues, hB0, sub_zero]
    exact (hexhaust b).symm
  have hrelative :
      addOrderOf (CCanonical.relativeResidues aCanonical B0) =
        addOrderOf U := by
    let embedPi := colorVectorEmbed
      (ι := CCanonical.ActiveResidue aCanonical)
      (addOrderOf U) R.q H.intrinsic.logicalOrder_dvd_physical
    have hembed : embedPi gammaCanonical =
        CCanonical.relativeResidues aCanonical B0 := by
      funext b
      exact hresidue b
    have hembedInj : Function.Injective embedPi :=
      colorVectorEmbed_injective (addOrderOf U) R.q
        H.intrinsic.logicalOrder_gt_one hq
        H.intrinsic.logicalOrder_dvd_physical
    rw [← hembed]
    exact (addOrderOf_injective embedPi hembedInj gammaCanonical).trans hcolors
  have hprojective :
      addOrderOf
        (CCanonical.projectiveClassMap
          ⟨phaseHom n R.q hq aCanonical, hpresCanonical⟩) =
        addOrderOf U := by
    rw [CCanonical.projectiveOrder_eq_relativeResiduesOrder
      hq aCanonical hpresCanonical B0]
    exact hrelative
  refine ⟨t, sigma, ?_⟩
  dsimp only [generalCanonicalCoefficient, generalCanonicalCode]
  refine ⟨ht, hmono, hprimitive, hgcd, hpresCanonical, hphysical,
    hfinrank, hactive, hexhaust, hcolors, (fun _ ↦ hprojective), ?_⟩
  intro d hd
  exact C.hasDistanceAtLeast_xor_permutation hd t sigma

/-- The end-to-end canonical forward normal form for a nonzero projective
diagonal logical class on a distance-at-least-two code. -/
def HasCanonicalGeneralSSLPNormalForm
    (U : C.ProjectiveDiagonalGroup) : Prop :=
  ∃ (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma),
      C.HasCanonicalGeneralSSLPData U R hpres b0 gamma H

/-- **General SSLP theorem in canonical coordinates.**

The intrinsic sectors are transported by actual linear equivalences to the
sorted subset-sum fibers labelled by the embedded primitive logical colors.
Their multiplicities, every Pauli distance condition, and the exact
projective order are preserved. -/
theorem general_sslp_canonical_normal_form
    {d : ℕ} (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    C.HasCanonicalGeneralSSLPNormalForm U := by
  obtain ⟨R, hpres, b0, gamma, H⟩ :=
    C.general_sslp_normal_form hd hd2 U hU
  exact ⟨R, hpres, b0, gamma, H,
    C.exists_canonical_general_sslp_data U R hpres b0 gamma H⟩

end CodeProjector

end

end QECC
