import QECC.ColoredSSLP
import QECC.CanonicalSSLP
import QECC.SectorProbabilities

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K d : ℕ} (C : CodeProjector n K)

/-- All algebraic, dimensional, and support data in the general SSLP normal
form, indexed by concrete witnesses.  Canonical local-`X` and coordinate
transport is supplied by `exists_xor_permutation_normalization`. -/
structure GeneralSSLPData
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U)) : Prop where
  intrinsic : C.IntrinsicSSLPData U R hpres b0
  anchorColor : gamma b0 = 0
  colorsDistinct : Function.Injective gamma
  residueFormula : ∀ b,
    colorEmbed (addOrderOf U) R.q
      intrinsic.logicalOrder_dvd_physical (gamma b) =
        C.relativeResidues R.a b0 b
  colorsPrimitive :
    letI : NeZero R.q :=
      ⟨(lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two).ne'⟩
    ColorPrimitive (addOrderOf U) gamma
  colorGCD_eq_one :
    letI : NeZero R.q :=
      ⟨(lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two).ne'⟩
    colorGCD (addOrderOf U) gamma = 1

/-- Existential packaging of the complete forward SSLP data. -/
def HasGeneralSSLPData (U : C.ProjectiveDiagonalGroup) : Prop :=
  ∃ (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U)),
      C.GeneralSSLPData U R hpres b0 gamma

/-- **SSLP normal form for general code dimension (forward direction).**

This packages the reduced physical order, divisibility `m ∣ q`, distinct
logical colors with anchor zero and gcd one, positive sector multiplicities
summing to `K`, and support inside their subset-sum fibers.  The accompanying
canonical-transport theorem turns the relative residue formula here into the
paper's fibers `S_{(q/m)γ}` with sorted coefficient representatives. -/
theorem general_sslp_normal_form
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    C.HasGeneralSSLPData U := by
  obtain ⟨R, hpres, b0, H⟩ :=
    C.intrinsic_sslp_normal_form hd hd2 U hU
  obtain ⟨gamma, hzero, hinj, hformula, hprimitive, hgcd⟩ :=
    C.exists_primitive_sslp_colors U R hpres b0 H
  exact ⟨R, hpres, b0, gamma,
    { intrinsic := H
      anchorColor := hzero
      colorsDistinct := hinj
      residueFormula := hformula
      colorsPrimitive := hprimitive
      colorGCD_eq_one := hgcd }⟩

/-- Put a concrete general-normal-form witness into the displayed canonical
form of the paper.  After local `X` transport and coordinate sorting, the
sector indexed by `b` is supported in the fiber with label
`colorEmbed m q (gamma b)`, i.e. `(q / m) * gamma b`. -/
theorem exists_canonical_colored_normalization
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (gamma : C.ActiveResidue R.a → ZMod (addOrderOf U))
    (H : C.GeneralSSLPData U R hpres b0 gamma) :
    ∃ (t : BitString n) (sigma : Equiv.Perm (Fin n)),
      subsetSum R.a t = b0.1 ∧
      let aX := xorCoefficient t R.a
      let aCanonical := permuteCoefficient sigma aX
      Monotone (fun j => (aCanonical j).val) ∧
      addOrderOf aCanonical = R.q ∧
      ((C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)).Preserves
        (phaseHom n R.q
          (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) aCanonical) ∧
      (∀ b : C.ActiveResidue R.a,
        coordinateEquiv sigma '' (xorEquiv t '' subsetSumFiber R.a b.1) =
          subsetSumFiber aCanonical
            (colorEmbed (addOrderOf U) R.q
              H.intrinsic.logicalOrder_dvd_physical (gamma b))) := by
  obtain ⟨t, sigma, ht, hmono, hprimitive, hcanonicalPres, hfibers⟩ :=
    C.exists_xor_permutation_normalization R hpres b0
  refine ⟨t, sigma, ht, hmono, hprimitive, hcanonicalPres, ?_⟩
  intro b
  rw [hfibers b.1, H.residueFormula b]
  rfl

/-- **General converse on an exact code projector.**

If the active sectors have the prescribed embedded colors and that color
vector is primitive, then the preserving modular gate has exact projective
order `m`.  Supplying the full Pauli KL equations as `HasDistanceAtLeast d₀`
gives the stated distance conclusion. -/
theorem general_sslp_converse
    {q m d0 : ℕ} (hq : 0 < q) (hm : 2 ≤ m) (hmq : m ∣ q)
    (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b0 : C.ActiveResidue a)
    (gamma : C.ActiveResidue a → ZMod m)
    (hresidue : ∀ b,
      colorEmbed m q hmq (gamma b) = C.relativeResidues a b0 b)
    (hprimitive :
      letI : NeZero q := ⟨hq.ne'⟩
      ColorPrimitive m gamma)
    (hKL : C.HasDistanceAtLeast d0) :
    addOrderOf (C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩) = m ∧
      C.HasDistanceAtLeast d0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  let embedPi := colorVectorEmbed
    (ι := C.ActiveResidue a) m q hmq
  have hembedInj : Function.Injective embedPi :=
    colorVectorEmbed_injective m q hm hq hmq
  have hembed : embedPi gamma = C.relativeResidues a b0 := by
    funext b
    exact hresidue b
  have hrelative : addOrderOf (C.relativeResidues a b0) = m := by
    rw [← hembed]
    exact (addOrderOf_injective embedPi hembedInj gamma).trans hprimitive
  exact C.sslp_converse_order_and_distance hq a hpres b0 m d0
    hrelative hKL

/-- The probability-distribution and low-degree-moment consequences attached
to the active sectors in the SSLP normal form. -/
structure SSLPSectorProbabilityConclusion
    {q d0 : ℕ} (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hKL : C.HasDistanceAtLeast d0) : Prop where
  nonnegative : ∀ (b : C.ActiveResidue a) (x : BitString n),
    0 ≤ C.sectorDistribution a b x
  totalMass : ∀ b : C.ActiveResidue a,
    ∑ x : BitString n, C.sectorDistribution a b x = 1
  supportedOnFiber : ∀ (b : C.ActiveResidue a) (x : BitString n),
    subsetSum a x ≠ b.1 → C.sectorDistribution a b x = 0
  momentsIndependent : ∀ (J : Finset (Fin n)), J.card < d0 →
    ∀ b c : C.ActiveResidue a,
      (∑ x : BitString n,
          C.sectorDistribution a b x * binaryMonomialValue J x) =
        ∑ x : BitString n,
          C.sectorDistribution a c x * binaryMonomialValue J x

/-- **LP consequence of the SSLP normal form.**  Each normalized sector
diagonal is a probability distribution on its subset-sum fiber, and all
binary moments of degree below the code distance agree between sectors. -/
theorem sslp_sector_probabilities_and_moments
    {q d0 : ℕ} (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hKL : C.HasDistanceAtLeast d0) :
    C.SSLPSectorProbabilityConclusion hq a hpres hKL :=
  { nonnegative := fun b x =>
      C.sectorDistribution_nonneg hq a hpres b x
    totalMass := fun b => C.sum_sectorDistribution hq a hpres b
    supportedOnFiber := fun b x hx =>
      C.sectorDistribution_eq_zero_of_not_mem a b x hx
    momentsIndependent := fun J hJ b c =>
      C.sectorMoment_eq_of_hasDistanceAtLeast hq a hpres hKL J hJ b c }

end CodeProjector

end

end QECC
