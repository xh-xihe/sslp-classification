import QECC.CanonicalSSLP
import QECC.PauliTransport
import QECC.RankTwoSSLP
import QECC.SectorProbabilities

namespace QECC

open scoped BigOperators

noncomputable section

/-- Multiply every modular coefficient by a unit.  This is the physical
operation of replacing a finite-order diagonal generator by a unit power. -/
def unitScaleCoefficient {n q : ℕ} (u : (ZMod q)ˣ)
    (a : Fin n → ZMod q) : Fin n → ZMod q :=
  fun j ↦ (u : ZMod q) * a j

/-- Unit scaling is an additive equivalence on coefficient vectors. -/
def unitScaleCoefficientEquiv {n q : ℕ} (u : (ZMod q)ˣ) :
    (Fin n → ZMod q) ≃+ (Fin n → ZMod q) where
  toFun := unitScaleCoefficient u
  invFun := unitScaleCoefficient u⁻¹
  left_inv a := by
    funext j
    simp [unitScaleCoefficient]
  right_inv a := by
    funext j
    simp [unitScaleCoefficient]
  map_add' a c := by
    funext j
    simp [unitScaleCoefficient, mul_add]

@[simp] theorem unitScaleCoefficientEquiv_apply {n q : ℕ}
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q) :
    unitScaleCoefficientEquiv u a = unitScaleCoefficient u a :=
  rfl

/-- Subset sums scale with the coefficient vector. -/
theorem subsetSum_unitScaleCoefficient {n q : ℕ} (u : (ZMod q)ˣ)
    (a : Fin n → ZMod q) (x : BitString n) :
    subsetSum (unitScaleCoefficient u a) x =
      (u : ZMod q) * subsetSum a x := by
  simp only [subsetSum, unitScaleCoefficient]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases x j <;> simp

/-- A unit power relabels a fiber by multiplication with that unit without
changing its underlying set of computational basis strings. -/
theorem subsetSumFiber_unitScaleCoefficient {n q : ℕ}
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q) (b : ZMod q) :
    subsetSumFiber (unitScaleCoefficient u a) ((u : ZMod q) * b) =
      subsetSumFiber a b := by
  ext x
  change subsetSum (unitScaleCoefficient u a) x = (u : ZMod q) * b ↔
    subsetSum a x = b
  rw [subsetSum_unitScaleCoefficient]
  constructor
  · intro h
    have h' := congrArg (fun z : ZMod q => (u⁻¹ : ZMod q) * z) h
    simpa [mul_assoc] using h'
  · exact congrArg (fun z : ZMod q => (u : ZMod q) * z)

/-- Scaling all coefficients by a unit preserves their exact additive order. -/
theorem addOrderOf_unitScaleCoefficient {n q : ℕ} (u : (ZMod q)ˣ)
    (a : Fin n → ZMod q) :
    addOrderOf (unitScaleCoefficient u a) = addOrderOf a := by
  refine addOrderOf_injective
    (unitScaleCoefficientEquiv (n := n) u).toAddMonoidHom ?_ a
  exact (unitScaleCoefficientEquiv (n := n) u).injective

theorem unitScaleCoefficient_primitive {n q : ℕ} (u : (ZMod q)ˣ)
    (a : Fin n → ZMod q) (ha : addOrderOf a = q) :
    addOrderOf (unitScaleCoefficient u a) = q := by
  rw [addOrderOf_unitScaleCoefficient, ha]

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- Replacing a preserving modular generator by a unit power still preserves
the same code. -/
theorem preserves_phaseHom_unitScaleCoefficient (hq : 0 < q)
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) :
    C.Preserves (phaseHom n q hq (unitScaleCoefficient u a)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let k := (u : ZMod q).val
  have hcoeff : unitScaleCoefficient u a = k • a := by
    funext j
    simp only [unitScaleCoefficient, Pi.smul_apply, nsmul_eq_mul]
    rw [ZMod.natCast_zmod_val]
  have hphase : phaseHom n q hq (unitScaleCoefficient u a) =
      k • phaseHom n q hq a := by
    rw [hcoeff, map_nsmul]
  rw [hphase]
  exact C.preservingPhases.nsmul_mem hpres k

/-- Unit scaling does not change a phase sector as a subspace when its label
is scaled at the same time. -/
theorem phaseSector_unitScaleCoefficient (u : (ZMod q)ˣ)
    (a : Fin n → ZMod q) (b : ZMod q) :
    C.phaseSector (unitScaleCoefficient u a) ((u : ZMod q) * b) =
      C.phaseSector a b := by
  rw [phaseSector, phaseSector]
  congr 1
  ext psi
  constructor <;> intro hpsi x hx
  · apply hpsi x
    intro hscaled
    apply hx
    have h' := congrArg (fun z : ZMod q => (u⁻¹ : ZMod q) * z) hscaled
    simpa [subsetSum_unitScaleCoefficient, mul_assoc] using h'
  · apply hpsi x
    intro hold
    apply hx
    rw [subsetSum_unitScaleCoefficient, hold]

/-- Reindexing a code and a matching subset-sum fiber preserves the sector
dimension. -/
theorem finrank_phaseSector_reindex_of_image
    (e : BitString n ≃ BitString n)
    (a a' : Fin n → ZMod q) (b b' : ZMod q)
    (hq : 0 < q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hpres' : (C.reindex e).Preserves (phaseHom n q hq a'))
    (hfiber : e '' subsetSumFiber a b = subsetSumFiber a' b') :
    Module.finrank ℂ ((C.reindex e).phaseSector a' b') =
      Module.finrank ℂ (C.phaseSector a b) := by
  have hprojector :
      (C.reindex e).sectorProjector a' b' =
        reindexOperator e (C.sectorProjector a b) := by
    classical
    ext x y
    have hx : subsetSum a' x = b' ↔ subsetSum a (e.symm x) = b := by
      change x ∈ subsetSumFiber a' b' ↔ e.symm x ∈ subsetSumFiber a b
      rw [← hfiber]
      simp
    simp only [sectorProjector_apply, reindexOperator,
      Matrix.reindex_apply, Matrix.submatrix_apply, reindex_proj_apply]
    rw [if_congr hx rfl rfl]
  rw [← (C.reindex e).rank_sectorProjector hq a' hpres' b',
    ← C.rank_sectorProjector hq a hpres b, hprojector]
  change Matrix.rank (Matrix.reindex e e (C.sectorProjector a b)) = _
  rw [Matrix.rank_reindex]

/-- The coefficient vector after taking a unit power, translating one chosen
support string to zero by local `X`, and permuting the qubits. -/
def rankTwoCanonicalCoefficient (u : (ZMod q)ˣ) (t : BitString n)
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) :
    Fin n → ZMod q :=
  permuteCoefficient sigma (xorCoefficient t (unitScaleCoefficient u a))

/-- The code after the two basis relabelings used in the canonical rank-two
normal form. -/
def rankTwoCanonicalCode (t : BitString n) (sigma : Equiv.Perm (Fin n)) :
    CodeProjector n K :=
  (C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)

/-- Complete canonical data for one nontrivial modular logical action on a
rank-two code.  The two old active sectors are transported to the displayed
fibers `0` and `q / m`; the new action has exact physical order `q` and exact
projective order `m`. -/
def HasRankTwoCanonicalNormalization
    (hq : 0 < q) (m : ℕ) (a : Fin n → ZMod q) : Prop :=
  ∃ (b0 b1 : C.ActiveResidue a) (u : (ZMod q)ˣ)
    (t : BitString n) (sigma : Equiv.Perm (Fin n)),
    let aCanonical := rankTwoCanonicalCoefficient u t sigma a
    let CCanonical := C.rankTwoCanonicalCode t sigma
    b0 ≠ b1 ∧
    (∀ b : C.ActiveResidue a, b = b0 ∨ b = b1) ∧
    (u : ZMod q) * (b1.1 - b0.1) = (q / m : ZMod q) ∧
    subsetSum a t = b0.1 ∧
    Monotone (fun j ↦ (aCanonical j).val) ∧
    addOrderOf aCanonical = q ∧
    Nat.gcd q (Finset.univ.gcd fun j : Fin n ↦ (aCanonical j).val) = 1 ∧
    CCanonical.Preserves (phaseHom n q hq aCanonical) ∧
    orderOf (diagonalGate (phaseHom n q hq aCanonical)) = q ∧
    coordinateEquiv sigma '' (xorEquiv t '' subsetSumFiber a b0.1) =
      subsetSumFiber aCanonical 0 ∧
    coordinateEquiv sigma '' (xorEquiv t '' subsetSumFiber a b1.1) =
      subsetSumFiber aCanonical (q / m : ZMod q) ∧
    Module.finrank ℂ (CCanonical.phaseSector aCanonical 0) = 1 ∧
    Module.finrank ℂ
      (CCanonical.phaseSector aCanonical (q / m : ZMod q)) = 1 ∧
    (∀ b : CCanonical.ActiveResidue aCanonical,
      b.1 = 0 ∨ b.1 = (q / m : ZMod q)) ∧
    (∀ hpresCanonical :
        CCanonical.Preserves (phaseHom n q hq aCanonical),
      addOrderOf
        (CCanonical.projectiveClassMap
          ⟨phaseHom n q hq aCanonical, hpresCanonical⟩) = m) ∧
    ∀ d : ℕ, C.HasDistanceAtLeast d → CCanonical.HasDistanceAtLeast d

/-- **Canonical rank-two SSLP normalization.**

Starting with the two active residues supplied by
`exists_normalized_rankTwo_activeResidues`, first take its unit power.  A
support string in the first sector is then translated to zero, and a final
coordinate permutation sorts the canonical coefficient representatives.
All code distances are preserved by the two basis relabelings. -/
theorem exists_rankTwoCanonicalNormalization
    {n q : ℕ} (C : CodeProjector n 2)
    [NeZero q] (hq : 0 < q) (m : ℕ) (a : Fin n → ZMod q)
    (ha : addOrderOf a = q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ ≠ 0)
    (hm : 2 ≤ m) (hmq : m ∣ q)
    (horder : addOrderOf
      (C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩) = m) :
    C.HasRankTwoCanonicalNormalization hq m a := by
  classical
  letI : NeZero m := ⟨(by omega : m ≠ 0)⟩
  letI : Fact (1 < m) := ⟨by omega⟩
  obtain ⟨b0, b1, u, hb01, hexhaust, hdim0, hdim1, hnormalized⟩ :=
    C.exists_normalized_rankTwo_activeResidues hq a hpres hne hm hmq horder
  obtain ⟨t, ht⟩ := C.exists_support_string_of_activeResidue a b0
  let aU := unitScaleCoefficient u a
  have htU : subsetSum aU t = (u : ZMod q) * b0.1 := by
    rw [subsetSum_unitScaleCoefficient, ht]
  let aX := xorCoefficient t aU
  obtain ⟨sigma, hmono⟩ := exists_permuteCoefficient_monotone_val aX
  let aCanonical := permuteCoefficient sigma aX
  let CCanonical := C.rankTwoCanonicalCode t sigma
  have hpresU : C.Preserves (phaseHom n q hq aU) := by
    exact C.preserves_phaseHom_unitScaleCoefficient hq u a hpres
  have hpresX : (C.reindex (xorEquiv t)).Preserves
      (phaseHom n q hq aX) := by
    exact C.reindex_xor_preserves_phaseHom hq aU t hpresU
  have hpresCanonical : CCanonical.Preserves
      (phaseHom n q hq aCanonical) := by
    exact (C.reindex (xorEquiv t)).reindex_coordinate_preserves_phaseHom
      hq sigma aX hpresX
  have hprimitiveU : addOrderOf aU = q := by
    exact unitScaleCoefficient_primitive u a ha
  have hprimitiveX : addOrderOf aX = q := by
    exact xorCoefficient_primitive t aU hprimitiveU
  have hprimitiveCanonical : addOrderOf aCanonical = q := by
    exact permuteCoefficient_primitive sigma aX hprimitiveX
  let RCanonical : ReducedDiagonalRepresentative n :=
    { q := q
      q_ge_two := le_trans hm (Nat.le_of_dvd (by omega) hmq)
      a := aCanonical
      primitive := hprimitiveCanonical }
  have hgcdCanonical :
      Nat.gcd q (Finset.univ.gcd fun j : Fin n ↦ (aCanonical j).val) = 1 := by
    exact RCanonical.commonGCD_eq_one
  have hphysicalOrder :
      orderOf (diagonalGate (phaseHom n q hq aCanonical)) = q := by
    calc
      orderOf (diagonalGate (phaseHom n q hq aCanonical)) =
          addOrderOf (phaseHom n q hq aCanonical) := diagonalGate_order _
      _ = addOrderOf aCanonical :=
        addOrderOf_injective (phaseHom n q hq)
          (phaseHom_injective n q hq) aCanonical
      _ = q := hprimitiveCanonical
  have hscaleFiber (b : ZMod q) :
      subsetSumFiber aU ((u : ZMod q) * b) = subsetSumFiber a b := by
    exact subsetSumFiber_unitScaleCoefficient u a b
  have hfiber0 :
      coordinateEquiv sigma '' (xorEquiv t '' subsetSumFiber a b0.1) =
        subsetSumFiber aCanonical 0 := by
    rw [← hscaleFiber b0.1, image_subsetSumFiber_xorEquiv,
      image_subsetSumFiber_coordinateEquiv, htU, sub_self]
  have hfiber1 :
      coordinateEquiv sigma '' (xorEquiv t '' subsetSumFiber a b1.1) =
        subsetSumFiber aCanonical (q / m : ZMod q) := by
    rw [← hscaleFiber b1.1, image_subsetSumFiber_xorEquiv,
      image_subsetSumFiber_coordinateEquiv, htU]
    congr 1
    rw [← mul_sub, hnormalized]
  have hdimU0 :
      Module.finrank ℂ (C.phaseSector aU ((u : ZMod q) * b0.1)) = 1 := by
    rw [C.phaseSector_unitScaleCoefficient u a b0.1]
    exact hdim0
  have hdimU1 :
      Module.finrank ℂ (C.phaseSector aU ((u : ZMod q) * b1.1)) = 1 := by
    rw [C.phaseSector_unitScaleCoefficient u a b1.1]
    exact hdim1
  have hxorFiber0 :
      xorEquiv t '' subsetSumFiber aU ((u : ZMod q) * b0.1) =
        subsetSumFiber aX 0 := by
    rw [image_subsetSumFiber_xorEquiv, htU, sub_self]
  have hxorFiber1 :
      xorEquiv t '' subsetSumFiber aU ((u : ZMod q) * b1.1) =
        subsetSumFiber aX (q / m : ZMod q) := by
    rw [image_subsetSumFiber_xorEquiv, htU]
    congr 1
    rw [← mul_sub, hnormalized]
  have hdimX0 : Module.finrank ℂ
      ((C.reindex (xorEquiv t)).phaseSector aX 0) = 1 := by
    rw [C.finrank_phaseSector_reindex_of_image (xorEquiv t) aU aX
      ((u : ZMod q) * b0.1) 0 hq hpresU hpresX hxorFiber0]
    exact hdimU0
  have hdimX1 : Module.finrank ℂ
      ((C.reindex (xorEquiv t)).phaseSector aX (q / m : ZMod q)) = 1 := by
    rw [C.finrank_phaseSector_reindex_of_image (xorEquiv t) aU aX
      ((u : ZMod q) * b1.1) (q / m : ZMod q) hq hpresU hpresX hxorFiber1]
    exact hdimU1
  have hcoordFiber0 :
      coordinateEquiv sigma '' subsetSumFiber aX 0 =
        subsetSumFiber aCanonical 0 := by
    exact image_subsetSumFiber_coordinateEquiv sigma aX 0
  have hcoordFiber1 :
      coordinateEquiv sigma '' subsetSumFiber aX (q / m : ZMod q) =
        subsetSumFiber aCanonical (q / m : ZMod q) := by
    exact image_subsetSumFiber_coordinateEquiv sigma aX _
  have hdimCanonical0 :
      Module.finrank ℂ (CCanonical.phaseSector aCanonical 0) = 1 := by
    change Module.finrank ℂ
      (((C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)).phaseSector
        aCanonical 0) = 1
    calc
      _ = Module.finrank ℂ
          ((C.reindex (xorEquiv t)).phaseSector aX 0) :=
        (C.reindex (xorEquiv t)).finrank_phaseSector_reindex_of_image
          (coordinateEquiv sigma) aX aCanonical 0 0 hq hpresX
          hpresCanonical hcoordFiber0
      _ = 1 := hdimX0
  have hdimCanonical1 : Module.finrank ℂ
      (CCanonical.phaseSector aCanonical (q / m : ZMod q)) = 1 := by
    change Module.finrank ℂ
      (((C.reindex (xorEquiv t)).reindex (coordinateEquiv sigma)).phaseSector
        aCanonical (q / m : ZMod q)) = 1
    calc
      _ = Module.finrank ℂ
          ((C.reindex (xorEquiv t)).phaseSector aX (q / m : ZMod q)) :=
        (C.reindex (xorEquiv t)).finrank_phaseSector_reindex_of_image
          (coordinateEquiv sigma) aX aCanonical (q / m : ZMod q)
          (q / m : ZMod q) hq hpresX hpresCanonical hcoordFiber1
      _ = 1 := hdimX1
  have hlabel_ne : (0 : ZMod q) ≠ (q / m : ZMod q) := by
    intro hzero
    have hembed : colorEmbed m q hmq (0 : ZMod m) =
        colorEmbed m q hmq (1 : ZMod m) := by
      simpa [colorEmbed_one_eq_div (m := m) (q := q) hmq] using hzero
    have h01 : (0 : ZMod m) = 1 :=
      colorEmbed_injective m q hm hq hmq hembed
    exact (zero_ne_one : (0 : ZMod m) ≠ 1) h01
  have hactive0 : CCanonical.phaseSector aCanonical 0 ≠ ⊥ := by
    intro hbot
    have hz := Submodule.finrank_eq_zero.mpr hbot
    omega
  have hactive1 :
      CCanonical.phaseSector aCanonical (q / m : ZMod q) ≠ ⊥ := by
    intro hbot
    have hz := Submodule.finrank_eq_zero.mpr hbot
    omega
  let B0 : CCanonical.ActiveResidue aCanonical := ⟨0, hactive0⟩
  let B1 : CCanonical.ActiveResidue aCanonical :=
    ⟨(q / m : ZMod q), hactive1⟩
  have hB01 : B0 ≠ B1 := by
    intro h
    apply hlabel_ne
    exact congrArg Subtype.val h
  have hcardle : Fintype.card (CCanonical.ActiveResidue aCanonical) ≤ 2 :=
    CCanonical.card_activeResidue_le hq aCanonical hpresCanonical
  have hpair_univ :
      ({B0, B1} : Finset (CCanonical.ActiveResidue aCanonical)) =
        Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (by simp)
    simpa [Finset.card_pair hB01] using hcardle
  have hexhaustCanonical (b : CCanonical.ActiveResidue aCanonical) :
      b.1 = 0 ∨ b.1 = (q / m : ZMod q) := by
    have hb : b ∈ ({B0, B1} : Finset
        (CCanonical.ActiveResidue aCanonical)) := by
      rw [hpair_univ]
      simp
    rcases Finset.mem_insert.mp hb with hb0 | hb1
    · left
      exact congrArg Subtype.val hb0
    · right
      exact congrArg Subtype.val (Finset.mem_singleton.mp hb1)
  have hexhaustB (b : CCanonical.ActiveResidue aCanonical) :
      b = B0 ∨ b = B1 := by
    rcases hexhaustCanonical b with hb | hb
    · left
      exact Subtype.ext hb
    · right
      exact Subtype.ext hb
  have honeOrder : addOrderOf (1 : ZMod m) = m := by
    have hm0 : m ≠ 0 := by omega
    rw [show (1 : ZMod m) = ((1 : ℕ) : ZMod m) by norm_num]
    rw [ZMod.addOrderOf_coe 1 hm0]
    simp
  have hlabelOrder : addOrderOf (q / m : ZMod q) = m := by
    rw [← colorEmbed_one_eq_div (m := m) (q := q) hmq]
    exact (addOrderOf_injective (colorEmbed m q hmq)
      (colorEmbed_injective m q hm hq hmq) 1).trans honeOrder
  have hprojectiveOrder : addOrderOf
      (CCanonical.projectiveClassMap
        ⟨phaseHom n q hq aCanonical, hpresCanonical⟩) = m := by
    rw [CCanonical.projectiveOrder_eq_relativeResiduesOrder
      hq aCanonical hpresCanonical B0]
    rw [CCanonical.addOrderOf_relativeResidues_eq_difference
      aCanonical B0 B1 hexhaustB]
    change addOrderOf ((q / m : ZMod q) - 0) = m
    simpa using hlabelOrder
  refine ⟨b0, b1, u, t, sigma, ?_⟩
  dsimp only [rankTwoCanonicalCoefficient, rankTwoCanonicalCode]
  refine ⟨hb01, hexhaust, hnormalized, ht, hmono,
    hprimitiveCanonical, hgcdCanonical, hpresCanonical, hphysicalOrder,
    hfiber0, hfiber1, hdimCanonical0, hdimCanonical1,
    hexhaustCanonical, (fun _ => hprojectiveOrder), ?_⟩
  intro d hd
  exact C.hasDistanceAtLeast_xor_permutation hd t sigma

/-- The rank-two SSLP corollary with all harmless physical normalizations
performed.  Besides cyclicity and a generating projective class, this stores
the canonical two-fiber witness produced by
`exists_rankTwoCanonicalNormalization`. -/
def HasCanonicalRankTwoSSLPNormalForm {n : ℕ}
    (C : CodeProjector n 2) : Prop :=
  IsAddCyclic C.ProjectiveDiagonalGroup ∧
    ∃ U : C.ProjectiveDiagonalGroup,
      U ≠ 0 ∧
      (∀ V : C.ProjectiveDiagonalGroup,
        V ∈ AddSubgroup.zmultiples U) ∧
      ∃ (m : ℕ) (R : ReducedDiagonalRepresentative n)
        (hpres : C.Preserves R.phase),
        m = addOrderOf U ∧
        C.projectiveClassMap ⟨R.phase, hpres⟩ = U ∧
        2 ≤ m ∧
        m ∣ R.q ∧
        C.HasRankTwoCanonicalNormalization
          (lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two) m R.a

/-- **Rank-two SSLP normal form in the displayed canonical coordinates.**

For a distance-at-least-two rank-two code with a nonzero projective diagonal
class, the projective diagonal group is cyclic.  A generator admits a reduced
finite-order representative, and unit-power, local-`X`, and coordinate
normalization put its two one-dimensional sectors at residues `0` and
`q / m`, while preserving every Pauli distance condition. -/
theorem rankTwo_sslp_canonical_normal_form
    {n d : ℕ} (C : CodeProjector n 2)
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U0 : C.ProjectiveDiagonalGroup) (hU0 : U0 ≠ 0) :
    C.HasCanonicalRankTwoSSLPNormalForm := by
  obtain ⟨hcyclic, U, hU, hgenerates, m, R, hpres, hmU, hclass,
      _hgcd, _hphysical, hm, hmq, _b0, _b1, _u, _hb01, _hexhaust,
      _hdim0, _hdim1, _hnormalized⟩ :=
    C.rankTwo_sslp_normal_form hd hd2 U0 hU0
  have hq : 0 < R.q :=
    lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  have hne : C.projectiveClassMap
      ⟨phaseHom n R.q hq R.a, hpres⟩ ≠ 0 := by
    change C.projectiveClassMap ⟨R.phase, hpres⟩ ≠ 0
    rw [hclass]
    exact hU
  have horder : addOrderOf
      (C.projectiveClassMap ⟨phaseHom n R.q hq R.a, hpres⟩) = m := by
    change addOrderOf (C.projectiveClassMap ⟨R.phase, hpres⟩) = m
    rw [hclass]
    exact hmU.symm
  have hcanonical := C.exists_rankTwoCanonicalNormalization
    hq m R.a R.primitive hpres hne hm hmq horder
  exact ⟨hcyclic, U, hU, hgenerates, m, R, hpres,
    hmU, hclass, hm, hmq, hcanonical⟩

end CodeProjector

end

end QECC
