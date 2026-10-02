import QECC.SectorDecomposition
import QECC.PauliKL

namespace QECC

open scoped BigOperators ComplexOrder

noncomputable section

namespace PauliString

variable {n : ℕ}

/-- The phase-free Pauli string that is `Z` on `J` and identity elsewhere. -/
def zOn (J : Finset (Fin n)) : PauliString n :=
  fun j => if j ∈ J then PauliLetter.Z else PauliLetter.I

@[simp] theorem support_zOn (J : Finset (Fin n)) : (zOn J).support = J := by
  ext j
  simp [support, zOn]

@[simp] theorem weight_zOn (J : Finset (Fin n)) : (zOn J).weight = J.card := by
  simp [weight]

/-- Computational-basis eigenvalue of a `Z` string. -/
def zParityValue (J : Finset (Fin n)) (x : BitString n) : ℂ :=
  ∏ j ∈ J, if x j then (-1 : ℂ) else 1

/-- A `Z` string is diagonal, with its usual parity eigenvalue. -/
theorem operator_zOn_apply (J : Finset (Fin n)) (x y : BitString n) :
    (zOn J).operator x y =
      if x = y then zParityValue J x else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    change (∏ j : Fin n,
      ((if j ∈ J then PauliLetter.Z else PauliLetter.I).entry (x j) (x j))) = _
    have hfactor : ∀ j : Fin n,
        ((if j ∈ J then PauliLetter.Z else PauliLetter.I).entry (x j) (x j)) =
          if j ∈ J then (if x j then (-1 : ℂ) else 1) else 1 := by
      intro j
      by_cases hj : j ∈ J <;> simp [hj, PauliLetter.entry]
    simp_rw [hfactor]
    simpa only [zParityValue, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using
      (Finset.prod_filter (s := Finset.univ) (fun j : Fin n => j ∈ J)
        (fun j => if x j then (-1 : ℂ) else 1)).symm
  · have hcoord : ∃ k : Fin n, x k ≠ y k := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨k, hk⟩ := hcoord
    have hentry : ((zOn J) k).entry (x k) (y k) = 0 := by
      by_cases hkJ : k ∈ J <;>
        simp [zOn, hkJ, PauliLetter.entry, hk]
    have hprod : ∏ i, ((zOn J) i).entry (x i) (y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hentry
    simp [operator, hxy, hprod]

end PauliString

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- KL detection is closed under scalar multiplication. -/
theorem detects_smul {E : Operator n} (hE : C.Detects E) (c : ℂ) :
    C.Detects (c • E) := by
  rcases hE with ⟨lam, hlam⟩
  refine ⟨c * lam, ?_⟩
  simp [hlam, smul_smul]

/-- KL detection is closed under addition. -/
theorem detects_add {E F : Operator n} (hE : C.Detects E)
    (hF : C.Detects F) : C.Detects (E + F) := by
  rcases hE with ⟨lam, hlam⟩
  rcases hF with ⟨mu, hmu⟩
  refine ⟨lam + mu, ?_⟩
  rw [Matrix.mul_add, Matrix.add_mul, hlam, hmu, add_smul]

/-- A finite sum of detected operators is detected. -/
theorem detects_sum {I : Type*} (s : Finset I) (E : I → Operator n)
    (hE : ∀ i ∈ s, C.Detects (E i)) :
    C.Detects (∑ i ∈ s, E i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact C.detects_add (hE i (Finset.mem_insert_self i s))
        (ih fun j hj => hE j (Finset.mem_insert_of_mem hj))

/-- The orthogonal projector onto the part of the code in subset-sum fiber
`b`.  Preservation is not part of the definition, but is what makes the two
factors commute and hence makes their product an orthogonal projector. -/
def sectorProjector (a : Fin n → ZMod q) (b : ZMod q) : Operator n :=
  fiberProjector a b * C.proj

@[simp] theorem sectorProjector_apply (a : Fin n → ZMod q) (b : ZMod q)
    (x y : BitString n) :
    C.sectorProjector a b x y =
      if subsetSum a x = b then C.proj x y else 0 := by
  classical
  simp [sectorProjector, fiberProjector, Matrix.diagonal_mul]

/-- A sector projector is Hermitian when the modular diagonal gate preserves
the code. -/
theorem sectorProjector_hermitian (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q) :
    (C.sectorProjector a b).conjTranspose = C.sectorProjector a b := by
  rw [sectorProjector, Matrix.conjTranspose_mul,
    fiberProjector_conjTranspose, C.hermitian]
  exact C.commutes_fiberProjector hq a hpres b

/-- A sector projector is idempotent when the modular diagonal gate preserves
the code. -/
theorem sectorProjector_idempotent (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q) :
    C.sectorProjector a b * C.sectorProjector a b =
      C.sectorProjector a b := by
  let F := fiberProjector a b
  have hcomm : C.proj * F = F * C.proj :=
    C.commutes_fiberProjector hq a hpres b
  change (F * C.proj) * (F * C.proj) = F * C.proj
  calc
    (F * C.proj) * (F * C.proj) = F * (C.proj * F) * C.proj := by
      simp only [Matrix.mul_assoc]
    _ = F * (F * C.proj) * C.proj := by rw [hcomm]
    _ = (F * F) * (C.proj * C.proj) := by
      simp only [Matrix.mul_assoc]
    _ = F * C.proj := by
      rw [fiberProjector_idempotent, C.idempotent]

/-- The range of the sector projector is exactly the intersection of the code
with the corresponding subset-sum fiber. -/
theorem range_sectorProjector_mulVecLin (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (b : ZMod q) :
    LinearMap.range (C.sectorProjector a b).mulVecLin =
      C.phaseSector a b := by
  let F := fiberProjector a b
  let Q := C.sectorProjector a b
  have hcomm : C.proj * F = F * C.proj :=
    C.commutes_fiberProjector hq a hpres b
  have hPQ : C.proj * Q = Q := by
    change C.proj * (F * C.proj) = F * C.proj
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, C.idempotent]
  have hFQ : F * Q = Q := by
    change F * (F * C.proj) = F * C.proj
    rw [← Matrix.mul_assoc, fiberProjector_idempotent]
  ext psi
  constructor
  · rintro ⟨phi, rfl⟩
    rw [C.mem_phaseSector]
    constructor
    · change C.proj.mulVec (Q.mulVec phi) = Q.mulVec phi
      rw [Matrix.mulVec_mulVec, hPQ]
    · rw [← fiberProjector_mulVec_eq_self_iff]
      change F.mulVec (Q.mulVec phi) = Q.mulVec phi
      rw [Matrix.mulVec_mulVec, hFQ]
  · intro hpsi
    rw [C.mem_phaseSector] at hpsi
    refine ⟨psi, ?_⟩
    change (F * C.proj).mulVec psi = psi
    rw [← Matrix.mulVec_mulVec, hpsi.1]
    exact (fiberProjector_mulVec_eq_self_iff a b psi).2 hpsi.2

/-- Matrix rank of a sector projector equals the complex dimension of the
corresponding phase sector. -/
theorem rank_sectorProjector (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q) :
    Matrix.rank (C.sectorProjector a b) =
      Module.finrank ℂ (C.phaseSector a b) := by
  change Module.finrank ℂ
      (LinearMap.range (C.sectorProjector a b).mulVecLin) = _
  rw [C.range_sectorProjector_mulVecLin hq a hpres b]

/-- Sector projectors are positive semidefinite. -/
theorem sectorProjector_posSemidef (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q) :
    (C.sectorProjector a b).PosSemidef := by
  let Q := C.sectorProjector a b
  have hherm : Q.conjTranspose = Q :=
    C.sectorProjector_hermitian hq a hpres b
  have hidem : Q * Q = Q :=
    C.sectorProjector_idempotent hq a hpres b
  have hpositive := Matrix.posSemidef_conjTranspose_mul_self Q
  simpa [hherm, hidem] using hpositive

/-- The diagonal entries of a sector projector are real. -/
theorem sectorProjector_diag_eq_re (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q)
    (x : BitString n) :
    ((C.sectorProjector a b x x).re : ℂ) =
      C.sectorProjector a b x x := by
  have hherm := C.sectorProjector_hermitian hq a hpres b
  have hentry := congrFun (congrFun hherm x) x
  have hstar : star (C.sectorProjector a b x x) =
      C.sectorProjector a b x x := by
    simpa [Matrix.conjTranspose_apply] using hentry
  exact Complex.conj_eq_iff_re.mp hstar

/-- The real diagonal of a sector projector is nonnegative. -/
theorem sectorProjector_diag_re_nonneg (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (b : ZMod q) (x : BitString n) :
    0 ≤ (C.sectorProjector a b x x).re := by
  have hnonneg : (0 : ℂ) ≤ C.sectorProjector a b x x :=
    (C.sectorProjector_posSemidef hq a hpres b).diag_nonneg
  exact (Complex.nonneg_iff.mp hnonneg).1

/-- Dimension of a modular phase sector. -/
def sectorDimension (a : Fin n → ZMod q) (b : ZMod q) : ℕ :=
  Module.finrank ℂ (C.phaseSector a b)

/-- The normalized computational-basis diagonal of a nonzero sector
projector.  It is defined for an active residue so its denominator is
positive. -/
def sectorDistribution (a : Fin n → ZMod q) (b : C.ActiveResidue a) :
    BitString n → ℝ :=
  fun x => (C.sectorProjector a b.1 x x).re /
    (C.sectorDimension a b.1 : ℝ)

theorem sectorDimension_pos [NeZero q] (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) : 0 < C.sectorDimension a b.1 := by
  exact C.activeResidue_finrank_pos a b

/-- Sector distributions are pointwise nonnegative. -/
theorem sectorDistribution_nonneg (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b : C.ActiveResidue a) (x : BitString n) :
    0 ≤ C.sectorDistribution a b x := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact div_nonneg (C.sectorProjector_diag_re_nonneg hq a hpres b.1 x)
    (Nat.cast_nonneg _)

/-- A sector distribution vanishes away from its full subset-sum fiber.
Inside the fiber it may still have zero entries. -/
theorem sectorDistribution_eq_zero_of_not_mem (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) (x : BitString n)
    (hx : subsetSum a x ≠ b.1) :
    C.sectorDistribution a b x = 0 := by
  simp [sectorDistribution, sectorProjector_apply, hx]

/-- The trace of a sector projector is its sector dimension. -/
theorem trace_sectorProjector (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) (b : ZMod q) :
    Matrix.trace (C.sectorProjector a b) =
      (C.sectorDimension a b : ℂ) := by
  let Q := C.sectorProjector a b
  let f : Module.End ℂ (State n) := Q.mulVecLin
  have hidemMatrix : Q * Q = Q :=
    C.sectorProjector_idempotent hq a hpres b
  have hidem : IsIdempotentElem f := by
    change f * f = f
    change Q.mulVecLin ∘ₗ Q.mulVecLin = Q.mulVecLin
    rw [← Matrix.mulVecLin_mul, hidemMatrix]
  have hproj : LinearMap.IsProj (LinearMap.range f) f :=
    LinearMap.IsIdempotentElem.isProj_range f hidem
  have htrace := hproj.trace
  have hrange : LinearMap.range f = C.phaseSector a b := by
    exact C.range_sectorProjector_mulVecLin hq a hpres b
  have hmatrixTrace : (LinearMap.trace ℂ (State n)) f = Matrix.trace Q := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (BitString n)) f]
    rw [LinearMap.toMatrix_eq_toMatrix']
    change (LinearMap.toMatrix' Q.mulVecLin).trace = Q.trace
    rw [show Q.mulVecLin = Matrix.toLin' Q by rfl,
      LinearMap.toMatrix'_toLin']
  rw [hmatrixTrace, hrange] at htrace
  exact htrace

/-- Every active-sector distribution has total mass one. -/
theorem sum_sectorDistribution (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (b : C.ActiveResidue a) :
    ∑ x : BitString n, C.sectorDistribution a b x = 1 := by
  letI : NeZero q := ⟨hq.ne'⟩
  let k := C.sectorDimension a b.1
  have hk : 0 < k := C.sectorDimension_pos a b
  have htrace := C.trace_sectorProjector hq a hpres b.1
  have hsumRe :
      ∑ x : BitString n, (C.sectorProjector a b.1 x x).re = (k : ℝ) := by
    have hre := congrArg Complex.re htrace
    change (∑ x : BitString n, C.sectorProjector a b.1 x x).re = (k : ℂ).re at hre
    simpa [map_sum] using hre
  simp only [sectorDistribution]
  rw [← Finset.sum_div, hsumRe]
  exact div_self (Nat.cast_ne_zero.mpr hk.ne')

/-- Real part of the trace of an observable on a sector, normalized by the
sector dimension. -/
def normalizedSectorTrace (a : Fin n → ZMod q) (b : C.ActiveResidue a)
    (E : Operator n) : ℝ :=
  (Matrix.trace (C.sectorProjector a b.1 * E)).re /
    (C.sectorDimension a b.1 : ℝ)

/-- A KL-detected operator has its detected scalar as the normalized trace on
every active phase sector. -/
theorem normalizedSectorTrace_eq_detectedScalar (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (E : Operator n) (lam : ℂ)
    (hdet : C.proj * E * C.proj = lam • C.proj)
    (b : C.ActiveResidue a) :
    C.normalizedSectorTrace a b E = lam.re := by
  letI : NeZero q := ⟨hq.ne'⟩
  let F := fiberProjector a b.1
  let Q := C.sectorProjector a b.1
  let k := C.sectorDimension a b.1
  have hk : 0 < k := C.sectorDimension_pos a b
  have hPQ : C.proj * Q = Q := by
    change C.proj * (F * C.proj) = F * C.proj
    rw [← Matrix.mul_assoc,
      C.commutes_fiberProjector hq a hpres b.1,
      Matrix.mul_assoc, C.idempotent]
  have htraceQ : Matrix.trace Q = (k : ℂ) := by
    exact C.trace_sectorProjector hq a hpres b.1
  have htrace : Matrix.trace (Q * E) = lam * (k : ℂ) := by
    calc
      Matrix.trace (Q * E) = Matrix.trace ((C.proj * Q) * E) := by rw [hPQ]
      _ = Matrix.trace (Q * E * C.proj) :=
        (Matrix.trace_mul_cycle Q E C.proj).symm
      _ = Matrix.trace (F * (C.proj * E * C.proj)) := by
        simp only [Q, F, sectorProjector, Matrix.mul_assoc]
      _ = Matrix.trace (F * (lam • C.proj)) := by rw [hdet]
      _ = Matrix.trace (lam • Q) := by
        rw [Matrix.mul_smul]
        rfl
      _ = lam * Matrix.trace Q := by rw [Matrix.trace_smul, smul_eq_mul]
      _ = lam * (k : ℂ) := by rw [htraceQ]
  unfold normalizedSectorTrace
  change (Matrix.trace (Q * E)).re / (k : ℝ) = lam.re
  rw [htrace]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero]
  exact (mul_div_cancel_right₀ lam.re (Nat.cast_ne_zero.mpr hk.ne')).trans rfl

/-- Any KL-detected operator has the same normalized trace on every pair of
active sectors. -/
theorem normalizedSectorTrace_eq_of_detects (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (E : Operator n) (hdet : C.Detects E)
    (b c : C.ActiveResidue a) :
    C.normalizedSectorTrace a b E = C.normalizedSectorTrace a c E := by
  rcases hdet with ⟨lam, hlam⟩
  rw [C.normalizedSectorTrace_eq_detectedScalar hq a hpres E lam hlam b,
    C.normalizedSectorTrace_eq_detectedScalar hq a hpres E lam hlam c]

/-- The binary monomial associated with a set of physical qubits. -/
def binaryMonomialValue (J : Finset (Fin n)) (x : BitString n) : ℝ :=
  ∏ j ∈ J, bitReal (x j)

/-- Diagonal observable whose value on `x` is the binary monomial supported
on `J`. -/
def binaryMonomial (J : Finset (Fin n)) : Operator n :=
  Matrix.diagonal fun x => (binaryMonomialValue J x : ℂ)

/-- Fourier expansion of a binary monomial in phase-free Pauli `Z` strings. -/
theorem binaryMonomial_eq_pauliExpansion (J : Finset (Fin n)) :
    binaryMonomial J =
      ((2 : ℂ) ^ J.card)⁻¹ •
        ∑ S ∈ J.powerset,
          ((-1 : ℂ) ^ S.card) • (PauliString.zOn S).operator := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [binaryMonomial, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, PauliString.operator_zOn_apply,
      if_pos]
    let z : Fin n → ℂ := fun j => if x j then -1 else 1
    have hexpand :
        (∏ j ∈ J, ((1 : ℂ) - z j)) =
          ∑ S ∈ J.powerset,
            (-1 : ℂ) ^ S.card * PauliString.zParityValue S x := by
      simpa [z, PauliString.zParityValue] using
        (Finset.prod_sub (fun _ : Fin n => (1 : ℂ)) z J)
    have hlocal : ∀ j : Fin n,
        (1 : ℂ) - z j = 2 * (bitReal (x j) : ℂ) := by
      intro j
      cases hx : x j <;> norm_num [z, bitReal, hx]
    have hproduct :
        (∏ j ∈ J, ((1 : ℂ) - z j)) =
          (2 : ℂ) ^ J.card * (binaryMonomialValue J x : ℂ) := by
      simp_rw [hlocal]
      rw [Finset.prod_mul_distrib]
      simp [binaryMonomialValue]
    rw [← hexpand, hproduct]
    field_simp
  · simp [binaryMonomial, Matrix.smul_apply, Matrix.sum_apply,
      PauliString.operator_zOn_apply, hxy]

/-- Distance at least `d` implies detection of every binary monomial of
degree strictly less than `d`. -/
theorem detects_binaryMonomial_of_hasDistanceAtLeast {d : ℕ}
    (hd : C.HasDistanceAtLeast d) (J : Finset (Fin n))
    (hJ : J.card < d) : C.Detects (binaryMonomial J) := by
  classical
  have hterms : ∀ S ∈ J.powerset,
      C.Detects (((-1 : ℂ) ^ S.card) • (PauliString.zOn S).operator) := by
    intro S hS
    have hsubset : S ⊆ J := Finset.mem_powerset.mp hS
    have hweight : (PauliString.zOn S).weight < d := by
      rw [PauliString.weight_zOn]
      exact (Finset.card_le_card hsubset).trans_lt hJ
    exact C.detects_smul (hd (PauliString.zOn S) hweight)
      ((-1 : ℂ) ^ S.card)
  have hsum : C.Detects
      (∑ S ∈ J.powerset,
        ((-1 : ℂ) ^ S.card) • (PauliString.zOn S).operator) :=
    C.detects_sum J.powerset _ hterms
  have hscaled := C.detects_smul hsum (((2 : ℂ) ^ J.card)⁻¹)
  rw [← binaryMonomial_eq_pauliExpansion J] at hscaled
  exact hscaled

/-- The probability moment of an active sector is its normalized trace against
the corresponding binary-monomial observable. -/
theorem sectorMoment_eq_normalizedSectorTrace (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) (J : Finset (Fin n)) :
    ∑ x : BitString n,
        C.sectorDistribution a b x * binaryMonomialValue J x =
      C.normalizedSectorTrace a b (binaryMonomial J) := by
  let Q := C.sectorProjector a b.1
  let k := C.sectorDimension a b.1
  have htrace :
      (Matrix.trace (Q * binaryMonomial J)).re =
        ∑ x : BitString n, (Q x x).re * binaryMonomialValue J x := by
    change (Matrix.trace (Q * Matrix.diagonal
      (fun x => (binaryMonomialValue J x : ℂ)))).re = _
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
    change Complex.reCLM
      (∑ x : BitString n, Q x x * (binaryMonomialValue J x : ℂ)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp
  unfold sectorDistribution normalizedSectorTrace
  change (∑ x : BitString n,
      (Q x x).re / (k : ℝ) * binaryMonomialValue J x) =
    (Matrix.trace (Q * binaryMonomial J)).re / (k : ℝ)
  rw [htrace, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Consequently, detection of a binary monomial makes that moment
independent of the active phase sector. -/
theorem sectorMoment_eq_of_detects_binaryMonomial (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (J : Finset (Fin n)) (hdet : C.Detects (binaryMonomial J))
    (b c : C.ActiveResidue a) :
    (∑ x : BitString n,
        C.sectorDistribution a b x * binaryMonomialValue J x) =
      ∑ x : BitString n,
        C.sectorDistribution a c x * binaryMonomialValue J x := by
  rw [C.sectorMoment_eq_normalizedSectorTrace a b J,
    C.sectorMoment_eq_normalizedSectorTrace a c J]
  exact C.normalizedSectorTrace_eq_of_detects hq a hpres
    (binaryMonomial J) hdet b c

/-- Low-degree binary moments agree across active sectors of a code with the
corresponding distance. -/
theorem sectorMoment_eq_of_hasDistanceAtLeast {d : ℕ} (hq : 0 < q)
    (a : Fin n → ZMod q) (hpres : C.Preserves (phaseHom n q hq a))
    (hd : C.HasDistanceAtLeast d) (J : Finset (Fin n)) (hJ : J.card < d)
    (b c : C.ActiveResidue a) :
    (∑ x : BitString n,
        C.sectorDistribution a b x * binaryMonomialValue J x) =
      ∑ x : BitString n,
        C.sectorDistribution a c x * binaryMonomialValue J x := by
  exact C.sectorMoment_eq_of_detects_binaryMonomial hq a hpres J
    (C.detects_binaryMonomial_of_hasDistanceAtLeast hd J hJ) b c

end CodeProjector

end

end QECC
