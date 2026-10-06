import QECC.Basic

namespace QECC

/-- A phase-free single-qubit Pauli letter.  The four constructors denote the
standard Hermitian matrices `I`, `X`, `Y`, and `Z`; no global Pauli phase is
stored in this type. -/
inductive PauliLetter where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Fintype, Repr

namespace PauliLetter

/-- Computational-basis matrix entries of a phase-free Pauli letter. -/
def entry : PauliLetter → Bool → Bool → ℂ
  | I, x, y => if x = y then 1 else 0
  | X, x, y => if x = y then 0 else 1
  | Y, x, y => if x = y then 0 else if x then Complex.I else -Complex.I
  | Z, x, y => if x = y then if x then -1 else 1 else 0

/-- The standard two-by-two matrix represented by a Pauli letter. -/
def matrix (p : PauliLetter) : Matrix Bool Bool ℂ :=
  fun x y => p.entry x y

theorem star_entry_swap (p : PauliLetter) (x y : Bool) :
    star (p.entry y x) = p.entry x y := by
  cases p <;> cases x <;> cases y <;> simp [entry]

/-- Every phase-free single-qubit Pauli matrix is Hermitian. -/
theorem matrix_hermitian (p : PauliLetter) :
    p.matrix.conjTranspose = p.matrix := by
  ext x y
  simpa [matrix, Matrix.conjTranspose_apply] using p.star_entry_swap x y

end PauliLetter

/-- A phase-free `n`-qubit Pauli string. -/
abbrev PauliString (n : ℕ) := Fin n → PauliLetter

namespace PauliString

variable {n : ℕ}

/-- The qubits on which a Pauli string is nonidentity. -/
def support (p : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter fun j => p j ≠ PauliLetter.I

/-- The Hamming weight of a Pauli string. -/
def weight (p : PauliString n) : ℕ := p.support.card

/-- The identity Pauli string. -/
def identity : PauliString n := fun _ => PauliLetter.I

/-- A Pauli letter acting at one specified qubit and identity elsewhere. -/
def single (j : Fin n) (p : PauliLetter) : PauliString n :=
  fun k => if k = j then p else PauliLetter.I

/-- Pauli `Z` acting at one specified qubit. -/
def singleZ (j : Fin n) : PauliString n := single j PauliLetter.Z

@[simp] theorem support_identity : (identity : PauliString n).support = ∅ := by
  ext j
  simp [support, identity]

@[simp] theorem weight_identity : (identity : PauliString n).weight = 0 := by
  simp [weight]

theorem support_single {j : Fin n} {p : PauliLetter}
    (hp : p ≠ PauliLetter.I) : (single j p).support = {j} := by
  ext k
  by_cases hkj : k = j
  · subst k
    simp [support, single, hp]
  · simp [support, single, hkj]

theorem weight_single {j : Fin n} {p : PauliLetter}
    (hp : p ≠ PauliLetter.I) : (single j p).weight = 1 := by
  rw [weight, support_single hp]
  simp

@[simp] theorem weight_singleZ (j : Fin n) : (singleZ j).weight = 1 := by
  exact weight_single (by simp)

/-- The tensor-product operator represented by a Pauli string, written directly
in the computational basis. -/
def operator (p : PauliString n) : Operator n :=
  fun x y => ∏ j, (p j).entry (x j) (y j)

/-- Every phase-free Pauli-string operator is Hermitian. -/
theorem operator_hermitian (p : PauliString n) :
    p.operator.conjTranspose = p.operator := by
  ext x y
  change star (∏ j, (p j).entry (y j) (x j)) =
    ∏ j, (p j).entry (x j) (y j)
  change (starRingEnd ℂ) (∏ j, (p j).entry (y j) (x j)) =
    ∏ j, (p j).entry (x j) (y j)
  rw [map_prod (starRingEnd ℂ)]
  apply Finset.prod_congr rfl
  intro j _
  exact (p j).star_entry_swap (x j) (y j)

/-- The tensor-product realization of a single-site `Z` agrees with the
pre-existing computational-basis operator `zOp`. -/
theorem operator_singleZ (j : Fin n) : (singleZ j).operator = zOp j := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    have hprod :
        (∏ i, ((singleZ j) i).entry (x i) (x i)) =
          ((singleZ j) j).entry (x j) (x j) := by
      apply Finset.prod_eq_single_of_mem j (Finset.mem_univ j)
      intro k _ hkj
      simp [singleZ, single, hkj, PauliLetter.entry]
    rw [show (singleZ j).operator x x =
        ∏ i, ((singleZ j) i).entry (x i) (x i) by rfl]
    rw [hprod]
    cases hx : x j
    · simp [singleZ, single, PauliLetter.entry, zOp, bitReal, hx]
    · norm_num [singleZ, single, PauliLetter.entry, zOp, bitReal, hx]
  · have hcoord : ∃ k : Fin n, x k ≠ y k := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨k, hk⟩ := hcoord
    have hentry : ((singleZ j) k).entry (x k) (y k) = 0 := by
      by_cases hkj : k = j
      · subst k
        simp [singleZ, single, PauliLetter.entry, hk]
      · simp [singleZ, single, hkj, PauliLetter.entry, hk]
    have hprod : ∏ i, ((singleZ j) i).entry (x i) (y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hentry
    simp [operator, zOp, hxy, hprod]

end PauliString

namespace CodeProjector

variable {n K : ℕ}

/-- The Knill--Laflamme detection equation for one operator. -/
def Detects (C : CodeProjector n K) (E : Operator n) : Prop :=
  ∃ lam : ℂ, C.proj * E * C.proj = lam • C.proj

/-- A code has distance at least `d` when it detects every phase-free Pauli
string of weight strictly less than `d`. -/
def HasDistanceAtLeast (C : CodeProjector n K) (d : ℕ) : Prop :=
  ∀ p : PauliString n, p.weight < d → C.Detects p.operator

/-- Entrywise form of the one-operator Knill--Laflamme equation. -/
theorem detects_iff_entries (C : CodeProjector n K) (E : Operator n) :
    C.Detects E ↔
      ∃ lam : ℂ, ∀ x y, (C.proj * E * C.proj) x y = lam * C.proj x y := by
  constructor
  · rintro ⟨lam, h⟩
    refine ⟨lam, fun x y => ?_⟩
    have hxy := congrFun (congrFun h x) y
    simpa using hxy
  · rintro ⟨lam, h⟩
    refine ⟨lam, ?_⟩
    ext x y
    simpa using h x y

/-- If a Hermitian operator is detected by an orthogonal projector, its KL
scalar may be chosen real.  This also covers the zero projector. -/
theorem detects_real_of_hermitian (C : CodeProjector n K) (E : Operator n)
    (hE : E.conjTranspose = E) (hdet : C.Detects E) :
    ∃ lam : ℝ, C.proj * E * C.proj = (lam : ℂ) • C.proj := by
  rcases hdet with ⟨lam, hlam⟩
  by_cases hproj : C.proj = 0
  · refine ⟨0, ?_⟩
    simp [hproj]
  · have hherm : (C.proj * E * C.proj).conjTranspose =
        C.proj * E * C.proj := by
      simp [Matrix.conjTranspose_mul, C.hermitian, hE, Matrix.mul_assoc]
    have hscalar : star lam • C.proj = lam • C.proj := by
      calc
        star lam • C.proj = (lam • C.proj).conjTranspose := by
          simp [Matrix.conjTranspose_smul, C.hermitian]
        _ = (C.proj * E * C.proj).conjTranspose := by rw [hlam]
        _ = C.proj * E * C.proj := hherm
        _ = lam • C.proj := hlam
    have hnonzero : ∃ x y, C.proj x y ≠ 0 := by
      by_contra h
      push_neg at h
      apply hproj
      ext x y
      exact h x y
    obtain ⟨x, y, hxy⟩ := hnonzero
    have hstar : star lam = lam := by
      have hentry := congrFun (congrFun hscalar x) y
      simp only [Matrix.smul_apply, smul_eq_mul] at hentry
      exact mul_right_cancel₀ hxy hentry
    have hre : (lam.re : ℂ) = lam := Complex.conj_eq_iff_re.mp hstar
    refine ⟨lam.re, ?_⟩
    calc
      C.proj * E * C.proj = lam • C.proj := hlam
      _ = (lam.re : ℂ) • C.proj := by rw [hre]

/-- Distance at least two implies the single-site `Z` detection hypothesis used
by the first theorem. -/
theorem detectsSingleZ_of_hasDistanceAtLeast_two (C : CodeProjector n K)
    (hd : C.HasDistanceAtLeast 2) : C.DetectsSingleZ := by
  have hj : ∀ j : Fin n, ∃ lam : ℝ,
      C.proj * zOp j * C.proj = (lam : ℂ) • C.proj := by
    intro j
    have hdetPauli : C.Detects (PauliString.singleZ j).operator :=
      hd (PauliString.singleZ j) (by simp)
    have hdetZ : C.Detects (zOp j) := by
      simpa [PauliString.operator_singleZ] using hdetPauli
    have hhermZ : (zOp j).conjTranspose = zOp j := by
      rw [← PauliString.operator_singleZ]
      exact PauliString.operator_hermitian _
    exact C.detects_real_of_hermitian (zOp j) hhermZ hdetZ
  choose lam hlam using hj
  exact ⟨lam, hlam⟩

end CodeProjector

end QECC
