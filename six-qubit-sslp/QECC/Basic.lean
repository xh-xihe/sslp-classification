import Mathlib
import QECC.MathlibCompat

namespace QECC

/-- Computational-basis labels for `n` qubits. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- State vectors in the computational basis. -/
abbrev State (n : ℕ) := BitString n → ℂ

/-- Operators in the computational basis. -/
abbrev Operator (n : ℕ) := Matrix (BitString n) (BitString n) ℂ

/-- Interpret a bit as an integer. -/
def bitInt (b : Bool) : ℤ := if b then 1 else 0

/-- Interpret a bit as a real number. -/
def bitReal (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem bitInt_false : bitInt false = 0 := rfl
@[simp] theorem bitInt_true : bitInt true = 1 := rfl
@[simp] theorem bitReal_false : bitReal false = 0 := rfl
@[simp] theorem bitReal_true : bitReal true = 1 := rfl

/-- The computational-basis number operator on qubit `j`. -/
def numberOp {n : ℕ} (j : Fin n) : Operator n :=
  Matrix.diagonal fun x => (bitReal (x j) : ℂ)

/-- Pauli `Z` on qubit `j`, in the fixed computational basis. -/
def zOp {n : ℕ} (j : Fin n) : Operator n :=
  Matrix.diagonal fun x => ((1 - 2 * bitReal (x j) : ℝ) : ℂ)

/-- A finite-dimensional qubit code represented by its orthogonal projector. -/
structure CodeProjector (n K : ℕ) where
  /-- The matrix of the code projector. -/
  proj : Operator n
  hermitian : proj.conjTranspose = proj
  idempotent : proj * proj = proj
  rank_eq : Matrix.rank proj = K

namespace CodeProjector

variable {n K : ℕ}

/-- The code space as the range of its projector. -/
abbrev CodeSpace (C : CodeProjector n K) := LinearMap.range C.proj.mulVecLin

/-- The stored matrix rank is the complex dimension of the code space. -/
theorem codeSpace_finrank (C : CodeProjector n K) :
    Module.finrank ℂ C.CodeSpace = K := by
  simpa [CodeSpace, Matrix.rank] using C.rank_eq

/-- For an idempotent projector, code vectors are exactly its fixed vectors. -/
theorem mem_codeSpace_iff (C : CodeProjector n K) (psi : State n) :
    psi ∈ C.CodeSpace ↔ C.proj.mulVec psi = psi := by
  constructor
  · rintro ⟨w, rfl⟩
    calc
      C.proj.mulVec (C.proj.mulVec w) = (C.proj * C.proj).mulVec w :=
        Matrix.mulVec_mulVec _ _ _
      _ = C.proj.mulVec w := by rw [C.idempotent]
  · intro h
    exact ⟨psi, h⟩

/-- Detection of every single-site `Z` in the chosen product basis. -/
def DetectsSingleZ (C : CodeProjector n K) : Prop :=
  ∃ lam : Fin n → ℝ, ∀ j,
    C.proj * zOp j * C.proj = (lam j : ℂ) • C.proj

/-- Equivalent number-operator form of single-site detection. -/
def DetectsNumberOps (C : CodeProjector n K) : Prop :=
  ∃ μ : Fin n → ℝ, ∀ j,
    C.proj * numberOp j * C.proj = (μ j : ℂ) • C.proj

theorem zOp_eq_one_sub_two_numberOp (j : Fin n) :
    zOp j = 1 - (2 : ℂ) • numberOp j := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [zOp, numberOp]
  · simp [zOp, numberOp, hxy]

/-- The `Z`-detection equations imply the equivalent number-operator equations. -/
theorem detectsNumberOps_of_detectsSingleZ (C : CodeProjector n K)
    (hZ : C.DetectsSingleZ) : C.DetectsNumberOps := by
  rcases hZ with ⟨lam, hlam⟩
  refine ⟨fun j => (1 - lam j) / 2, fun j => ?_⟩
  have hPone : C.proj * (1 : Operator n) * C.proj = C.proj := by
    simpa [Matrix.mul_assoc] using C.idempotent
  have hz := hlam j
  rw [zOp_eq_one_sub_two_numberOp] at hz
  have hz' :
      C.proj - (2 : ℂ) • (C.proj * numberOp j * C.proj) =
        (lam j : ℂ) • C.proj := by
    simpa [Matrix.mul_sub, Matrix.sub_mul, C.idempotent, Matrix.mul_assoc] using hz
  have htwo :
      (2 : ℂ) • (C.proj * numberOp j * C.proj) =
        ((1 : ℂ) - (lam j : ℂ)) • C.proj := by
    rw [sub_smul, one_smul]
    apply (eq_sub_iff_add_eq).2
    rw [add_comm]
    exact ((sub_eq_iff_eq_add).mp hz').symm
  calc
    C.proj * numberOp j * C.proj
        = (2 : ℂ)⁻¹ • ((2 : ℂ) • (C.proj * numberOp j * C.proj)) := by
            rw [smul_smul]
            norm_num
    _ = (2 : ℂ)⁻¹ • (((1 : ℂ) - (lam j : ℂ)) • C.proj) := by rw [htwo]
    _ = (((1 - lam j) / 2 : ℝ) : ℂ) • C.proj := by
          rw [smul_smul]
          congr 1
          push_cast
          ring

end CodeProjector

end QECC
