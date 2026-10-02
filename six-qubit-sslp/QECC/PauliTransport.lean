import QECC.CodeTransport
import QECC.PauliKL

namespace QECC

noncomputable section

namespace PauliLetter

/-- The phase-free Pauli letter obtained by conjugating by `X` when `t` is
true.  Conjugation fixes the underlying phase-free letter; its sign is stored
separately in `xorConjugationSign`. -/
def xorConjugate : Bool → PauliLetter → PauliLetter
  | false, p => p
  | true, I => I
  | true, X => X
  | true, Y => Y
  | true, Z => Z

/-- The sign in `X^t p X^t` for a phase-free Pauli letter `p`. -/
def xorConjugationSign : Bool → PauliLetter → ℂ
  | false, _ => 1
  | true, I => 1
  | true, X => 1
  | true, Y => -1
  | true, Z => -1

@[simp] theorem xorConjugate_eq (t : Bool) (p : PauliLetter) :
    xorConjugate t p = p := by
  cases t <;> cases p <;> rfl

@[simp] theorem xorConjugationSign_ne_zero (t : Bool) (p : PauliLetter) :
    xorConjugationSign t p ≠ 0 := by
  cases t <;> cases p <;> norm_num [xorConjugationSign]

/-- Entrywise form of conjugation of a Pauli letter by a computational-basis
bit flip. -/
theorem entry_xor_conjugate (t x y : Bool) (p : PauliLetter) :
    p.entry (x ^^ t) (y ^^ t) =
      xorConjugationSign t p * (xorConjugate t p).entry x y := by
  cases t <;> cases p <;> cases x <;> cases y <;>
    norm_num [xorConjugationSign, xorConjugate, entry]

end PauliLetter

namespace PauliString

variable {n : ℕ}

/-- The phase-free Pauli string obtained after conjugating by the tensor
product of the `X` operators selected by `t`. -/
def xorReindex (t : BitString n) (p : PauliString n) : PauliString n :=
  fun j => PauliLetter.xorConjugate (t j) (p j)

/-- The global sign produced by conjugating `p` by the bit flip `t`. -/
def xorPhase (t : BitString n) (p : PauliString n) : ℂ :=
  ∏ j, PauliLetter.xorConjugationSign (t j) (p j)

@[simp] theorem xorReindex_apply (t : BitString n) (p : PauliString n)
    (j : Fin n) : xorReindex t p j = p j := by
  simp [xorReindex]

@[simp] theorem xorReindex_eq (t : BitString n) (p : PauliString n) :
    xorReindex t p = p := by
  funext j
  simp

@[simp] theorem support_xorReindex (t : BitString n) (p : PauliString n) :
    (xorReindex t p).support = p.support := by
  ext j
  simp [support]

/-- Bit-flip conjugation preserves Pauli weight. -/
@[simp] theorem weight_xorReindex (t : BitString n) (p : PauliString n) :
    (xorReindex t p).weight = p.weight := by
  simp [weight]

@[simp] theorem xorPhase_ne_zero (t : BitString n) (p : PauliString n) :
    xorPhase t p ≠ 0 := by
  unfold xorPhase
  exact Finset.prod_ne_zero_iff.mpr
    (by intro j _; exact PauliLetter.xorConjugationSign_ne_zero _ _)

/-- Reindexing the computational basis by XOR conjugates a Pauli operator.
The phase-free Pauli string is unchanged, while `xorPhase` records the global
sign. -/
theorem operator_xorReindex (t : BitString n) (p : PauliString n) :
    reindexOperator (xorEquiv t) p.operator =
      xorPhase t p • (xorReindex t p).operator := by
  ext x y
  change (∏ j, (p j).entry (x j ^^ t j) (y j ^^ t j)) =
    (∏ j, PauliLetter.xorConjugationSign (t j) (p j)) *
      ∏ j, (PauliLetter.xorConjugate (t j) (p j)).entry (x j) (y j)
  simp_rw [PauliLetter.entry_xor_conjugate]
  exact Finset.prod_mul_distrib

/-- Relabel the tensor factors of a Pauli string by a coordinate
permutation. -/
def coordinateReindex (sigma : Equiv.Perm (Fin n))
    (p : PauliString n) : PauliString n :=
  fun j => p (sigma.symm j)

@[simp] theorem coordinateReindex_apply (sigma : Equiv.Perm (Fin n))
    (p : PauliString n) (j : Fin n) :
    coordinateReindex sigma p j = p (sigma.symm j) := rfl

@[simp] theorem coordinateReindex_symm (sigma : Equiv.Perm (Fin n))
    (p : PauliString n) :
    coordinateReindex sigma (coordinateReindex sigma.symm p) = p := by
  funext j
  simp

@[simp] theorem support_coordinateReindex (sigma : Equiv.Perm (Fin n))
    (p : PauliString n) :
    (coordinateReindex sigma p).support = p.support.map sigma.toEmbedding := by
  ext j
  simp [support, coordinateReindex]

/-- A coordinate permutation preserves Pauli weight. -/
@[simp] theorem weight_coordinateReindex (sigma : Equiv.Perm (Fin n))
    (p : PauliString n) :
    (coordinateReindex sigma p).weight = p.weight := by
  simp [weight]

/-- Reindexing the computational basis by a coordinate permutation gives the
operator of the correspondingly reindexed Pauli string. -/
theorem operator_coordinateReindex (sigma : Equiv.Perm (Fin n))
    (p : PauliString n) :
    reindexOperator (coordinateEquiv sigma) p.operator =
      (coordinateReindex sigma p).operator := by
  ext x y
  change (∏ j, (p j).entry (x (sigma j)) (y (sigma j))) =
    ∏ j, (p (sigma.symm j)).entry (x j) (y j)
  exact Fintype.prod_equiv sigma _ _ (by intro j; simp)

end PauliString

namespace CodeProjector

variable {n K d : ℕ}

/-- Detection is transported by any permutation of the computational basis. -/
theorem detects_reindexOperator (C : CodeProjector n K)
    (e : BitString n ≃ BitString n) (E : Operator n) (h : C.Detects E) :
    (C.reindex e).Detects (reindexOperator e E) := by
  rcases h with ⟨lam, hlam⟩
  refine ⟨lam, ?_⟩
  let R := Matrix.reindexAlgEquiv ℂ ℂ e
  change R C.proj * R E * R C.proj = lam • R C.proj
  calc
    R C.proj * R E * R C.proj = R (C.proj * E * C.proj) := by simp [R]
    _ = R (lam • C.proj) := by rw [hlam]
    _ = lam • R C.proj := by simp

/-- A nonzero scalar multiple is detected only if the original operator is
detected. -/
theorem detects_of_smul (C : CodeProjector n K) (E : Operator n) (a : ℂ)
    (ha : a ≠ 0) (h : C.Detects (a • E)) : C.Detects E := by
  rcases h with ⟨lam, hlam⟩
  refine ⟨a⁻¹ * lam, ?_⟩
  have hh := congrArg (fun A : Operator n => a⁻¹ • A) hlam
  simpa [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ha, mul_assoc] using hh

/-- Code distance is preserved by conjugating the code with any tensor product
of computational-basis bit flips. -/
theorem hasDistanceAtLeast_reindex_xor (C : CodeProjector n K)
    (hC : C.HasDistanceAtLeast d) (t : BitString n) :
    (C.reindex (xorEquiv t)).HasDistanceAtLeast d := by
  intro p hp
  have hdet := C.detects_reindexOperator (xorEquiv t) p.operator (hC p hp)
  rw [PauliString.operator_xorReindex] at hdet
  have hdet' := (C.reindex (xorEquiv t)).detects_of_smul
    (PauliString.xorReindex t p).operator (PauliString.xorPhase t p)
    (PauliString.xorPhase_ne_zero t p) hdet
  simpa using hdet'

/-- Code distance is preserved by permuting the qubit coordinates. -/
theorem hasDistanceAtLeast_reindex_coordinate (C : CodeProjector n K)
    (hC : C.HasDistanceAtLeast d) (sigma : Equiv.Perm (Fin n)) :
    (C.reindex (coordinateEquiv sigma)).HasDistanceAtLeast d := by
  intro p hp
  let pOld := PauliString.coordinateReindex sigma.symm p
  have hpOld : pOld.weight < d := by
    simpa [pOld] using hp
  have hdet := C.detects_reindexOperator (coordinateEquiv sigma)
    pOld.operator (hC pOld hpOld)
  rw [PauliString.operator_coordinateReindex] at hdet
  simpa [pOld] using hdet

end CodeProjector

end

end QECC
