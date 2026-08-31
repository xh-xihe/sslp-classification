import MainTheory.BinaryDetSmallCircuit
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Sorted-prefix endpoint for the size-four and size-five beta bounds

Permuting the rows of a matrix preserves the absolute determinant.  Thus the
finite arithmetic tables for an `(n+1) × (n+1)` matrix need only contain the
weakly increasing `n`-tuples of row codes before the last-row reduction.  For
the two required sizes this is `choose(18,3)=816` and `choose(35,4)=52360`
closed prefixes, rather than `16^3` and `32^4` ordered prefixes.
-/

namespace MainTheory.BinaryBetaSmallSemantic

open MainTheory.BinaryBeta
open MainTheory.BinaryDetLastRow

/-- Matrix made from `n` encoded rows followed by one zero row. -/
def prefixRowsMatrix {n : ℕ} (f : Fin n → BitVec (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  intMatrixOfRowBits (Fin.lastCases 0 f)

/-- Extend a permutation of the prefix rows while fixing the last row. -/
def extendPrefixPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  σ.viaFintypeEmbedding Fin.castSuccEmb

@[simp] theorem extendPrefixPerm_castSucc {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPrefixPerm σ i.castSucc = (σ i).castSucc := by
  simpa [extendPrefixPerm] using
    (Equiv.Perm.viaFintypeEmbedding_apply_image σ Fin.castSuccEmb i)

@[simp] theorem extendPrefixPerm_last {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    extendPrefixPerm σ (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  simp

/-- The exact finite-table interface: every monotone prefix-code tuple has a
checked cofactor envelope. -/
def MonotonePrefixCertificate (n B : ℕ) : Prop :=
  ∀ f : Fin n → BitVec (n + 1), Monotone (fun i ↦ (f i).toNat) →
    ReducedAtRow (prefixRowsMatrix f) (Fin.last n) B

private theorem permutedUpdatedMatrix_eq_submatrix
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Bool)
    (f : Fin n → BitVec (n + 1))
    (σ : Equiv.Perm (Fin n))
    (hf : ∀ i : Fin n, f i = BitVec.ofFnLE (A i.castSucc)) :
    (prefixRowsMatrix (f ∘ σ)).updateRow (Fin.last n)
        (fun j ↦ bitZ (A (Fin.last n) j)) =
      (intMatrixOfBool A).submatrix (extendPrefixPerm σ) id := by
  ext i j
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simp [prefixRowsMatrix, intMatrixOfBool, Matrix.updateRow]
  · simp [prefixRowsMatrix, intMatrixOfRowBits, rowOfBits,
      intMatrixOfBool, Matrix.updateRow, hf (σ k)]

private theorem natAbs_det_extendPrefixPerm
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (σ : Equiv.Perm (Fin n)) :
    (M.submatrix (extendPrefixPerm σ) id).det.natAbs = M.det.natAbs := by
  have habs :
      |(M.submatrix (extendPrefixPerm σ) id).det| = |M.det| := by
    simpa using Matrix.abs_det_submatrix_equiv_equiv
      (extendPrefixPerm σ) (Equiv.refl _) M
  have hcast :
      ((M.submatrix (extendPrefixPerm σ) id).det.natAbs : ℤ) =
        (M.det.natAbs : ℤ) := by
    simpa only [Int.abs_eq_natAbs] using habs
  exact Int.ofNat_inj.mp hcast

/-- Sorted-prefix arithmetic implies the semantic beta upper bound at size
`n+1` and, through identity padding, at every smaller positive size. -/
theorem betaBound_of_monotonePrefixCertificate {n B : ℕ}
    (h : MonotonePrefixCertificate n B) : BetaBound (n + 1) B := by
  apply betaBound_of_bool_detNatAbs_bound
  intro A
  let f : Fin n → BitVec (n + 1) :=
    fun i ↦ BitVec.ofFnLE (A i.castSucc)
  let code : Fin n → Nat := fun i ↦ (f i).toNat
  let σ : Equiv.Perm (Fin n) := Tuple.sort code
  have hmono : Monotone (fun i ↦ ((f ∘ σ) i).toNat) := by
    change Monotone (code ∘ σ)
    exact Tuple.monotone_sort code
  have hdet := (h (f ∘ σ) hmono).detNatAbs_updateRow
    (fun j ↦ A (Fin.last n) j)
  have hf : ∀ i : Fin n, f i = BitVec.ofFnLE (A i.castSucc) := by
    intro i
    rfl
  rw [permutedUpdatedMatrix_eq_submatrix A f σ hf] at hdet
  rw [natAbs_det_extendPrefixPerm] at hdet
  exact hdet

end MainTheory.BinaryBetaSmallSemantic
