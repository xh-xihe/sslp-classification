import MainTheory.FinitePipeline
import MainTheory.IntegerMatrixRankCertificate

/-! The actual two normalization rows and 21 degree-two Boolean moment rows. -/

namespace MainTheory.FiniteMomentMatrix

open scoped Matrix BigOperators

abbrev LabeledWord := Bool × MainTheory.FinitePipeline.Word6

def bitZ (x : MainTheory.FinitePipeline.Word6) (i : Fin 6) : ℤ :=
  if x.val.testBit i.val then 1 else 0

def featureZ (x : MainTheory.FinitePipeline.Word6) : Fin 21 → ℤ :=
  let b := bitZ x
  ![b 0, b 1, b 2, b 3, b 4, b 5,
    b 0 * b 1, b 0 * b 2, b 0 * b 3, b 0 * b 4, b 0 * b 5,
    b 1 * b 2, b 1 * b 3, b 1 * b 4, b 1 * b 5,
    b 2 * b 3, b 2 * b 4, b 2 * b 5,
    b 3 * b 4, b 3 * b 5, b 4 * b 5]

theorem featureZ_eq_feature (x : MainTheory.FinitePipeline.Word6) (i : Fin 21) :
    (featureZ x i : ℚ) = MainTheory.FinitePipeline.feature x i := by
  have hb (j : Fin 6) : (bitZ x j : ℚ) = MainTheory.FinitePipeline.bit x j := by
    cases h : x.val.testBit j.val <;> simp [bitZ, MainTheory.FinitePipeline.bit, h]
  fin_cases i <;> norm_num [featureZ, MainTheory.FinitePipeline.feature, hb]

def entryZ (r : Fin 23) (c : LabeledWord) : ℤ :=
  Fin.append ![if c.1 then 0 else 1, if c.1 then 1 else 0]
    (fun i => (if c.1 then -1 else 1) * featureZ c.2 i) r

def matrixZ {ι : Type*} (columns : ι → LabeledWord) : Matrix (Fin 23) ι ℤ :=
  fun r j => entryZ r (columns j)

noncomputable def matrix {ι : Type*} (columns : ι → LabeledWord) : Matrix (Fin 23) ι ℝ :=
  (matrixZ columns).map (Int.castRingHom ℝ)

def rhsQ : Fin 23 → ℚ := Fin.append (![1, 1] : Fin 2 → ℚ) (fun _ : Fin 21 => 0)

noncomputable def rhs : Fin 23 → ℝ := fun r => (rhsQ r : ℝ)

theorem entryZ_norm_zero (c : LabeledWord) : entryZ 0 c = if c.1 then 0 else 1 := rfl

theorem entryZ_norm_one (c : LabeledWord) : entryZ 1 c = if c.1 then 1 else 0 := rfl

theorem entryZ_moment (c : LabeledWord) (i : Fin 21) :
    entryZ (Fin.natAdd 2 i) c = (if c.1 then -1 else 1) * featureZ c.2 i := by
  exact Fin.append_right _ _ _

end MainTheory.FiniteMomentMatrix
