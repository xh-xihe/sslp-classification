import MainTheory.Orbit8RotationSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.AncillaCompression

def insertOne (r : Fin 6) (x : SS.BitString 5) : SS.BitString 6 :=
  Fin.insertNth r true x

theorem insert_injective (r : Fin 6) : Function.Injective (insertOne r) :=
  Fin.insertNth_right_injective (α := fun _ : Fin 6 => Bool) true

noncomputable def inclusion (r : Fin 6) : Matrix (SS.BitString 6) (SS.BitString 5) ℂ :=
  fun x y => if x=insertOne r y then 1 else 0

noncomputable def compress (r : Fin 6) (M : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) :
    Matrix (SS.BitString 5) (SS.BitString 5) ℂ := fun x y => M (insertOne r x) (insertOne r y)

theorem inclusion_isometry (r : Fin 6) : (inclusion r).conjTranspose*inclusion r=1 := by
  classical
  ext x y
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,inclusion,
    (insert_injective r).eq_iff,Matrix.one_apply,eq_comm]

theorem compression_matrix (r : Fin 6) (M : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) :
    compress r M=(inclusion r).conjTranspose*M*inclusion r := by
  classical
  ext x y
  simp [compress,Matrix.mul_apply,Matrix.conjTranspose_apply,inclusion,mul_ite,ite_mul]

noncomputable def F (C S : ℝ) (E : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) :=
  compress 4 ((MainTheory.Orbit8RotationSemantics.physicalRotation C S).conjTranspose*
    E*MainTheory.Orbit8RotationSemantics.physicalRotation C S)

theorem physical_formula (C S : ℝ) (E : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) :
    F C S E=(inclusion 4).conjTranspose*
      (MainTheory.Orbit8RotationSemantics.physicalRotation C S).conjTranspose*E*
      MainTheory.Orbit8RotationSemantics.physicalRotation C S*inclusion 4 := by
  rw [F,compression_matrix]
  simp only [Matrix.mul_assoc]

theorem entries (C S : ℝ) (E : Matrix (SS.BitString 6) (SS.BitString 6) ℂ)
    (x y : SS.BitString 5) :
    F C S E x y=((MainTheory.Orbit8RotationSemantics.physicalRotation C S).conjTranspose*
      E*MainTheory.Orbit8RotationSemantics.physicalRotation C S) (insertOne 4 x) (insertOne 4 y) := rfl

end MainTheory.AncillaCompression
