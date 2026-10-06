import MainTheory.Orbit30GraphClassification
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit30GraphMaskEncoding
open MainTheory.Orbit30GraphClassification
def packed (p : Fin 10 → Bool) : BitVec 10 :=
  BitVec.cons (p ⟨9,by decide⟩) (BitVec.cons (p ⟨8,by decide⟩)
    (BitVec.cons (p ⟨7,by decide⟩) (BitVec.cons (p ⟨6,by decide⟩)
      (BitVec.cons (p ⟨5,by decide⟩) (BitVec.cons (p ⟨4,by decide⟩)
        (BitVec.cons (p ⟨3,by decide⟩) (BitVec.cons (p ⟨2,by decide⟩)
          (BitVec.cons (p ⟨1,by decide⟩) (BitVec.cons (p ⟨0,by decide⟩) (0#0))))))))))
def encoded (p : Fin 10 → Bool) : Fin 1024 := (packed p).toFin
theorem decoded (p : Fin 10 → Bool) (e : Fin 10) : pattern (encoded p) e=p e := by
  change (packed p).toNat.testBit e.val=p e
  rw [← BitVec.getElem_eq_testBit_toNat (packed p) e.val e.isLt]
  fin_cases e <;> simp [packed,BitVec.getElem_cons]
theorem every_pattern (p : Fin 10 → Bool) : ∃ m : Fin 1024,pattern m=p :=
  ⟨encoded p,funext (decoded p)⟩
end MainTheory.Orbit30GraphMaskEncoding
