import MainTheory.SignMatrixCertificate

namespace MainTheory.SignRowEnumeration

def row {N : ℕ} (mask : Fin (2^N)) (j : Fin N) : ℤ :=
  if mask.val.testBit j.val then -1 else 1

theorem exists_bits {N : ℕ} (f : Fin N → Bool) :
    ∃ x : BitVec N, ∀ i : Fin N, x.getLsbD i.val = f i := by
  induction N with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih (fun i => f i.castSucc)
    refine ⟨BitVec.cons (f (Fin.last n)) x, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.val_last, BitVec.getLsbD_cons, ↓reduceIte]
    · rw [BitVec.getLsbD_cons, if_neg (by simpa using Nat.ne_of_lt i.isLt)]
      exact hx i

theorem row_surjective {N : ℕ} (v : Fin N → ℤ)
    (hv : ∀ j, v j = 1 ∨ v j = -1) : ∃ mask : Fin (2^N), row mask = v := by
  obtain ⟨x, hx⟩ := exists_bits (fun j => decide (v j = -1))
  refine ⟨x.toFin, funext (fun j => ?_)⟩
  have he : x.toFin.val.testBit j.val = decide (v j = -1) := hx j
  dsimp only [row]
  rw [he]
  rcases hv j with h | h <;> simp [h]

theorem row_isSign {N : ℕ} (mask : Fin (2^N)) (j : Fin N) :
    row mask j = 1 ∨ row mask j = -1 := by
  dsimp only [row]
  split <;> simp

end MainTheory.SignRowEnumeration
