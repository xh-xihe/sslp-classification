import MainTheory.SmithGcdPair

namespace MainTheory.SmithExistence

open Matrix

noncomputable section

variable {s t : Type*} [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]

theorem IntegralEquivalent.reindex {C D : Matrix s s ℤ}
    (h : IntegralEquivalent C D) (e : s ≃ t) :
    IntegralEquivalent (Matrix.reindex e e C) (Matrix.reindex e e D) := by
  obtain ⟨U, V, h⟩ := h
  let f := Matrix.reindexAlgEquiv ℤ ℤ e
  refine ⟨Units.map f.toMonoidHom U, Units.map f.toMonoidHom V, ?_⟩
  simpa [f, map_mul] using congrArg f h

def blockUnit (U : (Matrix s s ℤ)ˣ) : (Matrix (s ⊕ t) (s ⊕ t) ℤ)ˣ where
  val := Matrix.fromBlocks (U : Matrix s s ℤ) 0 0 1
  inv := Matrix.fromBlocks (↑(U⁻¹) : Matrix s s ℤ) 0 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

theorem IntegralEquivalent.block {C D : Matrix s s ℤ}
    (h : IntegralEquivalent C D) (B : Matrix t t ℤ) :
    IntegralEquivalent (Matrix.fromBlocks C 0 0 B) (Matrix.fromBlocks D 0 0 B) := by
  obtain ⟨U, V, h⟩ := h
  refine ⟨blockUnit U, blockUnit V, ?_⟩
  change Matrix.fromBlocks (↑U) 0 0 1 * Matrix.fromBlocks C 0 0 B *
    Matrix.fromBlocks (↑V) 0 0 1 = _
  simp [Matrix.fromBlocks_multiply, h]

def pairEquiv (i j : s) (hij : i ≠ j) :
    (Fin 2 ⊕ {k : s // k ≠ i ∧ k ≠ j}) ≃ s where
  toFun := Sum.elim (fun k => if k = 0 then i else j) Subtype.val
  invFun k := if hi : k = i then Sum.inl 0 else
    if hj : k = j then Sum.inl 1 else Sum.inr ⟨k, hi, hj⟩
  left_inv := by
    intro k
    rcases k with k | k
    · fin_cases k <;> simp [Ne.symm hij]
    · simp [k.property.1, k.property.2]
  right_inv := by
    intro k
    dsimp only
    split_ifs with hi hj
    · simpa using hi.symm
    · simpa using hj.symm
    · rfl

omit [Fintype s] in
theorem pair_diagonal (d : s → ℤ) (i j : s) (hij : i ≠ j) :
    Matrix.reindex (pairEquiv i j hij).symm (pairEquiv i j hij).symm (Matrix.diagonal d) =
      Matrix.fromBlocks (Matrix.diagonal ![d i, d j]) 0 0
        (Matrix.diagonal (fun k : {k : s // k ≠ i ∧ k ≠ j} => d k.val)) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q
  · fin_cases p <;> fin_cases q <;>
      simp [Matrix.reindex, Matrix.submatrix, Matrix.diagonal_apply, pairEquiv, hij, Ne.symm hij]
  · fin_cases p <;>
      simp [Matrix.reindex, Matrix.submatrix, Matrix.diagonal_apply, pairEquiv,
        Ne.symm q.property.1, Ne.symm q.property.2]
  · fin_cases q <;>
      simp [Matrix.reindex, Matrix.submatrix, Matrix.diagonal_apply, pairEquiv,
        p.property.1, p.property.2]
  · simp [Matrix.reindex, Matrix.submatrix, Matrix.diagonal_apply, pairEquiv,
      Subtype.ext_iff]

def gcdUpdate (d : s → ℕ) (i j : s) : s → ℕ :=
  Function.update (Function.update d i (Nat.gcd (d i) (d j))) j (Nat.lcm (d i) (d j))

theorem diagonal_gcd_update (d : s → ℕ) (hd : ∀ k, 0 < d k)
    (i j : s) (hij : i ≠ j) :
    IntegralEquivalent (Matrix.diagonal (fun k => (d k : ℤ)))
      (Matrix.diagonal (fun k => (gcdUpdate d i j k : ℤ))) := by
  let e := pairEquiv i j hij
  let B : Matrix {k : s // k ≠ i ∧ k ≠ j} {k : s // k ≠ i ∧ k ≠ j} ℤ :=
    Matrix.diagonal (fun k => (d k.val : ℤ))
  have h := (diagonal_gcd_pair (d i) (d j) (hd i)).block B
  have hrest : (fun k : {k : s // k ≠ i ∧ k ≠ j} => (gcdUpdate d i j k.val : ℤ)) =
      (fun k => (d k.val : ℤ)) := by
    funext k
    simp [gcdUpdate, k.property.1, k.property.2]
  have hblock : IntegralEquivalent
      (Matrix.reindex e.symm e.symm (Matrix.diagonal (fun k => (d k : ℤ))))
      (Matrix.reindex e.symm e.symm (Matrix.diagonal (fun k => (gcdUpdate d i j k : ℤ)))) := by
    change IntegralEquivalent
      (Matrix.reindex (pairEquiv i j hij).symm (pairEquiv i j hij).symm _)
      (Matrix.reindex (pairEquiv i j hij).symm (pairEquiv i j hij).symm _)
    rw [pair_diagonal, pair_diagonal, hrest]
    simpa only [gcdUpdate, Function.update_self, Function.update_of_ne hij] using h
  have hfinal := hblock.reindex e
  simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using hfinal

end

end MainTheory.SmithExistence
