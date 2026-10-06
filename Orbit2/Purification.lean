import Orbit2.Encoder

namespace Orbit2
open scoped BigOperators
open SS.MacWilliams

def referenceSplit : SS.BitString 7 ≃ Bool × SS.BitString 6 where
  toFun x := (x 0,fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by rcases x with ⟨b,t⟩; rfl

/-- Unnormalized purification, whose squared norm is two. Keeping this
normalization avoids inserting square-root coefficients into the identities. -/
def Encoder.purification (V : Encoder) : SS.State 7 ℂ := fun x =>
  V.psi (if x 0 then 1 else 0) (fun i => x i.succ)

theorem Encoder.purification_norm (V : Encoder) :
    SS.innerC V.purification V.purification = 2 := by
  have he := referenceSplit.symm.sum_comp
    (fun x => star (V.purification x) * V.purification x)
  change (∑ x, star (V.purification x) * V.purification x) = 2
  rw [← he]
  simp only [Fintype.sum_prod_type]
  change (∑ b : Bool, SS.innerC (V.psi (if b then 1 else 0))
    (V.psi (if b then 1 else 0))) = 2
  simp [V.orthonormal]

noncomputable def Encoder.purificationMass (V : Encoder) (p : SS.PauliString 7) : ℝ :=
  Complex.normSq (SS.innerC V.purification (SS.pauliAct p V.purification))/4

theorem Encoder.purificationMass_nonneg (V : Encoder) (p : SS.PauliString 7) :
    0 ≤ V.purificationMass p := div_nonneg (Complex.normSq_nonneg _) (by norm_num)

theorem Encoder.purificationMass_identity (V : Encoder) :
    V.purificationMass (identityPauli 7) = 1 := by
  unfold Encoder.purificationMass
  rw [pauliAct_identity,V.purification_norm]
  norm_num

/-- Complementary purity for the actual purified encoder, derived from the
proved subset Pauli Parseval identity, without a purity axiom. -/
theorem Encoder.complementary_purity (V : Encoder) (S : Finset (Fin 7)) :
    128 * (∑ p ∈ Finset.univ.filter (fun p : SS.PauliString 7 => supp p ⊆ S),
      V.purificationMass p) =
    (4 : ℝ)^S.card * (∑ p ∈ Finset.univ.filter (fun p : SS.PauliString 7 =>
      ∀ i ∈ S, p.x i = false ∧ p.z i = false), V.purificationMass p) := by
  have hd := subset_duality (fun _ : Fin 1 => V.purification) S
  have h1 (p : SS.PauliString 7) :
      frob (fun _ : Fin 1 => V.purification) p =
        Complex.normSq (SS.innerC V.purification (SS.pauliAct p V.purification)) := by
    simp [frob]
  have h2 (p : SS.PauliString 7) :
      trProj (fun _ : Fin 1 => V.purification) p =
        SS.innerC V.purification (SS.pauliAct p V.purification) := by simp [trProj]
  simp_rw [h1,h2] at hd
  norm_num at hd
  unfold Encoder.purificationMass
  simp only [← Finset.sum_div]
  linear_combination hd / 4

end Orbit2
