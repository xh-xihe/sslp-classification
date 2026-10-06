import MainTheory.FlipCharacterObstruction

/-! Physical cross-KL rows with independently sized incidence and character
sets. This retains every incidence and never requires an active amplitude. -/
set_option autoImplicit false
namespace MainTheory.RectangularFlipCharacters
open scoped BigOperators Matrix
noncomputable section
variable {n N M : ℕ}
def matrix (characters : Fin M → SS.BitString n) (sources : Fin N → SS.BitString n) :
    Matrix (Fin M) (Fin N) ℂ := fun i j => MainTheory.FlipCharacter.character (characters i) (sources j)
theorem physical_rows (S0 S1 : Finset (SS.BitString n)) (c d : SS.State n ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3)
    (flip : SS.BitString n) (characters : Fin M → SS.BitString n) (sources : Fin N → SS.BitString n)
    (hinj : Function.Injective sources)
    (hinc : Finset.univ.image sources=S1.filter (fun x => SS.bxor x flip ∈ S0))
    (hwt : ∀ i, (⟨flip,characters i⟩ : SS.PauliString n).wt ≤ 2) :
    matrix characters sources *ᵥ (fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (sources j))=0 := by
  ext i
  have he := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl flip (characters i) (hwt i)
  rw [MainTheory.FlipCharacter.offSum_eq_indexed S0 S1 c d flip (characters i) sources hinj hinc] at he
  exact he
end
end MainTheory.RectangularFlipCharacters
