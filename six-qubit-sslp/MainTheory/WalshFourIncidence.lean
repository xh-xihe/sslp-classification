import MainTheory.OrderSevenWalshMatrix
import MainTheory.FlipCharacterObstruction

set_option autoImplicit false

namespace MainTheory.WalshFourIncidence

open MainTheory.OrderSevenWalshMatrix MainTheory.FlipCharacter

theorem matrix_equation {n : ℕ} (S0 S1 : Finset (SS.BitString n)) (c d : SS.State n ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (e : SS.BitString n)
    (ys : Fin 4 → SS.BitString n) (zs : Fin 3 → SS.BitString n)
    (hy : Function.Injective ys) (hI : Finset.univ.image ys=incidenceSet S0 S1 e)
    (hw : ∀ i,(⟨e,zs i⟩ : SS.PauliString n).wt ≤ 2)
    (signs : Fin 3 → ℂ) (hn : ∀ i,signs i ≠ 0)
    (hchar : ∀ i j,character (zs i) (ys j)=signs i*W i j) :
    W.mulVec (fun j => incidenceMonomial c d e (ys j))=0 := by
  ext i
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl e (zs i) (hw i)
  rw [offSum_eq_indexed S0 S1 c d e (zs i) ys hy hI] at h
  simp_rw [hchar] at h
  have he : signs i*(W.mulVec (fun j => incidenceMonomial c d e (ys j))) i=0 := by
    simpa only [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc] using h
  exact (mul_eq_zero.mp he).resolve_left (hn i)

end MainTheory.WalshFourIncidence
