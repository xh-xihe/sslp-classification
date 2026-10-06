import MainTheory.FlipCharacterObstruction
set_option autoImplicit false
namespace MainTheory.DiagonalLinearCombination
open MainTheory.FlipCharacter

theorem equation {n k l m : ℕ} (S0 S1 : Finset (SS.BitString n)) (c d : SS.State n ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (e : SS.BitString n)
    (xs : Fin k → SS.BitString n) (ys : Fin l → SS.BitString n) (zs : Fin m → SS.BitString n)
    (hx : Function.Injective xs) (hy : Function.Injective ys)
    (hX : Finset.univ.image xs=incidenceSet S0 S0 e)
    (hY : Finset.univ.image ys=incidenceSet S1 S1 e)
    (hw : ∀ i,(⟨e,zs i⟩ : SS.PauliString n).wt ≤ 2)
    (coeff : Fin m → ℂ) (tx : Fin k → ℂ) (ty : Fin l → ℂ)
    (hcx : ∀ j,∑ i,coeff i*character (zs i) (xs j)=tx j)
    (hcy : ∀ j,∑ i,coeff i*character (zs i) (ys j)=ty j) :
    ∑ j,tx j*incidenceMonomial c c e (xs j)=
      ∑ j,ty j*incidenceMonomial d d e (ys j) := by
  have rows : ∀ i,∑ j,character (zs i) (xs j)*incidenceMonomial c c e (xs j)=
      ∑ j,character (zs i) (ys j)*incidenceMonomial d d e (ys j) := by
    intro i
    have h := SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl e (zs i) (hw i)
    change SixQubit.offSumOn S0 S0 c c e (zs i)=SixQubit.offSumOn S1 S1 d d e (zs i) at h
    rwa [offSum_eq_indexed S0 S0 c c e (zs i) xs hx hX,
      offSum_eq_indexed S1 S1 d d e (zs i) ys hy hY] at h
  calc
    _=∑ i,coeff i*(∑ j,character (zs i) (xs j)*incidenceMonomial c c e (xs j)) := by
      simp_rw [← hcx]
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
      exact Finset.sum_comm
    _=∑ i,coeff i*(∑ j,character (zs i) (ys j)*incidenceMonomial d d e (ys j)) := by simp_rw [rows]
    _=_ := by
      simp_rw [← hcy]
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
      exact Finset.sum_comm
end MainTheory.DiagonalLinearCombination
