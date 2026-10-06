import MainTheory.FlipCharacterObstruction

set_option autoImplicit false

namespace MainTheory.FlipLinearCombination

open MainTheory.FlipCharacter

theorem equation {n k l : ℕ} (S0 S1 : Finset (SS.BitString n)) (c d : SS.State n ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (e : SS.BitString n)
    (ys : Fin k → SS.BitString n) (zs : Fin l → SS.BitString n)
    (hy : Function.Injective ys) (hI : Finset.univ.image ys=incidenceSet S0 S1 e)
    (hw : ∀ i,(⟨e,zs i⟩ : SS.PauliString n).wt ≤ 2)
    (coeff : Fin l → ℂ) (target : Fin k → ℂ)
    (hcert : ∀ j,∑ i,coeff i*character (zs i) (ys j)=target j) :
    ∑ j,target j*incidenceMonomial c d e (ys j)=0 := by
  have hrows : ∀ i,∑ j,character (zs i) (ys j)*incidenceMonomial c d e (ys j)=0 := by
    intro i
    have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl e (zs i) (hw i)
    rwa [offSum_eq_indexed S0 S1 c d e (zs i) ys hy hI] at h
  calc
    _=∑ j,(∑ i,coeff i*character (zs i) (ys j))*incidenceMonomial c d e (ys j) := by simp_rw [hcert]
    _=∑ i,coeff i*(∑ j,character (zs i) (ys j)*incidenceMonomial c d e (ys j)) := by
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
      exact Finset.sum_comm
    _=0 := by simp only [hrows,mul_zero,Finset.sum_const_zero]

end MainTheory.FlipLinearCombination
