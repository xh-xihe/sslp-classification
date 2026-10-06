import MainTheory.FullRankFlipObstruction

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.TwoEdgeWalshDisplays

open MainTheory.FlipCharacter

variable {n : ℕ}

theorem equations (S0 S1 : Finset (SS.BitString n)) (c d : SS.State n ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin n) (y y' : SS.BitString n)
    (hi : incidenceSet S0 S1 (SS.stdBasis i)={y,y'}) (hj : y j ≠ y' j) :
    (star (c (SS.bxor y (SS.stdBasis i)))*d y)+
      (star (c (SS.bxor y' (SS.stdBasis i)))*d y')=0 ∧
    (star (c (SS.bxor y (SS.stdBasis i)))*d y)-
      (star (c (SS.bxor y' (SS.stdBasis i)))*d y')=0 := by
  classical
  let ys : Fin 2 → SS.BitString n := ![y,y']
  let zs : Fin 2 → SS.BitString n := ![fun _ => false,SS.stdBasis j]
  have hy : Function.Injective ys := by
    intro a b hab
    have hne : y ≠ y' := fun h => hj (congrFun h j)
    fin_cases a <;> fin_cases b <;> simp_all [ys]
  have hI : Finset.univ.image ys=incidenceSet S0 S1 (SS.stdBasis i) := by
    rw [hi,show (Finset.univ : Finset (Fin 2))={0,1} from by decide]
    simp [ys]
  have hw : ∀ a,(⟨SS.stdBasis i,zs a⟩ : SS.PauliString n).wt ≤ 2 := by
    intro a
    fin_cases a
    · exact wt_single_flip_zero_dressing i
    · exact wt_single_flip_single_dressing i j
  have h := restricted_matrix_times_monomials S0 S1 c d hc hd hkl
    (SS.stdBasis i) zs ys hy hI hw
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [restrictedCharacterMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    ys,zs,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    character_zero,character_single,incidenceMonomial,Pi.zero_apply,one_mul] at h0 h1
  constructor
  · exact h0
  · cases hb : y j <;> cases hb' : y' j <;> simp_all [sub_eq_add_neg]
    linear_combination -h1

def matrix : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;1,-1]

theorem matrix_equation (A B : ℂ) : matrix.mulVec ![A,B]=0 ↔ A+B=0 ∧ A-B=0 := by
  simp [matrix,funext_iff,Fin.forall_fin_two,sub_eq_add_neg]

theorem determinant : matrix.det= -2 := by norm_num [matrix,Matrix.det_fin_two]

end MainTheory.TwoEdgeWalshDisplays
