import MainTheory.Orbit6LineCompletion
set_option autoImplicit false
namespace MainTheory.RankOneSpinorFrame
open scoped Matrix BigOperators
open MainTheory.Orbit6SpinorDisplays MainTheory.Orbit6LineCompletion
noncomputable section

def outer (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.vecMulVec v (star v)
def perp (u : Fin 2 → ℂ) : Fin 2 → ℂ := ![-star (u 1),star (u 0)]

theorem pairing_perp (u v : Fin 2 → ℂ) : pairing (perp u) v=wedge u v := by
  simp only [pairing,perp,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,star_neg,star_star,wedge]
  ring

theorem contraction_outer (w v : Fin 2 → ℂ) :
    pairing w ((outer v).mulVec w)=(Complex.normSq (pairing v w) : ℂ) := by
  simp only [pairing,outer,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    Matrix.vecMulVec_apply,Pi.star_apply,Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.star_def,star_add,star_mul',star_star]
  ring

theorem contraction_sum {α : Type*} [Fintype α] (w : Fin 2 → ℂ) (b : α → Fin 2 → ℂ) :
    pairing w ((∑ i,outer (b i)).mulVec w)=
      ∑ i,(Complex.normSq (pairing (b i) w) : ℂ) := by
  simp only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.sum_apply]
  simp only [Finset.sum_mul]
  simp only [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using contraction_outer w (b i)

theorem frame_wedges_zero {α : Type*} [Fintype α]
    (u v : Fin 2 → ℂ) (b : α → Fin 2 → ℂ)
    (hframe : outer u+outer v=∑ i,outer (b i)) (hw : wedge u v=0) :
    ∀ i,wedge u (b i)=0 := by
  have hq := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
    pairing (perp u) (M.mulVec (perp u))) hframe
  dsimp only at hq
  have hu : pairing u (perp u)=0 := by
    rw [← pairing_conjugate,pairing_perp]
    simp only [wedge,mul_comm,sub_self,star_zero]
  have hv : pairing v (perp u)=0 := by
    rw [← pairing_conjugate,pairing_perp,hw,star_zero]
  have hleft : pairing (perp u) ((outer u+outer v).mulVec (perp u))=0 := by
    simp only [pairing,Matrix.add_mulVec,Pi.add_apply,mul_add]
    rw [add_add_add_comm]
    change pairing (perp u) ((outer u).mulVec (perp u))+
      pairing (perp u) ((outer v).mulVec (perp u))=0
    rw [contraction_outer,contraction_outer,hu,hv,Complex.normSq_zero]
    norm_num
  rw [hleft,contraction_sum] at hq
  have hs : (∑ i,Complex.normSq (pairing (b i) (perp u)))=0 := by
    exact_mod_cast hq.symm
  have hz (i : α) : Complex.normSq (pairing (b i) (perp u))=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp hs i (Finset.mem_univ _)
  intro i
  have hh := Complex.normSq_eq_zero.mp (hz i)
  rw [← pairing_perp,← pairing_conjugate,hh,star_zero]

end
end MainTheory.RankOneSpinorFrame
