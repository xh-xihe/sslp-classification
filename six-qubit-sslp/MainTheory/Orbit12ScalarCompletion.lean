import MainTheory.Orbit12EdgeLines
import MainTheory.Orbit12AnchorScalars
set_option autoImplicit false
namespace MainTheory.Orbit12ScalarCompletion
open scoped Matrix BigOperators
open SixQubit.Orbit12 MainTheory.Orbit12Frames MainTheory.Orbit12MomentDisplays
open MainTheory.Orbit12AnchorScalars MainTheory.Orbit12EdgeLines
open MainTheory.Orbit6SpinorDisplays MainTheory.Orbit6LineCompletion
noncomputable section

def ScalarData (c d : SS.State 6 ℂ) (alpha0 alpha4 beta0 beta4 : ℂ)
    (A B : Fin 6 → ℂ) : Prop :=
  nsq (unitBottom c)=1 ∧ nsq (unitTop d)=1 ∧
  u c=alpha0 • unitBottom c ∧ v c=alpha4 • unitBottom c ∧
  ut d=beta0 • unitTop d ∧ vt d=beta4 • unitTop d ∧
  (∀ e,a c e=A e • unitTop d) ∧ (∀ e,b d e=B e • unitBottom c)

theorem actual_all_scalars (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ alpha0 alpha4 beta0 beta4 : ℂ,∃ A B : Fin 6 → ℂ,
      ScalarData c d alpha0 alpha4 beta0 beta4 A B := by
  obtain ⟨a0,a4,b0,b4,hL,hM,hu,hv,hU,hV⟩ := actual_anchor_scalars c d hc hd hnc hnd hkl
  obtain ⟨hb,ha⟩ := actual_edge_lines c d hc hd hnc hnd hkl
  choose A hA using ha
  choose B hB using hb
  refine ⟨a0,a4,b0,b4,fun e => A e/2,fun e => B e/2,hL,hM,hu,hv,hU,hV,?_,?_⟩
  · intro e
    rw [hA e]
    funext i
    simp only [unitTop,Pi.smul_apply,smul_eq_mul]
    ring
  · intro e
    rw [hB e]
    funext i
    simp only [unitBottom,Pi.smul_apply,smul_eq_mul]
    ring

theorem norm_one_nonzero (x : Fin 2 → ℂ) (h : nsq x=1) : x≠0 := by
  intro hx
  rw [hx] at h
  norm_num [nsq] at h

theorem norm_one_coordinate (x : Fin 2 → ℂ) (h : nsq x=1) : ∃ i,x i≠0 := by
  by_contra hn
  push_neg at hn
  apply norm_one_nonzero x h
  funext i
  exact hn i

theorem scalar_cancellation (l m : Fin 2 → ℂ) (alpha0 alpha4 beta0 beta4 : ℂ)
    (hL : nsq l=1) (hM : nsq m=1)
    (hx : Matrix.vecMulVec (beta0 • m) (star (alpha0 • l))+
      Matrix.vecMulVec (beta4 • m) (star (alpha4 • l))=0) :
    beta0*star alpha0+beta4*star alpha4=0 := by
  obtain ⟨i,hi⟩ := norm_one_coordinate m hM
  obtain ⟨j,hj⟩ := norm_one_coordinate l hL
  have hh := congrFun (congrFun hx i) j
  simp only [Matrix.add_apply,Matrix.vecMulVec_apply,Pi.star_apply,
    Pi.smul_apply,smul_eq_mul,star_mul',Matrix.zero_apply] at hh
  have hf : (beta0*star alpha0+beta4*star alpha4)*(m i*star (l j))=0 := by
    linear_combination hh
  exact (mul_eq_zero.mp hf).resolve_right (mul_ne_zero hi (star_ne_zero.mpr hj))

theorem actual_anchor_cancellation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (alpha0 alpha4 beta0 beta4 : ℂ) (A B : Fin 6 → ℂ)
    (hs : ScalarData c d alpha0 alpha4 beta0 beta4 A B) :
    beta0*star alpha0+beta4*star alpha4=0 := by
  obtain ⟨hL,hM,hu,hv,hU,hV,_,_⟩ := hs
  have hx := (physical_blocks c d hc hd hnc hnd hkl).1
  change Matrix.vecMulVec (ut d) (star (u c))+Matrix.vecMulVec (vt d) (star (v c))=0 at hx
  rw [hu,hv,hU,hV] at hx
  exact scalar_cancellation _ _ _ _ _ _ hL hM hx

theorem unit_pairing (x : Fin 2 → ℂ) (h : nsq x=1) : pairing x x=1 := by
  have hh := congrArg (fun r : ℝ => (r : ℂ)) h
  simp only [nsq] at hh
  push_cast at hh
  simp only [Complex.normSq_eq_conj_mul_self,← Complex.star_def] at hh
  exact hh

theorem pair_scalar_rows (l m : Fin 2 → ℂ) (alpha0 alpha4 beta0 beta4 A B : ℂ)
    (hL : nsq l=1) (hM : nsq m=1)
    (h1 : pairing (A • m) (beta0 • m)+pairing (alpha4 • l) (B • l)=0)
    (h2 : pairing (alpha0 • l) (B • l)+pairing (A • m) (beta4 • m)=0) :
    (star A*beta0+star alpha4*B=0) ∧ (star alpha0*B+star A*beta4=0) := by
  simp only [pairing_smul_left,pairing_smul_right,unit_pairing l hL,
    unit_pairing m hM,mul_one] at h1 h2
  constructor
  · linear_combination h1
  · linear_combination h2

theorem eliminated_anchor_equality (alpha0 alpha4 beta0 beta4 A B : ℂ)
    (hA : A≠0)
    (h1 : star A*beta0+star alpha4*B=0)
    (h2 : star alpha0*B+star A*beta4=0) :
    beta0*star alpha0=beta4*star alpha4 := by
  apply mul_left_cancel₀ (star_ne_zero.mpr hA)
  linear_combination star alpha0*h1-star alpha4*h2

end
end MainTheory.Orbit12ScalarCompletion
