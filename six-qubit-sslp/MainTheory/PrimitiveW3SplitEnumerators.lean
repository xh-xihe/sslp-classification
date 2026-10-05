import MainTheory.ArbitrarySplitEnumerators
import MainTheory.PrimitiveW3SplitScalarDisplays
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.PrimitiveW3SplitEnumerators
open scoped BigOperators Matrix
open Orbit2.TensorPauli Orbit2.HilbertBridge
open MainTheory.ArbitrarySplitSixQubit MainTheory.ArbitrarySplitEnumerators
open MainTheory.PrimitiveW3SplitScalarDisplays
noncomputable section
def zLabel : Label 6 := ![0,3,0,0,0,0]
def zxLabel : Label 6 := ![3,1,0,0,0,0]
def PZ : SS.PauliString 6 := Orbit2.decode zLabel
def PZX : SS.PauliString 6 := Orbit2.decode zxLabel

theorem shapes : ∀ p : Label 6,
    (p=(fun _ => 0) ↔ tailLabel p=(fun _ => 0) ∧ p 0=0 ∧ p 1=0) ∧
    (p=zLabel ↔ tailLabel p=(fun _ => 0) ∧ p 0=0 ∧ p 1=3) ∧
    (p=zxLabel ↔ tailLabel p=(fun _ => 0) ∧ p 0=3 ∧ p 1=1) := by decide +kernel

theorem sparse_scalar (θ : ℝ) (p : Label 6) (hp : weight6 p≠0) :
    scalar (MainTheory.PrimitiveSplitDisplays.W3 θ) p=
      if p=zLabel then (Real.cos θ : ℂ) else
      if p=zxLabel then (Real.sin θ : ℂ) else 0 := by
  have hn : p≠(fun _ => 0) := by
    intro h
    apply hp
    simp [weight6,h]
  obtain ⟨h0,hz,hxz⟩ := shapes p
  rw [physical_scalar]
  split_ifs <;> simp_all

theorem labels_eq (p : SS.PauliString 6) (q : Label 6) : label p=q ↔ p=Orbit2.decode q := by
  constructor
  · intro h
    apply label_injective
    rwa [Orbit2.label_decode]
  · rintro rfl
    exact Orbit2.label_decode q

theorem weight_PZ : PZ.wt=1 := by decide +kernel
theorem weight_PZX : PZX.wt=2 := by decide +kernel
theorem distinct : PZ≠PZX := by decide +kernel

theorem low_norm (θ : ℝ) (p : SS.PauliString 6) (hp : p.wt=1 ∨ p.wt=2) :
    Complex.normSq (SS.MacWilliams.trProj
      (words (code (MainTheory.PrimitiveSplitDisplays.W3 θ))) p)=
      (if p=PZ then 4*Real.cos θ^2 else 0)+
      (if p=PZX then 4*Real.sin θ^2 else 0) := by
  rw [low_trace _ (MainTheory.PrimitiveSplitDisplays.W3_isometry θ) p (by omega),
    sparse_scalar θ (label p) (by simpa only [weight6,label_weight] using (show p.wt≠0 by omega))]
  simp only [labels_eq]
  change Complex.normSq (2*(if p=PZ then (Real.cos θ : ℂ) else
    if p=PZX then (Real.sin θ : ℂ) else 0))=_
  by_cases hz : p=PZ
  · have hx : p≠PZX := by simpa only [hz] using distinct
    simp only [if_pos hz,if_neg hx,add_zero]
    norm_num [Complex.normSq_apply,-Complex.ofReal_cos,-Complex.ofReal_sin]
    ring
  · by_cases hx : p=PZX
    · simp only [if_neg hz,if_pos hx,zero_add]
      norm_num [Complex.normSq_apply,-Complex.ofReal_cos,-Complex.ofReal_sin]
      ring
    · simp only [hz,hx,if_false,mul_zero,Complex.normSq_zero,add_zero]

theorem low_enumerators (θ : ℝ) :
    A (MainTheory.PrimitiveSplitDisplays.W3 θ) 1=Real.cos θ^2 ∧
    A (MainTheory.PrimitiveSplitDisplays.W3 θ) 2=Real.sin θ^2 ∧
    A (MainTheory.PrimitiveSplitDisplays.W3 θ) 3=0 := by
  have h (w : ℕ) (hw : w=1 ∨ w=2) :
      SS.MacWilliams.Aco (words (code (MainTheory.PrimitiveSplitDisplays.W3 θ))) w=
      (if w=1 then 4*Real.cos θ^2 else 0)+(if w=2 then 4*Real.sin θ^2 else 0) := by
    unfold SS.MacWilliams.Aco
    calc
      _=(∑ p ∈ Finset.univ.filter (fun p : SS.PauliString 6 => p.wt=w),
        ((if p=PZ then 4*Real.cos θ^2 else 0)+(if p=PZX then 4*Real.sin θ^2 else 0))) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact low_norm θ p (by rw [(Finset.mem_filter.mp hp).2]; exact hw)
      _=_ := by simp [Finset.sum_add_distrib,weight_PZ,weight_PZX,eq_comm]
  refine ⟨?_,?_,A_three _ (MainTheory.PrimitiveSplitDisplays.W3_isometry θ)⟩
  · rw [A,h 1 (Or.inl rfl)]
    norm_num
  · rw [A,h 2 (Or.inr rfl)]
    norm_num

theorem enumerator (θ : ℝ) :
    (fun w : Fin 7 => A (MainTheory.PrimitiveSplitDisplays.W3 θ) w.val)=
      Orbit2.enumeratorLine (Real.cos θ^2) := by
  obtain ⟨h1,h2,h3⟩ := low_enumerators θ
  have h0 := A_zero _ (MainTheory.PrimitiveSplitDisplays.W3_isometry θ)
  obtain ⟨h4,h5,h6⟩ := macwilliams _ (MainTheory.PrimitiveSplitDisplays.W3_isometry θ)
  have ht := Real.sin_sq_add_cos_sq θ
  ext w
  fin_cases w <;> simp only [Orbit2.enumeratorLine,h0,h1,h2,h3,h4,h5,h6]
  all_goals norm_num
  all_goals nlinarith

end
end MainTheory.PrimitiveW3SplitEnumerators
