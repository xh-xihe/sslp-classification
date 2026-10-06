import SixQubit.Order9
import MainTheory.FullKLDisplays

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.OrderNineEdgeDisplays

open SixQubit.Order9

theorem edge_labels : y0=bs false false false false false false ∧
    y6=bs false true true true true true ∧
    t1=bs true false false false false false ∧
    t2=bs true true true true true true := ⟨rfl,rfl,rfl,rfl⟩

theorem X1_element (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0) :
    SS.innerC c (SS.pauliAct ⟨e1,w0⟩ d)=A c d+B c d := by
  rw [SixQubit.innerC_eq_offSumOn S0 S1 c d hc hd]
  have hy : (⟨e1,w0⟩ : SS.PauliString 6).numY=0 := by decide +kernel
  rw [hy,pow_zero,one_mul]
  exact offSum_X1 c d

theorem X1Z2_element (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0) :
    SS.innerC c (SS.pauliAct ⟨e1,e2⟩ d)=A c d-B c d := by
  rw [SixQubit.innerC_eq_offSumOn S0 S1 c d hc hd]
  have hy : (⟨e1,e2⟩ : SS.PauliString 6).numY=0 := by decide +kernel
  rw [hy,pow_zero,one_mul]
  exact offSum_X1Z2 c d

theorem KL_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : A c d+B c d=0 ∧ A c d-B c d=0 := by
  have h0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl e1 w0
    (by decide : (⟨e1,w0⟩ : SS.PauliString 6).wt ≤ 2)
  have h1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl e1 e2
    (by decide : (⟨e1,e2⟩ : SS.PauliString 6).wt ≤ 2)
  change offSum c d e1 w0=0 at h0
  change offSum c d e1 e2=0 at h1
  exact ⟨by simpa only [offSum_X1] using h0,by simpa only [offSum_X1Z2] using h1⟩

theorem magnitude_from_normSq (z : ℂ) (h : Complex.normSq z=5/81) :
    ‖z‖=Real.sqrt 5/9 := by
  have hz := Complex.sq_norm z
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := norm_nonneg z
  have hs := Real.sqrt_nonneg (5 : ℝ)
  rw [h] at hz
  nlinarith

theorem magnitudes (c d : SS.State 6 ℂ)
    (hc0 : Complex.normSq (c y0)=2/9) (hc6 : Complex.normSq (c y6)=5/18)
    (hd1 : Complex.normSq (d t1)=5/18) (hd2 : Complex.normSq (d t2)=2/9) :
    ‖A c d‖=Real.sqrt 5/9 ∧ ‖B c d‖=Real.sqrt 5/9 := by
  constructor <;> apply magnitude_from_normSq <;>
    norm_num [A,B,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc0,hc6,hd1,hd2]

theorem radical_products : Real.sqrt ((2/9 : ℝ)*(5/18))=Real.sqrt 5/9 ∧
    Real.sqrt ((5/18 : ℝ)*(2/9))=Real.sqrt 5/9 := by
  have h : Real.sqrt ((5 : ℝ)/81)=Real.sqrt 5/9 := by
    rw [Real.sqrt_div] <;> norm_num
  constructor
  · rw [show (2/9 : ℝ)*(5/18)=5/81 by norm_num]
    exact h
  · rw [show (5/18 : ℝ)*(2/9)=5/81 by norm_num]
    exact h

end MainTheory.OrderNineEdgeDisplays
