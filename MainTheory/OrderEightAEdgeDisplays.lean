import SixQubit.Orbit64
import MainTheory.FullKLDisplays

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.OrderEightAEdgeDisplays

open SixQubit.Orbit64

theorem edge_labels : y0=bs false false false false false false ∧
    y1=bs false true true true true true ∧
    t1=bs true false false false false false ∧
    t2=bs true true true true true true := ⟨rfl,rfl,rfl,rfl⟩

theorem X1_element (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0) :
    SS.innerC c (SS.pauliAct ⟨e1,(fun _ => false)⟩ d)=A c d+B c d := by
  rw [SixQubit.innerC_eq_offSumOn S0 S1 c d hc hd]
  have hy : (⟨e1,(fun _ => false)⟩ : SS.PauliString 6).numY=0 := by decide +kernel
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
  have h0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl e1 (fun _ => false)
    (by decide : (⟨e1,(fun _ => false)⟩ : SS.PauliString 6).wt ≤ 2)
  have h1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl e1 e2
    (by decide : (⟨e1,e2⟩ : SS.PauliString 6).wt ≤ 2)
  change offSum c d e1 (fun _ => false)=0 at h0
  change offSum c d e1 e2=0 at h1
  exact ⟨by simpa only [offSum_X1] using h0,by simpa only [offSum_X1Z2] using h1⟩

theorem magnitude_from_normSq (z : ℂ) (h : Complex.normSq z=15/256) :
    ‖z‖=Real.sqrt 15/16 := by
  have hz := Complex.sq_norm z
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)
  have hn := norm_nonneg z
  have hs := Real.sqrt_nonneg (15 : ℝ)
  rw [h] at hz
  nlinarith

theorem magnitudes (c d : SS.State 6 ℂ)
    (hc0 : Complex.normSq (c y0)=5/16) (hc1 : Complex.normSq (c y1)=3/16)
    (hd1 : Complex.normSq (d t1)=3/16) (hd2 : Complex.normSq (d t2)=5/16) :
    ‖A c d‖=Real.sqrt 15/16 ∧ ‖B c d‖=Real.sqrt 15/16 := by
  constructor <;> apply magnitude_from_normSq <;>
    norm_num [A,B,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc0,hc1,hd1,hd2]

theorem radical_products : Real.sqrt ((5/16 : ℝ)*(3/16))=Real.sqrt 15/16 ∧
    Real.sqrt ((3/16 : ℝ)*(5/16))=Real.sqrt 15/16 := by
  have h : Real.sqrt ((15 : ℝ)/256)=Real.sqrt 15/16 := by
    rw [Real.sqrt_div] <;> norm_num
  constructor
  · rw [show (5/16 : ℝ)*(3/16)=15/256 by norm_num]
    exact h
  · rw [show (3/16 : ℝ)*(5/16)=15/256 by norm_num]
    exact h

theorem radical_positive : 0 < Real.sqrt (15 : ℝ)/16 := by positivity

end MainTheory.OrderEightAEdgeDisplays
