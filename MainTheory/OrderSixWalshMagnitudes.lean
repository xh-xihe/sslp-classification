import MainTheory.OrderSixWalshDisplays
import MainTheory.AmplitudeProductMagnitude

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSixWalshMagnitudes
open MainTheory.OrderSixSupportDisplays MainTheory.OrderSixWalshDisplays
open MainTheory.OrderSevenWalshMatrix


theorem orbit53X1 (c d : SS.State 6 ℂ) (p : Fin 10 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom53 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top53 i))=p i)
    (hs0 : ∀ x,x ∉ SixQubit.Orbit53.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit53.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p 0*p 9=p 3*p 6 := by
  have h := (relations _ (Orbit53X1.matrix_equation c d hs0 hs1 hkl)).2.2
  change star (c (bottom53 6))*d (top53 3)= -(star (c (bottom53 9))*d (top53 0)) at h
  have hm := MainTheory.AmplitudeProductMagnitude.equal_products
    (fun i => c (bottom53 i)) (fun i => d (top53 i)) p hc hd 9 0 6 3 h
  simpa only [mul_comm] using hm


theorem orbit53X2 (c d : SS.State 6 ℂ) (p : Fin 10 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom53 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top53 i))=p i)
    (hs0 : ∀ x,x ∉ SixQubit.Orbit53.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit53.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p 0*p 8=p 3*p 5 := by
  have h := (relations _ (Orbit53X2.matrix_equation c d hs0 hs1 hkl)).2.2
  change star (c (bottom53 5))*d (top53 3)= -(star (c (bottom53 8))*d (top53 0)) at h
  have hm := MainTheory.AmplitudeProductMagnitude.equal_products
    (fun i => c (bottom53 i)) (fun i => d (top53 i)) p hc hd 8 0 5 3 h
  simpa only [mul_comm] using hm


theorem orbit53X3 (c d : SS.State 6 ℂ) (p : Fin 10 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom53 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top53 i))=p i)
    (hs0 : ∀ x,x ∉ SixQubit.Orbit53.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit53.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p 0*p 7=p 3*p 4 := by
  have h := (relations _ (Orbit53X3.matrix_equation c d hs0 hs1 hkl)).2.2
  change star (c (bottom53 4))*d (top53 3)= -(star (c (bottom53 7))*d (top53 0)) at h
  have hm := MainTheory.AmplitudeProductMagnitude.equal_products
    (fun i => c (bottom53 i)) (fun i => d (top53 i)) p hc hd 7 0 4 3 h
  simpa only [mul_comm] using hm


theorem orbit54X1 (c d : SS.State 6 ℂ) (p : Fin 9 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom54 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top54 i))=p i)
    (hs0 : ∀ x,x ∉ SixQubit.Orbit54.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit54.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p 0*p 8=p 4*p 6 := by
  have h := (relations _ (Orbit54X1.matrix_equation c d hs0 hs1 hkl)).2.2
  change star (c (bottom54 6))*d (top54 4)= -(star (c (bottom54 8))*d (top54 0)) at h
  have hm := MainTheory.AmplitudeProductMagnitude.equal_products
    (fun i => c (bottom54 i)) (fun i => d (top54 i)) p hc hd 8 0 6 4 h
  simpa only [mul_comm] using hm


theorem orbit54X2 (c d : SS.State 6 ℂ) (p : Fin 9 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom54 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top54 i))=p i)
    (hs0 : ∀ x,x ∉ SixQubit.Orbit54.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit54.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p 0*p 7=p 4*p 5 := by
  have h := (relations _ (Orbit54X2.matrix_equation c d hs0 hs1 hkl)).2.2
  change star (c (bottom54 5))*d (top54 4)= -(star (c (bottom54 7))*d (top54 0)) at h
  have hm := MainTheory.AmplitudeProductMagnitude.equal_products
    (fun i => c (bottom54 i)) (fun i => d (top54 i)) p hc hd 7 0 5 4 h
  simpa only [mul_comm] using hm


theorem orbit54X6 (c d : SS.State 6 ℂ) (p : Fin 9 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom54 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top54 i))=p i)
    (hs0 : ∀ x,x ∉ SixQubit.Orbit54.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit54.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p 5*p 8=p 6*p 7 := by
  have h := (relations _ (Orbit54X6.matrix_equation c d hs0 hs1 hkl)).2.2
  change star (c (bottom54 7))*d (top54 6)= -(star (c (bottom54 8))*d (top54 5)) at h
  have hm := MainTheory.AmplitudeProductMagnitude.equal_products
    (fun i => c (bottom54 i)) (fun i => d (top54 i)) p hc hd 8 5 7 6 h
  simpa only [mul_comm] using hm


theorem orbit56X1 (c d : SS.State 6 ℂ) (p : Fin 10 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom56 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top56 i))=p i)
    (hs0 : ∀ x,x ∉ SixQubit.Orbit56.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit56.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p 0*p 9=p 1*p 8 := by
  have h := (relations _ (Orbit56X1.matrix_equation c d hs0 hs1 hkl)).2.2
  change star (c (bottom56 8))*d (top56 1)= -(star (c (bottom56 9))*d (top56 0)) at h
  have hm := MainTheory.AmplitudeProductMagnitude.equal_products
    (fun i => c (bottom56 i)) (fun i => d (top56 i)) p hc hd 9 0 8 1 h
  simpa only [mul_comm] using hm


end MainTheory.OrderSixWalshMagnitudes
