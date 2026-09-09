import MainTheory.SupportKetExpansion
import MainTheory.OrderSevenSupportDisplays
import MainTheory.OrderSixSupportDisplays

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.PaperFiberExpansions
open MainTheory.SupportKetExpansion

theorem order_eight_A (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit64.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit64.S1 → d x=0) :
    c=∑ x ∈ SixQubit.Orbit64.S0,c x • ket x ∧
    d=∑ y ∈ SixQubit.Orbit64.S1,d y • ket y :=
  ⟨expansion _ c hc,expansion _ d hd⟩


theorem orbit53 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit53.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit53.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSixSupportDisplays.bottom53 i) • ket (MainTheory.OrderSixSupportDisplays.bottom53 i) ∧
    d=∑ i,d (MainTheory.OrderSixSupportDisplays.top53 i) • ket (MainTheory.OrderSixSupportDisplays.top53 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.bottom_image53 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.top_image53 d hd⟩


theorem orbit54 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit54.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit54.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSixSupportDisplays.bottom54 i) • ket (MainTheory.OrderSixSupportDisplays.bottom54 i) ∧
    d=∑ i,d (MainTheory.OrderSixSupportDisplays.top54 i) • ket (MainTheory.OrderSixSupportDisplays.top54 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.bottom_image54 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.top_image54 d hd⟩


theorem orbit55 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit55.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit55.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSixSupportDisplays.bottom55 i) • ket (MainTheory.OrderSixSupportDisplays.bottom55 i) ∧
    d=∑ i,d (MainTheory.OrderSixSupportDisplays.top55 i) • ket (MainTheory.OrderSixSupportDisplays.top55 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.bottom_image55 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.top_image55 d hd⟩


theorem orbit56 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit56.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit56.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSixSupportDisplays.bottom56 i) • ket (MainTheory.OrderSixSupportDisplays.bottom56 i) ∧
    d=∑ i,d (MainTheory.OrderSixSupportDisplays.top56 i) • ket (MainTheory.OrderSixSupportDisplays.top56 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.bottom_image56 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSixSupportDisplays.top_image56 d hd⟩


theorem orbit57 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit57.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit57.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSevenSupportDisplays.bottom57 i) • ket (MainTheory.OrderSevenSupportDisplays.bottom57 i) ∧
    d=∑ i,d (MainTheory.OrderSevenSupportDisplays.top57 i) • ket (MainTheory.OrderSevenSupportDisplays.top57 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.bottom_image57 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.top_image57 d hd⟩


theorem orbit58 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit58.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit58.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSevenSupportDisplays.bottom58 i) • ket (MainTheory.OrderSevenSupportDisplays.bottom58 i) ∧
    d=∑ i,d (MainTheory.OrderSevenSupportDisplays.top58 i) • ket (MainTheory.OrderSevenSupportDisplays.top58 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.bottom_image58 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.top_image58 d hd⟩


theorem orbit59 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit59.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit59.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSevenSupportDisplays.bottom59 i) • ket (MainTheory.OrderSevenSupportDisplays.bottom59 i) ∧
    d=∑ i,d (MainTheory.OrderSevenSupportDisplays.top59 i) • ket (MainTheory.OrderSevenSupportDisplays.top59 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.bottom_image59 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.top_image59 d hd⟩


theorem orbit60 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit60.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit60.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSevenSupportDisplays.bottom60 i) • ket (MainTheory.OrderSevenSupportDisplays.bottom60 i) ∧
    d=∑ i,d (MainTheory.OrderSevenSupportDisplays.top60 i) • ket (MainTheory.OrderSevenSupportDisplays.top60 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.bottom_image60 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.top_image60 d hd⟩


theorem orbit61 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit61.S0 → c x=0)
    (hd : ∀ x,x ∉ SixQubit.Orbit61.S1 → d x=0) :
    c=∑ i,c (MainTheory.OrderSevenSupportDisplays.bottom61 i) • ket (MainTheory.OrderSevenSupportDisplays.bottom61 i) ∧
    d=∑ i,d (MainTheory.OrderSevenSupportDisplays.top61 i) • ket (MainTheory.OrderSevenSupportDisplays.top61 i) := by
  exact ⟨indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.bottom_image61 c hc,
    indexed_expansion _ _ (by decide +kernel) MainTheory.OrderSevenSupportDisplays.top_image61 d hd⟩


end MainTheory.PaperFiberExpansions
