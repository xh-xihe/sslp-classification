import MainTheory.D3BoundedNormalForm
import MainTheory.SmallBetaValues

set_option autoImplicit false

namespace MainTheory.EndpointLiftDisplays

theorem eight_arithmetic (q : ℕ) (hq : 0<q) (hd : 8 ∣ q) (hb : q ≤ 9) :
    q=8 ∧ q/8=1 := by
  obtain ⟨k,hk⟩ := hd
  omega

theorem nine_arithmetic (q : ℕ) (hq : 0<q) (hd : 9 ∣ q) (hb : q ≤ 9) :
    q=9 ∧ q/9=1 := by
  obtain ⟨k,hk⟩ := hd
  omega

theorem controlled_bound (C : MainTheory.CodeSpec.ExactCode 6 2 3)
    (S : MainTheory.SortedForm.SortedNormalForm C) (hb : S.q ≤ 9) :
    S.m ∣ S.q ∧ S.q ≤ MainTheory.BetaExists.betaOf 6 ∧ MainTheory.BetaExists.betaOf 6=9 := by
  rw [MainTheory.SmallBetaValues.betaOf_six]
  exact ⟨S.m_dvd_q,hb,rfl⟩

theorem eight_lift (C : MainTheory.CodeSpec.ExactCode 6 2 3)
    (S : MainTheory.SortedForm.SortedNormalForm C) (hb : S.q ≤ 9) (hm : S.m=8) :
    S.q=8 ∧ S.q/S.m=1 := by
  rw [hm]
  exact eight_arithmetic S.q (by have h := S.two_le_q; omega) (hm ▸ S.m_dvd_q) hb

theorem nine_lift (C : MainTheory.CodeSpec.ExactCode 6 2 3)
    (S : MainTheory.SortedForm.SortedNormalForm C) (hb : S.q ≤ 9) (hm : S.m=9) :
    S.q=9 ∧ S.q/S.m=1 := by
  rw [hm]
  exact nine_arithmetic S.q (by have h := S.two_le_q; omega) (hm ▸ S.m_dvd_q) hb

end MainTheory.EndpointLiftDisplays
