import Mathlib

/-! Scalar phase-ratio consequences, including zero-amplitude boundaries.
No final impossibility theorem is used for any intermediate relation.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.ComplementaryPhasePair
noncomputable section

def sigma (c d : ℂ) : ℂ := star d/c

theorem reconstruct (c d : ℂ) (hp : Complex.normSq d=Complex.normSq c) :
    star d=sigma c d*c := by
  by_cases hc : c=0
  · have hd : d=0 := by apply Complex.normSq_eq_zero.1; rw [hp,hc,Complex.normSq_zero]
    simp [sigma,hc,hd]
  · exact (div_mul_cancel₀ (star d) hc).symm

theorem unit (c d : ℂ) (hp : Complex.normSq d=Complex.normSq c) (hc : c≠0) :
    Complex.normSq (sigma c d)=1 := by
  rw [sigma,Complex.normSq_div]
  change Complex.normSq ((starRingEnd ℂ) d)/Complex.normSq c=1
  rw [Complex.normSq_conj,hp]
  exact div_self (mt Complex.normSq_eq_zero.1 hc)

theorem nonzero (c d : ℂ) (hp : Complex.normSq d=Complex.normSq c) (hc : c≠0) :
    sigma c d≠0 := by
  have hd : d≠0 := by intro h; rw [h,Complex.normSq_zero] at hp; exact hc (Complex.normSq_eq_zero.1 hp.symm)
  exact div_ne_zero (star_ne_zero.2 hd) hc

theorem weighted_opposition (b s db ds : ℂ) (hs : s≠0)
    (h : star b*ds+star s*db=0) : star db = -sigma s ds*b := by
  have he := congrArg star h
  simp only [star_add,star_mul',star_star,star_zero] at he
  apply mul_left_cancel₀ hs
  calc
    s*star db=-(b*star ds) := by linear_combination he
    _=s*(-sigma s ds*b) := by
      unfold sigma
      calc
        -(b*star ds)=-(star ds/s*s*b) := by rw [div_mul_cancel₀ _ hs]; ring
        _=s*(-(star ds/s)*b) := by ring

theorem active_opposition (b s db ds : ℂ) (hb : b≠0) (hs : s≠0)
    (h : star b*ds+star s*db=0) : sigma b db = -sigma s ds := by
  apply (div_eq_iff hb).2
  exact weighted_opposition b s db ds hs h

theorem active_equality (a b da db : ℂ) (ha : a≠0) (hb : b≠0)
    (h : star a*db=star b*da) : sigma a da=sigma b db := by
  apply (div_eq_div_iff ha hb).2
  have he := congrArg star h
  simp only [star_mul',star_star] at he
  linear_combination -he

theorem active_column_opposition (a b s da db ds : ℂ) (ha : a≠0) (hb : b≠0) (hs : s≠0)
    (hrec : star a*ds+star s*da=0) (hsync : star a*db=star b*da) :
    sigma b db=sigma a da ∧ sigma a da = -sigma s ds :=
  ⟨(active_equality a b da db ha hb hsync).symm,active_opposition a s da ds ha hs hrec⟩

end
end MainTheory.ComplementaryPhasePair
