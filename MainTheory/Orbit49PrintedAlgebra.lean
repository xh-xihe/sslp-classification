import MainTheory.Orbit49PrintedRows
import MainTheory.ComplementaryPhasePair

/-! The phase propagation, four quadrics, literal parameter pinning and final
ratio triangle of orbit 49. Intermediate statements are proved without a
no-code hypothesis, including the closed boundary of the moment polytope. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit49PrintedAlgebra
open scoped BigOperators Matrix
open MainTheory.OrderThreePrintedMoments.Orbit49
noncomputable section

def bottomAmplitudes (c : SS.State 6 ℂ) : Fin 10 → ℂ := fun i => c (bottom i)
def topAmplitudes (d : SS.State 6 ℂ) : Fin 10 → ℂ := fun i => d (top i)
def rec (c d : Fin 10 → ℂ) (a i : Fin 10) : ℂ := star (c i)*d a+star (c a)*d i
def rho (c d : Fin 10 → ℂ) (i : Fin 10) : ℂ := d i/star (c i)

theorem reciprocal_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit49.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit49.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∀ i : Fin 8, rec (bottomAmplitudes c) (topAmplitudes d) ⟨8,by decide⟩ ⟨i.val,by omega⟩=0 ∧
      rec (bottomAmplitudes c) (topAmplitudes d) ⟨9,by decide⟩ ⟨i.val,by omega⟩=0 := by
  have h0 := MainTheory.Orbit49PrintedRows.Row00.physical_relations c d hc hd hkl
  have h1 := MainTheory.Orbit49PrintedRows.Row01.physical_relations c d hc hd hkl
  have h2 := MainTheory.Orbit49PrintedRows.Row02.physical_relations c d hc hd hkl
  have h3 := MainTheory.Orbit49PrintedRows.Row03.physical_relations c d hc hd hkl
  have h4 := MainTheory.Orbit49PrintedRows.Row04.physical_relations c d hc hd hkl
  have h5 := MainTheory.Orbit49PrintedRows.Row05.physical_relations c d hc hd hkl
  have h6 := MainTheory.Orbit49PrintedRows.Row06.physical_relations c d hc hd hkl
  have h7 := MainTheory.Orbit49PrintedRows.Row07.physical_relations c d hc hd hkl
  intro i
  fin_cases i
  · change star (c SixQubit.Orbit49.y0)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z0=0 ∧
      star (c SixQubit.Orbit49.y0)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z0=0
    simpa only [add_comm] using And.intro h0.1 h1.1
  · change star (c SixQubit.Orbit49.y1)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z1=0 ∧
      star (c SixQubit.Orbit49.y1)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z1=0
    simpa only [add_comm] using And.intro h1.2 h0.2
  · change star (c SixQubit.Orbit49.y2)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z2=0 ∧
      star (c SixQubit.Orbit49.y2)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z2=0
    simpa only [add_comm] using And.intro h2.1 h3.1
  · change star (c SixQubit.Orbit49.y3)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z3=0 ∧
      star (c SixQubit.Orbit49.y3)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z3=0
    simpa only [add_comm] using And.intro h3.2 h2.2
  · change star (c SixQubit.Orbit49.y4)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z4=0 ∧
      star (c SixQubit.Orbit49.y4)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z4=0
    simpa only [add_comm] using And.intro h4.1 h5.1
  · change star (c SixQubit.Orbit49.y5)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z5=0 ∧
      star (c SixQubit.Orbit49.y5)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z5=0
    simpa only [add_comm] using And.intro h5.2 h4.2
  · change star (c SixQubit.Orbit49.y6)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z6=0 ∧
      star (c SixQubit.Orbit49.y6)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z6=0
    simpa only [add_comm] using And.intro h6.1 h7.1
  · change star (c SixQubit.Orbit49.y7)*d SixQubit.Orbit49.z8+star (c SixQubit.Orbit49.y8)*d SixQubit.Orbit49.z7=0 ∧
      star (c SixQubit.Orbit49.y7)*d SixQubit.Orbit49.z9+star (c SixQubit.Orbit49.y9)*d SixQubit.Orbit49.z7=0
    simpa only [add_comm] using And.intro h7.2 h6.2

theorem reconstruct_from_anchor (c d b e : ℂ) (hb : b≠0)
    (h : star c*e+star b*d=0) : d=-(e/star b)*star c := by
  calc
    d=-(e*star c)/star b := by
      apply (eq_div_iff (star_ne_zero.2 hb)).2
      linear_combination h
    _=-(e/star b)*star c := by ring

theorem uniform_phase (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : ∀ i : Fin 8, rec c d ⟨8,by decide⟩ ⟨i.val,by omega⟩=0 ∧
      rec c d ⟨9,by decide⟩ ⟨i.val,by omega⟩=0) :
    rho c d ⟨8,by decide⟩=rho c d ⟨9,by decide⟩ ∧
    rho c d ⟨8,by decide⟩≠0 ∧
    (∀ i : Fin 8, d ⟨i.val,by omega⟩=-(rho c d ⟨8,by decide⟩)*star (c ⟨i.val,by omega⟩)) := by
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have hd8 := consequence18 hm
  have h1 := consequence1 hm
  change Complex.normSq (c ⟨8,by decide⟩)=1/6 at h8
  change Complex.normSq (c ⟨9,by decide⟩)=1/6 at h9
  change Complex.normSq (d ⟨8,by decide⟩)=1/6 at hd8
  change Complex.normSq (c 1)=1/6-Complex.normSq (c 0) at h1
  have hc8 : c ⟨8,by decide⟩≠0 := Complex.normSq_pos.1 (by rw [h8]; norm_num)
  have hc9 : c ⟨9,by decide⟩≠0 := Complex.normSq_pos.1 (by rw [h9]; norm_num)
  have he8 : d ⟨8,by decide⟩≠0 := Complex.normSq_pos.1 (by rw [hd8]; norm_num)
  have hu : ∀ i : Fin 8, d ⟨i.val,by omega⟩=-(rho c d ⟨8,by decide⟩)*star (c ⟨i.val,by omega⟩) := by
    intro i
    exact reconstruct_from_anchor _ _ _ _ hc8 (hr i).1
  have hn : c 0≠0 ∨ c 1≠0 := by
    by_contra h
    push_neg at h
    rw [h.1,h.2,Complex.normSq_zero] at h1
    norm_num at h1
  have equal_anchor (i : Fin 8) (hi : c ⟨i.val,by omega⟩≠0) :
      rho c d ⟨8,by decide⟩=rho c d ⟨9,by decide⟩ := by
    have he := (hr i).2
    unfold rec at he
    rw [hu i] at he
    have hquot : d ⟨9,by decide⟩=rho c d ⟨8,by decide⟩*star (c ⟨9,by decide⟩) := by
      apply mul_left_cancel₀ (star_ne_zero.2 hi)
      linear_combination he
    change rho c d ⟨8,by decide⟩=d ⟨9,by decide⟩/star (c ⟨9,by decide⟩)
    rw [hquot,mul_div_cancel_right₀ _ (star_ne_zero.2 hc9)]
  refine ⟨?_,div_ne_zero he8 (star_ne_zero.2 hc8),hu⟩
  rcases hn with hn|hn
  · exact equal_anchor 0 hn
  · exact equal_anchor 1 hn

theorem poly_from_four_reciprocals (a b c d e f g h s t : ℂ) (ht : t≠0)
    (h0 : star s*e+star a*t=0) (h1 : star s*f+star b*t=0)
    (h2 : star s*g+star c*t=0) (h3 : star s*h+star d*t=0)
    (hr : star a*h+star b*g+star c*f+star d*e=0) : a*d+b*c=0 := by
  have hk : (star a*star d+star b*star c)*t=0 := by
    linear_combination (-star s/2)*hr+(star d/2)*h0+(star c/2)*h1+(star b/2)*h2+(star a/2)*h3
  have hz := (mul_eq_zero.1 hk).resolve_right ht
  have he := congrArg star hz
  simpa only [star_add,star_mul',star_star,star_zero] using he

theorem norm_product (a b c d : ℂ) (h : a*b+c*d=0) :
    Complex.normSq a*Complex.normSq b=Complex.normSq c*Complex.normSq d := by
  have he : a*b=-(c*d) := by linear_combination h
  have hn := congrArg Complex.normSq he
  simpa only [Complex.normSq_mul,Complex.normSq_neg] using hn

theorem pin_parameters (a b g : ℝ)
    (h1 : g*(1/6-b)=(1/6-g)*b)
    (h2 : g*(1/6-a)=(1/6-g)*a)
    (h3 : g*(a+b+g-1/6)=(1/6-g)*(1/3-a-b-g)) :
    a=1/12 ∧ b=1/12 ∧ g=1/12 := by
  have hgb : g=b := by linear_combination 6*h1
  have hga : g=a := by linear_combination 6*h2
  rw [← hgb,← hga] at h3
  have hg : g=1/12 := by linear_combination (3/2)*h3
  exact ⟨hga.symm.trans hg,hgb.symm.trans hg,hg⟩

theorem pinned_point (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (h1 : c 0*c ⟨3,by decide⟩+c 1*c ⟨2,by decide⟩=0)
    (h2 : c 0*c ⟨5,by decide⟩+c 1*c ⟨4,by decide⟩=0)
    (h4 : c 0*c ⟨7,by decide⟩+c 1*c ⟨6,by decide⟩=0) :
    (∀ i, Complex.normSq (c i)=if i.val<8 then 1/12 else 1/6) ∧
    (∀ i, Complex.normSq (d i)=if i.val<8 then 1/12 else 1/6) := by
  have e1 := norm_product _ _ _ _ h1
  have e2 := norm_product _ _ _ _ h2
  have e4 := norm_product _ _ _ _ h4
  obtain ⟨hq1,hq2,hq4⟩ := hm.pinned e1 e2 e4
  change Complex.normSq (c 1)=1/12 at hq1
  change Complex.normSq (c ⟨2,by decide⟩)=1/12 at hq2
  change Complex.normSq (c ⟨4,by decide⟩)=1/12 at hq4
  have hq0 : Complex.normSq (c 0)=1/12 := by
    have he := consequence1 hm
    change Complex.normSq (c 1)=1/6-Complex.normSq (c 0) at he
    linarith only [he,hq1]
  obtain ⟨hc,hd⟩ := normal_coordinates _ _ hm
  constructor
  · intro i
    have he := congrFun hc i
    fin_cases i <;> norm_num [bottomProb,hq0,hq2,hq4,Fin.succ] at he ⊢ <;> exact he
  · intro i
    have he := congrFun hd i
    fin_cases i <;> norm_num [topProb,hq0,hq2,hq4,Fin.succ] at he ⊢ <;> exact he

def triangle : Matrix (Fin 3) (Fin 3) ℚ := !![1,1,0;1,0,1;0,1,1]
theorem triangle_determinant : triangle.det=-2 := by decide +kernel
def triangleC : Matrix (Fin 3) (Fin 3) ℂ := !![1,1,0;1,0,1;0,1,1]
theorem triangle_equations (a b c : ℂ) :
    triangleC *ᵥ ![a,b,c]=0 ↔ a+b=0 ∧ a+c=0 ∧ b+c=0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h ⟨2,by decide⟩
    norm_num [triangleC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2
    exact ⟨h0,h1,h2⟩
  · rintro ⟨h0,h1,h2⟩
    ext i
    fin_cases i
    · simpa [triangleC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] using h0
    · simpa [triangleC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] using h1
    · simpa [triangleC,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] using h2

theorem ratio_triangle (a b c d e f : ℂ) (hb : b≠0) (hd : d≠0) (hf : f≠0)
    (h1 : a*d+b*c=0) (h2 : a*f+b*e=0) (h3 : c*f+d*e=0) :
    a/b+c/d=0 ∧ a/b+e/f=0 ∧ c/d+e/f=0 := by
  refine ⟨?_,?_,?_⟩
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2
  · field_simp
    linear_combination h3

end
end MainTheory.Orbit49PrintedAlgebra
