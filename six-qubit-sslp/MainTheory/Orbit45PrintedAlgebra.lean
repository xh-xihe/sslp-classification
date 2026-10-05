import MainTheory.Orbit45PrintedMoments
import MainTheory.Orbit45PrintedConsequences
import MainTheory.Orbit45TrianglePolynomial

/-! Literal coefficient algebra in the SI orbit-45 derivation. These lemmas
retain zero amplitudes and use the printed moment and Walsh hypotheses,
rather than assuming the final enumerator conclusion.
-/

namespace MainTheory.Orbit45PrintedAlgebra
open scoped BigOperators ComplexConjugate
noncomputable section

def probability (c : ℂ) : ℝ := Complex.normSq c
def cross (c d : ℂ) : ℂ := conj c*d

theorem cross_magnitude (c d : ℂ) (h : probability c=probability d) :
    ‖cross c d‖=probability c := by
  have hn : ‖c‖=‖d‖ := by
    simp only [probability,Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg c,norm_nonneg d]
  simp only [cross,norm_mul,Complex.norm_conj,← hn,probability]
  rw [Complex.normSq_eq_norm_sq,pow_two]

theorem recover (c d : ℂ) (h : 0<probability c) :
    d=cross c d/conj c ∧ d=cross c d*c/(probability c : ℂ) := by
  have hc : c≠0 := by
    intro hc
    simp [probability,hc] at h
  have hp : (probability c : ℂ)≠0 := by exact_mod_cast ne_of_gt h
  have hconj : conj c≠0 := by simpa using hc
  constructor
  · unfold cross
    field_simp
  · unfold cross
    have hm : conj c*c=(probability c : ℂ) := by
      rw [mul_comm,Complex.mul_conj]
      rfl
    calc d = (probability c : ℂ)*d/(probability c : ℂ) := by field_simp
      _ = _ := by rw [← hm]; congr 1; ring

theorem paired_products (c d c' d' : ℂ)
    (hm : probability c=probability c') (hz : cross c d=cross c' d') :
    c*d'=c'*d := by
  by_cases hc : c=0
  · have hc' : c'=0 := by
      apply Complex.normSq_eq_zero.mp
      simpa [probability,hc] using hm.symm
    simp [hc,hc']
  · have hp : 0<probability c := by
      exact Complex.normSq_pos.mpr hc
    have hp' : 0<probability c' := hm ▸ hp
    rw [(recover c d hp).2,(recover c' d' hp').2,← hm,← hz]
    ring

theorem moment_reversal (a b c : ℝ) (r : Fin 10) :
    Orbit45PrintedMoments.pattern a b c r.rev=Orbit45PrintedMoments.pattern a b c r := by
  fin_cases r <;> rfl

theorem cross_reversal (a b c : ℂ) (r : Fin 10) :
    Orbit45PrintedWalsh.pattern a b c r.rev=Orbit45PrintedWalsh.pattern a b c r := by
  fin_cases r <;> rfl

theorem one_body_Z (b c : ℝ) (i : Fin 6) :
    (∑ r : Fin 10, Orbit45PrintedMoments.pattern (1/8) b c r*
      (if Orbit45PrintedFibers.bottom r i then -1 else 1))=0 := by
  fin_cases i <;>
    norm_num [Orbit45PrintedMoments.pattern,Orbit45PrintedFibers.bottom,
      Orbit21LiteralData.bits,SixQubit.Realize.nbit,
      Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.sum_univ_succ] <;> ring

theorem triangle_identity (b c s : ℝ) (xi eta : ℂ)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (ht : (b : ℂ)*xi+(c : ℂ)*eta+(s : ℂ)=0) :
    b*s*Complex.normSq (1+xi)=c^2-(b-s)^2 ∧
    b*c*Complex.normSq (xi+eta)=s^2-(b-c)^2 ∧
    c*s*Complex.normSq (1+eta)=b^2-(c-s)^2 := by
  have he1 : (b : ℂ)*xi+(s : ℂ)=-(c : ℂ)*eta := by linear_combination ht
  have he2 : (b : ℂ)*xi+(c : ℂ)*eta=-(s : ℂ) := by linear_combination ht
  have he3 : (c : ℂ)*eta+(s : ℂ)=-(b : ℂ)*xi := by linear_combination ht
  have h1 := congrArg Complex.normSq he1
  have h2 := congrArg Complex.normSq he2
  have h3 := congrArg Complex.normSq he3
  simp only [Complex.normSq_mul,Complex.normSq_neg,Complex.normSq_ofReal,hxi,heta,
    mul_one] at h1 h2 h3
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at h1 h2 h3
  simp only [Complex.normSq_apply] at hxi heta
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.one_re,Complex.one_im,zero_add]
  constructor
  · linear_combination h1 + (b*s-b^2)*hxi
  constructor
  · linear_combination h2 + (b*c-b^2)*hxi + (b*c-c^2)*heta
  · linear_combination h3 + (c*s-c^2)*heta

theorem diagonal_sum (b c s : ℝ) (ht : b+c+s=1/4) :
    2*(4*c-1/2)^2+2*(1/2-4*s)^2+2*(1/2-4*b)^2+
      (-4*b)^2+(-4*s)^2+(4*c)^2=48*Orbit45TrianglePolynomial.R b c s-1/2 := by
  unfold Orbit45TrianglePolynomial.R
  nlinarith

theorem off_diagonal_sum (b c s : ℝ) (xi eta : ℂ)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (ht : (b : ℂ)*xi+(c : ℂ)*eta+(s : ℂ)=0) (hs : b+c+s=1/4) :
    8*(b*s*Complex.normSq (1+xi)+b*c*Complex.normSq (xi+eta)+
      c*s*Complex.normSq (1+eta))=1/2-16*Orbit45TrianglePolynomial.R b c s := by
  obtain ⟨h1,h2,h3⟩ := triangle_identity b c s xi eta hxi heta ht
  rw [h1,h2,h3]
  unfold Orbit45TrianglePolynomial.R
  nlinarith

end
end MainTheory.Orbit45PrintedAlgebra
