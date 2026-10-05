import SixQubit.Orbit32

/-! The displayed squared-modulus, reflection factors and odd triangle,
proved before invoking any no-go conclusion. -/
set_option autoImplicit false
namespace MainTheory.Orbit32PrintedLocalAlgebra
noncomputable section

def T : Matrix (Fin 3) (Fin 3) ℚ := ![![2/3,2/3,-1/3],![2/3,-1/3,2/3],![-1/3,2/3,2/3]]
theorem reflection_involution : T*T=1 := by decide +kernel

theorem absolute_product {a b c d : ℂ} (h : star a*b+star c*d=0) :
    Complex.normSq a*Complex.normSq b=Complex.normSq c*Complex.normSq d := by
  have he : star a*b= -(star c*d) := by linear_combination h
  have hn := congrArg Complex.normSq he
  simpa only [Complex.normSq_mul,Complex.normSq_conj,Complex.normSq_neg,
    Complex.star_def] using hn

theorem moduli {a b c e f g : ℂ}
    (h1 : star a*f+star b*g=0) (h2 : star a*e+star c*g=0)
    (h3 : star b*e+star c*f=0) :
    Complex.normSq a*Complex.normSq f=Complex.normSq b*Complex.normSq g ∧
    Complex.normSq a*Complex.normSq e=Complex.normSq c*Complex.normSq g ∧
    Complex.normSq b*Complex.normSq e=Complex.normSq c*Complex.normSq f :=
  ⟨absolute_product h1,absolute_product h2,absolute_product h3⟩

theorem factors (A B C E F G : ℝ)
    (hA : A=(2*E+2*F-G)/3) (hB : B=(2*E-F+2*G)/3)
    (hC : C=(-E+2*F+2*G)/3) :
    A*F-B*G=(2/3)*(F-G)*(E+F+G) ∧
    A*E-C*G=(2/3)*(E-G)*(E+F+G) ∧
    B*E-C*F=(2/3)*(E-F)*(E+F+G) := by
  rw [hA,hB,hC]
  constructor
  · ring
  · constructor <;> ring

theorem positive_triple (A B C E F G : ℝ)
    (hA : A=(2*E+2*F-G)/3) (hB : B=(2*E-F+2*G)/3)
    (hC : C=(-E+2*F+2*G)/3) (hE : 0 < E) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hm1 : A*F=B*G) (hm2 : A*E=C*G) :
    E=F ∧ F=G ∧ A=E ∧ B=E ∧ C=E ∧ 0 < E+F+G := by
  have hs : 0 < E+F+G := by linarith
  obtain ⟨hf1,hf2,_⟩ := factors A B C E F G hA hB hC
  have hg1 : F-G=0 := by
    have hz : (F-G)*(E+F+G)=0 := by nlinarith [hf1]
    exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hs)
  have hg2 : E-G=0 := by
    have hz : (E-G)*(E+F+G)=0 := by nlinarith [hf2]
    exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hs)
  refine ⟨?_,?_,?_,?_,?_,hs⟩ <;> linarith

theorem triangle_identity (a b c e f g : ℂ) :
    star c*(star a*f+star b*g)-star b*(star a*e+star c*g)+
      star a*(star b*e+star c*f)=2*star a*star c*f := by ring

end
end MainTheory.Orbit32PrintedLocalAlgebra
