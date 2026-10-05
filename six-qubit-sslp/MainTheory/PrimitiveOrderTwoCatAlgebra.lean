import Mathlib

/-! Literal coefficients of the SI five-cat construction, before embedding
the cats in the physical Hilbert space. All square-root factors are retained.
-/

namespace MainTheory.PrimitiveOrderTwoCatAlgebra
noncomputable section
open scoped BigOperators ComplexConjugate
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def h : ℝ := (Real.sqrt 2)⁻¹
theorem h_square : h^2 = 1/2 := by
  unfold h
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem two_h : 2*h=Real.sqrt 2 := by
  unfold h
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  apply (mul_right_cancel₀ hn)
  rw [mul_assoc,inv_mul_cancel₀ hn,mul_one]
  nlinarith [hs]

def gamma : Fin 5 → ℂ := ![0,0,0,1/2,Complex.I/2]
def delta (a b : ℝ) : Fin 5 → ℂ :=
  ![(h/2 : ℝ)+(b*h : ℝ)*Complex.I,
    (-h/2 : ℝ)+(b*h : ℝ)*Complex.I,
    -(2*a*h : ℝ)*Complex.I,0,0]
def e (a b : ℝ) : Fin 5 → ℝ := ![a,a,b,0,0]
def x (a b : ℝ) (j : Fin 5) : Fin 2 → ℂ := ![gamma j,delta a b j]
def y (a b : ℝ) (j : Fin 5) : Fin 2 → ℂ := ![conj (delta a b j),-conj (gamma j)]

theorem gamma_norm : (∑ j : Fin 5, Complex.normSq (gamma j)) = 1/2 := by
  norm_num [gamma,Fin.sum_univ_succ,Fin.succ,Complex.normSq_apply]

theorem delta_norm (a b : ℝ) (hab : 2*a^2+b^2=1/4) :
    (∑ j : Fin 5, Complex.normSq (delta a b j)) = 1/2 := by
  simp [delta,Fin.sum_univ_succ,Fin.succ,Complex.normSq_apply]
  ring_nf
  rw [h_square]
  nlinarith [hab]

theorem hermitian_orthogonal (a b : ℝ) :
    (∑ j : Fin 5, conj (gamma j) * delta a b j) = 0 := by
  simp [gamma,delta,Fin.sum_univ_succ,Fin.succ]

theorem bilinear (a b : ℝ) (hab : 2*a^2+b^2=1/4) :
    (∑ j : Fin 5, gamma j * gamma j) = 0 ∧
    (∑ j : Fin 5, delta a b j * delta a b j) = 0 ∧
    (∑ j : Fin 5, gamma j * delta a b j) = 0 := by
  constructor
  · apply Complex.ext <;>
      norm_num [gamma,Fin.sum_univ_succ,Fin.succ,Complex.mul_re,Complex.mul_im,
        Complex.div_re,Complex.div_im]
  constructor
  · apply Complex.ext
    · simp [delta,Fin.sum_univ_succ,Fin.succ,Complex.mul_re]
      ring_nf
      rw [h_square]
      nlinarith [hab]
    · simp [delta,Fin.sum_univ_succ,Fin.succ,Complex.mul_im]
      ring
  · simp [gamma,delta,Fin.sum_univ_succ,Fin.succ]

theorem real_gram (a b : ℝ) (hab : 2*a^2+b^2=1/4) (j k : Fin 5) :
    (∑ t : Fin 2, conj (x a b j t) * x a b k t).re =
      (if j=k then (1/4 : ℝ) else 0) - e a b j * e a b k := by
  fin_cases j <;> fin_cases k
  all_goals norm_num [x,gamma,delta,e,Fin.sum_univ_two,Complex.mul_re,
    Complex.conj_re,Complex.conj_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.star_def,Complex.div_re,Complex.div_im,map_ofNat]
  all_goals ring_nf
  all_goals try rw [h_square]
  all_goals nlinarith [hab]

def gram (u v : Fin 2 → ℂ) : ℂ := ∑ t : Fin 2, conj (u t) * v t

theorem gram_swap (a b : ℝ) (j k : Fin 5) :
    gram (x a b j) (x a b k) = gram (y a b k) (y a b j) := by
  simp [gram,x,y,Fin.sum_univ_two]
  ring

theorem cross_antisymmetric (a b : ℝ) (j k : Fin 5) :
    gram (x a b j) (y a b k) = -gram (x a b k) (y a b j) := by
  simp [gram,x,y,Fin.sum_univ_two]
  ring

theorem cross_formula (a b : ℝ) (j k : Fin 5) :
    gram (x a b j) (y a b k) =
      conj (gamma j * delta a b k - delta a b j * gamma k) := by
  simp [gram,x,y,Fin.sum_univ_two]
  ring

theorem tail_symmetric (a b : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : ∀ j k, M j k = M k j) :
    (∑ j : Fin 5, ∑ k : Fin 5, (M j k : ℂ) * gram (x a b j) (x a b k)) =
      (∑ j : Fin 5, ∑ k : Fin 5, (M j k : ℂ) * gram (y a b j) (y a b k)) ∧
    (∑ j : Fin 5, ∑ k : Fin 5, (M j k : ℂ) * gram (x a b j) (y a b k)) = 0 := by
  constructor
  · calc
      _ = ∑ j : Fin 5, ∑ k : Fin 5,
          (M k j : ℂ) * gram (x a b k) (x a b j) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hM k j,gram_swap]
  · have hs :
        (∑ j : Fin 5, ∑ k : Fin 5, (M j k : ℂ) * gram (x a b j) (y a b k)) =
        -(∑ j : Fin 5, ∑ k : Fin 5, (M j k : ℂ) * gram (x a b j) (y a b k)) := by
      calc
        _ = ∑ j : Fin 5, ∑ k : Fin 5,
            (M k j : ℂ) * gram (x a b k) (y a b j) := Finset.sum_comm
        _ = ∑ j : Fin 5, ∑ k : Fin 5,
            -((M j k : ℂ) * gram (x a b j) (y a b k)) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [hM k j,cross_antisymmetric,mul_neg]
        _ = _ := by simp only [Finset.sum_neg_distrib]
    linear_combination hs/2

theorem first_KL (a b : ℝ) (hab : 2*a^2+b^2=1/4) (i k : Fin 2) :
    (∑ j : Fin 5, x a b j i * conj (x a b j k)) = (if i=k then (1/2 : ℂ) else 0) ∧
    (∑ j : Fin 5, y a b j i * conj (y a b j k)) = (if i=k then (1/2 : ℂ) else 0) ∧
    (∑ j : Fin 5, y a b j i * conj (x a b j k)) = 0 := by
  fin_cases i <;> fin_cases k
  all_goals refine ⟨?_,?_,?_⟩
  all_goals apply Complex.ext
  all_goals norm_num [x,y,gamma,delta,Fin.sum_univ_succ,Fin.succ,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.div_re,Complex.div_im,Complex.star_def,map_ofNat]
  all_goals ring_nf
  all_goals try rw [h_square]
  all_goals nlinarith [hab]

def pathA (r : ℝ) : ℝ := Real.sqrt ((1-r)/12)
def pathB (r : ℝ) : ℝ := Real.sqrt ((1+2*r)/12)
def parameter (a b : ℝ) : ℝ := 1/2+8*(2*a^4+b^4)

theorem path_norm (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    2*(pathA r)^2+(pathB r)^2=1/4 := by
  unfold pathA pathB
  rw [Real.sq_sqrt (by linarith [hr.2]),Real.sq_sqrt (by linarith [hr.1])]
  ring

theorem path_parameter (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    parameter (pathA r) (pathB r)=2/3+r^2/3 := by
  unfold parameter pathA pathB
  rw [show (Real.sqrt ((1-r)/12))^4 = ((Real.sqrt ((1-r)/12))^2)^2 by ring,
    show (Real.sqrt ((1+2*r)/12))^4 = ((Real.sqrt ((1+2*r)/12))^2)^2 by ring,
    Real.sq_sqrt (by linarith [hr.2]),Real.sq_sqrt (by linarith [hr.1])]
  ring

theorem path_surjective (t : ℝ) (ht : t ∈ Set.Icc (2/3 : ℝ) 1) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, parameter (pathA r) (pathB r)=t := by
  have hn : 0 ≤ 3*t-2 := by linarith [ht.1]
  have hs := Real.sq_sqrt hn
  have hr : Real.sqrt (3*t-2) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_nonneg _
    · nlinarith [Real.sqrt_nonneg (3*t-2),ht.2]
  refine ⟨Real.sqrt (3*t-2),hr,?_⟩
  rw [path_parameter _ hr]
  nlinarith [hs]

end
end MainTheory.PrimitiveOrderTwoCatAlgebra
