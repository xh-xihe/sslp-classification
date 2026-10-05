import MainTheory.PrimitiveOrderTwoCatKL

/-! Physical scalar coefficients and their squared sum for the literal cat code. -/

namespace MainTheory.PrimitiveOrderTwoCatEnumerator
open MainTheory.PrimitiveOrderTwoCatAlgebra
open MainTheory.PrimitiveOrderTwoCatCompression
open MainTheory.PrimitiveOrderTwoCatEncoder
open MainTheory.PrimitiveOrderTwoCatKL
open Orbit2.TensorPauli
open scoped BigOperators Matrix Kronecker
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 16000000

def scalar (a b : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) : ℝ :=
  ∑ j,∑ k,M j k*((if j=k then (1/4 : ℝ) else 0)-e a b j*e a b k)

theorem real_tail_scalar (a b : ℝ) (hab : 2*a^2+b^2=1/4)
    (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : ∀ j k,M j k=M k j) :
    (spinors a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (fun j k => (M j k : ℂ)))*
      spinors a b=(scalar a b M : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  let T := (spinors a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (fun j k => (M j k : ℂ)))*spinors a b
  obtain ⟨l,hl⟩ := real_tail_KL a b M hM
  have h00 : T 0 0=l := by
    simpa [T,Matrix.smul_apply,smul_eq_mul] using congrArg (fun A => A 0 0) hl
  have hr : l.re=scalar a b M := by
    rw [← h00]
    unfold T
    rw [tail_entry]
    have hg (j k : Fin 5) : (gram (column a b 0 j) (column a b 0 k)).re=
        (if j=k then (1/4 : ℝ) else 0)-e a b j*e a b k := by
      simpa only [column,ite_true,gram] using real_gram a b hab j k
    simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,hg,scalar]
  have hH : Matrix.conjTranspose (fun j k : Fin 5 => (M j k : ℂ))=
      (fun j k => (M j k : ℂ)) := by
    ext j k
    simpa [Matrix.conjTranspose_apply] using congrArg Complex.ofReal (hM k j)
  have ht : T.conjTranspose=T := by
    simp only [T,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,hH,Matrix.mul_assoc]
  have hi : l.im=0 := by
    have he := congrArg (fun A => (A 0 0).im) ht
    simp only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_im,h00] at he
    linarith
  have he : l=(scalar a b M : ℂ) := Complex.ext hr (by simpa using hi)
  rw [he] at hl
  exact hl

def diagonalZZ (i j : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun r s => (if r=s then 1 else 0)-
    2*(if r=i ∧ s=i then 1 else 0)-2*(if r=j ∧ s=j then 1 else 0)

def offDiagonal (i j : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun r s => (if r=i ∧ s=j then 1 else 0)+(if r=j ∧ s=i then 1 else 0)

theorem e_squared_sum (a b : ℝ) (hab : 2*a^2+b^2=1/4) :
    (∑ j : Fin 5,(e a b j)^2)=1/4 := by
  norm_num [e,Fin.sum_univ_succ,Fin.succ]
  nlinarith [hab]

theorem diagonalZZ_scalar (a b : ℝ) (hab : 2*a^2+b^2=1/4) (i j : Fin 5) :
    scalar a b (diagonalZZ i j)=2*((e a b i)^2+(e a b j)^2) := by
  unfold scalar diagonalZZ
  simp only [sub_mul,Finset.sum_sub_distrib]
  simp [ite_mul,ite_and]
  have he := e_squared_sum a b hab
  simp only [pow_two] at he
  linarith

theorem offDiagonal_scalar (a b : ℝ) (i j : Fin 5) (hij : i≠j) :
    scalar a b (offDiagonal i j)=-2*e a b i*e a b j := by
  unfold scalar offDiagonal
  simp [add_mul,ite_mul,ite_and,Finset.sum_add_distrib,hij,Ne.symm hij]
  ring

theorem diagonalZZ_symmetric (i j : Fin 5) :
    ∀ r s,diagonalZZ i j r s=diagonalZZ i j s r := by
  intro r s
  simp [diagonalZZ,eq_comm,and_comm]

theorem offDiagonal_symmetric (i j : Fin 5) :
    ∀ r s,offDiagonal i j r s=offDiagonal i j s r := by
  intro r s
  simp [offDiagonal,and_comm,add_comm]

theorem ZZ_compression (a b : ℝ) (hab : 2*a^2+b^2=1/4)
    (i j : Fin 5) (hij : i≠j) :
    (encoder a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator (pair i j 3 3))*encoder a b=
        (2*((e a b i)^2+(e a b j)^2) : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hm : cats.conjTranspose*operator (pair i j 3 3)*cats=
      fun r s => (diagonalZZ i j r s : ℂ) := by
    ext r s
    rw [ZZ i j hij]
    simp only [diagonalZZ]
    split_ifs <;> norm_num
  rw [encoder_compression,hm,real_tail_scalar a b hab _ (diagonalZZ_symmetric i j),
    diagonalZZ_scalar a b hab]
  rfl

theorem XX_YY_compression (a b : ℝ) (hab : 2*a^2+b^2=1/4)
    (i j : Fin 5) (hij : i≠j) (p : Fin 2) :
    (encoder a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator (pair i j p.succ.castSucc p.succ.castSucc))*
      encoder a b=(-2*e a b i*e a b j : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hm : cats.conjTranspose*operator (pair i j p.succ.castSucc p.succ.castSucc)*cats=
      fun r s => (offDiagonal i j r s : ℂ) := by
    ext r s
    fin_cases p
    · change (cats.conjTranspose*operator (pair i j 1 1)*cats) r s= _
      rw [(XX_YY i j hij r s).1]; simp only [offDiagonal]; split_ifs <;> norm_num
    · change (cats.conjTranspose*operator (pair i j 2 2)*cats) r s= _
      rw [(XX_YY i j hij r s).2]; simp only [offDiagonal]; split_ifs <;> norm_num
  rw [encoder_compression,hm,real_tail_scalar a b hab _ (offDiagonal_symmetric i j),
    offDiagonal_scalar a b i j hij]
  rfl

def coefficient (a b : ℝ) (E : Matrix PhysicalBasis PhysicalBasis ℂ) : ℂ :=
  Matrix.trace ((encoder a b).conjTranspose*E*encoder a b)/2

theorem coefficient_projector (a b : ℝ) (E : Matrix PhysicalBasis PhysicalBasis ℂ) :
    coefficient a b E=Matrix.trace (encoder a b*(encoder a b).conjTranspose*E)/2 := by
  rw [coefficient,Matrix.trace_mul_cycle]

theorem coefficient_scalar (a b : ℝ) (E : Matrix PhysicalBasis PhysicalBasis ℂ)
    (l : ℂ) (hl : (encoder a b).conjTranspose*E*encoder a b=l • 1) :
    coefficient a b E=l := by
  rw [coefficient,hl,Matrix.trace_smul,Matrix.trace_one]
  norm_num

def tailPairScalar (a b : ℝ) (i j : Fin 5) (p q : Fin 3) : ℝ :=
  if p=q then (if p=2 then 2*((e a b i)^2+(e a b j)^2)
    else -2*e a b i*e a b j) else 0

theorem tail_pair_compression (a b : ℝ) (hab : 2*a^2+b^2=1/4)
    (i j : Fin 5) (hij : i≠j) (p q : Fin 3) :
    (encoder a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator (pair i j p.succ q.succ))*encoder a b=
        (tailPairScalar a b i j p q : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  by_cases hpq : p=q
  · subst q
    fin_cases p
    · simpa only [tailPairScalar,ite_true,show (0 : Fin 3)≠2 by decide,ite_false] using
        XX_YY_compression a b hab i j hij 0
    · simpa only [tailPairScalar,ite_true,show (1 : Fin 3)≠2 by decide,ite_false] using
        XX_YY_compression a b hab i j hij 1
    · simpa only [tailPairScalar,ite_true] using ZZ_compression a b hab i j hij
  · rw [encoder_compression,mixed_zero i j hij p q hpq,
      Matrix.kronecker_zero,Matrix.mul_zero,Matrix.zero_mul]
    simp [tailPairScalar,hpq]

theorem tail_pair_coefficient (a b : ℝ) (hab : 2*a^2+b^2=1/4)
    (i j : Fin 5) (hij : i≠j) (p q : Fin 3) :
    coefficient a b ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator (pair i j p.succ q.succ))=
      (tailPairScalar a b i j p q : ℂ) :=
  coefficient_scalar a b _ _ (tail_pair_compression a b hab i j hij p q)

theorem first_tail_coefficient (a b : ℝ) (i : Fin 5) (p q : Fin 3) :
    coefficient a b (localC p.succ ⊗ₖ operator (single i q.succ))=0 := by
  apply coefficient_scalar
  rw [encoder_compression,single_zero,Matrix.kronecker_zero,Matrix.mul_zero,
    Matrix.zero_mul]
  simp

theorem first_coefficient (a b : ℝ) (hab : 2*a^2+b^2=1/4) (p : Fin 3) :
    coefficient a b (localC p.succ ⊗ₖ (1 : Matrix Bits Bits ℂ))=0 := by
  apply coefficient_scalar
  rw [encoder_compression,Matrix.mul_one,orthonormal,first_pauli_KL a b hab]
  simp

theorem tail_coefficient (a b : ℝ) (i : Fin 5) (p : Fin 3) :
    coefficient a b ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator (single i p.succ))=0 := by
  apply coefficient_scalar
  rw [encoder_compression,single_zero,Matrix.kronecker_zero,Matrix.mul_zero,
    Matrix.zero_mul]
  simp

def A1 (a b : ℝ) : ℝ :=
  (∑ p : Fin 3,Complex.normSq (coefficient a b
    (localC p.succ ⊗ₖ (1 : Matrix Bits Bits ℂ))))+
  ∑ i : Fin 5,∑ p : Fin 3,Complex.normSq (coefficient a b
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator (single i p.succ)))

def A2 (a b : ℝ) : ℝ :=
  (∑ i : Fin 5,∑ p : Fin 3,∑ q : Fin 3,Complex.normSq (coefficient a b
    (localC p.succ ⊗ₖ operator (single i q.succ))))+
  ∑ i : Fin 5,∑ j : Fin 5,if i<j then
    ∑ p : Fin 3,∑ q : Fin 3,Complex.normSq (coefficient a b
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator (pair i j p.succ q.succ))) else 0

theorem A1_zero (a b : ℝ) (hab : 2*a^2+b^2=1/4) : A1 a b=0 := by
  simp [A1,first_coefficient a b hab,tail_coefficient]

def pairSquaredSum (a b : ℝ) : ℝ :=
  4*∑ i : Fin 5,∑ j : Fin 5,if i<j then
    ((e a b i)^2+(e a b j)^2)^2+2*(e a b i)^2*(e a b j)^2 else 0

theorem tail_pair_squared (a b : ℝ) (i j : Fin 5) :
    (∑ p : Fin 3,∑ q : Fin 3,(tailPairScalar a b i j p q)^2)=
      4*(((e a b i)^2+(e a b j)^2)^2+2*(e a b i)^2*(e a b j)^2) := by
  have h0 : (0 : Fin 3)≠2 := by decide
  have h1 : (1 : Fin 3)≠2 := by decide
  norm_num [tailPairScalar,Fin.sum_univ_three,h0,h1]
  ring

theorem A2_pair_sum (a b : ℝ) (hab : 2*a^2+b^2=1/4) : A2 a b=pairSquaredSum a b := by
  simp only [A2,first_tail_coefficient,map_zero,Finset.sum_const_zero,zero_add,
    pairSquaredSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i<j
  · simp only [hij,ite_true,tail_pair_coefficient a b hab i j (ne_of_lt hij),
      Complex.normSq_ofReal]
    simpa only [pow_two] using tail_pair_squared a b i j
  · simp [hij]

theorem sum_five {α : Type*} [AddCommMonoid α] (f : Fin 5 → α) :
    (∑ j : Fin 5,f j)=f 0+(f 1+f 2+f 3+f 4) := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_four]
  rfl

theorem e_values (a b : ℝ) :
    e a b 0=a ∧ e a b 1=a ∧ e a b 2=b ∧ e a b 3=0 ∧ e a b 4=0 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem pair_squared_polynomial (a b : ℝ) (hab : 2*a^2+b^2=1/4) :
    pairSquaredSum a b=1/2+8*(∑ j : Fin 5,(e a b j)^4) := by
  have hh := congrArg (fun r : ℝ => r^2) hab
  obtain ⟨h0,h1,h2,h3,h4⟩ := e_values a b
  simp only [pairSquaredSum,sum_five]
  norm_num [h0,h1,h2,h3,h4,Fin.lt_def,Fin.coe_ofNat_eq_mod]
  ring_nf at hh ⊢
  nlinarith [hh]

theorem A2_formula (a b : ℝ) (hab : 2*a^2+b^2=1/4) :
    A2 a b=1/2+8*(∑ j : Fin 5,(e a b j)^4) ∧ A2 a b=1/2+8*(2*a^4+b^4) := by
  have hA : A2 a b=1/2+8*(∑ j : Fin 5,(e a b j)^4) := by
    rw [A2_pair_sum a b hab,pair_squared_polynomial a b hab]
  refine ⟨hA,?_⟩
  rw [hA]
  obtain ⟨h0,h1,h2,h3,h4⟩ := e_values a b
  norm_num [sum_five,h0,h1,h2,h3,h4]
  ring

end
end MainTheory.PrimitiveOrderTwoCatEnumerator
