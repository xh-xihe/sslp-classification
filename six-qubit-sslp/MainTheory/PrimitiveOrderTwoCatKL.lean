import MainTheory.PrimitiveOrderTwoCatEncoder
import Orbit2.FiveQubit

/-! Full physical KL compression of the literal five-cat encoder. The
finite Pauli support statements concern the actual cat matrix, while the
coefficient identities retain arbitrary real normalized parameters.
-/

namespace MainTheory.PrimitiveOrderTwoCatKL
open MainTheory.PrimitiveOrderTwoCatAlgebra
open MainTheory.PrimitiveOrderTwoCatCompression
open MainTheory.PrimitiveOrderTwoCatEncoder
open Orbit2.TensorPauli
open scoped BigOperators Matrix Kronecker ComplexConjugate
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 16000000

theorem single_real (i : Fin 5) (p : Fin 4) (j k : Fin 5) :
    (rawCompression (single i p) j k).im=0 ∧
      (rawCompression (single i p) j k).re=(rawCompression (single i p) k j).re := by
  rcases Fin.eq_zero_or_eq_succ p with hp | ⟨q,hp⟩
  · have hi : single i 0=(fun _ => 0) := by funext l; simp [single]
    rw [hp,hi,identity_raw,identity_raw]
    by_cases hj : j=k <;> simp [hj,eq_comm]
  · rw [hp,single_raw,single_raw]
    norm_num

theorem pair_real (i j : Fin 5) (hij : i≠j) (p q : Fin 4) (r s : Fin 5) :
    (rawCompression (pair i j p q) r s).im=0 ∧
      (rawCompression (pair i j p q) r s).re=(rawCompression (pair i j p q) s r).re := by
  rcases Fin.eq_zero_or_eq_succ p with hp | ⟨p',hp⟩
  · have he : pair i j 0 q=single j q := by
      funext l
      by_cases hi : l=i <;> by_cases hj : l=j
      all_goals simp_all [pair,single]
    rw [hp,he]
    exact single_real j q r s
  rcases Fin.eq_zero_or_eq_succ q with hq | ⟨q',hq⟩
  · have he : pair i j p 0=single i p := by funext l; simp [pair,single]
    rw [hq,he]
    exact single_real i p r s
  rw [hp,hq]
  by_cases heq : p'=q'
  · subst q'
    fin_cases p'
    · change (rawCompression (pair i j 1 1) r s).im=0 ∧
        (rawCompression (pair i j 1 1) r s).re=(rawCompression (pair i j 1 1) s r).re
      rw [(XX_YY_raw i j hij r s).1,(XX_YY_raw i j hij s r).1]
      constructor
      · split_ifs <;> norm_num
      · simp [or_comm,and_comm]
    · change (rawCompression (pair i j 2 2) r s).im=0 ∧
        (rawCompression (pair i j 2 2) r s).re=(rawCompression (pair i j 2 2) s r).re
      rw [(XX_YY_raw i j hij r s).2,(XX_YY_raw i j hij s r).2]
      constructor
      · split_ifs <;> norm_num
      · simp [or_comm,and_comm]
    · change (rawCompression (pair i j 3 3) r s).im=0 ∧
        (rawCompression (pair i j 3 3) r s).re=(rawCompression (pair i j 3 3) s r).re
      rw [ZZ_raw i j hij r s,ZZ_raw i j hij s r]
      by_cases hrs : r=s
      · subst s; split_ifs <;> norm_num
      · simp [hrs,Ne.symm hrs]
  · rw [mixed_raw i j hij p' q' heq r s,mixed_raw i j hij p' q' heq s r]
    norm_num

theorem small_label (p : Label 5) (hp : Orbit2.FiveQubit.weight p≤2) :
    p=(fun _ => 0) ∨ (∃ i,p=single i (p i)) ∨
      (∃ i j,i≠j ∧ p=pair i j (p i) (p j)) := by
  let S := Finset.univ.filter (fun i : Fin 5 => p i≠0)
  have hc : S.card=Orbit2.FiveQubit.weight p := by
    simp only [S,Finset.card_filter,Orbit2.FiveQubit.weight]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i=0 <;> simp [hi]
  have hout (i : Fin 5) (hi : i∉S) : p i=0 := by simpa [S] using hi
  have cases : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases cases with h0 | h1 | h2
  · left
    have hS := Finset.card_eq_zero.mp h0
    funext i
    exact hout i (by simp [hS])
  · right; left
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h1
    refine ⟨i,?_⟩
    funext k
    by_cases hk : k=i
    · simp [single,hk]
    · simp [single,hk,hout k (by simp [hi,hk])]
  · right; right
    obtain ⟨i,j,hij,hS⟩ := Finset.card_eq_two.mp h2
    refine ⟨i,j,hij,?_⟩
    funext k
    by_cases hki : k=i
    · subst k; simp [pair]
    by_cases hkj : k=j
    · subst k; simp [pair,Ne.symm hij]
    · simp [pair,hki,hkj,hout k (by simp [hS,hki,hkj])]

theorem small_tail_raw (p : Label 5) (hp : Orbit2.FiveQubit.weight p≤2)
    (j k : Fin 5) : (rawCompression p j k).im=0 ∧
      (rawCompression p j k).re=(rawCompression p k j).re := by
  rcases small_label p hp with h | ⟨i,h⟩ | ⟨i,l,hil,h⟩
  · rw [h,identity_raw,identity_raw]
    by_cases hj : j=k <;> simp [hj,eq_comm]
  · rw [h]; exact single_real i (p i) j k
  · rw [h]; exact pair_real i l hil (p i) (p l) j k

def tailReal (p : Label 5) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun j k => (rawCompression p j k).re/2

theorem tail_symmetric_real (p : Label 5) (hp : Orbit2.FiveQubit.weight p≤2) :
    (∀ j k,tailReal p j k=tailReal p k j) ∧
    cats.conjTranspose*operator p*cats=fun j k => (tailReal p j k : ℂ) := by
  constructor
  · intro j k
    unfold tailReal
    rw [(small_tail_raw p hp j k).2]
  · ext j k
    rw [compression]
    simp only [tailReal,GaussianInt.toComplex_def,(small_tail_raw p hp j k).1,
      Int.cast_zero,zero_mul,add_zero,Complex.ofReal_div]
    norm_cast

def column (a b : ℝ) (q : Fin 2) (j : Fin 5) : Fin 2 → ℂ :=
  if q=0 then x a b j else y a b j

theorem spinors_column (a b : ℝ) (ij : Fin 2 × Fin 5) (q : Fin 2) :
    spinors a b ij q=column a b q ij.2 ij.1 := by
  by_cases hq : q=0 <;> simp [spinors,column,hq]

theorem tail_entry (a b : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) (q r : Fin 2) :
    ((spinors a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (fun j k => (M j k : ℂ)))*
      spinors a b) q r=
    ∑ j : Fin 5,∑ k : Fin 5,(M j k : ℂ)*gram (column a b q j) (column a b r k) := by
  norm_num [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Matrix.kronecker_apply,Matrix.one_apply,spinors_column,gram,
    Fin.sum_univ_succ,Fin.succ,Complex.star_def]
  ring

theorem real_tail_KL (a b : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : ∀ j k,M j k=M k j) :
    ∃ l : ℂ,(spinors a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (fun j k => (M j k : ℂ)))*
      spinors a b=l • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  let T := (spinors a b).conjTranspose*
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (fun j k => (M j k : ℂ)))*spinors a b
  have hxy := tail_symmetric a b M hM
  have hd : T 0 0=T 1 1 := by simpa [T,tail_entry,column] using hxy.1
  have hz : T 0 1=0 := by simpa [T,tail_entry,column] using hxy.2
  have hH : Matrix.conjTranspose (fun j k : Fin 5 => (M j k : ℂ))=
      (fun j k => (M j k : ℂ)) := by
    ext j k
    simpa [Matrix.conjTranspose_apply] using congrArg Complex.ofReal (hM k j)
  have ht : T.conjTranspose=T := by
    simp only [T,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,hH,Matrix.mul_assoc]
  have h10 : T 1 0=0 := by
    have he := congrArg (fun A => A 1 0) ht
    simpa [Matrix.conjTranspose_apply,hz] using he.symm
  refine ⟨T 0 0,?_⟩
  change T= _
  ext q r
  fin_cases q <;> fin_cases r <;>
    simp [Matrix.smul_apply,smul_eq_mul,hz,h10,← hd]

theorem first_pauli_KL (a b : ℝ) (hab : 2*a^2+b^2=1/4) (p : Fin 4) :
    (spinors a b).conjTranspose*(localC p ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ))*
      spinors a b=if p=0 then 1 else 0 := by
  fin_cases p
  · simpa [localC_zero,Matrix.one_kronecker_one] using spinors_isometry a b hab
  all_goals ext q r
  all_goals fin_cases q <;> fin_cases r
  all_goals apply Complex.ext
  all_goals norm_num [Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.kronecker_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ,
    Matrix.one_apply,Matrix.zero_apply,spinors,x,y,gamma,delta,localC,localG,
    GaussianInt.toComplex_def,Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.div_re,Complex.div_im,Complex.star_def,map_ofNat]
  all_goals ring_nf
  all_goals try rw [h_square]
  all_goals nlinarith [hab]

theorem one_label (p : Label 5) (hp : Orbit2.FiveQubit.weight p≤1)
    (hne : p≠(fun _ => 0)) : ∃ i : Fin 5,∃ q : Fin 3,p=single i q.succ := by
  let S := Finset.univ.filter (fun i : Fin 5 => p i≠0)
  have hc : S.card=Orbit2.FiveQubit.weight p := by
    simp only [S,Finset.card_filter,Orbit2.FiveQubit.weight]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i=0 <;> simp [hi]
  obtain ⟨i,hi⟩ : ∃ i,p i≠0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have him : i∈S := by simp [S,hi]
  obtain ⟨q,hq⟩ := Fin.eq_succ_of_ne_zero hi
  refine ⟨i,q,?_⟩
  funext k
  by_cases hk : k=i
  · subst k; simp [single,hq]
  · have hk0 : p k=0 := by
      by_contra hkn
      have hkm : k∈S := by simp [S,hkn]
      exact hk ((Finset.card_le_one.mp (by omega : S.card≤1)) k hkm i him)
    simp [single,hk,hk0]

theorem one_tail_zero (p : Label 5) (hp : Orbit2.FiveQubit.weight p≤1)
    (hne : p≠(fun _ => 0)) : cats.conjTranspose*operator p*cats=0 := by
  obtain ⟨i,q,hp'⟩ := one_label p hp hne
  rw [hp']
  exact single_zero i q

def tail (p : Label 6) : Label 5 := fun i => p i.succ
def totalWeight (p : Label 6) : ℕ := ∑ i,if p i=0 then 0 else 1
def physicalPauli (p : Label 6) : Matrix PhysicalBasis PhysicalBasis ℂ :=
  localC (p 0) ⊗ₖ operator (tail p)

theorem weight_split (p : Label 6) :
    totalWeight p=(if p 0=0 then 0 else 1)+Orbit2.FiveQubit.weight (tail p) := by
  simp [totalWeight,Orbit2.FiveQubit.weight,tail,Fin.sum_univ_succ]

theorem full_KL (a b : ℝ) (hab : 2*a^2+b^2=1/4) (p : Label 6)
    (hp : totalWeight p≤2) : ∃ l : ℂ,
      (encoder a b).conjTranspose*physicalPauli p*encoder a b=
        l • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [physicalPauli,encoder_compression]
  have hw := weight_split p
  by_cases hp0 : p 0=0
  · have ht : Orbit2.FiveQubit.weight (tail p)≤2 := by simp [hp0] at hw; omega
    obtain ⟨hs,hm⟩ := tail_symmetric_real (tail p) ht
    rw [hp0,localC_zero,hm]
    exact real_tail_KL a b (tailReal (tail p)) hs
  · have ht : Orbit2.FiveQubit.weight (tail p)≤1 := by simp [hp0] at hw; omega
    by_cases htail : tail p=(fun _ => 0)
    · rw [htail,operator_zero,Matrix.mul_one,orthonormal,
        first_pauli_KL a b hab,if_neg hp0]
      exact ⟨0,by simp⟩
    · rw [one_tail_zero (tail p) ht htail,Matrix.kronecker_zero,
        Matrix.mul_zero,Matrix.zero_mul]
      exact ⟨0,by simp⟩

end
end MainTheory.PrimitiveOrderTwoCatKL
