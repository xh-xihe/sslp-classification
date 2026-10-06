import MainTheory.PrimitiveOrderTwoCatAlgebra
import Orbit2.TensorPauli

/-! Physical five-qubit cat compressions. The finite Gaussian calculations
are connected to the normalized tensor-Pauli matrices, rather than treated
as assumed compression data.
-/

namespace MainTheory.PrimitiveOrderTwoCatCompression
noncomputable section
open Orbit2.TensorPauli MainTheory.PrimitiveOrderTwoCatAlgebra
open scoped BigOperators Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev Bits := Fin 5 → Fin 2
def unit (j : Fin 5) : Bits := fun i => if i=j then 1 else 0
def complement (s : Bits) : Bits := fun i => if s i=0 then 1 else 0
def tensorG (p : Label 5) (s t : Bits) : GaussianInt :=
  ∏ i : Fin 5, localG (p i) (s i) (t i)
def rawCompression (p : Label 5) (j k : Fin 5) : GaussianInt :=
  tensorG p (unit j) (unit k) + tensorG p (unit j) (complement (unit k)) +
  tensorG p (complement (unit j)) (unit k) +
  tensorG p (complement (unit j)) (complement (unit k))

def cats : Matrix Bits (Fin 5) ℂ := fun s j =>
  (h : ℂ) * ((if s=unit j then 1 else 0) +
    (if s=complement (unit j) then 1 else 0))

theorem tensorG_complex (p : Label 5) (s t : Bits) :
    (tensorG p s t : ℂ) = operator p s t := by
  simp [tensorG,operator,tensor,localC]

theorem cats_star (s : Bits) (j : Fin 5) : star (cats s j) = cats s j := by
  by_cases hs : s=unit j <;> by_cases ht : s=complement (unit j)
  all_goals simp [cats,hs,ht]

theorem sum_cats (j : Fin 5) (f : Bits → ℂ) :
    (∑ s : Bits, cats s j * f s) = (h : ℂ)*(f (unit j)+f (complement (unit j))) := by
  calc
    _ = (h : ℂ) * ∑ s : Bits,
        ((if s=unit j then 1 else 0)+(if s=complement (unit j) then 1 else 0))*f s := by
      simp only [cats,mul_assoc,Finset.mul_sum]
    _ = _ := by simp [add_mul,ite_mul,Finset.sum_add_distrib]

theorem compression (p : Label 5) (j k : Fin 5) :
    (cats.conjTranspose * operator p * cats) j k =
      (rawCompression p j k : ℂ)/2 := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,cats_star]
  simp_rw [mul_comm _ (cats _ k)]
  rw [sum_cats]
  simp only [sum_cats]
  have hh : (h : ℂ)*(h : ℂ)=(1/2 : ℂ) := by
    rw [← Complex.ofReal_mul,show h*h=(1/2 : ℝ) by nlinarith [h_square]]
    norm_num
  simp only [rawCompression,map_add,tensorG_complex]
  calc
    _ = ((h : ℂ)*(h : ℂ)) *
        (operator p (unit j) (unit k)+operator p (unit j) (complement (unit k))+
         operator p (complement (unit j)) (unit k)+
         operator p (complement (unit j)) (complement (unit k))) := by ring
    _ = _ := by rw [hh]; ring

def single (i : Fin 5) (p : Fin 4) : Label 5 := fun j => if j=i then p else 0
def pair (i j : Fin 5) (p q : Fin 4) : Label 5 :=
  fun k => if k=i then p else if k=j then q else 0

theorem identity_raw : ∀ j k : Fin 5,
    rawCompression (fun _ => 0) j k = if j=k then 2 else 0 := by decide +kernel

theorem single_raw : ∀ i : Fin 5, ∀ p : Fin 3, ∀ j k : Fin 5,
    rawCompression (single i p.succ) j k = 0 := by decide +kernel

theorem ZZ_raw : ∀ i j : Fin 5, i≠j → ∀ r s : Fin 5,
    rawCompression (pair i j 3 3) r s =
      if r=s then (if r=i ∨ r=j then -2 else 2) else 0 := by decide +kernel

theorem XX_YY_raw : ∀ i j : Fin 5, i≠j → ∀ r s : Fin 5,
    rawCompression (pair i j 1 1) r s =
      (if (r=i ∧ s=j) ∨ (r=j ∧ s=i) then 2 else 0) ∧
    rawCompression (pair i j 2 2) r s =
      (if (r=i ∧ s=j) ∨ (r=j ∧ s=i) then 2 else 0) := by decide +kernel

theorem mixed_raw : ∀ i j : Fin 5, i≠j → ∀ p q : Fin 3, p≠q → ∀ r s : Fin 5,
    rawCompression (pair i j p.succ q.succ) r s=0 := by decide +kernel

theorem orthonormal : cats.conjTranspose*cats=1 := by
  have hc := compression (fun _ => 0)
  rw [operator_zero,Matrix.mul_one] at hc
  ext j k
  rw [hc,identity_raw]
  by_cases hj : j=k <;> norm_num [hj,Matrix.one_apply,GaussianInt.toComplex_def]

theorem single_zero (i : Fin 5) (p : Fin 3) :
    cats.conjTranspose*operator (single i p.succ)*cats=0 := by
  ext j k
  rw [compression,single_raw]
  norm_num

theorem ZZ (i j : Fin 5) (hij : i≠j) (r s : Fin 5) :
    (cats.conjTranspose*operator (pair i j 3 3)*cats) r s =
      (if r=s then (1 : ℂ) else 0) -
      2*(if r=i ∧ s=i then 1 else 0)-2*(if r=j ∧ s=j then 1 else 0) := by
  rw [compression,ZZ_raw i j hij]
  by_cases hrs : r=s <;> by_cases hri : r=i <;> by_cases hrj : r=j
  all_goals subst_vars
  all_goals norm_num [* ,GaussianInt.toComplex_def] <;> tauto

theorem XX_YY (i j : Fin 5) (hij : i≠j) (r s : Fin 5) :
    (cats.conjTranspose*operator (pair i j 1 1)*cats) r s =
      (if r=i ∧ s=j then (1 : ℂ) else 0)+(if r=j ∧ s=i then 1 else 0) ∧
    (cats.conjTranspose*operator (pair i j 2 2)*cats) r s =
      (if r=i ∧ s=j then (1 : ℂ) else 0)+(if r=j ∧ s=i then 1 else 0) := by
  have hh := XX_YY_raw i j hij r s
  rw [compression,compression,hh.1,hh.2]
  by_cases ha : r=i ∧ s=j <;> by_cases hb : r=j ∧ s=i
  all_goals norm_num [ha,hb,GaussianInt.toComplex_def] <;> tauto

theorem mixed_zero (i j : Fin 5) (hij : i≠j) (p q : Fin 3) (hpq : p≠q) :
    cats.conjTranspose*operator (pair i j p.succ q.succ)*cats=0 := by
  ext r s
  rw [compression,mixed_raw i j hij p q hpq]
  norm_num

end
end MainTheory.PrimitiveOrderTwoCatCompression
