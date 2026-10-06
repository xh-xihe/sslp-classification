import Mathlib

/-! # Kernel-reducible accumulation of integer polynomial coefficients

A fixed-depth tree permits logarithmic updates without an external evaluator.
The update theorem and fold theorem connect the computed coefficient tree to
the original list of signed coordinate terms, including repeated terms.
-/

namespace MainTheory.DyadicCoefficientTree

open scoped BigOperators

inductive Tree : ℕ → Type where
  | leaf (value : ℤ) : Tree 0
  | node {h : ℕ} (left right : Tree h) : Tree (h + 1)
deriving DecidableEq

def zero : (h : ℕ) → Tree h
  | 0 => .leaf 0
  | h + 1 => .node (zero h) (zero h)

def lookup : {h : ℕ} → Tree h → ℕ → ℤ
  | 0, .leaf v, _ => v
  | h + 1, .node l r, i => if i < 2 ^ h then lookup l i else lookup r (i - 2 ^ h)

def addAt : {h : ℕ} → Tree h → ℕ → ℤ → Tree h
  | 0, .leaf v, _, c => .leaf (v + c)
  | h + 1, .node l r, i, c =>
      if i < 2 ^ h then .node (addAt l i c) r else .node l (addAt r (i - 2 ^ h) c)

theorem zero_lookup (h i : ℕ) : lookup (zero h) i = 0 := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp only [zero, lookup]; split_ifs <;> apply ih

theorem lookup_addAt {h : ℕ} (t : Tree h) (i j : ℕ) (c : ℤ)
    (hi : i < 2 ^ h) (hj : j < 2 ^ h) :
    lookup (addAt t i c) j = lookup t j + if j = i then c else 0 := by
  induction t generalizing i j with
  | leaf v =>
    have hi0 : i = 0 := by simpa using hi
    have hj0 : j = 0 := by simpa using hj
    subst i; subst j
    simp [addAt, lookup]
  | @node h l r ihl ihr =>
    have hpow : 2 ^ (h + 1) = 2 ^ h + 2 ^ h := by rw [pow_succ]; omega
    by_cases hil : i < 2 ^ h <;> by_cases hjl : j < 2 ^ h
    · simp only [addAt, if_pos hil, lookup, if_pos hjl]
      exact ihl i j hil hjl
    · have hji : j ≠ i := by omega
      simp [addAt, lookup, hil, hjl, hji]
    · have hji : j ≠ i := by omega
      simp [addAt, lookup, hil, hjl, hji]
    · have hii : i - 2 ^ h < 2 ^ h := by rw [hpow] at hi; omega
      have hjj : j - 2 ^ h < 2 ^ h := by rw [hpow] at hj; omega
      have he : j - 2 ^ h = i - 2 ^ h ↔ j = i := by omega
      simp only [addAt, if_neg hil, lookup, if_neg hjl]
      simpa only [he] using ihr (i - 2 ^ h) (j - 2 ^ h) hii hjj

noncomputable def evaluate {h : ℕ} (t : Tree h) (y : Fin (2 ^ h) → ℝ) : ℝ :=
  ∑ j, (lookup t j.val : ℝ) * y j

theorem evaluate_zero (h : ℕ) (y : Fin (2 ^ h) → ℝ) : evaluate (zero h) y = 0 := by
  simp [evaluate, zero_lookup]

theorem evaluate_addAt {h : ℕ} (t : Tree h) (i : Fin (2 ^ h)) (c : ℤ)
    (y : Fin (2 ^ h) → ℝ) :
    evaluate (addAt t i.val c) y = evaluate t y + (c : ℝ) * y i := by
  unfold evaluate
  simp_rw [lookup_addAt t i.val _ c i.isLt (Fin.isLt _), Int.cast_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  have he (j : Fin (2 ^ h)) :
      ((if j.val = i.val then c else 0 : ℤ) : ℝ) * y j =
        if j = i then (c : ℝ) * y i else 0 := by
    by_cases hij : j = i
    · subst j; simp
    · have hv : j.val ≠ i.val := fun hv => hij (Fin.ext hv)
      simp [hij, hv]
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

def accumulate {h : ℕ} (t : Tree h) (terms : List (Fin (2 ^ h) × ℤ)) : Tree h :=
  terms.foldl (fun acc e => addAt acc e.1.val e.2) t

theorem evaluate_accumulate {h : ℕ} (t : Tree h) (terms : List (Fin (2 ^ h) × ℤ))
    (y : Fin (2 ^ h) → ℝ) :
    evaluate (accumulate t terms) y = evaluate t y +
      (terms.map fun e => (e.2 : ℝ) * y e.1).sum := by
  induction terms generalizing t with
  | nil => simp [accumulate]
  | cons e terms ih =>
    rw [accumulate, List.foldl_cons]
    change evaluate (accumulate (addAt t e.1.val e.2) terms) y = _
    rw [ih, evaluate_addAt]
    simp only [List.map_cons, List.sum_cons]
    ring

end MainTheory.DyadicCoefficientTree
