import Mathlib

/-! # A pure balanced lookup representation for finite certificate data

This is a reducible tree, with ordinary kernel reduction only. Concrete
tables are still checked against their mathematical definitions over every
bounded input; the tree supplies no truth oracle or certification axiom.
-/

namespace MainTheory.BalancedFiniteTable

inductive Tree (A : Type*) where
  | leaf (value : A)
  | node (split : ℕ) (left right : Tree A)

def lookup {A : Type*} : Tree A → ℕ → A
  | .leaf value, _ => value
  | .node split left right, n =>
      if n < split then lookup left n else lookup right (n - split)

theorem lookup_left {A : Type*} (left right : Tree A) (split n : ℕ) (h : n < split) :
    lookup (.node split left right) n = lookup left n := by
  simp only [lookup, if_pos h]

theorem lookup_right {A : Type*} (left right : Tree A) (split n : ℕ) (h : ¬n < split) :
    lookup (.node split left right) n = lookup right (n - split) := by
  simp only [lookup, if_neg h]

end MainTheory.BalancedFiniteTable
