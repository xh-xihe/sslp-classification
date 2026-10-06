import Mathlib

/-! # Pure sparse binary lookup for finite certificate entries

The lookup is reducible and adds no axiom. Concrete certificate tables must
prove both their coverage and the mathematical property of every lookup.
-/

namespace MainTheory.SparseFiniteTable

inductive Tree (A : Type*) where
  | empty
  | node (key : ℕ) (value : A) (left right : Tree A)

def lookup {A : Type*} : Tree A → ℕ → Option A
  | .empty, _ => none
  | .node key value left right, n =>
      if n < key then lookup left n else if n = key then some value else lookup right n

end MainTheory.SparseFiniteTable
