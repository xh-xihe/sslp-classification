import Mathlib

/-!
# Orbit 7: exhaustive support-mask reduction on `K_5`

If a four-vertex hafnian vanishes, its three matching monomials cannot have
exactly one nonzero term.  This file exhausts the resulting `2^10` support
masks.  It deliberately contains no amplitudes: the output consists of the
five support patterns used by the separate algebraic proof.

The explicit star and complete-graph witnesses at the end are regression
tests against a vacuous Boolean classifier.
-/

namespace SixQubit.Orbit7Mask

set_option maxHeartbeats 4000000

structure Mask where
  e01 : Bool
  e02 : Bool
  e03 : Bool
  e04 : Bool
  e12 : Bool
  e13 : Bool
  e14 : Bool
  e23 : Bool
  e24 : Bool
  e34 : Bool
  deriving DecidableEq

def edge (g : Mask) : Fin 5 → Fin 5 → Bool :=
  ![![false,g.e01,g.e02,g.e03,g.e04],
    ![g.e01,false,g.e12,g.e13,g.e14],
    ![g.e02,g.e12,false,g.e23,g.e24],
    ![g.e03,g.e13,g.e23,false,g.e34],
    ![g.e04,g.e14,g.e24,g.e34,false]]

def Adj (g : Mask) (i j : Fin 5) : Prop := edge g i j = true

def good3 (a b c : Bool) : Bool :=
  a.toNat + b.toNat + c.toNat != 1

/-- None of the five induced four-sets has exactly one active perfect
matching. -/
def AdmissibleB (g : Mask) : Bool :=
  good3 (g.e12 && g.e34) (g.e13 && g.e24) (g.e14 && g.e23) &&
  good3 (g.e02 && g.e34) (g.e03 && g.e24) (g.e04 && g.e23) &&
  good3 (g.e01 && g.e34) (g.e03 && g.e14) (g.e04 && g.e13) &&
  good3 (g.e01 && g.e24) (g.e02 && g.e14) (g.e04 && g.e12) &&
  good3 (g.e01 && g.e23) (g.e02 && g.e13) (g.e03 && g.e12)

def Isolated (g : Mask) : Prop :=
  ∃ s, ∀ t, t ≠ s → ¬ Adj g s t

def Full (g : Mask) : Prop :=
  ∀ i j, i ≠ j → Adj g i j

/-- All active edges lie in one star.  Outside the `Isolated` branch this is
exactly `K_{1,4}`. -/
def Centered (g : Mask) : Prop :=
  ∃ s, ∀ i j, Adj g i j → i = s ∨ j = s

def FiveDistinct (a b c d e : Fin 5) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
  b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
  c ≠ d ∧ c ≠ e ∧ d ≠ e

/-- The `K_{2,3}` / `K_5 \ K_3` contradiction template: all six cross
edges are active and all three edges in the three-vertex part are absent.
The edge in the two-vertex part is intentionally unrestricted. -/
def SparsePattern (g : Mask) : Prop :=
  ∃ a b c d e, FiveDistinct a b c d e ∧
    Adj g a c ∧ Adj g a d ∧ Adj g a e ∧
    Adj g b c ∧ Adj g b d ∧ Adj g b e ∧
    ¬ Adj g c d ∧ ¬ Adj g c e ∧ ¬ Adj g d e

/-- The `K_5 \ 2K_2` / `K_5 \ K_2` contradiction template: one missing
edge has all six cross edges from the other three vertices active. -/
def DensePattern (g : Mask) : Prop :=
  ∃ a b c d e, FiveDistinct a b c d e ∧
    ¬ Adj g d e ∧
    Adj g a d ∧ Adj g a e ∧
    Adj g b d ∧ Adj g b e ∧
    Adj g c d ∧ Adj g c e

def all5 (p : Fin 5 → Bool) : Bool :=
  p 0 && p 1 && p 2 && p 3 && p 4

def any5 (p : Fin 5 → Bool) : Bool :=
  p 0 || p 1 || p 2 || p 3 || p 4

lemma all5_eq_true (p : Fin 5 → Bool) :
    all5 p = true ↔ ∀ i, p i = true := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [all5]
  · intro h
    simp [all5, h]

lemma any5_of_eq_true (p : Fin 5 → Bool) (i : Fin 5) :
    p i = true → any5 p = true := by
  fin_cases i
  · intro h
    have h0 : p 0 = true := by simpa using h
    simp [any5, h0]
  · intro h
    have h1 : p 1 = true := by simpa using h
    simp [any5, h1]
  · intro h
    have h2 : p 2 = true := by simpa using h
    simp [any5, h2]
  · intro h
    have h3 : p 3 = true := by simpa using h
    simp [any5, h3]
  · intro h
    have h4 : p 4 = true := by simpa using h
    simp [any5, h4]

lemma any5_eq_true (p : Fin 5 → Bool) :
    any5 p = true ↔ ∃ i, p i = true := by
  constructor
  · intro h
    by_cases h0 : p 0 = true
    · exact ⟨0,h0⟩
    by_cases h1 : p 1 = true
    · exact ⟨1,h1⟩
    by_cases h2 : p 2 = true
    · exact ⟨2,h2⟩
    by_cases h3 : p 3 = true
    · exact ⟨3,h3⟩
    have h0f := Bool.eq_false_of_not_eq_true h0
    have h1f := Bool.eq_false_of_not_eq_true h1
    have h2f := Bool.eq_false_of_not_eq_true h2
    have h3f := Bool.eq_false_of_not_eq_true h3
    have h4 : p 4 = true := by simpa [any5,h0f,h1f,h2f,h3f] using h
    exact ⟨4,h4⟩
  · rintro ⟨i,hi⟩
    exact any5_of_eq_true p i hi

def isolatedB (g : Mask) : Bool :=
  any5 fun s => all5 fun t => (t == s) || !(edge g s t)

def fullB (g : Mask) : Bool :=
  all5 fun i => all5 fun j => (i == j) || edge g i j

def centeredB (g : Mask) : Bool :=
  any5 fun s => all5 fun i => all5 fun j =>
    !(edge g i j) || (i == s) || (j == s)

def fiveDistinctB (a b c d e : Fin 5) : Bool :=
  (a != b) && (a != c) && (a != d) && (a != e) &&
  (b != c) && (b != d) && (b != e) &&
  (c != d) && (c != e) && (d != e)

def sparseAtB (g : Mask) (a b c d e : Fin 5) : Bool :=
  fiveDistinctB a b c d e &&
  edge g a c && edge g a d && edge g a e &&
  edge g b c && edge g b d && edge g b e &&
  !(edge g c d) && !(edge g c e) && !(edge g d e)

def sparseB (g : Mask) : Bool :=
  any5 fun a => any5 fun b => any5 fun c => any5 fun d => any5 fun e =>
    sparseAtB g a b c d e

def denseAtB (g : Mask) (a b c d e : Fin 5) : Bool :=
  fiveDistinctB a b c d e && !(edge g d e) &&
  edge g a d && edge g a e && edge g b d && edge g b e &&
  edge g c d && edge g c e

def denseB (g : Mask) : Bool :=
  any5 fun a => any5 fun b => any5 fun c => any5 fun d => any5 fun e =>
    denseAtB g a b c d e

def resultB (g : Mask) : Bool :=
  isolatedB g || fullB g || centeredB g || sparseB g || denseB g

lemma isolatedB_eq_true (g : Mask) : isolatedB g = true ↔ Isolated g := by
  simp only [isolatedB, any5_eq_true, all5_eq_true]
  constructor
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    intro t hts hadj
    have ht := hs t
    simp [hts] at ht
    change edge g s t = true at hadj
    rw [hadj] at ht
    contradiction
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    intro t
    by_cases hts : t = s
    · simp [hts]
    · have hn := hs t hts
      simp [hts, Adj] at hn ⊢
      exact hn

lemma fullB_eq_true (g : Mask) : fullB g = true ↔ Full g := by
  simp only [fullB, all5_eq_true]
  constructor
  · intro h i j hij
    have hh := h i j
    simp [hij] at hh
    exact hh
  · intro h i j
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij, Adj] using h i j hij

lemma centeredB_eq_true (g : Mask) : centeredB g = true ↔ Centered g := by
  simp only [centeredB, any5_eq_true, all5_eq_true]
  constructor
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    intro i j hij
    have hh := hs i j
    change edge g i j = true at hij
    rw [hij] at hh
    simp at hh
    exact hh
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    intro i j
    by_cases hij : Adj g i j
    · rcases hs i j hij with hi | hj
      · change edge g i j = true at hij
        simp [hi]
      · change edge g i j = true at hij
        simp [hj]
    · change ¬ edge g i j = true at hij
      have hz : edge g i j = false := Bool.eq_false_of_not_eq_true hij
      simp [hz]

lemma fiveDistinctB_eq_true (a b c d e : Fin 5) :
    fiveDistinctB a b c d e = true ↔ FiveDistinct a b c d e := by
  simp [fiveDistinctB, FiveDistinct]
  tauto

lemma sparseAtB_eq_true (g : Mask) (a b c d e : Fin 5) :
    sparseAtB g a b c d e = true ↔
      FiveDistinct a b c d e ∧
      Adj g a c ∧ Adj g a d ∧ Adj g a e ∧
      Adj g b c ∧ Adj g b d ∧ Adj g b e ∧
      ¬ Adj g c d ∧ ¬ Adj g c e ∧ ¬ Adj g d e := by
  simp [sparseAtB, fiveDistinctB_eq_true, Adj]
  tauto

lemma denseAtB_eq_true (g : Mask) (a b c d e : Fin 5) :
    denseAtB g a b c d e = true ↔
      FiveDistinct a b c d e ∧ ¬ Adj g d e ∧
      Adj g a d ∧ Adj g a e ∧ Adj g b d ∧ Adj g b e ∧
      Adj g c d ∧ Adj g c e := by
  simp [denseAtB, fiveDistinctB_eq_true, Adj]
  tauto

lemma sparseB_eq_true (g : Mask) : sparseB g = true ↔ SparsePattern g := by
  simp only [sparseB, any5_eq_true]
  simp [SparsePattern, sparseAtB_eq_true]

lemma denseB_eq_true (g : Mask) : denseB g = true ↔ DensePattern g := by
  simp only [denseB, any5_eq_true]
  simp [DensePattern, denseAtB_eq_true]

lemma resultB_eq_true (g : Mask) :
    resultB g = true ↔
      Isolated g ∨ Full g ∨ Centered g ∨ SparsePattern g ∨ DensePattern g := by
  simp [resultB, isolatedB_eq_true, fullB_eq_true, centeredB_eq_true,
    sparseB_eq_true, denseB_eq_true]
  tauto

/-- The actual exhaustive kernel computation over all ten independent
Boolean edges. -/
theorem classify_bits :
    ∀ e01 e02 e03 e04 e12 e13 e14 e23 e24 e34 : Bool,
      let g : Mask := ⟨e01,e02,e03,e04,e12,e13,e14,e23,e24,e34⟩
      AdmissibleB g = true → resultB g = true := by
  decide

/-- Exhaustive support classification, packaged for an arbitrary mask. -/
theorem classify (g : Mask) (h : AdmissibleB g = true) :
    Isolated g ∨ Full g ∨ Centered g ∨ SparsePattern g ∨ DensePattern g := by
  rcases g with ⟨e01,e02,e03,e04,e12,e13,e14,e23,e24,e34⟩
  exact (resultB_eq_true _).mp
    (classify_bits e01 e02 e03 e04 e12 e13 e14 e23 e24 e34 h)

def star0 : Mask :=
  ⟨true,true,true,true,false,false,false,false,false,false⟩

def complete : Mask :=
  ⟨true,true,true,true,true,true,true,true,true,true⟩

def oneMatching : Mask :=
  ⟨false,false,false,false,true,false,false,false,false,true⟩

/-- Nonvacuity regression: the star support really reaches the classifier. -/
theorem star0_admissible : AdmissibleB star0 = true := by decide
theorem star0_centered : Centered star0 := by
  refine ⟨0, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [Adj, edge, star0] at hij ⊢

/-- Nonvacuity regression: the full-support branch also reaches it. -/
theorem complete_admissible : AdmissibleB complete = true := by decide
theorem complete_full : Full complete := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Adj, edge, complete]

/-- Negative regression: one lone perfect-matching monomial is rejected. -/
theorem oneMatching_rejected : AdmissibleB oneMatching = false := by decide

end SixQubit.Orbit7Mask
