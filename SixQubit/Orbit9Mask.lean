import SixQubit.Orbit9Graph

/-!
# Orbit 9: finite support-mask classification

This file contains only the finite combinatorics of a symmetric graph on six
vertices.  Its fifteen Boolean fields are the zero/nonzero mask of the
component-specific edge matrix.  The exhaustive theorem is proved by kernel
reduction (`decide`), over exactly `2^15` masks; no complex amplitudes or
floating-point computation occur here.
-/

namespace SixQubit.Orbit9Mask

set_option maxSynthPendingDepth 100
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-- The fifteen independent entries of a symmetric loopless graph on six
labelled vertices. -/
structure Mask where
  e01 : Bool
  e02 : Bool
  e03 : Bool
  e04 : Bool
  e05 : Bool
  e12 : Bool
  e13 : Bool
  e14 : Bool
  e15 : Bool
  e23 : Bool
  e24 : Bool
  e25 : Bool
  e34 : Bool
  e35 : Bool
  e45 : Bool
  deriving DecidableEq

def edge (g : Mask) : Fin 6 → Fin 6 → Bool :=
  ![![false, g.e01, g.e02, g.e03, g.e04, g.e05],
    ![g.e01, false, g.e12, g.e13, g.e14, g.e15],
    ![g.e02, g.e12, false, g.e23, g.e24, g.e25],
    ![g.e03, g.e13, g.e23, false, g.e34, g.e35],
    ![g.e04, g.e14, g.e24, g.e34, false, g.e45],
    ![g.e05, g.e15, g.e25, g.e35, g.e45, false]]

def Adj (g : Mask) (i j : Fin 6) : Prop := edge g i j = true

def TriangleClosed (g : Mask) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    Adj g i j → Adj g i k → Adj g j k

/-- Every active edge has a third vertex adjacent to one endpoint.  Together
with triangle closure this excludes a two-vertex component. -/
def NoK2Component (g : Mask) : Prop :=
  ∀ i j, Adj g i j → ∃ k, k ≠ i ∧ k ≠ j ∧ Adj g i k

/-- An active triangle has an edge leaving it. -/
def NoK3Component (g : Mask) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    Adj g i j → Adj g i k → Adj g j k →
      ∃ l, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧
        (Adj g i l ∨ Adj g j l ∨ Adj g k l)

/-- A complete graph on the five vertices other than `t` has a crossing edge
to `t`; equivalently, no connected component is a `K_5`. -/
def NoK5Component (g : Mask) : Prop :=
  ∀ t, (∀ i j, i ≠ t → j ≠ t → i ≠ j → Adj g i j) →
    ∃ i, i ≠ t ∧ Adj g t i

def NoK6 (g : Mask) : Prop :=
  ¬ ∀ i j, i ≠ j → Adj g i j

def K4Component (g : Mask) (i j k l : Fin 6) : Prop :=
  i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
  Adj g i j ∧ Adj g i k ∧ Adj g i l ∧
  Adj g j k ∧ Adj g j l ∧ Adj g k l ∧
  ∀ t, t ≠ i → t ≠ j → t ≠ k → t ≠ l →
    ¬ Adj g i t ∧ ¬ Adj g j t ∧ ¬ Adj g k t ∧ ¬ Adj g l t

theorem edge_symm (g : Mask) (i j : Fin 6) : edge g i j = edge g j i := by
  fin_cases i <;> fin_cases j <;> rfl

def Valid (g : Mask) : Prop :=
  TriangleClosed g ∧ NoK2Component g ∧ NoK3Component g ∧
    NoK5Component g ∧ NoK6 g

def Result (g : Mask) : Prop :=
  ∀ i j, Adj g i j → ∃ k l, K4Component g i j k l

def all6 (p : Fin 6 → Bool) : Bool :=
  p 0 && p 1 && p 2 && p 3 && p 4 && p 5
def any6 (p : Fin 6 → Bool) : Bool :=
  p 0 || p 1 || p 2 || p 3 || p 4 || p 5

def triangleCellB (g : Mask) (i j k : Fin 6) : Bool :=
    !((i != j) && (i != k) && (j != k) && edge g i j && edge g i k) ||
      edge g j k

def triangleClosedB (g : Mask) : Bool :=
  all6 fun i => all6 fun j => all6 fun k => triangleCellB g i j k

def noK2ComponentB (g : Mask) : Bool :=
  all6 fun i => all6 fun j =>
    !(edge g i j) || any6 fun k =>
      (k != i) && (k != j) && edge g i k

def noK3ComponentB (g : Mask) : Bool :=
  all6 fun i => all6 fun j => all6 fun k =>
    !((i != j) && (i != k) && (j != k) &&
      edge g i j && edge g i k && edge g j k) ||
    any6 fun l => (l != i) && (l != j) && (l != k) &&
      (edge g i l || edge g j l || edge g k l)

def completeOtherB (g : Mask) (t : Fin 6) : Bool :=
  all6 fun i => all6 fun j =>
    (i == t) || (j == t) || (i == j) || edge g i j

def crossingB (g : Mask) (t : Fin 6) : Bool :=
  any6 fun i => (i != t) && edge g t i

def noK5ComponentB (g : Mask) : Bool :=
  all6 fun t => !(completeOtherB g t) || crossingB g t

def complete6B (g : Mask) : Bool :=
  all6 fun i => all6 fun j => (i == j) || edge g i j

def noK6B (g : Mask) : Bool := !(complete6B g)

def isolated4B (g : Mask) (i j k l : Fin 6) : Bool :=
  all6 fun t => (t == i) || (t == j) || (t == k) || (t == l) ||
    (!(edge g i t) && !(edge g j t) && !(edge g k t) && !(edge g l t))

def k4ComponentB (g : Mask) (i j k l : Fin 6) : Bool :=
  (i != j) && (i != k) && (i != l) && (j != k) && (j != l) && (k != l) &&
  edge g i j && edge g i k && edge g i l &&
  edge g j k && edge g j l && edge g k l &&
  isolated4B g i j k l

def validB (g : Mask) : Bool :=
  triangleClosedB g && noK2ComponentB g && noK3ComponentB g &&
    noK5ComponentB g && noK6B g

def resultB (g : Mask) : Bool :=
  all6 fun i => all6 fun j =>
    !(edge g i j) || any6 fun k => any6 fun l => k4ComponentB g i j k l

/-- A nonempty regression fixture: the `K_4` on vertices `0,1,2,3`.  These
checks prevent the finite theorem from becoming vacuous through an overly
strong Boolean antecedent. -/
def k4Example : Mask :=
  ⟨true, true, true, false, false, true, true, false, false,
    true, false, false, false, false, false⟩

theorem k4Example_valid : validB k4Example = true := by decide
theorem k4Example_result : resultB k4Example = true := by decide

/-- A second regression fixture: a single nonzero edge is not a valid
component mask (it is a forbidden two-vertex component).  Together with
`k4Example_valid`, this checks both polarities of the executable guard. -/
def singleEdgeExample : Mask :=
  ⟨true, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false⟩
theorem singleEdgeExample_nonempty : edge singleEdgeExample 0 1 = true := rfl
theorem singleEdgeExample_invalid : validB singleEdgeExample = false := by decide

lemma triangleCellB_of_closed (g : Mask) (h : TriangleClosed g)
    (i j k : Fin 6) : triangleCellB g i j k = true := by
  by_cases hij : i = j
  · simp [triangleCellB, hij]
  by_cases hik : i = k
  · simp [triangleCellB, hik]
  by_cases hjk : j = k
  · simp [triangleCellB, hjk]
  by_cases hijE : edge g i j = true
  · by_cases hikE : edge g i k = true
    · have hjkE := h i j k hij hik hjk hijE hikE
      change edge g j k = true at hjkE
      simp [triangleCellB, hjkE]
    · simp [triangleCellB, hikE]
  · simp [triangleCellB, hijE]

lemma all6_eq_true_iff (p : Fin 6 → Bool) :
    all6 p = true ↔ ∀ i, p i = true := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [all6]
  · intro h
    simp [all6, h]

lemma any6_eq_true_iff (p : Fin 6 → Bool) :
    any6 p = true ↔ ∃ i, p i = true := by
  constructor
  · intro h
    by_cases h0 : p 0 = true
    · exact ⟨0, h0⟩
    by_cases h1 : p 1 = true
    · exact ⟨1, h1⟩
    by_cases h2 : p 2 = true
    · exact ⟨2, h2⟩
    by_cases h3 : p 3 = true
    · exact ⟨3, h3⟩
    by_cases h4 : p 4 = true
    · exact ⟨4, h4⟩
    have hf0 := Bool.eq_false_of_not_eq_true h0
    have hf1 := Bool.eq_false_of_not_eq_true h1
    have hf2 := Bool.eq_false_of_not_eq_true h2
    have hf3 := Bool.eq_false_of_not_eq_true h3
    have hf4 := Bool.eq_false_of_not_eq_true h4
    refine ⟨5, ?_⟩
    simpa [any6, hf0, hf1, hf2, hf3, hf4] using h
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [any6]

/-- The executable guard and the mathematical triangle-closure predicate have
exactly the same distinctness hypotheses. -/
theorem triangleClosedB_iff (g : Mask) :
    triangleClosedB g = true ↔ TriangleClosed g := by
  constructor
  · intro hb i j k hij hik hjk hijE hikE
    change edge g i j = true at hijE
    change edge g i k = true at hikE
    have hc : triangleCellB g i j k = true :=
      (all6_eq_true_iff _).mp ((all6_eq_true_iff _).mp
        ((all6_eq_true_iff _).mp hb i) j) k
    have hc' : (edge g i j = false ∨ edge g i k = false) ∨
        edge g j k = true := by
      simpa [triangleCellB, hij, hik, hjk] using hc
    rcases hc' with (hfalse | hfalse) | hjkE
    · rw [hijE] at hfalse
      contradiction
    · rw [hikE] at hfalse
      contradiction
    · exact hjkE
  · intro h
    apply (all6_eq_true_iff _).mpr
    intro i
    apply (all6_eq_true_iff _).mpr
    intro j
    apply (all6_eq_true_iff _).mpr
    intro k
    exact triangleCellB_of_closed g h i j k

theorem noK2ComponentB_iff (g : Mask) :
    noK2ComponentB g = true ↔ NoK2Component g := by
  constructor
  · intro hb i j hijE
    change edge g i j = true at hijE
    have hc := (all6_eq_true_iff _).mp ((all6_eq_true_iff _).mp hb i) j
    have ha : any6 (fun k => (k != i) && (k != j) && edge g i k) = true := by
      simpa [noK2ComponentB, hijE] using hc
    rcases (any6_eq_true_iff _).mp ha with ⟨k, hk⟩
    have hk' : (k ≠ i ∧ k ≠ j) ∧ edge g i k = true := by
      simpa using hk
    exact ⟨k, hk'.1.1, hk'.1.2, hk'.2⟩
  · intro h
    apply (all6_eq_true_iff _).mpr
    intro i
    apply (all6_eq_true_iff _).mpr
    intro j
    by_cases hijE : edge g i j = true
    · have ha : Adj g i j := hijE
      rcases h i j ha with ⟨k, hki, hkj, hikE⟩
      change edge g i k = true at hikE
      have hany : any6 (fun k => (k != i) && (k != j) && edge g i k) = true :=
        (any6_eq_true_iff _).mpr ⟨k, by simp [hki, hkj, hikE]⟩
      simp [hijE, hany]
    · simp [hijE]

lemma noK3CellB_of_prop (g : Mask) (h : NoK3Component g)
    (i j k : Fin 6) :
    (!((i != j) && (i != k) && (j != k) &&
      edge g i j && edge g i k && edge g j k) ||
    any6 fun l => (l != i) && (l != j) && (l != k) &&
      (edge g i l || edge g j l || edge g k l)) = true := by
  by_cases hij : i = j
  · simp [hij]
  by_cases hik : i = k
  · simp [hik]
  by_cases hjk : j = k
  · simp [hjk]
  by_cases hijE : edge g i j = true
  · by_cases hikE : edge g i k = true
    · by_cases hjkE : edge g j k = true
      · have hout := h i j k hij hik hjk hijE hikE hjkE
        rcases hout with ⟨l, hli, hlj, hlk, hl⟩
        have hany : any6 (fun l => (l != i) && (l != j) && (l != k) &&
            (edge g i l || edge g j l || edge g k l)) = true := by
          apply (any6_eq_true_iff _).mpr
          refine ⟨l, ?_⟩
          rcases hl with hil | hjl | hkl
          · change edge g i l = true at hil
            simp [hli, hlj, hlk, hil]
          · change edge g j l = true at hjl
            simp [hli, hlj, hlk, hjl]
          · change edge g k l = true at hkl
            simp [hli, hlj, hlk, hkl]
        simp [hany]
      · simp [hjkE]
    · simp [hikE]
  · simp [hijE]

theorem noK3ComponentB_iff (g : Mask) :
    noK3ComponentB g = true ↔ NoK3Component g := by
  constructor
  · intro hb i j k hij hik hjk hijE hikE hjkE
    change edge g i j = true at hijE
    change edge g i k = true at hikE
    change edge g j k = true at hjkE
    have hc := (all6_eq_true_iff _).mp ((all6_eq_true_iff _).mp
      ((all6_eq_true_iff _).mp hb i) j) k
    have ha : any6 (fun l => (l != i) && (l != j) && (l != k) &&
        (edge g i l || edge g j l || edge g k l)) = true := by
      simpa [noK3ComponentB, hij, hik, hjk, hijE, hikE, hjkE] using hc
    rcases (any6_eq_true_iff _).mp ha with ⟨l, hl⟩
    have hl' : (((l ≠ i ∧ l ≠ j) ∧ l ≠ k) ∧
        ((edge g i l = true ∨ edge g j l = true) ∨ edge g k l = true)) := by
      simpa using hl
    refine ⟨l, hl'.1.1.1, hl'.1.1.2, hl'.1.2, ?_⟩
    rcases hl'.2 with (hil | hjl) | hkl
    · exact Or.inl hil
    · exact Or.inr (Or.inl hjl)
    · exact Or.inr (Or.inr hkl)
  · intro h
    apply (all6_eq_true_iff _).mpr
    intro i
    apply (all6_eq_true_iff _).mpr
    intro j
    apply (all6_eq_true_iff _).mpr
    intro k
    exact noK3CellB_of_prop g h i j k

lemma completeOtherB_iff (g : Mask) (t : Fin 6) :
    completeOtherB g t = true ↔
      ∀ i j, i ≠ t → j ≠ t → i ≠ j → Adj g i j := by
  constructor
  · intro hb i j hit hjt hij
    have hc := (all6_eq_true_iff _).mp
      ((all6_eq_true_iff _).mp hb i) j
    change edge g i j = true
    simpa [completeOtherB, hit, hjt, hij] using hc
  · intro h
    unfold completeOtherB
    apply (all6_eq_true_iff _).mpr
    intro i
    apply (all6_eq_true_iff _).mpr
    intro j
    by_cases hit : i = t
    · simp [hit]
    by_cases hjt : j = t
    · simp [hjt]
    by_cases hij : i = j
    · simp [hij]
    have he := h i j hit hjt hij
    change edge g i j = true at he
    simp [he]

lemma crossingB_iff (g : Mask) (t : Fin 6) :
    crossingB g t = true ↔ ∃ i, i ≠ t ∧ Adj g t i := by
  constructor
  · intro hb
    rcases (any6_eq_true_iff _).mp hb with ⟨i, hi⟩
    have hi' : i ≠ t ∧ edge g t i = true := by
      simpa [crossingB] using hi
    exact ⟨i, hi'.1, hi'.2⟩
  · rintro ⟨i, hit, hi⟩
    apply (any6_eq_true_iff _).mpr
    refine ⟨i, ?_⟩
    change edge g t i = true at hi
    simp [hit, hi]

theorem noK5ComponentB_iff (g : Mask) :
    noK5ComponentB g = true ↔ NoK5Component g := by
  constructor
  · intro hb t hcomplete
    have ht := (all6_eq_true_iff _).mp hb t
    have hc : completeOtherB g t = true :=
      (completeOtherB_iff g t).mpr hcomplete
    have hx : crossingB g t = true := by
      simpa [noK5ComponentB, hc] using ht
    exact (crossingB_iff g t).mp hx
  · intro h
    unfold noK5ComponentB
    apply (all6_eq_true_iff _).mpr
    intro t
    by_cases hc : completeOtherB g t = true
    · have hx : crossingB g t = true :=
        (crossingB_iff g t).mpr (h t ((completeOtherB_iff g t).mp hc))
      simp [hc, hx]
    · have hcf : completeOtherB g t = false :=
        Bool.eq_false_of_not_eq_true hc
      simp [hcf]

lemma complete6B_iff (g : Mask) :
    complete6B g = true ↔ ∀ i j, i ≠ j → Adj g i j := by
  constructor
  · intro hb i j hij
    have hc := (all6_eq_true_iff _).mp
      ((all6_eq_true_iff _).mp hb i) j
    change edge g i j = true
    simpa [complete6B, hij] using hc
  · intro h
    unfold complete6B
    apply (all6_eq_true_iff _).mpr
    intro i
    apply (all6_eq_true_iff _).mpr
    intro j
    by_cases hij : i = j
    · simp [hij]
    have he := h i j hij
    change edge g i j = true at he
    simp [he]

theorem noK6B_iff (g : Mask) : noK6B g = true ↔ NoK6 g := by
  constructor
  · intro hb hcomplete
    have hc : complete6B g = true := (complete6B_iff g).mpr hcomplete
    simp [noK6B, hc] at hb
  · intro h
    by_cases hc : complete6B g = true
    · exact False.elim (h ((complete6B_iff g).mp hc))
    · have hcf : complete6B g = false := Bool.eq_false_of_not_eq_true hc
      simp [noK6B, hcf]

theorem validB_iff (g : Mask) : validB g = true ↔ Valid g := by
  simp only [validB, Bool.and_eq_true, triangleClosedB_iff,
    noK2ComponentB_iff, noK3ComponentB_iff, noK5ComponentB_iff, noK6B_iff]
  constructor
  · rintro ⟨⟨⟨⟨ht, h2⟩, h3⟩, h5⟩, h6⟩
    exact ⟨ht, h2, h3, h5, h6⟩
  · rintro ⟨ht, h2, h3, h5, h6⟩
    exact ⟨⟨⟨⟨ht, h2⟩, h3⟩, h5⟩, h6⟩

lemma isolated4B_iff (g : Mask) (i j k l : Fin 6) :
    isolated4B g i j k l = true ↔
      ∀ t, t ≠ i → t ≠ j → t ≠ k → t ≠ l →
        ¬ Adj g i t ∧ ¬ Adj g j t ∧ ¬ Adj g k t ∧ ¬ Adj g l t := by
  constructor
  · intro hb t hti htj htk htl
    have ht := (all6_eq_true_iff _).mp hb t
    have ht' : (((edge g i t = false ∧ edge g j t = false) ∧
        edge g k t = false) ∧ edge g l t = false) := by
      simpa [isolated4B, hti, htj, htk, htl] using ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Adj, ht'.1.1.1]
    · simp [Adj, ht'.1.1.2]
    · simp [Adj, ht'.1.2]
    · simp [Adj, ht'.2]
  · intro h
    unfold isolated4B
    apply (all6_eq_true_iff _).mpr
    intro t
    by_cases hti : t = i
    · simp [hti]
    by_cases htj : t = j
    · simp [htj]
    by_cases htk : t = k
    · simp [htk]
    by_cases htl : t = l
    · simp [htl]
    rcases h t hti htj htk htl with ⟨hi, hj, hk, hl⟩
    have hif : edge g i t = false := Bool.eq_false_of_not_eq_true hi
    have hjf : edge g j t = false := Bool.eq_false_of_not_eq_true hj
    have hkf : edge g k t = false := Bool.eq_false_of_not_eq_true hk
    have hlf : edge g l t = false := Bool.eq_false_of_not_eq_true hl
    simp [hif, hjf, hkf, hlf]

theorem k4ComponentB_iff (g : Mask) (i j k l : Fin 6) :
    k4ComponentB g i j k l = true ↔ K4Component g i j k l := by
  simp [k4ComponentB, K4Component, isolated4B_iff, Adj, and_assoc]

theorem resultB_iff (g : Mask) : resultB g = true ↔ Result g := by
  constructor
  · intro hb i j hijE
    change edge g i j = true at hijE
    have hc := (all6_eq_true_iff _).mp ((all6_eq_true_iff _).mp hb i) j
    have ha : any6 (fun k => any6 fun l => k4ComponentB g i j k l) = true := by
      simpa [resultB, hijE] using hc
    rcases (any6_eq_true_iff _).mp ha with ⟨k, hk⟩
    rcases (any6_eq_true_iff _).mp hk with ⟨l, hl⟩
    exact ⟨k, l, (k4ComponentB_iff g i j k l).mp hl⟩
  · intro h
    unfold resultB
    apply (all6_eq_true_iff _).mpr
    intro i
    apply (all6_eq_true_iff _).mpr
    intro j
    by_cases hijE : edge g i j = true
    · rcases h i j hijE with ⟨k, l, hk4⟩
      have hl : k4ComponentB g i j k l = true :=
        (k4ComponentB_iff g i j k l).mpr hk4
      have hk : any6 (fun l => k4ComponentB g i j k l) = true :=
        (any6_eq_true_iff _).mpr ⟨l, hl⟩
      have ha : any6 (fun k => any6 fun l => k4ComponentB g i j k l) = true :=
        (any6_eq_true_iff _).mpr ⟨k, hk⟩
      simp [hijE, ha]
    · simp [hijE]

end SixQubit.Orbit9Mask
