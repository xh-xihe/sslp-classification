import Mathlib
import MainTheory.CubeAction

/-!
# Hamming-distance signatures for six-qubit moment skeletons

The final orbit reduction in Section 7 of `main.tex` keeps the logical order
and quotients a pair of Boolean fibres by cube isometries and interchange of
the two logical colours.  Before comparing full orbit keys, one can reject two
records whenever their Hamming-distance signatures differ.

For an individual fibre we count ordered pairs at each distance.  This avoids
choosing an arbitrary total order on Boolean strings; at every positive
distance it is exactly twice the unordered-pair count.  The two internal
histograms are themselves stored as a two-element multiset, so the signature
is genuinely insensitive to logical colour interchange.
-/

namespace MainTheory.DistanceSignature

open MainTheory.CubeAction

variable {n : ℕ}

/-- Distance bins `0, ..., n`. -/
abbrev Histogram (n : ℕ) := Fin (n + 1) → ℕ

/-- Ordered-pair distance distribution inside one fibre. -/
def internalHistogram (A : Finset (SS.BitString n)) : Histogram n :=
  fun d => ((A ×ˢ A).filter fun p => hammingDistance p.1 p.2 = d.1).card

/-- Cross-colour distance distribution.  Each pair has its first entry in
`A` and its second entry in `B`. -/
def crossHistogram (A B : Finset (SS.BitString n)) : Histogram n :=
  fun d => ((A ×ˢ B).filter fun p => hammingDistance p.1 p.2 = d.1).card

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm (x y : SS.BitString n) :
    hammingDistance x y = hammingDistance y x := by
  unfold hammingDistance
  rw [SS.bxor_comm]

@[simp] theorem pointEquiv_symm_actPoint (g : Parameter n)
    (x : SS.BitString n) :
    (pointEquiv g).symm (actPoint g x) = x := by
  change (pointEquiv g).symm ((pointEquiv g) x) = x
  exact (pointEquiv g).symm_apply_apply x

/-- The internal histogram is unchanged by a cube action. -/
theorem internalHistogram_actFibers (g : Parameter n) (F : FiberPair n)
    (c : Bool) :
    internalHistogram (actFibers g F c) =
      internalHistogram (F (actColor g c)) := by
  funext d
  unfold internalHistogram
  symm
  apply Finset.card_equiv
    (Equiv.prodCongr (pointEquiv g) (pointEquiv g))
  intro p
  simp [actFibers, hammingDistance_actPoint]

/-- The cross histogram is unchanged by the common cube isometry; the only
possible change is the order of the two old colours. -/
theorem crossHistogram_actFibers_raw (g : Parameter n) (F : FiberPair n) :
    crossHistogram (actFibers g F false) (actFibers g F true) =
      crossHistogram (F (actColor g false)) (F (actColor g true)) := by
  funext d
  unfold crossHistogram
  symm
  apply Finset.card_equiv
    (Equiv.prodCongr (pointEquiv g) (pointEquiv g))
  intro p
  simp [actFibers, hammingDistance_actPoint]

/-- Reversing the two colours does not change the cross-distance counts. -/
theorem crossHistogram_comm (A B : Finset (SS.BitString n)) :
    crossHistogram A B = crossHistogram B A := by
  funext d
  unfold crossHistogram
  apply Finset.card_equiv (Equiv.prodComm _ _)
  intro p
  simp [hammingDistance_comm, and_comm]

/-- Consequently the cross histogram is invariant under both the cube
isometry and the optional colour swap. -/
theorem crossHistogram_actFibers (g : Parameter n) (F : FiberPair n) :
    crossHistogram (actFibers g F false) (actFibers g F true) =
      crossHistogram (F false) (F true) := by
  rw [crossHistogram_actFibers_raw]
  cases hs : g.swap
  · simp [actColor, hs]
  · simpa [actColor, hs] using crossHistogram_comm (F true) (F false)

/-- The two same-colour histograms as an unordered pair. -/
def unorderedInternalHistograms (F : FiberPair n) : Multiset (Histogram n) :=
  {internalHistogram (F false), internalHistogram (F true)}

/-- The unordered pair of internal histograms is invariant under every cube
action and logical colour interchange. -/
theorem unorderedInternalHistograms_actFibers
    (g : Parameter n) (F : FiberPair n) :
    unorderedInternalHistograms (actFibers g F) =
      unorderedInternalHistograms F := by
  unfold unorderedInternalHistograms
  rw [internalHistogram_actFibers, internalHistogram_actFibers]
  cases hs : g.swap
  · simp [actColor, hs]
  · simpa [actColor, hs] using
      (Multiset.pair_comm (internalHistogram (F true))
        (internalHistogram (F false)))

/-- The exact invariant used as a cheap prefilter for the final six-qubit
orbit comparison.  The logical order is retained, as required by the meaning
of the 66 moment-skeleton classes in `main.tex`. -/
structure Signature (n : ℕ) where
  liftOrder : ℕ
  logicalOrder : ℕ
  internal : Multiset (Histogram n)
  cross : Histogram n
  deriving DecidableEq

/-- Fieldwise extensionality stated explicitly because the histogram fields
are functions; generated certificates use this theorem to avoid asking a
derived `DecidableEq` to transport through function extensionality proofs. -/
@[ext] theorem Signature.ext {s t : Signature n}
    (hlift : s.liftOrder = t.liftOrder)
    (hlogical : s.logicalOrder = t.logicalOrder)
    (hinternal : s.internal = t.internal)
    (hcross : s.cross = t.cross) : s = t := by
  cases s
  cases t
  simp_all

/-- Distance signature of one labelled fibre pair. -/
def signature (q m : ℕ) (F : FiberPair n) : Signature n where
  liftOrder := q
  logicalOrder := m
  internal := unorderedInternalHistograms F
  cross := crossHistogram (F false) (F true)

/-- The complete distance signature is invariant under coordinate
permutations, common XOR translations and logical colour interchange. -/
theorem signature_actFibers (q m : ℕ) (g : Parameter n) (F : FiberPair n) :
    signature q m (actFibers g F) = signature q m F := by
  unfold signature
  rw [unorderedInternalHistograms_actFibers, crossHistogram_actFibers]

/-- Equivalence of records with the logical order retained. -/
def LabeledEquivalent (q m : ℕ) (F : FiberPair n)
    (q' m' : ℕ) (G : FiberPair n) : Prop :=
  q = q' ∧ m = m' ∧ FiberEquivalent F G

theorem labeledEquivalent_refl (q m : ℕ) (F : FiberPair n) :
    LabeledEquivalent q m F q m F :=
  ⟨rfl, rfl, fiberEquivalent_refl F⟩

theorem labeledEquivalent_symm {q m q' m' : ℕ} {F G : FiberPair n}
    (h : LabeledEquivalent q m F q' m' G) :
    LabeledEquivalent q' m' G q m F :=
  ⟨h.1.symm, h.2.1.symm, fiberEquivalent_symm h.2.2⟩

theorem labeledEquivalent_trans {q m q' m' q'' m'' : ℕ} {F G H : FiberPair n}
    (h₁ : LabeledEquivalent q m F q' m' G)
    (h₂ : LabeledEquivalent q' m' G q'' m'' H) :
    LabeledEquivalent q m F q'' m'' H :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
    fiberEquivalent_trans h₁.2.2 h₂.2.2⟩

/-- Equivalent labelled fibre pairs have identical signatures. -/
theorem signature_eq_of_labeledEquivalent
    {q m q' m' : ℕ} {F G : FiberPair n}
    (h : LabeledEquivalent q m F q' m' G) :
    signature q m F = signature q' m' G := by
  obtain ⟨rfl, rfl, g, rfl⟩ := h
  exact (signature_actFibers q m g F).symm

/-- Distinct signatures certify that two labelled fibre pairs cannot be in
the same cube-isometry/colour-swap orbit.  This is the rejection theorem used
to avoid a brute-force `66 × 46,080` comparison. -/
theorem not_labeledEquivalent_of_signature_ne
    {q m q' m' : ℕ} {F G : FiberPair n}
    (h : signature q m F ≠ signature q' m' G) :
    ¬ LabeledEquivalent q m F q' m' G := by
  intro heq
  exact h (signature_eq_of_labeledEquivalent heq)

/-- Same-order specialization: different signatures imply ordinary fibre-pair
non-equivalence. -/
theorem not_fiberEquivalent_of_signature_ne
    {q m : ℕ} {F G : FiberPair n}
    (h : signature q m F ≠ signature q m G) :
    ¬ FiberEquivalent F G := by
  intro heq
  exact not_labeledEquivalent_of_signature_ne h ⟨rfl, rfl, heq⟩

end MainTheory.DistanceSignature
