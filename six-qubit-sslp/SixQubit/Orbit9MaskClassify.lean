import SixQubit.Orbit9Mask

namespace SixQubit.Orbit9Mask

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- One eighth of the finite classification, with the first three mask bits
fixed.  Keeping each `decide` in a separate declaration bounds the lifetime of
Lean's reduction caches. -/
private abbrev ClassificationAt (e01 e02 e03 : Bool) : Prop :=
    ∀ e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 : Bool,
      let g : Mask :=
        ⟨e01, e02, e03, e04, e05, e12, e13, e14, e15,
          e23, e24, e25, e34, e35, e45⟩
      validB g = true → resultB g = true

private theorem classify_fff : ClassificationAt false false false := by decide
private theorem classify_fft : ClassificationAt false false true := by decide
private theorem classify_ftf : ClassificationAt false true false := by decide
private theorem classify_ftt : ClassificationAt false true true := by decide
private theorem classify_tff : ClassificationAt true false false := by decide
private theorem classify_tft : ClassificationAt true false true := by decide
private theorem classify_ttf : ClassificationAt true true false := by decide
private theorem classify_ttt : ClassificationAt true true true := by decide

/-- The actual `2^15` kernel computation, phrased entirely in `Bool` and with
fifteen explicit binders.  It is assembled from eight disjoint `2^12` kernel
computations to keep peak memory bounded. -/
theorem classify_bits :
    ∀ e01 e02 e03 e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 : Bool,
      let g : Mask :=
        ⟨e01, e02, e03, e04, e05, e12, e13, e14, e15,
          e23, e24, e25, e34, e35, e45⟩
      validB g = true → resultB g = true := by
  intro e01 e02 e03 e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45
  dsimp
  intro h
  cases e01 <;> cases e02 <;> cases e03
  · exact classify_fff e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h
  · exact classify_fft e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h
  · exact classify_ftf e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h
  · exact classify_ftt e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h
  · exact classify_tff e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h
  · exact classify_tft e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h
  · exact classify_ttf e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h
  · exact classify_ttt e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 h

theorem classify_bool (g : Mask) (h : validB g = true) : resultB g = true := by
  rcases g with ⟨e01, e02, e03, e04, e05, e12, e13, e14, e15,
    e23, e24, e25, e34, e35, e45⟩
  exact classify_bits e01 e02 e03 e04 e05 e12 e13 e14 e15
    e23 e24 e25 e34 e35 e45 h

/-- Mathematical form of the finite classification.  Both the antecedent and
the conclusion cross explicit Bool/Prop reflection theorems; the kernel
computation is not used as an untyped oracle. -/
theorem classify (g : Mask) (h : Valid g) : Result g :=
  (resultB_iff g).mp (classify_bool g ((validB_iff g).mpr h))

end SixQubit.Orbit9Mask
