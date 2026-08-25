import SixQubit.Orbit9Mask

namespace SixQubit.Orbit9Mask

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000 in
/-- The actual `2^15` kernel computation, phrased entirely in `Bool` and with
fifteen explicit binders. -/
theorem classify_bits :
    ∀ e01 e02 e03 e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 : Bool,
      let g : Mask :=
        ⟨e01, e02, e03, e04, e05, e12, e13, e14, e15,
          e23, e24, e25, e34, e35, e45⟩
      validB g = true → resultB g = true := by
  decide

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
