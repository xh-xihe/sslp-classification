import MainTheory.ClassificationLevels
import SS.Basic

/-!
# Two clauses of Section 3 that were stated and not proved

**`(q, a)` and `(rq, ra)` have the same fibres.**  The remark "What is actually
bounded" says "Replacing `(q,a)` by `(rq,ra)` gives the same local phases and
the same subset-sum fibers".  `PrimitiveReduction` covers the local-phase half,
and only in the reduction direction; the fibre half -- that
`S_b(a;q) = S_{rb}(ra;rq)` as subsets of `{0,1}^n` -- was nowhere.  It is what
licenses the whole primitivity reduction to be a *relabelling* rather than a
restriction: nothing about the two supports changes when the modulus is
inflated.

The scaling map `ZMod q -> ZMod (r*q)`, `x |-> r * x`, is not a ring
homomorphism, which is presumably why it was never written down.  It is an
injective additive one, and that is all the subset-sum weight needs, since the
bits are `0` and `1`.

**`m | q` for an arbitrary finite lift.**  `thm:finite-projective-group` says
"if `m` is its projective logical order and `q` is the order of *any* finite
physical lift, then `m | q`".  Every Lean form of that clause quantifies over
*primitive* lifts (`GeneralLiftOrder.orderOf_dvd_of_hasPrimitiveLift` requires
`Gate.Primitive`).  Without primitivity it is still true and shorter: the class
map is a group homomorphism, so a lift killed by `q` has a class killed by `q`.
-/

namespace MainTheory.ScaledModulusFibres

open MainTheory.ClassificationLevels

/-! ## Inflating the modulus -/

variable {n q r : ℕ}

/-- `x |-> r * x`, from residues mod `q` to residues mod `r * q`. -/
def scale (r q : ℕ) (x : ZMod q) : ZMod (r * q) := ((r * x.val : ℕ) : ZMod (r * q))

theorem scale_eq_iff [NeZero q] (hr : 0 < r) (x y : ZMod q) :
    scale r q x = scale r q y ↔ x = y := by
  constructor
  · intro h
    have hmod : (r * x.val) ≡ (r * y.val) [MOD r * q] := by
      simpa [scale] using (ZMod.natCast_eq_natCast_iff _ _ _).1 h
    have hdvd : ((r * q : ℕ) : ℤ) ∣ ((r * y.val : ℕ) : ℤ) - ((r * x.val : ℕ) : ℤ) :=
      (Nat.modEq_iff_dvd).1 hmod
    have hr0 : ((r : ℤ)) ≠ 0 := by exact_mod_cast hr.ne'
    have hq : ((q : ℕ) : ℤ) ∣ ((y.val : ℤ) - (x.val : ℤ)) := by
      have hrw : ((r * y.val : ℕ) : ℤ) - ((r * x.val : ℕ) : ℤ)
          = (r : ℤ) * ((y.val : ℤ) - (x.val : ℤ)) := by push_cast; ring
      rw [hrw, Nat.cast_mul] at hdvd
      exact (mul_dvd_mul_iff_left hr0).1 hdvd
    have : x.val ≡ y.val [MOD q] := (Nat.modEq_iff_dvd).2 hq
    have hx := (ZMod.natCast_eq_natCast_iff _ _ _).2 this
    simpa [ZMod.natCast_val, ZMod.cast_id] using hx
  · rintro rfl; rfl

theorem scale_add [NeZero q] (x y : ZMod q) :
    scale r q (x + y) = scale r q x + scale r q y := by
  have h : ((x + y).val : ℕ) ≡ x.val + y.val [MOD q] := by
    have := (ZMod.natCast_eq_natCast_iff ((x + y).val) (x.val + y.val) q).1 (by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      ring)
    exact this
  have hmod : r * ((x + y).val) ≡ r * (x.val + y.val) [MOD r * q] :=
    Nat.ModEq.mul_left' r h
  have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  simpa [scale, Nat.mul_add] using this

theorem scale_zero [NeZero q] : scale r q 0 = 0 := by
  simp [scale]

/-- Scaling is an additive homomorphism; it is not a ring one, which is
presumably why it was never written down. -/
def scaleHom (r q : ℕ) [NeZero q] : ZMod q →+ ZMod (r * q) where
  toFun := scale r q
  map_zero' := scale_zero
  map_add' := scale_add

/-- **The subset-sum weight is carried by the scaling map.** -/
theorem weight_scale [NeZero q] (a : Fin n → ZMod q) (s : SS.BitString n) :
    SS.weight (fun j => scale r q (a j)) s = scale r q (SS.weight a s) := by
  classical
  show SS.weight (fun j => scaleHom r q (a j)) s = scaleHom r q (SS.weight a s)
  unfold SS.weight
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases s j
  · simp [SS.bit]
  · simp [SS.bit]

/-- **The fibres do not move when the modulus is inflated.**

`S_b(a;q) = S_{rb}(ra;rq)`, the half of the remark that was missing. -/
theorem Sk_scale [NeZero q] (hr : 0 < r) (a : Fin n → ZMod q) (b : ZMod q) :
    SS.Sk (fun j => scale r q (a j)) (scale r q b) = SS.Sk a b := by
  ext s
  simp only [SS.mem_Sk, weight_scale]
  exact scale_eq_iff hr _ _

/-! ## `m | q` for an arbitrary finite lift -/

/-- **`thm:finite-projective-group`'s divisibility, without primitivity.**

If a diagonal symmetry is killed by `q`, so is its projective class, and hence
the class's order divides `q`.  The existing forms of this clause all ask the
lift to be primitive; the paper asks only that it be finite. -/
theorem orderOf_intrinsicClass_dvd {P : CodeProjector n}
    (u : diagonalSymmetryGroup P) (q : ℕ) (h : u ^ q = 1) :
    orderOf (intrinsicClass P u) ∣ q := by
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [intrinsicClass, ← QuotientGroup.mk_pow, h]
  rfl

end MainTheory.ScaledModulusFibres
