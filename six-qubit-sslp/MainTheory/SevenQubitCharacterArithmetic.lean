import QECC.ReducedRepresentative

/-! The exact Z4 x Z3 character and the physical order constraints. -/
namespace MainTheory.SevenQubitCharacterArithmetic

noncomputable section

def chiFn (a : ZMod 4 × ZMod 3) : ZMod 6 := (3 * a.1.val + 4 * a.2.val : ℕ)

theorem chi_add : ∀ a b, chiFn (a + b) = chiFn a + chiFn b := by decide +kernel

def chi : (ZMod 4 × ZMod 3) →+ ZMod 6 :=
  { toFun := chiFn
    map_zero' := by decide +kernel
    map_add' := chi_add }

theorem chi_surjective : Function.Surjective chiFn := by decide +kernel
theorem chi_kernel : ∀ a, chiFn a = 0 ↔ a = (0, 0) ∨ a = (2, 0) := by decide +kernel
theorem target_gcds : ∀ a, chiFn a = 1 →
    Nat.gcd 4 a.1.val = 1 ∧ Nat.gcd 3 a.2.val = 1 := by decide +kernel

theorem torsion_preimage {q : ℕ} [NeZero q] (hq : 0 < q)
    (u : QECC.LocalPhase) (hu : q • u = 0) :
    ∃ a : ZMod q, ZMod.toAddCircle a = u := by
  letI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨m, _hm, he⟩ := (AddCircle.nsmul_eq_zero_iff hq).mp hu
  refine ⟨(m : ZMod q), ?_⟩
  rw [ZMod.toAddCircle_natCast]
  simpa using he

theorem circle_character (a : ZMod 4) (b : ZMod 3) :
    2 • ZMod.toAddCircle a + 2 • ZMod.toAddCircle b = ZMod.toAddCircle (chiFn (a, b)) := by
  rw [ZMod.toAddCircle_apply a, ZMod.toAddCircle_apply b, chiFn,
    ZMod.toAddCircle_natCast, ← AddCircle.coe_nsmul, ← AddCircle.coe_nsmul,
    ← AddCircle.coe_add]
  congr 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem target_orders (a : ZMod 4) (b : ZMod 3) (h : chiFn (a, b) = 1) :
    addOrderOf a = 4 ∧ addOrderOf b = 3 := by
  obtain ⟨ha, hb⟩ := target_gcds (a, b) h
  constructor
  · rw [← ZMod.natCast_zmod_val a, ZMod.addOrderOf_coe a.val (by decide), ha]
  · rw [← ZMod.natCast_zmod_val b, ZMod.addOrderOf_coe b.val (by decide), hb]

theorem circle_target_orders (alpha beta : QECC.LocalPhase)
    (ha : 4 • alpha = 0) (hb : 3 • beta = 0)
    (ht : 2 • alpha + 2 • beta = ZMod.toAddCircle (1 : ZMod 6)) :
    addOrderOf alpha = 4 ∧ addOrderOf beta = 3 := by
  obtain ⟨a, rfl⟩ := torsion_preimage (by decide : 0 < 4) alpha ha
  obtain ⟨b, rfl⟩ := torsion_preimage (by decide : 0 < 3) beta hb
  rw [circle_character] at ht
  have he := ZMod.toAddCircle_injective 6 ht
  obtain ⟨ha, hb⟩ := target_orders a b he
  constructor
  · rw [addOrderOf_injective (ZMod.toAddCircle : ZMod 4 →+ QECC.LocalPhase)
      (ZMod.toAddCircle_injective 4), ha]
  · rw [addOrderOf_injective (ZMod.toAddCircle : ZMod 3 →+ QECC.LocalPhase)
      (ZMod.toAddCircle_injective 3), hb]

end
end MainTheory.SevenQubitCharacterArithmetic
