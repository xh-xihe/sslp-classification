import MainTheory.CubicPhaseProjection
import MainTheory.OrderTwoScalarBridge
import SS.BridgeD3

/-! # The actual phase projection has the certificate's support/charge blocks

Six local fourth-root phases and a logical parity phase act on actual complex
amplitudes. In the XOR-zero cubic block their occupation profiles agree
exactly when the physical support and the logical charge agree.
-/

namespace MainTheory.Orbit3PhaseBlocks

open MainTheory.CubicPhaseProjection MainTheory.OrderTwoScalarBridge
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

abbrev PhaseSite := Fin 6 ⊕ Unit

def bits (s : SS.BitString 6) : PhaseSite → Bool
  | .inl j => s j
  | .inr _ => SS.bdot orbit3Mask s

theorem bits_bxor (a b : SS.BitString 6) (j : PhaseSite) :
    bits (SS.bxor a b) j = xor (bits a j) (bits b j) := by
  cases j with
  | inl j => rfl
  | inr j => exact SS.bdot_bxor_right orbit3Mask a b

def triple (a b : SS.BitString 6) : SS.BitString 6 × SS.BitString 6 × SS.BitString 6 :=
  (a, b, SS.bxor a b)

theorem occupation_apply (a b : SS.BitString 6) (j : PhaseSite) :
    occupation bits (triple a b) j = if bits a j || bits b j then 2 else 0 := by
  apply Fin.ext
  unfold occupation binaryProfile triple
  dsimp only
  simp only [bits_bxor]
  cases bits a j <;> cases bits b j <;> rfl

def support (a b : SS.BitString 6) : SS.BitString 6 := fun j => a j || b j

def charge (a b : SS.BitString 6) : ℤ :=
  (if SS.bdot orbit3Mask a then -1 else 1) +
    (if SS.bdot orbit3Mask b then -1 else 1) +
    (if SS.bdot orbit3Mask (SS.bxor a b) then -1 else 1)

theorem charge_apply (a b : SS.BitString 6) :
    charge a b = if SS.bdot orbit3Mask a || SS.bdot orbit3Mask b then -1 else 3 := by
  unfold charge
  rw [SS.bdot_bxor_right]
  cases SS.bdot orbit3Mask a <;> cases SS.bdot orbit3Mask b <;> decide

def block (a b : SS.BitString 6) : SS.BitString 6 × ℤ := (support a b, charge a b)

private theorem count_injective (a b : Bool) :
    (if a then (2 : Fin 4) else 0) = (if b then (2 : Fin 4) else 0) ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem charge_injective (a b : Bool) :
    (if a then (-1 : ℤ) else 3) = (if b then (-1 : ℤ) else 3) ↔ a = b := by
  cases a <;> cases b <;> decide

theorem occupation_eq_iff (a b c d : SS.BitString 6) :
    occupation bits (triple a b) = occupation bits (triple c d) ↔ block a b = block c d := by
  constructor
  · intro h
    apply Prod.ext
    · funext j
      have hj := congrFun h (.inl j)
      simp only [occupation_apply, bits] at hj
      exact (count_injective _ _).mp hj
    · have hj := congrFun h (.inr ())
      simp only [occupation_apply, bits] at hj
      change charge a b = charge c d
      rw [charge_apply, charge_apply, (count_injective _ _).mp hj]
  · intro h
    have hs := congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    change charge a b = charge c d at hc
    rw [charge_apply, charge_apply] at hc
    have hp := (charge_injective _ _).mp hc
    funext j
    rw [occupation_apply, occupation_apply]
    cases j with
    | inl j =>
      have hj := congrFun hs j
      change (a j || b j) = (c j || d j) at hj
      change (if a j || b j then (2 : Fin 4) else 0) =
        (if c j || d j then (2 : Fin 4) else 0)
      rw [hj]
    | inr j =>
      change (if SS.bdot orbit3Mask a || SS.bdot orbit3Mask b then (2 : Fin 4) else 0) =
        (if SS.bdot orbit3Mask c || SS.bdot orbit3Mask d then (2 : Fin 4) else 0)
      rw [hp]

theorem physical_moment_apply (w : SS.State 6 ℂ) (a b c d : SS.BitString 6) :
    moment bits (fun t : SS.BitString 6 × SS.BitString 6 => triple t.1 t.2) w (a, b) (c, d) =
      if block a b = block c d then (4 : ℝ) ^ 7 *
        (star (w a * w b * w (SS.bxor a b)) * (w c * w d * w (SS.bxor c d))).re else 0 := by
  rw [moment_apply]
  change (if occupation bits (triple a b) = occupation bits (triple c d) then
    (4 : ℝ) ^ Fintype.card PhaseSite *
      (star (w a * w b * w (SS.bxor a b)) * (w c * w d * w (SS.bxor c d))).re else 0) = _
  simp only [occupation_eq_iff]
  have hcard : Fintype.card PhaseSite = 7 := by decide
  rw [hcard]

theorem physical_moment_posSemidef (w : SS.State 6 ℂ) :
    (moment bits (fun t : SS.BitString 6 × SS.BitString 6 => triple t.1 t.2) w).PosSemidef :=
  moment_posSemidef _ _ _

end
end MainTheory.Orbit3PhaseBlocks
