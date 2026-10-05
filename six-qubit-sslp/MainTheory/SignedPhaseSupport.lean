import Mathlib

/-! Signed support graphs: explicit colourings or odd closed walks.
The obstruction is valid for nonzero complex phases, not just signs.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MainTheory.SignedPhaseSupport

structure Edge (n : ℕ) where
  left : Fin n
  right : Fin n
  negative : Bool
  deriving DecidableEq

def sign (negative : Bool) (z : ℂ) : ℂ := if negative then -z else z

theorem sign_sign (a b : Bool) (z : ℂ) : sign a (sign b z) = sign (xor a b) z := by
  cases a <;> cases b <;> simp [sign]

def Assignment {n : ℕ} (support : Finset (Fin n)) (edges : List (Edge n))
    (phase : Fin n → ℂ) : Prop :=
  (∀ v ∈ support, phase v ≠ 0) ∧
  ∀ edge ∈ edges, phase edge.left = sign edge.negative (phase edge.right)

def Compatible {n : ℕ} (support : Finset (Fin n)) (edges : List (Edge n)) : Prop :=
  ∃ phase, Assignment support edges phase

def ValidWalk {n : ℕ} (edges : List (Edge n)) (start : Fin n) : List (Bool × Fin n) → Prop
  | [] => True
  | (negative,next)::rest =>
    (⟨start,next,negative⟩ ∈ edges ∨ ⟨next,start,negative⟩ ∈ edges) ∧
    ValidWalk edges next rest

instance {n : ℕ} (edges : List (Edge n)) (start : Fin n) (walk : List (Bool × Fin n)) :
    Decidable (ValidWalk edges start walk) := by
  induction walk generalizing start with
  | nil => unfold ValidWalk; infer_instance
  | cons step rest ih =>
    rcases step with ⟨negative,next⟩
    unfold ValidWalk
    letI := ih next
    infer_instance

def finish {n : ℕ} (start : Fin n) : List (Bool × Fin n) → Fin n
  | [] => start
  | (_,next)::rest => finish next rest

def parity {n : ℕ} : List (Bool × Fin n) → Bool
  | [] => false
  | (negative,_)::rest => xor negative (parity rest)

theorem walk_equation {n : ℕ} {support : Finset (Fin n)} {edges : List (Edge n)}
    {phase : Fin n → ℂ} (hp : Assignment support edges phase)
    {start : Fin n} {walk : List (Bool × Fin n)} (hw : ValidWalk edges start walk) :
    phase start = sign (parity walk) (phase (finish start walk)) := by
  induction walk generalizing start with
  | nil => simp [finish,parity,sign]
  | cons step rest ih =>
    rcases step with ⟨negative,next⟩
    rcases hw with ⟨he,hr⟩
    have hs : phase start = sign negative (phase next) := by
      rcases he with he|he
      · exact hp.2 _ he
      · have h := hp.2 _ he
        cases negative <;> simp_all [sign]
    rw [hs,ih hr,sign_sign]
    rfl

theorem odd_walk_excludes {n : ℕ} {support : Finset (Fin n)} {edges : List (Edge n)}
    {start : Fin n} {walk : List (Bool × Fin n)} (ha : start ∈ support)
    (hw : ValidWalk edges start walk) (hf : finish start walk = start)
    (ho : parity walk = true) : ¬ Compatible support edges := by
  rintro ⟨phase,hp⟩
  have h := walk_equation hp hw
  rw [hf,ho] at h
  change phase start = -phase start at h
  have hz : phase start = 0 := by linear_combination (1/2) * h
  exact hp.1 start ha hz

def Coloring {n : ℕ} (edges : List (Edge n)) (colors : Fin n → Bool) : Prop :=
  ∀ edge ∈ edges, xor (colors edge.left) (colors edge.right) = edge.negative

theorem compatible_of_coloring {n : ℕ} (support : Finset (Fin n)) (edges : List (Edge n))
    {colors : Fin n → Bool} (hc : Coloring edges colors) : Compatible support edges := by
  refine ⟨fun v => sign (colors v) 1,?_,?_⟩
  · intro v _
    cases h : colors v <;> norm_num [sign,h]
  · intro edge he
    have h := hc edge he
    cases hl : colors edge.left <;> cases hr : colors edge.right <;>
      cases hn : edge.negative <;> simp_all [sign]

end MainTheory.SignedPhaseSupport
