import SixQubit.ParityCircleFamily

/- Exact generated amplitude candidate; every certificate field is kernel checked. -/
namespace SixQubit.OpenLOrbit4

open SixQubit.Realize SixQubit.Orbit8Family SixQubit.ParityCircleFamily

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

def angle : Fin 6 → ZMod 2 := ![1, 1, 1, 1, 1, 1]

def L0 : List (SS.BitString 6) :=
  [nbit 0, nbit 3, nbit 5, nbit 6, nbit 9, nbit 10, nbit 12, nbit 15, nbit 17, nbit 18, nbit 20, nbit 23, nbit 24, nbit 27, nbit 29, nbit 30, nbit 33, nbit 34, nbit 36, nbit 39, nbit 40, nbit 43, nbit 45, nbit 46, nbit 48, nbit 51, nbit 53, nbit 54, nbit 57, nbit 58, nbit 60, nbit 63]

def c0 (x : SS.BitString 6) : LinZ :=
  (if x 0 then (if x 1 then (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩)))) else (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩))))) else (if x 1 then (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)))) else (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩))))))

def L1 : List (SS.BitString 6) :=
  [nbit 1, nbit 2, nbit 4, nbit 7, nbit 8, nbit 11, nbit 13, nbit 14, nbit 16, nbit 19, nbit 21, nbit 22, nbit 25, nbit 26, nbit 28, nbit 31, nbit 32, nbit 35, nbit 37, nbit 38, nbit 41, nbit 42, nbit 44, nbit 47, nbit 49, nbit 50, nbit 52, nbit 55, nbit 56, nbit 59, nbit 61, nbit 62]

def c1 (x : SS.BitString 6) : LinZ :=
  (if x 0 then (if x 1 then (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)))) else (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 4 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩))))) else (if x 1 then (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩)))) else (if x 2 then (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 4 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 0 0 0 0 (-4) 0 0 0), ZQ.zero⟩))) else (if x 3 then (if x 4 then (if x 5 then ⟨ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩)) else (if x 4 then (if x 5 then ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩ else ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩) else (if x 5 then ⟨ZQ.zero, (z8 4 0 0 0 0 0 0 0), ZQ.zero⟩ else ⟨ZQ.zero, ZQ.zero, ZQ.zero⟩))))))

def onePauli : SS.PauliString 6 := ⟨nbit 0, nbit 1⟩
def twoPauli : SS.PauliString 6 := ⟨nbit 3, nbit 0⟩

def klCheck (P : SS.PauliString 6) : Prop :=
  CircleZero (QuadZ.sub (qmat c0 c0 L0 P.x P.z) (qmat c1 c1 L1 P.x P.z)) ∧
    CircleZero (qmat c0 c1 L1 P.x P.z) ∧ CircleZero (qmat c1 c0 L0 P.x P.z)

instance (P : SS.PauliString 6) : Decidable (klCheck P) := by
  unfold klCheck
  infer_instance

def sameMasks (P Q : SS.PauliString 6) : Prop :=
  num P.x = num Q.x ∧ num P.z = num Q.z

instance (P Q : SS.PauliString 6) : Decidable (sameMasks P Q) := by
  unfold sameMasks
  infer_instance

theorem sameMasks_eq {P Q : SS.PauliString 6} (h : sameMasks P Q) : P = Q := by
  have hx : P.x = Q.x := by simpa only [nbit_num] using congrArg nbit h.1
  have hz : P.z = Q.z := by simpa only [nbit_num] using congrArg nbit h.2
  cases P; cases Q; cases hx; cases hz; rfl

def sparseCheck (P : SS.PauliString 6) : Prop :=
  P.wt ≤ 2 → ¬ sameMasks P identityPauli → ¬ sameMasks P onePauli →
    ¬ sameMasks P twoPauli →
    CircleZero (qtrace c0 c1 L0 L1 P)

instance (P : SS.PauliString 6) : Decidable (sparseCheck P) := by
  unfold sparseCheck
  infer_instance

end SixQubit.OpenLOrbit4
