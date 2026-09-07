import SixQubit.ParityMomentFamily

/- Exact proposed coefficients; all identities receive kernel proofs. -/
namespace SixQubit.OpenMParity

open SixQubit.Realize SixQubit.Orbit8Family
open SixQubit.ParityCircleFamily SixQubit.ParityMomentFamily

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def angle : Fin 6 → ZMod 2 := ![1,1,1,1,1,1]

def L0 : List (SS.BitString 6) :=
  [nbit 0, nbit 3, nbit 5, nbit 6, nbit 9, nbit 10, nbit 12, nbit 15, nbit 17, nbit 18, nbit 20, nbit 23, nbit 24, nbit 27, nbit 29, nbit 30, nbit 33, nbit 34, nbit 36, nbit 39, nbit 40, nbit 43, nbit 45, nbit 46, nbit 48, nbit 51, nbit 53, nbit 54, nbit 57, nbit 58, nbit 60, nbit 63]

def c0 (x : SS.BitString 6) : LinZ :=
  if x 0 then
    if x 1 then
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
      else
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
    else
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
      else
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
  else
    if x 1 then
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
      else
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
    else
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
      else
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩

def L1 : List (SS.BitString 6) :=
  [nbit 1, nbit 2, nbit 4, nbit 7, nbit 8, nbit 11, nbit 13, nbit 14, nbit 16, nbit 19, nbit 21, nbit 22, nbit 25, nbit 26, nbit 28, nbit 31, nbit 32, nbit 35, nbit 37, nbit 38, nbit 41, nbit 42, nbit 44, nbit 47, nbit 49, nbit 50, nbit 52, nbit 55, nbit 56, nbit 59, nbit 61, nbit 62]

def c1 (x : SS.BitString 6) : LinZ :=
  if x 0 then
    if x 1 then
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
      else
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
    else
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
      else
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
          else
            if x 5 then
              ⟨(z8 (-4) 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨(z8 (-4) 0 0 0 4 0 0 0), ZQ.zero, ZQ.zero⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 4 0 0 0 (-4) 0 0 0), ZQ.zero, ZQ.zero⟩
  else
    if x 1 then
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
      else
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 4 0 0 0 0 0 0 0)⟩
    else
      if x 2 then
        if x 3 then
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨ZQ.zero, (z8 0 (-4) 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
        else
          if x 4 then
            if x 5 then
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 (-4) 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
      else
        if x 3 then
          if x 4 then
            if x 5 then
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero
          else
            if x 5 then
              LinZ.zero
            else
              ⟨(z8 0 0 0 0 0 4 0 0), ZQ.zero, (z8 (-4) 0 0 0 0 0 0 0)⟩
        else
          if x 4 then
            if x 5 then
              LinZ.zero
            else
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
          else
            if x 5 then
              ⟨ZQ.zero, (z8 0 4 0 0 0 0 0 0), (z8 (-4) 0 0 0 0 0 0 0)⟩
            else
              LinZ.zero

def traceModel (P : SS.PauliString 6) : QuadZ :=
  if num P.x = 0 ∧ num P.z = 0 then ⟨(z8 1536 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0), ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩
  else if num P.x = 0 ∧ num P.z = 6 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 (-512) 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 0 ∧ num P.z = 10 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 (-512) 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 0 ∧ num P.z = 12 then ⟨(z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩
  else if num P.x = 0 ∧ num P.z = 50 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩
  else if num P.x = 0 ∧ num P.z = 52 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 0 ∧ num P.z = 56 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 6 ∧ num P.z = 0 then ⟨(z8 1024 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩
  else if num P.x = 6 ∧ num P.z = 6 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 10 ∧ num P.z = 0 then ⟨(z8 1024 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩
  else if num P.x = 10 ∧ num P.z = 10 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 12 ∧ num P.z = 0 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩
  else if num P.x = 12 ∧ num P.z = 12 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩
  else if num P.x = 18 ∧ num P.z = 0 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0), ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩
  else if num P.x = 18 ∧ num P.z = 50 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩
  else if num P.x = 20 ∧ num P.z = 0 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩
  else if num P.x = 20 ∧ num P.z = 52 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 24 ∧ num P.z = 0 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩
  else if num P.x = 24 ∧ num P.z = 56 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 34 ∧ num P.z = 0 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0), ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩
  else if num P.x = 34 ∧ num P.z = 50 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩
  else if num P.x = 36 ∧ num P.z = 0 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩
  else if num P.x = 36 ∧ num P.z = 52 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 40 ∧ num P.z = 0 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩
  else if num P.x = 40 ∧ num P.z = 56 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 48 ∧ num P.z = 50 then ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩
  else if num P.x = 48 ∧ num P.z = 52 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else if num P.x = 48 ∧ num P.z = 56 then ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩
  else QuadZ.zero

def klCheck (P : SS.PauliString 6) : Prop :=
  CircleZero (QuadZ.sub (qmat c0 c0 L0 P.x P.z) (qmat c1 c1 L1 P.x P.z)) ∧
    CircleZero (qmat c0 c1 L1 P.x P.z) ∧ CircleZero (qmat c1 c0 L0 P.x P.z)

instance (P : SS.PauliString 6) : Decidable (klCheck P) := by unfold klCheck; infer_instance

def rowCheck (P : SS.PauliString 6) : Prop :=
  (P.wt ≤ 2 → klCheck P) ∧
    (P.wt ≤ 3 → CircleZero (QuadZ.sub (qtrace c0 c1 L0 L1 P) (traceModel P)))

instance (P : SS.PauliString 6) : Decidable (rowCheck P) := by unfold rowCheck; infer_instance

def traceList1 : List (SS.PauliString 6) :=
  []

theorem traceList1_nodup : traceList1.Nodup := by decide
theorem traceList1_weight : ∀ P ∈ traceList1, P.wt = 1 := by
  intro P hP
  simp [traceList1] at hP

def modelList1 : List QuadZ :=
  []
theorem modelList1_correct : traceList1.map traceModel = modelList1 := by decide

def traceList2 : List (SS.PauliString 6) :=
  [⟨nbit 0, nbit 6⟩, ⟨nbit 0, nbit 10⟩, ⟨nbit 0, nbit 12⟩, ⟨nbit 6, nbit 0⟩, ⟨nbit 6, nbit 6⟩, ⟨nbit 10, nbit 0⟩, ⟨nbit 10, nbit 10⟩, ⟨nbit 12, nbit 0⟩, ⟨nbit 12, nbit 12⟩, ⟨nbit 18, nbit 0⟩, ⟨nbit 20, nbit 0⟩, ⟨nbit 24, nbit 0⟩, ⟨nbit 34, nbit 0⟩, ⟨nbit 36, nbit 0⟩, ⟨nbit 40, nbit 0⟩]

theorem traceList2_nodup : traceList2.Nodup := by decide
theorem traceList2_weight : ∀ P ∈ traceList2, P.wt = 2 := by
  intro P hP
  simp only [traceList2, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def modelList2 : List QuadZ :=
  [⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 (-512) 0 0 0 0 0 0), ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 (-512) 0 0 0 0 0 0), ZQ.zero⟩, ⟨(z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩, ⟨(z8 1024 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨(z8 1024 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩, ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩, ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0), ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩, ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0), ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0)⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 512 0 0 0 0 0 0 0)⟩]
theorem modelList2_correct : traceList2.map traceModel = modelList2 := by decide

def traceList3 : List (SS.PauliString 6) :=
  [⟨nbit 0, nbit 50⟩, ⟨nbit 0, nbit 52⟩, ⟨nbit 0, nbit 56⟩, ⟨nbit 18, nbit 50⟩, ⟨nbit 20, nbit 52⟩, ⟨nbit 24, nbit 56⟩, ⟨nbit 34, nbit 50⟩, ⟨nbit 36, nbit 52⟩, ⟨nbit 40, nbit 56⟩, ⟨nbit 48, nbit 50⟩, ⟨nbit 48, nbit 52⟩, ⟨nbit 48, nbit 56⟩]

theorem traceList3_nodup : traceList3.Nodup := by decide
theorem traceList3_weight : ∀ P ∈ traceList3, P.wt = 3 := by
  intro P hP
  simp only [traceList3, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def modelList3 : List QuadZ :=
  [⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨(z8 512 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero, (z8 (-512) 0 0 0 0 0 0 0), ZQ.zero, ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩, ⟨ZQ.zero, ZQ.zero, ZQ.zero, ZQ.zero, (z8 0 512 0 0 0 0 0 0), ZQ.zero⟩]
theorem modelList3_correct : traceList3.map traceModel = modelList3 := by decide

end SixQubit.OpenMParity
