import MainTheory.FiveQubitCitedGateData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.CitedFamilyMomentData

open SixQubit.Realize MainTheory.FiveQubitPerfectCore

def L : List (SS.BitString 6) := List.ofFn (fun x : Fin 64 => nbit x.val)

def base (i : Fin 2) (b : Bool) (x : SS.BitString 6) : ZQ :=
  if x 5=b then
    let w := MainTheory.FiveQubitCitedGateData.rawWord i ⟨number (Fin.init x),number_lt _⟩
    if x 4 && b then ZQ.neg w else w
  else ZQ.zero

def mass : ZQ := z8 192 0 (-64) 0 0 0 0 0

theorem L_nodup : L.Nodup := by decide +kernel
theorem L_complete : ∀ x : SS.BitString 6,x ∈ L := by decide +kernel

theorem gram : ∀ i j : Fin 2,∀ b b' : Bool,
    zmat (base i b) (base j b') L (fun _ => false) (fun _ => false)=
      if i=j ∧ b=b' then mass else ZQ.zero := by decide +kernel

theorem single_pauli : ∀ m < 64,∀ z < 64,
    (⟨nbit m,nbit z⟩ : SS.PauliString 6).wt=1 →
    ∀ i j : Fin 2,∀ b b' : Bool,
    zmat (base i b) (base j b') L (nbit m) (nbit z)=
      if m=0 ∧ z=32 ∧ i=j ∧ b=b' then (if b then ZQ.neg mass else mass)
      else ZQ.zero := by decide +kernel

end MainTheory.CitedFamilyMomentData
