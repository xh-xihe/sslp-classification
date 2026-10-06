import SixQubit.Realize
import SixQubit.Orbit21Cert

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace MainTheory.Orbit21LiteralData

open SixQubit.Realize

/-- The manuscript's displayed ket has qubit one at the left. -/
def bits (n : ℕ) : SS.BitString 6 := fun i => nbit n i.rev

def L0 : List (SS.BitString 6) := [0,9,23,28,39,44,50,59].map bits
def L1 : List (SS.BitString 6) := [4,13,19,24,35,40,54,63].map bits

def c0z (x : SS.BitString 6) : ZQ :=
  if x=bits 0 ∨ x=bits 9 ∨ x=bits 23 ∨ x=bits 28 ∨ x=bits 44 ∨ x=bits 59 then
    z8 0 1 0 0 0 0 0 0
  else if x=bits 39 ∨ x=bits 50 then z8 0 (-1) 0 0 0 0 0 0 else ZQ.zero

def c1z (x : SS.BitString 6) : ZQ :=
  if x=bits 4 ∨ x=bits 24 ∨ x=bits 54 ∨ x=bits 63 then z8 0 1 0 0 0 0 0 0
  else if x=bits 13 ∨ x=bits 19 ∨ x=bits 35 ∨ x=bits 40 then
    z8 0 (-1) 0 0 0 0 0 0 else ZQ.zero

theorem L0_nodup : L0.Nodup := by decide +kernel
theorem L1_nodup : L1.Nodup := by decide +kernel
theorem support0 : ∀ x ∈ L0,SS.weight SixQubit.Orbit21Cert.av x=0 := by decide +kernel
theorem support1 : ∀ x ∈ L1,SS.weight SixQubit.Orbit21Cert.av x=2 := by decide +kernel
theorem vanishes0 : ∀ x : SS.BitString 6,x ∉ L0 → c0z x=ZQ.zero := by decide +kernel
theorem vanishes1 : ∀ x : SS.BitString 6,x ∉ L1 → c1z x=ZQ.zero := by decide +kernel

theorem check_all : ∀ m < 64, ∀ k < 64,
    (⟨nbit m,nbit k⟩ : SS.PauliString 6).wt ≤ 2 →
    checkKL c0z c1z L0 L1 (nbit m) (nbit k)=true := by decide +kernel

theorem norm0 : zmat c0z c0z L0 (fun _ => false) (fun _ => false)=
    z8 16 0 0 0 0 0 0 0 := by decide +kernel
theorem norm1 : zmat c1z c1z L1 (fun _ => false) (fun _ => false)=
    z8 16 0 0 0 0 0 0 0 := by decide +kernel

end MainTheory.Orbit21LiteralData
