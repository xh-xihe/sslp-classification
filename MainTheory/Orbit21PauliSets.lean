import SixQubit.Orbit21Coef
import SixQubit.Orbit21Farkas

set_option autoImplicit false

namespace MainTheory.Orbit21PauliSets

/-- Displayed Pauli letters run from qubit one to qubit six. -/
def lettersMask : List Char → ℕ × ℕ
  | [] => (0,0)
  | c::cs =>
    let t := lettersMask cs
    ((if c='X' ∨ c='Y' then 1 else 0)+2*t.1,
     (if c='Z' ∨ c='Y' then 1 else 0)+2*t.2)

def mask (s : String) : ℕ × ℕ := lettersMask s.toList

theorem Bset : SixQubit.Orbit21Coef.bset=
    ["IIZIIZ","IZIIIZ","IZZIII"].map mask := by decide +kernel

theorem Tset : SixQubit.Orbit21Coef.tset=
    ["IIIZZZ","IIZIXZ","IIZIYZ","IIZIZZ","IIZXIZ","IIZYIZ","IIZZIZ","IIZZZI",
     "IZIIXZ","IZIIYZ","IZIIZZ","IZIXIZ","IZIYIZ","IZIZIZ","IZIZZI",
     "IZZIXI","IZZIYI","IZZIZI","IZZXII","IZZYII","IZZZII","IZZZZZ"].map mask := by
  decide +kernel

theorem R2set : SixQubit.Orbit21Coef.r2set=
    ["IIIXXI","IIIXYI","IIIYXI","IIIYYI","IIIZZI","IIZIZZ","IIZZIZ",
     "IZIIZZ","IZIZIZ","IZZIZI","IZZZII"].map mask := by decide +kernel

theorem R3set : SixQubit.Orbit21Coef.r3set=
    ["IIIIIZ","IIIIZI","IIIZII","IIZIII","IZIIII","IZZIIZ"].map mask := by decide +kernel

theorem R4set : SixQubit.Orbit21Coef.r4set=
    ["IIXIIX","IIXIIY","IXIIIX","IXIIIY","IXXIII","IXYIII","XIIIIX","XIIIIY",
     "XIXIII","XIYIII","XXIIII","XYIIII"].map mask := by decide +kernel

theorem B_paulis : SixQubit.Orbit21Coef.bset.map SixQubit.Orbit21Farkas.ofMask=
    [⟨fun _ => false,SS.bxor (SS.stdBasis 2) (SS.stdBasis 5)⟩,
     ⟨fun _ => false,SS.bxor (SS.stdBasis 1) (SS.stdBasis 5)⟩,
     ⟨fun _ => false,SS.bxor (SS.stdBasis 1) (SS.stdBasis 2)⟩] := by
  have h0 : SixQubit.Realize.nbit 0=(fun _ => false) := by funext i; fin_cases i <;> rfl
  have h36 : SixQubit.Realize.nbit 36=SS.bxor (SS.stdBasis 2) (SS.stdBasis 5) := by
    funext i; fin_cases i <;> rfl
  have h34 : SixQubit.Realize.nbit 34=SS.bxor (SS.stdBasis 1) (SS.stdBasis 5) := by
    funext i; fin_cases i <;> rfl
  have h6 : SixQubit.Realize.nbit 6=SS.bxor (SS.stdBasis 1) (SS.stdBasis 2) := by
    funext i; fin_cases i <;> rfl
  simp [SixQubit.Orbit21Coef.bset,SixQubit.Orbit21Farkas.ofMask,h0,h36,h34,h6]

end MainTheory.Orbit21PauliSets
