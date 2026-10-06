import MainTheory.Orbit13Frames
set_option autoImplicit false
namespace MainTheory.Orbit13DisplayCompletion
open scoped Matrix
open SixQubit.Orbit13 MainTheory.Orbit13Frames
noncomputable section

/-- The eight printed X6/Y6 probes, with qubit numbers converted to Fin indices. -/
def errors : Fin 8 → SS.PauliString 6 :=
  ![SS.pauliX 5, SS.pauliY 5,
    SS.pauli2 1 5 (false,true) (true,false),
    SS.pauli2 1 5 (false,true) (true,true),
    SS.pauli2 2 5 (false,true) (true,false),
    SS.pauli2 2 5 (false,true) (true,true),
    SS.pauli2 3 5 (false,true) (true,false),
    SS.pauli2 3 5 (false,true) (true,true)]

theorem error_weights : ∀ i : Fin 8,(errors i).wt≤2 := by decide +kernel

theorem physical_error_rows (c d : SS.State 6 ℂ)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 8) :
    SS.KLCondition ![c,d] (errors i) :=
  hkl (errors i) (error_weights i)

theorem physical_trace_test (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (r : Fin 4)
    (F : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (F*bottomFrame c r)=Matrix.trace (F*topFrame d r) := by
  rw [(physical_frames c d hc hd hnc hnd hkl r).2.1]

end
end MainTheory.Orbit13DisplayCompletion
