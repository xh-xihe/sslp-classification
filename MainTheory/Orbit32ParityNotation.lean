import SixQubit.Orbit32
set_option autoImplicit false
namespace MainTheory.Orbit32ParityNotation
open scoped BigOperators
def E : Finset (SS.BitString 3) :=
  {![false,false,false],![false,true,true],![true,false,true],![true,true,false]}
def O : Finset (SS.BitString 3) :=
  {![false,false,true],![false,true,false],![true,false,false],![true,true,true]}
def wt (u : SS.BitString 3) : ℕ := ∑ i,if u i then 1 else 0
def inner (x : SS.BitString 6) : SS.BitString 3 := ![x 2,x 3,x 4]
def outer (x : SS.BitString 6) : SS.BitString 3 := ![x 0,x 1,x 5]
theorem literal_parities :
    E.card=4 ∧ O.card=4 ∧ (∀ u,u∈E ↔ wt u%2=0) ∧ (∀ u,u∈O ↔ wt u%2=1) := by
  decide +kernel
theorem coordinate_identity : ∀ x : SS.BitString 6,
    SS.weight SixQubit.Orbit32.av x=
      ((if x 0 then 1 else 0)+(if x 1 then 1 else 0)-(if x 5 then 1 else 0)+
        2*(wt (inner x) : ZMod 4)) := by decide +kernel
theorem literal_fibers : ∀ x : SS.BitString 6,
    (x∈SixQubit.Orbit32.S0 ↔
      (outer x∈({![false,false,false],![false,true,true],![true,false,true]} : Finset (SS.BitString 3)) ∧ inner x∈E) ∨
      (outer x=![true,true,false] ∧ inner x∈O)) ∧
    (x∈SixQubit.Orbit32.S1 ↔
      (outer x∈({![false,true,false],![true,false,false],![true,true,true]} : Finset (SS.BitString 3)) ∧ inner x∈E) ∨
      (outer x=![false,false,true] ∧ inner x∈O)) := by decide +kernel
end MainTheory.Orbit32ParityNotation
