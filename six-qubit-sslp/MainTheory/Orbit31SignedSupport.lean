import MainTheory.Orbit31SupportSemantics
import MainTheory.SignedPhaseSupport

/-! The exact support predicates used in the orbit-31 audit.
They refer to the SI's A row and three B rows in the actual bottom fibre.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31SupportSemantics
open MainTheory.SignedPhaseSupport

def A (e : Fin 4) : Fin 16 := ⟨e.val,by omega⟩
def B (i : Fin 3) (e : Fin 4) : Fin 16 := ⟨4+4*i.val+e.val,by omega⟩
def active (mask : ℕ) (v : Fin 16) : Bool := mask.testBit v.val

def overlaps (mask : ℕ) (i : Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter fun e => active mask (A e) && active mask (B i e)

def NoSingleton (mask : ℕ) : Prop := ∀ i : Fin 3, (overlaps mask i).card ≠ 1
instance (mask : ℕ) : Decidable (NoSingleton mask) := by unfold NoSingleton; infer_instance
def noSingleton (mask : ℕ) : Bool := decide (NoSingleton mask)
theorem noSingleton_iff (mask : ℕ) : noSingleton mask = true ↔ NoSingleton mask := by
  simp [noSingleton]

def rowPairs : Fin 3 → Fin 3 × Fin 3 := ![(0,1),(0,2),(1,2)]
def colPairs : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

def verticalEdges (mask : ℕ) : List (Edge 16) :=
  (List.finRange 3).flatMap fun i => (List.finRange 4).flatMap fun e =>
    if active mask (A e) && active mask (B i e) then [⟨A e,B i e,false⟩] else []

def rectangleEdges (mask : ℕ) : List (Edge 16) :=
  (List.finRange 3).flatMap fun r => (List.finRange 6).flatMap fun k =>
    let i := (rowPairs r).1
    let j := (rowPairs r).2
    let e := (colPairs k).1
    let f := (colPairs k).2
    let left := active mask (B i e) && active mask (B j f)
    let right := active mask (B i f) && active mask (B j e)
    if left && !right then [⟨B i e,B j f,true⟩]
    else if right && !left then [⟨B i f,B j e,true⟩] else []

def edges (mask : ℕ) : List (Edge 16) := verticalEdges mask ++ rectangleEdges mask

def GraphCompatible (mask : ℕ) : Prop := Compatible (maskSet mask) (edges mask)

inductive Certificate where
  | coloring (colors : Fin 16 → Bool)
  | oddWalk (start : Fin 16) (walk : List (Bool × Fin 16))

def Valid (mask : ℕ) : Certificate → Prop
  | .coloring colors => Coloring (edges mask) colors
  | .oddWalk start walk =>
    active mask start = true ∧ ValidWalk (edges mask) start walk ∧
    finish start walk = start ∧ parity walk = true

instance (mask : ℕ) (certificate : Certificate) : Decidable (Valid mask certificate) := by
  cases certificate with
  | coloring colors => unfold Valid Coloring; infer_instance
  | oddWalk start walk => unfold Valid; infer_instance

def isColoring : Certificate → Bool
  | .coloring _ => true
  | .oddWalk _ _ => false

theorem compatible_iff {mask : ℕ} {certificate : Certificate} (hv : Valid mask certificate) :
    GraphCompatible mask ↔ isColoring certificate = true := by
  cases certificate with
  | coloring colors =>
    exact iff_of_true (compatible_of_coloring (maskSet mask) (edges mask) hv) rfl
  | oddWalk start walk =>
    exact iff_of_false (odd_walk_excludes ((mem_maskSet mask start).mpr hv.1)
      hv.2.1 hv.2.2.1 hv.2.2.2) Bool.false_ne_true

end MainTheory.Orbit31SignedSupport
