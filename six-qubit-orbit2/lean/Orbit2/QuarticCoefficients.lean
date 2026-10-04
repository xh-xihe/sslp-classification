import Orbit2.Global
import Orbit2.TensorPauli

/-! Integer coefficients reconstructed from Pauli traces. The normalization is
24 Q = zᴴ (2M) z. The conjugation character shortcut is proved separately. -/
namespace Orbit2.Quartic
open scoped BigOperators
open Orbit2.TensorPauli

abbrev basis (i : Fin 32) : Label 4 := pauliBasis i

def isThree (i : Fin 32) : Bool := pauliWeight (basis i) == 3

def single (i : Fin 4) (ax : Fin 4) : Label 4 := fun j => if j = i then ax else 0

def character (ax p : Fin 4) : ℤ := if ax = 0 ∨ p = 0 ∨ ax = p then 1 else -1

/-- Twelve times the five J multipliers, with the exact incidence conditions. -/
def jWeight (site : Fin 4) (ax : Fin 4) (u : Fin 32) : ℤ :=
  let p := basis u site
  if ax = 0 then 0 else if ax = 3 then
    if p = 1 ∨ p = 2 then (if isThree u then 10 else -18) else 0
  else if isThree u then
    if p = 3 then 5 else if (p = 1 ∨ p = 2) ∧ p ≠ ax then 7 else 0
  else if (p = 1 ∨ p = 2) ∧ p ≠ ax then 18 else 0

/-- Ordered projection-defect coefficient: conjugates (u,v), holomorphics (x,y). -/
def gCoeff (u v x y : Fin 32) : ℤ :=
  if isThree u then
    (wordTrace [basis u,basis x,basis v,basis y]).re -
      if u = x ∧ v = y then 2 else 0
  else 0

/-- The J trace difference, expressed using single-site conjugation characters. -/
def jCoeff (u v x y : Fin 32) : ℤ :=
  let four := (wordTrace [basis u,basis x,basis v,basis y]).re
  let left := product (basis x) (basis v)
  let right := product (basis u) (basis y)
  (∑ site : Fin 4, ∑ ax : Fin 4,
    jWeight site ax u * character ax (basis x site) *
      (character ax (basis v site) - 1)) * four -
  4 * (∑ site : Fin 4, ∑ ax : Fin 4,
    if left = single site ax ∧ right = single site ax then
      jWeight site ax u * character ax (basis u site) *
        (phase (basis x) (basis v) * phase (basis u) (basis y)).re
    else 0)

/-- Target c² and the four forbidden-set contractions, with exact multipliers. -/
def cCoeff (u v x y : Fin 32) : ℤ :=
  let left := product (basis x) (basis u)
  let right := product (basis y) (basis v)
  if left = right then
    let w := pauliWeight left
    let f := transverseCount left
    let mixed := isThree y != isThree v
    let both := isThree y && isThree v
    let multiplier : ℤ :=
      (if w = 3 ∧ f = 2 then -24 else 0) +
      (if w = 4 ∧ f = 2 then (if mixed then 68 else 0) + (if both then 76 else 0) else 0) +
      (if w = 3 ∧ f = 0 ∧ mixed then 100 else 0) +
      (if w = 2 ∧ f = 0 ∧ both then 8 else 0)
    multiplier * (phase (basis x) (basis u) * phase (basis y) (basis v)).re
  else 0

def rawCoefficient (u v x y : Fin 32) : ℤ :=
  cCoeff u v x y + jCoeff u v x y + jCoeff x y u v +
    6*gCoeff u v x y + 6*gCoeff x y u v

/-- The character gate will be justified by Pauli trace vanishing. -/
def gatedCoefficient (u v x y : Fin 32) : ℤ :=
  if product (basis u) (basis v) = product (basis x) (basis y) then
    rawCoefficient u v x y else 0

def orders (r : Fin 528) : List (Fin 32 × Fin 32) :=
  let p := monomials r
  if p.1 = p.2 then [p] else [p, (p.2,p.1)]

def twiceCoefficient (r c : Fin 528) : ℤ :=
  ((orders r).map fun uv => ((orders c).map fun xy =>
    gatedCoefficient uv.1 uv.2 xy.1 xy.2).sum).sum

end Orbit2.Quartic
