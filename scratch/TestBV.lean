import Mathlib

theorem test (x : BitVec 8) : x + 1 - 1 = x := by
  bv_decide

#print axioms test

#synth CommRing (BitVec 16)

abbrev F2 := Fin 2
def m16 (x : BitVec 4) : Matrix F2 F2 (BitVec 16) :=
  fun i j => if x.getLsbD (2 * i.val + j.val) then 1 else 0

theorem det2_bound (x : BitVec 4) :
    (-1 : BitVec 16).sle (m16 x).det ∧ (m16 x).det.sle 1 := by
  simp only [Matrix.det_fin_two, m16]
  bv_decide

abbrev F3 := Fin 3
def m3 (x : BitVec 9) : Matrix F3 F3 (BitVec 16) :=
  fun i j => if x.getLsbD (3 * i.val + j.val) then 1 else 0

set_option maxRecDepth 100000 in
theorem det3_bound (x : BitVec 9) :
    (-2 : BitVec 16).sle (m3 x).det ∧ (m3 x).det.sle 2 := by
  rw [Matrix.det_fin_three]
  simp only [m3]
  bv_decide

def laplaceDet {R : Type} [CommRing R] :
    (n : Nat) → Matrix (Fin n) (Fin n) R → R
  | 0, _ => 1
  | n + 1, A =>
      ∑ j : Fin (n + 1), (-1) ^ (j : Nat) * A 0 j *
        laplaceDet n (A.submatrix Fin.succ j.succAbove)

theorem laplaceDet_eq_det {R : Type} [CommRing R]
    (n : Nat) (A : Matrix (Fin n) (Fin n) R) : laplaceDet n A = A.det := by
  induction n with
  | zero => simp [laplaceDet]
  | succ n ih =>
      rw [Matrix.det_succ_row_zero]
      simp only [laplaceDet]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]

def finSum {R : Type} [AddMonoid R] : (n : Nat) → (Fin n → R) → R
  | 0, _ => 0
  | n + 1, f => f 0 + finSum n (fun i => f i.succ)

theorem finSum_eq_sum {R : Type} [AddCommMonoid R]
    (n : Nat) (f : Fin n → R) : finSum n f = ∑ i, f i := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [finSum]
      rw [ih]

def vecDet {ι R : Type} [CommRing R] (A : ι → ι → R) :
    (n : Nat) → (Fin n → ι) → (Fin n → ι) → R
  | 0, _, _ => 1
  | n + 1, rows, cols =>
      finSum (n + 1) fun j =>
        (-1) ^ (j : Nat) * A (rows 0) (cols j) *
          vecDet A n (fun i => rows i.succ) (fun i => cols (j.succAbove i))

theorem vecDet_eq_det {ι R : Type} [CommRing R] (A : ι → ι → R)
    (n : Nat) (rows cols : Fin n → ι) :
    vecDet A n rows cols =
      ((fun i j => A (rows i) (cols j)) : Matrix (Fin n) (Fin n) R).det := by
  induction n with
  | zero => simp [vecDet]
  | succ n ih =>
      rw [Matrix.det_succ_row_zero, ← finSum_eq_sum]
      simp only [vecDet]
      congr 1
      funext j
      rw [ih]
      rfl

def detCircuit {R : Type} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : R :=
  vecDet A 4 id id

theorem detCircuit_eq_det {R : Type} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) : detCircuit A = A.det := by
  simpa [detCircuit] using vecDet_eq_det A 4 id id

abbrev F4 := Fin 4
def m4 (x : BitVec 16) : Matrix F4 F4 (BitVec 16) :=
  fun i j => if x.getLsbD (4 * i.val + j.val) then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem det4_bound (x : BitVec 16) :
    (-3 : BitVec 16).sle (m4 x).det ∧ (m4 x).det.sle 3 := by
  rw [← detCircuit_eq_det]
  dsimp [detCircuit, vecDet, finSum, m4]
  bv_decide (timeout := 60)

#print Fin.succAbove
