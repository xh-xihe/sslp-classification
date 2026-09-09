import SixQubit.Realize

namespace MainTheory.ExactZQFinite

open SixQubit.Realize

def listSum (L : List ZQ) : ZQ := L.foldr ZQ.add ZQ.zero
def sum (n : ℕ) (f : Fin n → ZQ) : ZQ := listSum (List.ofFn f)
def listProd (L : List ZQ) : ZQ := L.foldr ZQ.mul (z8 1 0 0 0 0 0 0 0)
def prod (n : ℕ) (f : Fin n → ZQ) : ZQ := listProd (List.ofFn f)

theorem toC_listSum (L : List ZQ) : toC (listSum L)=(L.map toC).sum := by
  induction L with
  | nil => simp [listSum]
  | cons a L ih => simpa [listSum,toC_add] using congrArg (fun z => toC a+z) ih

theorem toC_sum (n : ℕ) (f : Fin n → ZQ) : toC (sum n f)=∑ i,toC (f i) := by
  rw [sum,toC_listSum]
  simp [List.sum_ofFn]

theorem toC_listProd (L : List ZQ) : toC (listProd L)=(L.map toC).prod := by
  induction L with
  | nil => simpa [listProd] using toC_intCast 1
  | cons a L ih => simpa [listProd,toC_mul] using congrArg (fun z => toC a*z) ih

theorem toC_prod (n : ℕ) (f : Fin n → ZQ) : toC (prod n f)=∏ i,toC (f i) := by
  rw [prod,toC_listProd]
  simp [List.prod_ofFn]

end MainTheory.ExactZQFinite
