import MainTheory.FiveQubitPerfectCore
import MainTheory.ExactZQFinite

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.FiveQubitCitedGateData

open SixQubit.Realize MainTheory.FiveQubitPerfectCore
open MainTheory.ExactZQFinite

def W : Fin 2 → Fin 2 → ZQ :=
  !![z8 (-2) 0 0 0 0 0 0 0, z8 (-1) 0 1 0 1 0 (-1) 0;
     z8 (-1) 0 1 0 (-1) 0 1 0, z8 2 0 0 0 0 0 0 0]
def T : Fin 2 → Fin 2 → ZQ :=
  !![z8 0 0 0 0 (-1) 0 0 0, z8 (-1) 0 0 0 0 0 0 0;
     z8 0 0 0 0 1 0 0 0, z8 (-1) 0 0 0 0 0 0 0]
def D : Fin 2 → Fin 2 → ZQ :=
  !![z8 1 0 0 0 0 0 (-1) 0, ZQ.zero;
     ZQ.zero, z8 1 0 0 0 0 0 1 0]
def index (b : Bool) : Fin 2 := if b then 1 else 0
def kernel (x y : Fin 32) : ZQ := ZQ.mul
  (prod 4 (fun j => T (index (bits x j.castSucc)) (index (bits y j.castSucc))))
  (D (index (bits x 4)) (index (bits y 4)))

def rawWord : Fin 2 → Fin 32 → ZQ :=
  ![![z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 1 0 (-1) 0,
    z8 2 0 0 0 0 0 0 0,
    z8 2 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 1 0 (-1) 0,
    z8 (-1) 0 1 0 1 0 (-1) 0,
    z8 2 0 0 0 0 0 0 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 2 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 1 0 (-1) 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 2 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 1 0 (-1) 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 2 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 1 0 (-1) 0],
  ![z8 (-1) 0 1 0 1 0 (-1) 0,
    z8 2 0 0 0 0 0 0 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 (-1) 0 1 0 1 0 (-1) 0,
    z8 2 0 0 0 0 0 0 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 (-1) 0 1 0 1 0 (-1) 0,
    z8 2 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 2 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 1 0 (-1) 0,
    z8 (-1) 0 1 0 1 0 (-1) 0,
    z8 2 0 0 0 0 0 0 0,
    z8 2 0 0 0 0 0 0 0,
    z8 1 0 (-1) 0 1 0 (-1) 0,
    z8 (-2) 0 0 0 0 0 0 0,
    z8 (-1) 0 1 0 (-1) 0 1 0,
    z8 1 0 (-1) 0 (-1) 0 1 0,
    z8 (-2) 0 0 0 0 0 0 0]]

def imageWord : Fin 2 → Fin 32 → ZQ :=
  ![![z8 (-8) 0 0 0 16 0 (-8) 0,
    z8 0 0 8 0 (-8) 0 0 0,
    z8 8 0 0 0 0 0 (-8) 0,
    z8 16 0 (-8) 0 (-8) 0 0 0,
    z8 (-8) 0 0 0 16 0 (-8) 0,
    z8 0 0 8 0 (-8) 0 0 0,
    z8 (-8) 0 0 0 0 0 8 0,
    z8 (-16) 0 8 0 8 0 0 0,
    z8 (-8) 0 0 0 16 0 (-8) 0,
    z8 0 0 8 0 (-8) 0 0 0,
    z8 8 0 0 0 0 0 (-8) 0,
    z8 16 0 (-8) 0 (-8) 0 0 0,
    z8 8 0 0 0 (-16) 0 8 0,
    z8 0 0 (-8) 0 8 0 0 0,
    z8 8 0 0 0 0 0 (-8) 0,
    z8 16 0 (-8) 0 (-8) 0 0 0,
    z8 8 0 0 0 0 0 (-8) 0,
    z8 16 0 (-8) 0 (-8) 0 0 0,
    z8 (-8) 0 0 0 16 0 (-8) 0,
    z8 0 0 8 0 (-8) 0 0 0,
    z8 8 0 0 0 0 0 (-8) 0,
    z8 16 0 (-8) 0 (-8) 0 0 0,
    z8 8 0 0 0 (-16) 0 8 0,
    z8 0 0 (-8) 0 8 0 0 0,
    z8 (-8) 0 0 0 0 0 8 0,
    z8 (-16) 0 8 0 8 0 0 0,
    z8 8 0 0 0 (-16) 0 8 0,
    z8 0 0 (-8) 0 8 0 0 0,
    z8 8 0 0 0 0 0 (-8) 0,
    z8 16 0 (-8) 0 (-8) 0 0 0,
    z8 8 0 0 0 (-16) 0 8 0,
    z8 0 0 (-8) 0 8 0 0 0],
  ![z8 0 0 8 0 8 0 0 0,
    z8 8 0 0 0 16 0 (-8) 0,
    z8 16 0 (-8) 0 8 0 0 0,
    z8 (-8) 0 0 0 0 0 (-8) 0,
    z8 0 0 (-8) 0 (-8) 0 0 0,
    z8 (-8) 0 0 0 (-16) 0 8 0,
    z8 16 0 (-8) 0 8 0 0 0,
    z8 (-8) 0 0 0 0 0 (-8) 0,
    z8 0 0 (-8) 0 (-8) 0 0 0,
    z8 (-8) 0 0 0 (-16) 0 8 0,
    z8 (-16) 0 8 0 (-8) 0 0 0,
    z8 8 0 0 0 0 0 8 0,
    z8 0 0 (-8) 0 (-8) 0 0 0,
    z8 (-8) 0 0 0 (-16) 0 8 0,
    z8 16 0 (-8) 0 8 0 0 0,
    z8 (-8) 0 0 0 0 0 (-8) 0,
    z8 16 0 (-8) 0 8 0 0 0,
    z8 (-8) 0 0 0 0 0 (-8) 0,
    z8 0 0 8 0 8 0 0 0,
    z8 8 0 0 0 16 0 (-8) 0,
    z8 (-16) 0 8 0 (-8) 0 0 0,
    z8 8 0 0 0 0 0 8 0,
    z8 0 0 8 0 8 0 0 0,
    z8 8 0 0 0 16 0 (-8) 0,
    z8 16 0 (-8) 0 8 0 0 0,
    z8 (-8) 0 0 0 0 0 (-8) 0,
    z8 0 0 8 0 8 0 0 0,
    z8 8 0 0 0 16 0 (-8) 0,
    z8 16 0 (-8) 0 8 0 0 0,
    z8 (-8) 0 0 0 0 0 (-8) 0,
    z8 0 0 (-8) 0 (-8) 0 0 0,
    z8 (-8) 0 0 0 (-16) 0 8 0]]

theorem rawWord_checked : ∀ i x, rawWord i x = sum 2 (fun b => ZQ.mul
    (W (index (bits x 4)) b)
    (z8 (raw i (Fin.snoc (fun j : Fin 4 => bits x j.castSucc) (decide (b=1)))) 0 0 0 0 0 0 0)) := by
  decide

theorem imageWord_checked : ∀ i x, imageWord i x =
    sum 32 (fun y => ZQ.mul (kernel x y) (rawWord i y)) := by decide

theorem orthogonal_checked : ∀ i j, sum 32 (fun x =>
    ZQ.mul (ZQ.conj (rawWord i x)) (imageWord j x)) = ZQ.zero := by decide

theorem gram_checked : ∀ i j, sum 32 (fun x =>
    ZQ.mul (ZQ.conj (rawWord i x)) (rawWord j x)) =
    if i=j then z8 192 0 (-64) 0 0 0 0 0 else ZQ.zero := by decide

theorem image_gram_checked : ∀ i j, sum 32 (fun x =>
    ZQ.mul (ZQ.conj (imageWord i x)) (imageWord j x)) =
    if i=j then z8 12288 0 (-4096) 0 0 0 0 0 else ZQ.zero := by decide

end MainTheory.FiveQubitCitedGateData
