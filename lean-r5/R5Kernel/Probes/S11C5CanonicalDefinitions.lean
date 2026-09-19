import R5Kernel.Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.all false
set_option maxErrors 1

open Lean Elab Command

namespace Erdos1011
open scoped BigOperators

def cycleRel (s ell : ℕ) (x y : Fin s) : Prop :=
  x.val < ell ∧ y.val < ell ∧
    (((x.val + 1) % ell = y.val) ∨ ((y.val + 1) % ell = x.val))

instance cycleRel_decidable (s ell : ℕ) : DecidableRel (cycleRel s ell) := by
  intro x y
  unfold cycleRel
  infer_instance

def cycleGraph (s ell : ℕ) : SimpleGraph (Fin s) :=
  SimpleGraph.fromRel (cycleRel s ell)

instance cycleGraph_decidable (s ell : ℕ) :
    DecidableRel (cycleGraph s ell).Adj := by
  intro x y
  change Decidable (x ≠ y ∧ (cycleRel s ell x y ∨ cycleRel s ell y x))
  infer_instance

def cycleTypes (s ell : ℕ) : Finset (Finset (Fin s)) :=
  Finset.univ.filter (fun I =>
    I.Nonempty ∧ (cycleGraph s ell).IsIndepSet (I : Set (Fin s)))

structure R5RepDualRecord11 where
  mask : Fin 2048
  beta : ℕ
  nums : Fin 11 → ℕ
  dens : Fin 11 → ℕ
  boundNum : ℕ
  boundDen : ℕ

def vec11 (xs : List ℕ) : Fin 11 → ℕ := fun i => xs.getD i.1 0

def vec11one (xs : List ℕ) : Fin 11 → ℕ := fun i => xs.getD i.1 1

def mkR5RepDual11 (mask beta : ℕ) (nums dens : List ℕ)
    (boundNum boundDen : ℕ) : R5RepDualRecord11 :=
  { mask := ⟨mask % 2048, by exact Nat.mod_lt _ (by norm_num)⟩
    beta := beta
    nums := vec11 nums
    dens := vec11one dens
    boundNum := boundNum
    boundDen := boundDen }

def r5RepMaskSet11 (m : Fin 2048) : Finset (Fin 11) :=
  Finset.univ.filter (fun i => (m.1 / (2 ^ i.1)) % 2 = 1)

def r5RepScaledNum11 (r : R5RepDualRecord11) (i : Fin 11) : ℕ :=
  (2 * r.nums i) / r.dens i

def r5RepNatScaledValue11 (r : R5RepDualRecord11) : ℕ :=
  let R := r5RepMaskSet11 r.mask
  let U := cycleTypes 11 5
  r.beta * (∑ e ∈ R, r5RepScaledNum11 r e) +
    ∑ I ∈ U, if (I ∩ R).Nonempty then
      2 * I.card - ∑ e ∈ I,
        if e ∈ R then r5RepScaledNum11 r e else 0
      else 0

def kernelS11RepresentativeMasks : List Nat := [1, 3, 5, 7, 11, 15, 31, 32, 33, 35, 37, 39, 43, 47, 63, 96, 97, 99, 101, 103, 107, 111, 127, 224, 225, 227, 229, 231, 235, 239, 255, 480, 481, 483, 485, 487, 491, 495, 511, 992, 993, 995, 997, 999, 1003, 1007, 1023, 2016, 2017, 2019, 2021, 2023, 2027, 2031, 2047]

def kernelS11Row (mask : Nat) : R5RepDualRecord11 :=
  match mask with
  | 1 => mkR5RepDual11 1 1 [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 8 1
  | 3 => mkR5RepDual11 3 1 [8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 16 1
  | 5 => mkR5RepDual11 5 2 [7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 30 1
  | 7 => mkR5RepDual11 7 2 [7, 8, 7, 0, 0, 0, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 46 1
  | 11 => mkR5RepDual11 11 2 [7, 7, 0, 6, 0, 0, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 43 1
  | 15 => mkR5RepDual11 15 2 [6, 7, 7, 6, 0, 0, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 56 1
  | 31 => mkR5RepDual11 31 2 [6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 65 1
  | 32 => mkR5RepDual11 32 1 [0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 8 1
  | 33 => mkR5RepDual11 33 2 [7, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 30 1
  | 35 => mkR5RepDual11 35 2 [7, 7, 0, 0, 0, 7, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 43 1
  | 37 => mkR5RepDual11 37 3 [6, 0, 6, 0, 0, 7, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 61 1
  | 39 => mkR5RepDual11 39 3 [6, 6, 6, 0, 0, 6, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 78 1
  | 43 => mkR5RepDual11 43 3 [6, 6, 0, 5, 0, 7, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 76 1
  | 47 => mkR5RepDual11 47 3 [5, 6, 6, 5, 0, 6, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 89 1
  | 63 => mkR5RepDual11 63 3 [5, 5, 5, 5, 5, 5, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 96 1
  | 96 => mkR5RepDual11 96 2 [0, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 28 1
  | 97 => mkR5RepDual11 97 3 [5, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 59 1
  | 99 => mkR5RepDual11 99 3 [5, 5, 0, 0, 0, 6, 6, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 72 1
  | 101 => mkR5RepDual11 101 4 [5, 0, 5, 0, 0, 6, 6, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 94 1
  | 103 => mkR5RepDual11 103 4 [5, 5, 5, 0, 0, 5, 5, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 108 1
  | 107 => mkR5RepDual11 107 4 [5, 5, 0, 4, 0, 6, 6, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 109 1
  | 111 => mkR5RepDual11 111 4 [4, 5, 5, 4, 0, 5, 5, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 118 1
  | 127 => mkR5RepDual11 127 4 [4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 119 1
  | 224 => mkR5RepDual11 224 3 [0, 0, 0, 0, 0, 6, 6, 6, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 54 1
  | 225 => mkR5RepDual11 225 4 [4, 0, 0, 0, 0, 5, 5, 5, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 87 1
  | 227 => mkR5RepDual11 227 4 [4, 4, 0, 0, 0, 5, 5, 5, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 99 1
  | 229 => mkR5RepDual11 229 5 [3, 0, 3, 0, 0, 5, 5, 5, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 123 1
  | 231 => mkR5RepDual11 231 5 [3, 4, 3, 0, 0, 4, 4, 4, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 130 1
  | 235 => mkR5RepDual11 235 5 [3, 3, 0, 2, 0, 5, 5, 5, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 135 1
  | 239 => mkR5RepDual11 239 5 [2, 3, 3, 3, 0, 4, 3, 4, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 136 1
  | 255 => mkR5RepDual11 255 5 [5, 5, 5, 5, 5, 5, 5, 5, 0, 0, 0] [2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1] 124 1
  | 480 => mkR5RepDual11 480 4 [0, 0, 0, 0, 0, 5, 5, 5, 5, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 80 1
  | 481 => mkR5RepDual11 481 5 [3, 0, 0, 0, 0, 4, 4, 4, 4, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 109 1
  | 483 => mkR5RepDual11 483 5 [3, 3, 0, 0, 0, 4, 4, 4, 4, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 118 1
  | 485 => mkR5RepDual11 485 6 [2, 0, 2, 0, 0, 4, 4, 4, 4, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 138 1
  | 487 => mkR5RepDual11 487 6 [2, 3, 2, 0, 0, 3, 3, 3, 3, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 134 1
  | 491 => mkR5RepDual11 491 6 [2, 2, 0, 1, 0, 3, 3, 3, 3, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 142 1
  | 495 => mkR5RepDual11 495 6 [3, 5, 5, 3, 0, 5, 5, 5, 5, 0, 0] [2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1] 132 1
  | 511 => mkR5RepDual11 511 6 [2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 117 1
  | 992 => mkR5RepDual11 992 5 [0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 100 1
  | 993 => mkR5RepDual11 993 6 [1, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 118 1
  | 995 => mkR5RepDual11 995 6 [3, 3, 0, 0, 0, 5, 5, 5, 5, 5, 0] [2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1] 239 2
  | 997 => mkR5RepDual11 997 7 [1, 0, 1, 0, 0, 3, 3, 3, 3, 3, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 138 1
  | 999 => mkR5RepDual11 999 7 [2, 2, 2, 0, 0, 2, 2, 2, 2, 2, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 126 1
  | 1003 => mkR5RepDual11 1003 7 [3, 3, 0, 1, 0, 5, 5, 5, 5, 5, 0] [2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1] 136 1
  | 1007 => mkR5RepDual11 1007 7 [1, 2, 2, 1, 0, 2, 2, 2, 2, 2, 0] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 122 1
  | 1023 => mkR5RepDual11 1023 7 [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0] [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1] 110 1
  | 2016 => mkR5RepDual11 2016 6 [0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 102 1
  | 2017 => mkR5RepDual11 2017 7 [1, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 111 1
  | 2019 => mkR5RepDual11 2019 7 [1, 1, 0, 0, 0, 2, 2, 2, 2, 2, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 108 1
  | 2021 => mkR5RepDual11 2021 8 [1, 0, 1, 0, 0, 2, 2, 2, 2, 2, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 126 1
  | 2023 => mkR5RepDual11 2023 8 [1, 3, 1, 0, 0, 3, 3, 3, 3, 3, 3] [1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2] 115 1
  | 2027 => mkR5RepDual11 2027 8 [1, 1, 0, 0, 0, 2, 2, 2, 2, 2, 2] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 123 1
  | 2031 => mkR5RepDual11 2031 8 [1, 3, 1, 1, 0, 3, 3, 3, 3, 3, 3] [1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2] 225 2
  | 2047 => mkR5RepDual11 2047 8 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 88 1
  | _ => mkR5RepDual11 0 0 [] [] 0 1

end Erdos1011
