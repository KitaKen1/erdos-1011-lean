import R5Kernel.S10C5Structure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C5
open scoped BigOperators

def kernelS10RepresentativeMasks : List ℕ := [1, 3, 5, 7, 11, 15, 31, 32, 33, 35, 37, 39, 43, 47, 63, 96, 97, 99, 101, 103, 107, 111, 127, 224, 225, 227, 229, 231, 235, 239, 255, 480, 481, 483, 485, 487, 491, 495, 511, 992, 993, 995, 997, 999, 1003, 1007, 1023]

def kernelS10Row (mask : ℕ) : ℕ × ℕ :=
  match mask with
  | 1 => (1, 14)
  | 3 => (1, 14)
  | 5 => (2, 12)
  | 7 => (2, 12)
  | 11 => (2, 12)
  | 15 => (2, 12)
  | 31 => (2, 10)
  | 32 => (1, 14)
  | 33 => (2, 12)
  | 35 => (2, 12)
  | 37 => (3, 12)
  | 39 => (3, 10)
  | 43 => (3, 10)
  | 47 => (3, 10)
  | 63 => (3, 8)
  | 96 => (2, 12)
  | 97 => (3, 10)
  | 99 => (3, 10)
  | 101 => (4, 10)
  | 103 => (4, 8)
  | 107 => (4, 8)
  | 111 => (4, 6)
  | 127 => (4, 5)
  | 224 => (3, 10)
  | 225 => (4, 8)
  | 227 => (4, 8)
  | 229 => (5, 8)
  | 231 => (5, 6)
  | 235 => (5, 6)
  | 239 => (5, 5)
  | 255 => (5, 4)
  | 480 => (4, 8)
  | 481 => (5, 6)
  | 483 => (5, 5)
  | 485 => (6, 5)
  | 487 => (6, 4)
  | 491 => (6, 4)
  | 495 => (6, 4)
  | 511 => (6, 3)
  | 992 => (5, 4)
  | 993 => (6, 4)
  | 995 => (6, 4)
  | 997 => (7, 4)
  | 999 => (7, 3)
  | 1003 => (7, 3)
  | 1007 => (7, 3)
  | 1023 => (7, 2)
  | _ => (0, 0)

def maskSet (m : Fin 1024) : Finset (Fin 10) := kernelSmallMask 10 m.val

theorem canonical_beta_fields : ∀ m ∈ kernelS10RepresentativeMasks,
    m % 32 ∈ kernelC5CanonicalMasks ∧
    kernelC5Slice (kernelSmallMask 10 m) = kernelC5SmallMask (m % 32) ∧
    kernelC5CanonicalAlpha (m % 32) +
      ((kernelSmallMask 10 m).filter (fun x => ¬ x.val < 5)).card ≤
        (kernelS10Row m).1 := by
  decide +kernel

theorem canonical_beta (m : ℕ) (hm : m ∈ kernelS10RepresentativeMasks)
    (I : Finset (Fin 10)) (hI : I ∈ cycleTypes 10 5)
    (hIR : I ⊆ kernelSmallMask 10 m) : I.card ≤ (kernelS10Row m).1 := by
  obtain ⟨hsmall, hslice, hsize⟩ := canonical_beta_fields m hm
  apply kernel_s10_beta_of_cycle_bound _ (kernelC5CanonicalAlpha (m % 32)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c5_canonical_beta_data (m % 32) hsmall

def coverValue (m : ℕ) : ℕ :=
  let R := kernelSmallMask 10 m
  let row := kernelS10Row m
  row.1 * (R.card * row.2) +
    ∑ p ∈ kernelC5Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0

theorem value_le_cover (m : ℕ) :
    R5Kernel.dualValue (cycleTypes 10 5) (kernelSmallMask 10 m)
        (kernelS10Row m).1 2 (fun _ => (kernelS10Row m).2) ≤ coverValue m := by
  rw [kernel_dualValue_uniform]
  exact Nat.add_le_add_left (kernel_s10_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``value_le_cover

end Erdos1011.S10C5
