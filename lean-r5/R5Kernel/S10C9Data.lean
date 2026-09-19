import R5Kernel.S10C9Structure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C9
open scoped BigOperators

def kernelS10RepresentativeMasks : List ℕ := [1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 27, 31, 35, 37, 39, 43, 45, 47, 51, 55, 63, 73, 75, 79, 83, 85, 87, 91, 93, 95, 103, 107, 111, 119, 127, 171, 175, 183, 191, 219, 223, 239, 255, 511, 512, 513, 515, 517, 519, 521, 523, 527, 529, 531, 533, 535, 539, 543, 547, 549, 551, 555, 557, 559, 563, 567, 575, 585, 587, 591, 595, 597, 599, 603, 605, 607, 615, 619, 623, 631, 639, 683, 687, 695, 703, 731, 735, 751, 767, 1023]

def kernelS10Row (mask : ℕ) : ℕ × ℕ :=
  match mask with
  | 1 => (1, 10)
  | 3 => (1, 10)
  | 5 => (2, 8)
  | 7 => (2, 8)
  | 9 => (2, 10)
  | 11 => (2, 8)
  | 15 => (2, 8)
  | 17 => (2, 8)
  | 19 => (2, 8)
  | 21 => (3, 8)
  | 23 => (3, 8)
  | 27 => (2, 8)
  | 31 => (3, 6)
  | 35 => (2, 8)
  | 37 => (3, 8)
  | 39 => (3, 8)
  | 43 => (3, 8)
  | 45 => (3, 8)
  | 47 => (3, 6)
  | 51 => (2, 8)
  | 55 => (3, 6)
  | 63 => (3, 6)
  | 73 => (3, 8)
  | 75 => (3, 8)
  | 79 => (3, 6)
  | 83 => (3, 8)
  | 85 => (4, 6)
  | 87 => (4, 6)
  | 91 => (3, 6)
  | 93 => (4, 6)
  | 95 => (4, 6)
  | 103 => (3, 6)
  | 107 => (3, 6)
  | 111 => (3, 6)
  | 119 => (4, 6)
  | 127 => (4, 4)
  | 171 => (4, 6)
  | 175 => (4, 6)
  | 183 => (4, 6)
  | 191 => (4, 4)
  | 219 => (3, 6)
  | 223 => (4, 4)
  | 239 => (4, 4)
  | 255 => (4, 4)
  | 511 => (4, 3)
  | 512 => (1, 10)
  | 513 => (2, 10)
  | 515 => (2, 8)
  | 517 => (3, 8)
  | 519 => (3, 6)
  | 521 => (3, 8)
  | 523 => (3, 6)
  | 527 => (3, 6)
  | 529 => (3, 8)
  | 531 => (3, 6)
  | 533 => (4, 6)
  | 535 => (4, 6)
  | 539 => (3, 6)
  | 543 => (4, 4)
  | 547 => (3, 6)
  | 549 => (4, 6)
  | 551 => (4, 6)
  | 555 => (4, 6)
  | 557 => (4, 6)
  | 559 => (4, 4)
  | 563 => (3, 6)
  | 567 => (4, 4)
  | 575 => (4, 4)
  | 585 => (4, 6)
  | 587 => (4, 6)
  | 591 => (4, 4)
  | 595 => (4, 6)
  | 597 => (5, 6)
  | 599 => (5, 4)
  | 603 => (4, 4)
  | 605 => (5, 4)
  | 607 => (5, 4)
  | 615 => (4, 4)
  | 619 => (4, 4)
  | 623 => (4, 4)
  | 631 => (5, 4)
  | 639 => (5, 3)
  | 683 => (5, 4)
  | 687 => (5, 4)
  | 695 => (5, 4)
  | 703 => (5, 3)
  | 731 => (4, 4)
  | 735 => (5, 3)
  | 751 => (5, 3)
  | 767 => (5, 3)
  | 1023 => (5, 2)
  | _ => (0, 0)

def maskSet (m : Fin 1024) : Finset (Fin 10) := kernelSmallMask 10 m.val

theorem canonical_beta_fields : ∀ m ∈ kernelS10RepresentativeMasks,
    m % 512 ∈ kernelC9CanonicalMasks ∧
    kernelC9Slice (kernelSmallMask 10 m) = kernelC9SmallMask (m % 512) ∧
    kernelC9CanonicalAlpha (m % 512) +
      ((kernelSmallMask 10 m).filter (fun x => ¬ x.val < 9)).card ≤
        (kernelS10Row m).1 := by
  decide +kernel

theorem canonical_beta (m : ℕ) (hm : m ∈ kernelS10RepresentativeMasks)
    (I : Finset (Fin 10)) (hI : I ∈ cycleTypes 10 9)
    (hIR : I ⊆ kernelSmallMask 10 m) : I.card ≤ (kernelS10Row m).1 := by
  obtain ⟨hsmall, hslice, hsize⟩ := canonical_beta_fields m hm
  apply kernel_s10_beta_of_cycle_bound _ (kernelC9CanonicalAlpha (m % 512)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c9_canonical_beta_data (m % 512) hsmall

def coverValue (m : ℕ) : ℕ :=
  let R := kernelSmallMask 10 m
  let row := kernelS10Row m
  row.1 * (R.card * row.2) +
    ∑ p ∈ kernelC9Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0

theorem value_le_cover (m : ℕ) :
    R5Kernel.dualValue (cycleTypes 10 9) (kernelSmallMask 10 m)
        (kernelS10Row m).1 2 (fun _ => (kernelS10Row m).2) ≤ coverValue m := by
  rw [kernel_dualValue_uniform]
  exact Nat.add_le_add_left (kernel_s10_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``value_le_cover

end Erdos1011.S10C9
