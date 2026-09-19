import R5Kernel.S10C7Structure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C7
open scoped BigOperators

def kernelS10RepresentativeMasks : List ℕ := [1, 3, 5, 7, 9, 11, 15, 19, 21, 23, 27, 31, 43, 47, 55, 63, 127, 128, 129, 131, 133, 135, 137, 139, 143, 147, 149, 151, 155, 159, 171, 175, 183, 191, 255, 384, 385, 387, 389, 391, 393, 395, 399, 403, 405, 407, 411, 415, 427, 431, 439, 447, 511, 896, 897, 899, 901, 903, 905, 907, 911, 915, 917, 919, 923, 927, 939, 943, 951, 959, 1023]

def kernelS10Row (mask : ℕ) : ℕ × ℕ :=
  match mask with
  | 1 => (1, 12)
  | 3 => (1, 12)
  | 5 => (2, 10)
  | 7 => (2, 10)
  | 9 => (2, 10)
  | 11 => (2, 10)
  | 15 => (2, 10)
  | 19 => (2, 10)
  | 21 => (3, 10)
  | 23 => (3, 10)
  | 27 => (2, 10)
  | 31 => (3, 8)
  | 43 => (3, 10)
  | 47 => (3, 8)
  | 55 => (3, 8)
  | 63 => (3, 8)
  | 127 => (3, 6)
  | 128 => (1, 12)
  | 129 => (2, 10)
  | 131 => (2, 10)
  | 133 => (3, 10)
  | 135 => (3, 8)
  | 137 => (3, 10)
  | 139 => (3, 8)
  | 143 => (3, 8)
  | 147 => (3, 8)
  | 149 => (4, 8)
  | 151 => (4, 8)
  | 155 => (3, 8)
  | 159 => (4, 6)
  | 171 => (4, 8)
  | 175 => (4, 6)
  | 183 => (4, 6)
  | 191 => (4, 5)
  | 255 => (4, 4)
  | 384 => (2, 10)
  | 385 => (3, 8)
  | 387 => (3, 8)
  | 389 => (4, 8)
  | 391 => (4, 6)
  | 393 => (4, 8)
  | 395 => (4, 6)
  | 399 => (4, 5)
  | 403 => (4, 6)
  | 405 => (5, 6)
  | 407 => (5, 5)
  | 411 => (4, 6)
  | 415 => (5, 4)
  | 427 => (5, 6)
  | 431 => (5, 4)
  | 439 => (5, 4)
  | 447 => (5, 4)
  | 511 => (5, 3)
  | 896 => (3, 8)
  | 897 => (4, 6)
  | 899 => (4, 6)
  | 901 => (5, 6)
  | 903 => (5, 4)
  | 905 => (5, 6)
  | 907 => (5, 4)
  | 911 => (5, 4)
  | 915 => (5, 4)
  | 917 => (6, 4)
  | 919 => (6, 4)
  | 923 => (5, 4)
  | 927 => (6, 3)
  | 939 => (6, 4)
  | 943 => (6, 3)
  | 951 => (6, 3)
  | 959 => (6, 3)
  | 1023 => (6, 2)
  | _ => (0, 0)

def maskSet (m : Fin 1024) : Finset (Fin 10) := kernelSmallMask 10 m.val

theorem canonical_beta_fields : ∀ m ∈ kernelS10RepresentativeMasks,
    m % 128 ∈ kernelC7CanonicalMasks ∧
    kernelC7Slice (kernelSmallMask 10 m) = kernelC7SmallMask (m % 128) ∧
    kernelC7CanonicalAlpha (m % 128) +
      ((kernelSmallMask 10 m).filter (fun x => ¬ x.val < 7)).card ≤
        (kernelS10Row m).1 := by
  decide +kernel

theorem canonical_beta (m : ℕ) (hm : m ∈ kernelS10RepresentativeMasks)
    (I : Finset (Fin 10)) (hI : I ∈ cycleTypes 10 7)
    (hIR : I ⊆ kernelSmallMask 10 m) : I.card ≤ (kernelS10Row m).1 := by
  obtain ⟨hsmall, hslice, hsize⟩ := canonical_beta_fields m hm
  apply kernel_s10_beta_of_cycle_bound _ (kernelC7CanonicalAlpha (m % 128)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c7_canonical_beta_data (m % 128) hsmall

def coverValue (m : ℕ) : ℕ :=
  let R := kernelSmallMask 10 m
  let row := kernelS10Row m
  row.1 * (R.card * row.2) +
    ∑ p ∈ kernelC7Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - (I ∩ R).card * row.2 else 0

theorem value_le_cover (m : ℕ) :
    R5Kernel.dualValue (cycleTypes 10 7) (kernelSmallMask 10 m)
        (kernelS10Row m).1 2 (fun _ => (kernelS10Row m).2) ≤ coverValue m := by
  rw [kernel_dualValue_uniform]
  exact Nat.add_le_add_left (kernel_s10_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``value_le_cover

end Erdos1011.S10C7
