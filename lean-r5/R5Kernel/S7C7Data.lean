import R5Kernel.S7C7Structure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S7C7
open scoped BigOperators

def kernelS7RepresentativeMasks : List ℕ := [1, 3, 5, 7, 9, 11, 15, 19, 21, 23, 27, 31, 43, 47, 55, 63, 127]

def kernelS7Row (mask : ℕ) : ℕ × List ℕ :=
  match mask with
  | 1 => (1, [6, 6, 6, 6, 6, 6, 6])
  | 3 => (1, [6, 6, 6, 6, 6, 6, 6])
  | 5 => (2, [4, 4, 4, 4, 4, 4, 4])
  | 7 => (2, [4, 4, 4, 4, 4, 4, 4])
  | 9 => (2, [4, 4, 4, 4, 4, 4, 4])
  | 11 => (2, [4, 4, 4, 4, 4, 4, 4])
  | 15 => (2, [4, 4, 4, 4, 4, 4, 4])
  | 19 => (2, [4, 4, 4, 4, 4, 4, 4])
  | 21 => (3, [3, 3, 3, 3, 3, 3, 3])
  | 23 => (3, [3, 3, 3, 3, 3, 3, 3])
  | 27 => (2, [4, 4, 4, 4, 4, 4, 4])
  | 31 => (3, [3, 3, 3, 3, 3, 3, 3])
  | 43 => (3, [2, 2, 2, 2, 2, 2, 2])
  | 47 => (3, [2, 2, 2, 2, 2, 2, 2])
  | 55 => (3, [2, 2, 2, 2, 2, 2, 2])
  | 63 => (3, [2, 2, 2, 2, 2, 2, 2])
  | 127 => (3, [2, 2, 2, 2, 2, 2, 2])
  | _ => (0, [])

def weight (m : ℕ) (i : Fin 7) : ℕ := (kernelS7Row m).2.getD i.val 0

def maskSet (m : Fin 128) : Finset (Fin 7) := kernelSmallMask 7 m.val

theorem canonical_beta_fields : ∀ m ∈ kernelS7RepresentativeMasks,
    m % 128 ∈ kernelC7CanonicalMasks ∧
    kernelC7Slice (kernelSmallMask 7 m) = kernelC7SmallMask (m % 128) ∧
    kernelC7CanonicalAlpha (m % 128) +
      ((kernelSmallMask 7 m).filter (fun x => ¬ x.val < 7)).card ≤
        (kernelS7Row m).1 := by
  decide +kernel

theorem canonical_beta (m : ℕ) (hm : m ∈ kernelS7RepresentativeMasks)
    (I : Finset (Fin 7)) (hI : I ∈ cycleTypes 7 7)
    (hIR : I ⊆ kernelSmallMask 7 m) : I.card ≤ (kernelS7Row m).1 := by
  obtain ⟨hsmall, hslice, hsize⟩ := canonical_beta_fields m hm
  apply kernel_s7_beta_of_cycle_bound _ (kernelC7CanonicalAlpha (m % 128)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c7_canonical_beta_data (m % 128) hsmall

def coverValue (m : ℕ) : ℕ :=
  let R := kernelSmallMask 7 m
  (kernelS7Row m).1 * (∑ x ∈ R, weight m x) +
    ∑ p ∈ kernelC7Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - ∑ x ∈ I, if x ∈ R then weight m x else 0
      else 0

theorem value_le_cover (m : ℕ) :
    R5Kernel.dualValue (cycleTypes 7 7) (kernelSmallMask 7 m)
        (kernelS7Row m).1 2 (weight m) ≤ coverValue m := by
  unfold R5Kernel.dualValue coverValue
  exact Nat.add_le_add_left (kernel_s7_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``value_le_cover

end Erdos1011.S7C7
