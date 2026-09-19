import R5Kernel.S7C5Structure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S7C5
open scoped BigOperators

def kernelS7RepresentativeMasks : List ℕ := [1, 3, 5, 7, 11, 15, 31, 32, 33, 35, 37, 39, 43, 47, 63, 96, 97, 99, 101, 103, 107, 111, 127]

def kernelS7Row (mask : ℕ) : ℕ × List ℕ :=
  match mask with
  | 1 => (1, [8, 0, 0, 0, 0, 0, 0])
  | 3 => (1, [8, 8, 0, 0, 0, 0, 0])
  | 5 => (2, [6, 0, 6, 0, 0, 0, 0])
  | 7 => (2, [6, 8, 6, 0, 0, 0, 0])
  | 11 => (2, [6, 6, 0, 4, 0, 0, 0])
  | 15 => (2, [4, 6, 6, 4, 0, 0, 0])
  | 31 => (2, [4, 4, 4, 4, 4, 0, 0])
  | 32 => (1, [0, 0, 0, 0, 0, 8, 0])
  | 33 => (2, [6, 0, 0, 0, 0, 8, 0])
  | 35 => (2, [6, 6, 0, 0, 0, 6, 0])
  | 37 => (3, [2, 0, 4, 0, 0, 6, 0])
  | 39 => (3, [4, 4, 4, 0, 0, 4, 0])
  | 43 => (3, [4, 4, 0, 2, 0, 6, 0])
  | 47 => (3, [2, 4, 4, 2, 0, 4, 0])
  | 63 => (3, [3, 3, 3, 3, 3, 3, 0])
  | 96 => (2, [0, 0, 0, 0, 0, 6, 6])
  | 97 => (3, [0, 0, 0, 0, 0, 6, 6])
  | 99 => (3, [2, 2, 0, 0, 0, 4, 4])
  | 101 => (4, [2, 0, 2, 0, 0, 4, 4])
  | 103 => (4, [2, 2, 2, 0, 0, 4, 4])
  | 107 => (4, [2, 2, 0, 0, 0, 4, 4])
  | 111 => (4, [2, 3, 2, 1, 0, 3, 3])
  | 127 => (4, [2, 2, 2, 2, 2, 2, 2])
  | _ => (0, [])

def weight (m : ℕ) (i : Fin 7) : ℕ := (kernelS7Row m).2.getD i.val 0

def maskSet (m : Fin 128) : Finset (Fin 7) := kernelSmallMask 7 m.val

theorem canonical_beta_fields : ∀ m ∈ kernelS7RepresentativeMasks,
    m % 32 ∈ kernelC5CanonicalMasks ∧
    kernelC5Slice (kernelSmallMask 7 m) = kernelC5SmallMask (m % 32) ∧
    kernelC5CanonicalAlpha (m % 32) +
      ((kernelSmallMask 7 m).filter (fun x => ¬ x.val < 5)).card ≤
        (kernelS7Row m).1 := by
  decide +kernel

theorem canonical_beta (m : ℕ) (hm : m ∈ kernelS7RepresentativeMasks)
    (I : Finset (Fin 7)) (hI : I ∈ cycleTypes 7 5)
    (hIR : I ⊆ kernelSmallMask 7 m) : I.card ≤ (kernelS7Row m).1 := by
  obtain ⟨hsmall, hslice, hsize⟩ := canonical_beta_fields m hm
  apply kernel_s7_beta_of_cycle_bound _ (kernelC5CanonicalAlpha (m % 32)) _ ?_
    hsize I (Finset.mem_filter.mp hI).2.2 hIR
  rw [hslice]
  exact kernel_c5_canonical_beta_data (m % 32) hsmall

def coverValue (m : ℕ) : ℕ :=
  let R := kernelSmallMask 7 m
  (kernelS7Row m).1 * (∑ x ∈ R, weight m x) +
    ∑ p ∈ kernelC5Product, let I := kernelJoinParts p
      if (I ∩ R).Nonempty then
        2 * I.card - ∑ x ∈ I, if x ∈ R then weight m x else 0
      else 0

theorem value_le_cover (m : ℕ) :
    R5Kernel.dualValue (cycleTypes 7 5) (kernelSmallMask 7 m)
        (kernelS7Row m).1 2 (weight m) ≤ coverValue m := by
  unfold R5Kernel.dualValue coverValue
  exact Nat.add_le_add_left (kernel_s7_sum_le_cover _) _

run_cmd R5Kernel.checkStandardAxioms ``canonical_beta
run_cmd R5Kernel.checkStandardAxioms ``value_le_cover

end Erdos1011.S7C5
