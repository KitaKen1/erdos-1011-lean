import R5Kernel.Probes.S11C5CanonicalDefinitions

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC11CanonicalMasks : List ℕ :=
  [0, 1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 27, 31, 33, 35, 37, 39,
   43, 45, 47, 51, 55, 63, 67, 69, 71, 73, 75, 77, 79, 83, 85, 87, 91,
   93, 95, 99, 103, 107, 111, 119, 127, 137, 139, 143, 147, 149, 151,
   153, 155, 157, 159, 163, 165, 167, 171, 173, 175, 179, 183, 187, 189,
   191, 199, 203, 207, 215, 219, 223, 231, 239, 255, 293, 295, 299, 301,
   303, 307, 311, 319, 331, 335, 339, 341, 343, 347, 349, 351, 359, 363,
   365, 367, 371, 375, 379, 381, 383, 411, 415, 427, 431, 439, 443, 447,
   463, 471, 479, 495, 511, 683, 687, 695, 703, 727, 731, 735, 751, 767,
   879, 887, 895, 959, 991, 1023, 2047]

def kernelC11SmallMask (m : ℕ) : Finset (Fin 11) :=
  Finset.univ.filter (fun x => (m / 2 ^ x.val) % 2 = 1)

def kernelC11CanonicalRep (i : Fin 125) : Fin 2048 :=
  ⟨kernelC11CanonicalMasks.getD i.val 0, by
    fin_cases i <;> decide⟩

theorem kernel_c11_canonical_rep_mem (i : Fin 125) :
    (kernelC11CanonicalRep i).val ∈ kernelC11CanonicalMasks := by
  fin_cases i <;> decide

end Erdos1011
