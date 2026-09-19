import R5Kernel.Probes.S11C9Structural

set_option Elab.async false

namespace Erdos1011

def kernelC9Action (d : Fin 18) (x : Fin 9) : Fin 9 :=
  ⟨(if d.val < 9 then x.val + d.val else d.val - x.val) % 9,
    Nat.mod_lt _ (by decide)⟩

def kernelC9CanonicalMasks : List ℕ :=
  [0, 1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 27, 31, 35, 37, 39, 43,
   45, 47, 51, 55, 63, 73, 75, 79, 83, 85, 87, 91, 93, 95, 103, 107,
   111, 119, 127, 171, 175, 183, 191, 219, 223, 239, 255, 511]

def kernelC9SmallMask (m : ℕ) : Finset (Fin 9) :=
  Finset.univ.filter (fun x => (m / 2 ^ x.val) % 2 = 1)

def kernelC9IsoPrefix (k : Fin 3) : Finset (Fin 2) :=
  Finset.univ.filter (fun x => x.val < k.val)

def kernelS11C9Pack (c : Fin 512) (k : Fin 3) : Fin 2048 :=
  ⟨(c.val + 512 * (2 ^ k.val - 1)) % 2048, Nat.mod_lt _ (by decide)⟩

end Erdos1011
