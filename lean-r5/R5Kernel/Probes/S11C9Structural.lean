import R5Kernel.Probes.S11C9Local

set_option Elab.async false

namespace Erdos1011

def kernelC9IsoEmbedding : Fin 2 ↪ Fin 11 where
  toFun x := ⟨x.val + 9, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin 11 => z.val) h
    apply Fin.ext
    change x.val + 9 = y.val + 9 at hv
    omega

def kernelC9IsoSlice (I : Finset (Fin 11)) : Finset (Fin 2) :=
  Finset.univ.filter (fun x => kernelC9IsoEmbedding x ∈ I)

def kernelC9JoinParts (p : Finset (Fin 9) × Finset (Fin 2)) : Finset (Fin 11) :=
  p.1.map kernelC9Embedding ∪ p.2.map kernelC9IsoEmbedding

end Erdos1011
