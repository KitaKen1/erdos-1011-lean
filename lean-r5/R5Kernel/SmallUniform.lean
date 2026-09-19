import R5Kernel.Probes.CycleSurplusBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace Erdos1011
open scoped BigOperators

/-- Decode a finite subset; no correctness assumption is attached to its mask. -/
def kernelSmallMask (s mask : ℕ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => mask / (2 ^ i.val) % 2 = 1)

def kernelSmallEncode {s : ℕ} (R : Finset (Fin s)) : Fin (2 ^ s) :=
  ⟨(∑ i ∈ R, 2 ^ i.val) % (2 ^ s), Nat.mod_lt _ (by positivity)⟩

/-- Uniform weights reduce the inner vertex sum to an intersection cardinality. -/
theorem kernel_dualValue_uniform {s : ℕ} (U : Finset (Finset (Fin s)))
    (R : Finset (Fin s)) (b d w : ℕ) :
    R5Kernel.dualValue U R b d (fun _ => w) =
      b * (R.card * w) +
        ∑ I ∈ U, if (I ∩ R).Nonempty then
          d * I.card - (I ∩ R).card * w else 0 := by
  unfold R5Kernel.dualValue
  simp only [Finset.sum_const, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hsum : (∑ e ∈ I, if e ∈ R then w else 0) = (I ∩ R).card * w := by
    rw [← Finset.sum_filter]
    have heq : I.filter (fun e => e ∈ R) = I ∩ R := by
      ext e
      simp
    rw [heq]
    simp
  rw [hsum]

run_cmd R5Kernel.checkStandardAxioms ``kernel_dualValue_uniform

end Erdos1011
