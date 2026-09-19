import R5Kernel.Probes.S11C11LowCardCoverage
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1011

theorem kernelC11_all_subsets_covered_card_le5 : ∀ J : Finset (Fin 11),
    J.card ≤ 5 →
      ∃ c : Fin 125, ∃ d : Fin 22,
        (kernelC11SmallMask (kernelC11CanonicalRep c).val).map
          (kernelC11ActionEquiv d).toEmbedding = J := by
  exact kernel_c11_low_card_coverage

run_cmd R5Kernel.checkStandardAxioms ``kernelC11_all_subsets_covered_card_le5

end Erdos1011
