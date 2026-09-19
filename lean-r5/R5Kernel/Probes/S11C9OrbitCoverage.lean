import R5Kernel.Probes.S11C9OrbitAction
import R5Kernel.Probes.S11C9OrbitWitnessCoverage

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Erdos1011

theorem kernelC9_all_subsets_covered : ∀ J : Finset (Fin 9),
    ∃ c : Fin 512, ∃ d : Fin 18, c.val ∈ kernelC9CanonicalMasks ∧
      (kernelC9SmallMask c.val).map (kernelC9ActionEquiv d).toEmbedding = J := by
  exact kernel_c9_orbit_witness_coverage

run_cmd R5Kernel.checkStandardAxioms ``kernelC9_all_subsets_covered

end Erdos1011
