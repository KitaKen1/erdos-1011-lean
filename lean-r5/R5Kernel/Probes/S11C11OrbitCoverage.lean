import R5Kernel.Probes.S11C11OrbitCoverageHigh

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1011

theorem kernelC11_all_subsets_covered : ∀ J : Finset (Fin 11),
      ∃ c : Fin 126, ∃ d : Fin 22,
      (kernelC11SmallMask (kernelC11CanonicalRep126 c).val).map
        (kernelC11ActionEquiv d).toEmbedding = J := by
  intro J
  by_cases hJ : J.card ≤ 5
  · obtain ⟨c, d, h⟩ := kernelC11_all_subsets_covered_card_le5 J hJ
    let c126 : Fin 126 := ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩
    have hcEq : kernelC11CanonicalRep126 c126 = kernelC11CanonicalRep c := by
      exact kernel_c11_canonical_rep126_prefix c
    refine ⟨c126, d, ?_⟩
    simpa only [hcEq] using h
  · exact kernelC11_all_subsets_covered_card_ge6 J (by omega)

run_cmd R5Kernel.checkStandardAxioms ``kernelC11_all_subsets_covered

end Erdos1011
