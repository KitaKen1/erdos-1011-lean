import R5Kernel.Probes.S11C11OrbitCoverageComplement

set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1011

theorem kernelC11_all_subsets_covered_card_ge6 : ∀ J : Finset (Fin 11),
    6 ≤ J.card →
      ∃ c : Fin 126, ∃ d : Fin 22,
        (kernelC11SmallMask (kernelC11CanonicalRep126 c).val).map
          (kernelC11ActionEquiv d).toEmbedding = J := by
  intro J hJ
  let Jc : Finset (Fin 11) := Finset.univ \ J
  have hJc : Jc.card ≤ 5 := by
    dsimp [Jc]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ J)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, d, hmap⟩ :=
    kernelC11_all_subsets_covered_card_le5 Jc hJc
  let c126 : Fin 126 := ⟨c.val, Nat.lt_succ_of_lt c.isLt⟩
  have hcEq : kernelC11CanonicalRep126 c126 = kernelC11CanonicalRep c := by
    exact kernel_c11_canonical_rep126_prefix c
  have hmap' : (kernelC11SmallMask (kernelC11CanonicalRep126 c126).val).map
      (kernelC11ActionEquiv d).toEmbedding = Jc := by
    simpa only [hcEq] using hmap
  obtain ⟨c', q, hcomp⟩ := kernel_c11_complement_canonical_orbit c126
  obtain ⟨t, ht⟩ := kernel_c11_action_comp q d
  have heq : (kernelC11ActionEquiv t).toEmbedding =
      (kernelC11ActionEquiv q).toEmbedding.trans
        (kernelC11ActionEquiv d).toEmbedding := by
    apply DFunLike.ext
    intro x
    change kernelC11Action t x =
      kernelC11Action d (kernelC11Action q x)
    exact ht x
  refine ⟨c', t, ?_⟩
  calc
    (kernelC11SmallMask (kernelC11CanonicalRep126 c').val).map
          (kernelC11ActionEquiv t).toEmbedding =
        ((kernelC11SmallMask (kernelC11CanonicalRep126 c').val).map
          (kernelC11ActionEquiv q).toEmbedding).map
            (kernelC11ActionEquiv d).toEmbedding := by
      rw [heq, Finset.map_map]
    _ = ((Finset.univ : Finset (Fin 11)) \
          kernelC11SmallMask (kernelC11CanonicalRep126 c126).val).map
            (kernelC11ActionEquiv d).toEmbedding := by
      rw [hcomp]
    _ = Finset.univ \ (kernelC11SmallMask (kernelC11CanonicalRep126 c126).val).map
          (kernelC11ActionEquiv d).toEmbedding :=
      kernel_c11_map_complement (kernelC11ActionEquiv d)
        (kernelC11SmallMask (kernelC11CanonicalRep126 c126).val)
    _ = Finset.univ \ Jc := by rw [hmap']
    _ = J := by
      dsimp [Jc]
      exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ J)

run_cmd R5Kernel.checkStandardAxioms ``kernelC11_all_subsets_covered_card_ge6

end Erdos1011
