import R5Kernel.Probes.S11C5Cover

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Erdos1011

def kernelS11Split : Fin 5 ⊕ Fin 6 ≃ Fin 11 := finSumFinEquiv

def kernelBlockEquiv (a : Fin 5 ≃ Fin 5) (b : Fin 6 ≃ Fin 6) : Fin 11 ≃ Fin 11 :=
  kernelS11Split.symm.trans ((Equiv.sumCongr a b).trans kernelS11Split)

theorem kernel_s11_split_adj : ∀ x y : Fin 5 ⊕ Fin 6,
    (cycleGraph 11 5).Adj (kernelS11Split x) (kernelS11Split y) ↔
      match x, y with
      | Sum.inl u, Sum.inl v => (cycleGraph 5 5).Adj u v
      | _, _ => False := by
  intro x y
  rcases x with x | x <;> rcases y with y | y
  all_goals (revert x y; decide +kernel)

theorem kernel_block_apply_sum (a : Fin 5 ≃ Fin 5) (b : Fin 6 ≃ Fin 6)
    (x : Fin 5 ⊕ Fin 6) :
    kernelBlockEquiv a b (kernelS11Split x) = kernelS11Split (Sum.map a b x) := by
  simp [kernelBlockEquiv]

theorem kernel_block_apply_cycle (a : Fin 5 ≃ Fin 5) (b : Fin 6 ≃ Fin 6) (x : Fin 5) :
    kernelBlockEquiv a b (kernelC5Embedding x) = kernelC5Embedding (a x) := by
  exact kernel_block_apply_sum a b (Sum.inl x)

theorem kernel_iso_embedding_as_sum (x : Fin 6) :
    kernelIsoEmbedding x = kernelS11Split (Sum.inr x) := by
  apply Fin.ext
  exact Nat.add_comm _ _

theorem kernel_block_apply_iso (a : Fin 5 ≃ Fin 5) (b : Fin 6 ≃ Fin 6) (x : Fin 6) :
    kernelBlockEquiv a b (kernelIsoEmbedding x) = kernelIsoEmbedding (b x) := by
  rw [kernel_iso_embedding_as_sum, kernel_iso_embedding_as_sum]
  exact kernel_block_apply_sum a b (Sum.inr x)

theorem kernel_block_adj (a : Fin 5 ≃ Fin 5) (b : Fin 6 ≃ Fin 6)
    (ha : ∀ x y, (cycleGraph 5 5).Adj (a x) (a y) ↔ (cycleGraph 5 5).Adj x y) :
    ∀ x y, (cycleGraph 11 5).Adj (kernelBlockEquiv a b x) (kernelBlockEquiv a b y) ↔
      (cycleGraph 11 5).Adj x y := by
  intro x y
  obtain ⟨x, rfl⟩ := kernelS11Split.surjective x
  obtain ⟨y, rfl⟩ := kernelS11Split.surjective y
  rw [kernel_block_apply_sum, kernel_block_apply_sum, kernel_s11_split_adj, kernel_s11_split_adj]
  cases x with
  | inl x => cases y with
    | inl y => exact ha x y
    | inr y => rfl
  | inr x => cases y <;> rfl

theorem kernel_block_map_join (a : Fin 5 ≃ Fin 5) (b : Fin 6 ≃ Fin 6)
    (J : Finset (Fin 5)) (K : Finset (Fin 6)) :
    (kernelJoinParts (J, K)).map (kernelBlockEquiv a b).toEmbedding =
      kernelJoinParts (J.map a.toEmbedding, K.map b.toEmbedding) := by
  have hc : kernelC5Embedding.trans (kernelBlockEquiv a b).toEmbedding =
      a.toEmbedding.trans kernelC5Embedding := by
    apply DFunLike.ext
    intro x
    exact kernel_block_apply_cycle a b x
  have hi : kernelIsoEmbedding.trans (kernelBlockEquiv a b).toEmbedding =
      b.toEmbedding.trans kernelIsoEmbedding := by
    apply DFunLike.ext
    intro x
    exact kernel_block_apply_iso a b x
  simp only [kernelJoinParts, Finset.map_union, Finset.map_map, hc, hi]

run_cmd R5Kernel.checkStandardAxioms ``kernel_block_adj
run_cmd R5Kernel.checkStandardAxioms ``kernel_block_map_join

end Erdos1011
