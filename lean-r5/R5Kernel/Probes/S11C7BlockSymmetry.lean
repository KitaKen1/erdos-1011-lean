import R5Kernel.Probes.S11C7Cover

set_option Elab.async false

namespace Erdos1011

def kernelC7Split : Fin 7 ⊕ Fin 4 ≃ Fin 11 := finSumFinEquiv

def kernelC7BlockEquiv (a : Fin 7 ≃ Fin 7) (b : Fin 4 ≃ Fin 4) : Fin 11 ≃ Fin 11 :=
  kernelC7Split.symm.trans ((Equiv.sumCongr a b).trans kernelC7Split)

theorem kernel_c7_split_adj : ∀ x y : Fin 7 ⊕ Fin 4,
    (cycleGraph 11 7).Adj (kernelC7Split x) (kernelC7Split y) ↔
      match x, y with
      | Sum.inl u, Sum.inl v => (cycleGraph 7 7).Adj u v
      | _, _ => False := by
  intro x y
  rcases x with x | x <;> rcases y with y | y
  all_goals (revert x y; decide +kernel)

theorem kernel_c7_block_apply_sum (a : Fin 7 ≃ Fin 7) (b : Fin 4 ≃ Fin 4)
    (x : Fin 7 ⊕ Fin 4) :
    kernelC7BlockEquiv a b (kernelC7Split x) = kernelC7Split (Sum.map a b x) := by
  simp [kernelC7BlockEquiv]

theorem kernel_c7_block_adj (a : Fin 7 ≃ Fin 7) (b : Fin 4 ≃ Fin 4)
    (ha : ∀ x y, (cycleGraph 7 7).Adj (a x) (a y) ↔ (cycleGraph 7 7).Adj x y) :
    ∀ x y, (cycleGraph 11 7).Adj (kernelC7BlockEquiv a b x) (kernelC7BlockEquiv a b y) ↔
      (cycleGraph 11 7).Adj x y := by
  intro x y
  obtain ⟨x, rfl⟩ := kernelC7Split.surjective x
  obtain ⟨y, rfl⟩ := kernelC7Split.surjective y
  rw [kernel_c7_block_apply_sum, kernel_c7_block_apply_sum,
    kernel_c7_split_adj, kernel_c7_split_adj]
  cases x with
  | inl x => cases y with
    | inl y => exact ha x y
    | inr y => rfl
  | inr x => cases y <;> rfl

theorem kernel_c7_iso_as_sum (x : Fin 4) :
    kernelC7IsoEmbedding x = kernelC7Split (Sum.inr x) := by
  unfold kernelC7IsoEmbedding kernelC7Split
  apply Fin.ext
  change x.val + 7 = (finSumFinEquiv (Sum.inr x)).val
  rw [finSumFinEquiv_apply_right]
  simpa only [Fin.val_natAdd] using (Nat.add_comm x.val 7)

theorem kernel_c7_block_apply_cycle (a : Fin 7 ≃ Fin 7) (b : Fin 4 ≃ Fin 4) (x : Fin 7) :
    kernelC7BlockEquiv a b (kernelC7Embedding x) = kernelC7Embedding (a x) := by
  exact kernel_c7_block_apply_sum a b (Sum.inl x)

theorem kernel_c7_block_apply_iso (a : Fin 7 ≃ Fin 7) (b : Fin 4 ≃ Fin 4) (x : Fin 4) :
    kernelC7BlockEquiv a b (kernelC7IsoEmbedding x) = kernelC7IsoEmbedding (b x) := by
  rw [kernel_c7_iso_as_sum, kernel_c7_iso_as_sum]
  exact kernel_c7_block_apply_sum a b (Sum.inr x)

theorem kernel_c7_block_map_join (a : Fin 7 ≃ Fin 7) (b : Fin 4 ≃ Fin 4)
    (J : Finset (Fin 7)) (K : Finset (Fin 4)) :
    (kernelC7JoinParts (J, K)).map (kernelC7BlockEquiv a b).toEmbedding =
      kernelC7JoinParts (J.map a.toEmbedding, K.map b.toEmbedding) := by
  have hc : kernelC7Embedding.trans (kernelC7BlockEquiv a b).toEmbedding =
      a.toEmbedding.trans kernelC7Embedding := by
    apply DFunLike.ext
    intro x
    exact kernel_c7_block_apply_cycle a b x
  have hi : kernelC7IsoEmbedding.trans (kernelC7BlockEquiv a b).toEmbedding =
      b.toEmbedding.trans kernelC7IsoEmbedding := by
    apply DFunLike.ext
    intro x
    exact kernel_c7_block_apply_iso a b x
  simp only [kernelC7JoinParts, Finset.map_union, Finset.map_map, hc, hi]

run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_split_adj
run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_block_adj
run_cmd R5Kernel.checkStandardAxioms ``kernel_c7_block_map_join

end Erdos1011
