import R5Kernel.Probes.S11C9Structural

set_option Elab.async false

namespace Erdos1011

def kernelC9Split : Fin 9 ⊕ Fin 2 ≃ Fin 11 := finSumFinEquiv

def kernelC9BlockEquiv (a : Fin 9 ≃ Fin 9) (b : Fin 2 ≃ Fin 2) : Fin 11 ≃ Fin 11 :=
  kernelC9Split.symm.trans ((Equiv.sumCongr a b).trans kernelC9Split)

theorem kernel_c9_split_adj : ∀ x y : Fin 9 ⊕ Fin 2,
    (cycleGraph 11 9).Adj (kernelC9Split x) (kernelC9Split y) ↔
      match x, y with
      | Sum.inl u, Sum.inl v => (cycleGraph 9 9).Adj u v
      | _, _ => False := by
  intro x y
  rcases x with x | x <;> rcases y with y | y
  all_goals (revert x y; decide +kernel)

theorem kernel_c9_block_apply_sum (a : Fin 9 ≃ Fin 9) (b : Fin 2 ≃ Fin 2)
    (x : Fin 9 ⊕ Fin 2) :
    kernelC9BlockEquiv a b (kernelC9Split x) = kernelC9Split (Sum.map a b x) := by
  simp [kernelC9BlockEquiv]

theorem kernel_c9_block_adj (a : Fin 9 ≃ Fin 9) (b : Fin 2 ≃ Fin 2)
    (ha : ∀ x y, (cycleGraph 9 9).Adj (a x) (a y) ↔ (cycleGraph 9 9).Adj x y) :
    ∀ x y, (cycleGraph 11 9).Adj (kernelC9BlockEquiv a b x) (kernelC9BlockEquiv a b y) ↔
      (cycleGraph 11 9).Adj x y := by
  intro x y
  obtain ⟨x, rfl⟩ := kernelC9Split.surjective x
  obtain ⟨y, rfl⟩ := kernelC9Split.surjective y
  rw [kernel_c9_block_apply_sum, kernel_c9_block_apply_sum,
    kernel_c9_split_adj, kernel_c9_split_adj]
  cases x with
  | inl x => cases y with
    | inl y => exact ha x y
    | inr y => rfl
  | inr x => cases y <;> rfl

theorem kernel_c9_iso_as_sum (x : Fin 2) :
    kernelC9IsoEmbedding x = kernelC9Split (Sum.inr x) := by
  unfold kernelC9IsoEmbedding kernelC9Split
  apply Fin.ext
  change x.val + 9 = (finSumFinEquiv (Sum.inr x)).val
  rw [finSumFinEquiv_apply_right]
  simpa only [Fin.val_natAdd] using (Nat.add_comm x.val 9)

theorem kernel_c9_block_apply_cycle (a : Fin 9 ≃ Fin 9) (b : Fin 2 ≃ Fin 2) (x : Fin 9) :
    kernelC9BlockEquiv a b (kernelC9Embedding x) = kernelC9Embedding (a x) := by
  exact kernel_c9_block_apply_sum a b (Sum.inl x)

theorem kernel_c9_block_apply_iso (a : Fin 9 ≃ Fin 9) (b : Fin 2 ≃ Fin 2) (x : Fin 2) :
    kernelC9BlockEquiv a b (kernelC9IsoEmbedding x) = kernelC9IsoEmbedding (b x) := by
  rw [kernel_c9_iso_as_sum, kernel_c9_iso_as_sum]
  exact kernel_c9_block_apply_sum a b (Sum.inr x)

theorem kernel_c9_block_map_join (a : Fin 9 ≃ Fin 9) (b : Fin 2 ≃ Fin 2)
    (J : Finset (Fin 9)) (K : Finset (Fin 2)) :
    (kernelC9JoinParts (J, K)).map (kernelC9BlockEquiv a b).toEmbedding =
      kernelC9JoinParts (J.map a.toEmbedding, K.map b.toEmbedding) := by
  have hc : kernelC9Embedding.trans (kernelC9BlockEquiv a b).toEmbedding =
      a.toEmbedding.trans kernelC9Embedding := by
    apply DFunLike.ext
    intro x
    exact kernel_c9_block_apply_cycle a b x
  have hi : kernelC9IsoEmbedding.trans (kernelC9BlockEquiv a b).toEmbedding =
      b.toEmbedding.trans kernelC9IsoEmbedding := by
    apply DFunLike.ext
    intro x
    exact kernel_c9_block_apply_iso a b x
  simp only [kernelC9JoinParts, Finset.map_union, Finset.map_map, hc, hi]

run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_split_adj
run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_block_adj
run_cmd R5Kernel.checkStandardAxioms ``kernel_c9_block_map_join

end Erdos1011
