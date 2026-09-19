import R5Kernel.S10C5Data
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011.S10C5
open scoped BigOperators

def kernelS10Split : Fin 5 ⊕ Fin 5 ≃ Fin 10 := finSumFinEquiv

def kernelBlockEquiv (a : Fin 5 ≃ Fin 5) (b : Fin 5 ≃ Fin 5) : Fin 10 ≃ Fin 10 :=
  kernelS10Split.symm.trans ((Equiv.sumCongr a b).trans kernelS10Split)

theorem kernel_s10_split_adj : ∀ x y : Fin 5 ⊕ Fin 5,
    (cycleGraph 10 5).Adj (kernelS10Split x) (kernelS10Split y) ↔
      match x, y with
      | Sum.inl u, Sum.inl v => (cycleGraph 5 5).Adj u v
      | _, _ => False := by
  intro x y
  rcases x with x | x <;> rcases y with y | y
  all_goals (revert x y; decide +kernel)

theorem kernel_block_apply_sum (a : Fin 5 ≃ Fin 5) (b : Fin 5 ≃ Fin 5)
    (x : Fin 5 ⊕ Fin 5) :
    kernelBlockEquiv a b (kernelS10Split x) = kernelS10Split (Sum.map a b x) := by
  simp [kernelBlockEquiv]

theorem kernel_block_apply_cycle (a : Fin 5 ≃ Fin 5) (b : Fin 5 ≃ Fin 5) (x : Fin 5) :
    kernelBlockEquiv a b (kernelC5Embedding x) = kernelC5Embedding (a x) := by
  exact kernel_block_apply_sum a b (Sum.inl x)

theorem kernel_iso_embedding_as_sum (x : Fin 5) :
    kernelIsoEmbedding x = kernelS10Split (Sum.inr x) := by
  apply Fin.ext
  exact Nat.add_comm _ _

theorem kernel_block_apply_iso (a : Fin 5 ≃ Fin 5) (b : Fin 5 ≃ Fin 5) (x : Fin 5) :
    kernelBlockEquiv a b (kernelIsoEmbedding x) = kernelIsoEmbedding (b x) := by
  rw [kernel_iso_embedding_as_sum, kernel_iso_embedding_as_sum]
  exact kernel_block_apply_sum a b (Sum.inr x)

theorem kernel_block_adj (a : Fin 5 ≃ Fin 5) (b : Fin 5 ≃ Fin 5)
    (ha : ∀ x y, (cycleGraph 5 5).Adj (a x) (a y) ↔ (cycleGraph 5 5).Adj x y) :
    ∀ x y, (cycleGraph 10 5).Adj (kernelBlockEquiv a b x) (kernelBlockEquiv a b y) ↔
      (cycleGraph 10 5).Adj x y := by
  intro x y
  obtain ⟨x, rfl⟩ := kernelS10Split.surjective x
  obtain ⟨y, rfl⟩ := kernelS10Split.surjective y
  rw [kernel_block_apply_sum, kernel_block_apply_sum, kernel_s10_split_adj, kernel_s10_split_adj]
  cases x with
  | inl x => cases y with
    | inl y => exact ha x y
    | inr y => rfl
  | inr x => cases y <;> rfl

theorem kernel_block_map_join (a : Fin 5 ≃ Fin 5) (b : Fin 5 ≃ Fin 5)
    (J : Finset (Fin 5)) (K : Finset (Fin 5)) :
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

def kernelIsoPrefix (k : Fin 6) : Finset (Fin 5) :=
  Finset.univ.filter (fun x => x.val < k.val)

theorem kernel_iso_prefix_card : ∀ k : Fin 6, (kernelIsoPrefix k).card = k.val := by
  decide +kernel

def kernelS10Pack (c : Fin 32) (k : Fin 6) : Fin 1024 :=
  ⟨(c.val + 32 * (2 ^ k.val - 1)) % 1024, Nat.mod_lt _ (by decide)⟩

-- Eight cycle shapes × seven isolated-vertex counts; the zero case is
-- retained explicitly, then excluded by nonemptiness in the general proof.
theorem kernel_s10_packed_shapes : ∀ c : Fin 32,
    c.val ∈ kernelC5CanonicalMasks → ∀ k : Fin 6,
      maskSet (kernelS10Pack c k) =
        kernelJoinParts (kernelC5SmallMask c.val, kernelIsoPrefix k) ∧
      ((kernelS10Pack c k).val ∈ kernelS10RepresentativeMasks ∨ kernelS10Pack c k = 0) := by
  decide +kernel

theorem kernel_s10_zero_mask : maskSet 0 = ∅ := by decide +kernel

theorem kernel_s10_all_subsets_canonical (R : Finset (Fin 10)) (hR : R.Nonempty) :
    ∃ m : Fin 1024, m.val ∈ kernelS10RepresentativeMasks ∧
      ∃ e : Fin 10 ≃ Fin 10,
        (∀ x y, (cycleGraph 10 5).Adj (e x) (e y) ↔ (cycleGraph 10 5).Adj x y) ∧
        (maskSet m).map e.toEmbedding = R := by
  obtain ⟨c, d, hc, hd⟩ := kernel_c5_all_subsets_covered (kernelC5Slice R)
  have hcard : (kernelIsoSlice R).card < 6 := by
    have h := Finset.card_le_univ (kernelIsoSlice R)
    simp only [Fintype.card_fin] at h
    omega
  let k : Fin 6 := ⟨(kernelIsoSlice R).card, hcard⟩
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_map_finset_eq (kernelIsoPrefix k) (kernelIsoSlice R)
    (kernel_iso_prefix_card k)
  let a := kernelC5ActionEquiv d
  let e := kernelBlockEquiv a b
  let m := kernelS10Pack c k
  obtain ⟨hparts, hm⟩ := kernel_s10_packed_shapes c hc k
  have hmap : (maskSet m).map e.toEmbedding = R := by
    change (maskSet (kernelS10Pack c k)).map
      (kernelBlockEquiv (kernelC5ActionEquiv d) b).toEmbedding = R
    rw [hparts, kernel_block_map_join, hd, hb, kernel_join_slices]
  have hmem : m.val ∈ kernelS10RepresentativeMasks := by
    rcases hm with hm | hm
    · exact hm
    · have hempty : R = ∅ := by
        rw [← hmap]
        change (maskSet (kernelS10Pack c k)).map e.toEmbedding = ∅
        rw [hm, kernel_s10_zero_mask, Finset.map_empty]
      exact (hR.ne_empty hempty).elim
  refine ⟨m, hmem, e, ?_, hmap⟩
  exact kernel_block_adj a b (kernel_c5_action_adj d)


run_cmd R5Kernel.checkStandardAxioms ``kernel_s10_all_subsets_canonical

end Erdos1011.S10C5
