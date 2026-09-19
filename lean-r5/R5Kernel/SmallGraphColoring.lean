import R5Kernel.OddCycleEmbedding
import R5Kernel.Probes.S11C5Local

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

namespace Erdos1011
open SimpleGraph

/- A triangle-free odd cycle has at least five vertices. No graph enumeration. -/
theorem kernel_triangle_free_odd_cycle_length_ge_five
    {n : ℕ} {G : SimpleGraph (Fin n)} (htri : G.CliqueFree 3)
    {u : Fin n} (p : G.Walk u u) (hcyc : p.IsCycle) (hodd : Odd p.length) :
    5 ≤ p.length := by
  have hlow := hcyc.three_le_length
  have hnot3 : p.length ≠ 3 := by
    intro h3
    obtain ⟨s, hs⟩ := (is3Clique_iff_exists_cycle_length_three (G := G)).mpr
      ⟨u, p, hcyc, h3⟩
    exact htri s hs
  obtain ⟨k, hk⟩ := hodd
  omega

theorem kernel_triangle_free_fin_le_four_colorable_two
    {n : ℕ} (hn : n ≤ 4) {G : SimpleGraph (Fin n)}
    (htri : G.CliqueFree 3) : G.Colorable 2 := by
  classical
  by_contra hnot
  obtain ⟨u, p, hcyc, hodd⟩ :=
    kernel_exists_odd_cycle_of_exists_odd_closed_walk
      (kernel_exists_odd_closed_walk_of_not_colorable_two hnot)
  have hlo := kernel_triangle_free_odd_cycle_length_ge_five htri p hcyc hodd
  have hhi := kernel_r5_odd_cycle_length_le_card p hcyc
  omega

/- Only the 25 ordered pairs of the fixed pentagon are checked here. -/
theorem kernel_c5_nonadjacent_common_neighbor : ∀ x y : Fin 5,
    x ≠ y → ¬ (cycleGraph 5 5).Adj x y →
      ∃ z : Fin 5, (cycleGraph 5 5).Adj x z ∧ (cycleGraph 5 5).Adj y z := by
  decide +kernel

theorem kernel_fin5_nonbip_iso_cycle
    {G : SimpleGraph (Fin 5)} (htri : G.CliqueFree 3)
    (hnot2 : ¬ G.Colorable 2) : Nonempty ((cycleGraph 5 5) ≃g G) := by
  classical
  obtain ⟨u, p, hcyc, hodd⟩ :=
    kernel_exists_odd_cycle_of_exists_odd_closed_walk
      (kernel_exists_odd_closed_walk_of_not_colorable_two hnot2)
  have hlo := kernel_triangle_free_odd_cycle_length_ge_five htri p hcyc hodd
  have hhi := kernel_r5_odd_cycle_length_le_card p hcyc
  have hlen : p.length = 5 := by omega
  let g : Fin 5 ↪ Fin 5 :=
    { toFun := fun i => p.getVert i.val
      inj' := by
        intro i j hij
        apply Fin.ext
        apply hcyc.getVert_injOn'
        · rw [hlen]; change i.val ≤ 5 - 1; omega
        · rw [hlen]; change j.val ≤ 5 - 1; omega
        · exact hij }
  let e : Fin 5 ≃ Fin 5 := Equiv.ofBijective g
    ⟨g.injective, (Finite.injective_iff_surjective).mp g.injective⟩
  have hforward : ∀ {x y : Fin 5}, (cycleGraph 5 5).Adj x y → G.Adj (e x) (e y) := by
    apply kernel_r5CycleGraphAdj_of_succ (by omega : 5 ≤ 5) (by omega : 0 < 5) e
    intro i
    exact kernel_r5WalkCycleAdj_mod p hcyc hlen (by omega) i
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro x y
  constructor
  · intro hadj
    by_contra hnot
    have hne : x ≠ y := fun h => hadj.ne (congrArg e h)
    obtain ⟨z, hxz, hyz⟩ := kernel_c5_nonadjacent_common_neighbor x y hne hnot
    exact htri _ (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨hadj, hforward hxz, hforward hyz⟩)
  · exact hforward

def kernelC5ThreeColor : Fin 5 → Fin 3 := ![0, 1, 0, 1, 2]

theorem kernel_c5_three_color_valid : ∀ x y : Fin 5,
    (cycleGraph 5 5).Adj x y → kernelC5ThreeColor x ≠ kernelC5ThreeColor y := by
  decide +kernel

theorem kernel_fin5_triangle_free_colorable_three
    {G : SimpleGraph (Fin 5)} (htri : G.CliqueFree 3) : G.Colorable 3 := by
  classical
  by_cases h2 : G.Colorable 2
  · exact h2.mono (by omega)
  obtain ⟨e⟩ := kernel_fin5_nonbip_iso_cycle htri h2
  have hc : (cycleGraph 5 5).Colorable 3 :=
    ⟨Coloring.mk kernelC5ThreeColor (fun {x y} h => kernel_c5_three_color_valid x y h)⟩
  exact SimpleGraph.Colorable.of_hom e.symm.toHom hc

theorem kernel_fin5_nonbip_independent_card_le_two
    {G : SimpleGraph (Fin 5)} (htri : G.CliqueFree 3) (hnot2 : ¬ G.Colorable 2)
    {I : Finset (Fin 5)} (hI : G.IsIndepSet (I : Set (Fin 5))) : I.card ≤ 2 := by
  classical
  obtain ⟨e⟩ := kernel_fin5_nonbip_iso_cycle htri hnot2
  let J := I.map e.symm.toEquiv.toEmbedding
  have hJ : (cycleGraph 5 5).IsIndepSet (J : Set (Fin 5)) := by
    intro x hx y hy hxy hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hI ha hb (fun hab => hxy (congrArg e.symm hab))
      (e.symm.map_rel_iff.mp hadj)
  have hcard := kernel_c5_local_alpha J hJ
  simpa only [J, Finset.card_map] using hcard

run_cmd R5Kernel.checkStandardAxioms ``kernel_triangle_free_fin_le_four_colorable_two
run_cmd R5Kernel.checkStandardAxioms ``kernel_fin5_nonbip_iso_cycle
run_cmd R5Kernel.checkStandardAxioms ``kernel_fin5_triangle_free_colorable_three
run_cmd R5Kernel.checkStandardAxioms ``kernel_fin5_nonbip_independent_card_le_two

end Erdos1011
