/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import Mathlib.Topology.Separation.Hausdorff

/-!
# `NRR.EMP.VariableBody.ClosedGraph` — the compact closed-graph criterion

This module provides the abstract topological input that turns uniqueness plus a closed relation into
continuity of a selection map.

* `continuous_of_isClosed_graph_of_compact`: a function into a compact Hausdorff space, out of a
  compact Hausdorff space, whose graph is closed, is continuous. Mathlib does not carry this exact
  statement as a single named theorem, so it is proved here via the compact-projection route.
* `isClosed_graph_of_isClosed_relation_of_unique`: if a closed relation `R` contains the graph of `f`
  and selects each value uniquely, then the graph of `f` is closed (indeed equal to `R`).

The compactness of both the domain and the codomain is essential: the closed-graph theorem is false
for continuity without it.
-/

namespace NRR.EMP.VariableBody

/-- **Compact closed-graph criterion.** A map `f : D → Y` between compact Hausdorff spaces whose
graph `{z | z.2 = f z.1}` is closed is continuous.

Proof route: for a closed `F ⊆ Y`, the set `graph f ∩ (univ ×ˢ F)` is closed in the compact product
`D × Y`, hence compact; its image under the first projection is compact, hence closed since `D` is
Hausdorff; and that image equals `f ⁻¹' F`. -/
theorem continuous_of_isClosed_graph_of_compact
    {D Y : Type*}
    [TopologicalSpace D] [CompactSpace D] [T2Space D]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : D → Y)
    (hgraph : IsClosed {z : D × Y | z.2 = f z.1}) :
    Continuous f := by
  rw [continuous_iff_isClosed]
  intro F hF
  have hcap : IsClosed ({z : D × Y | z.2 = f z.1} ∩ (Set.univ ×ˢ F)) :=
    hgraph.inter (isClosed_univ.prod hF)
  have hproj : IsCompact (Prod.fst '' ({z : D × Y | z.2 = f z.1} ∩ (Set.univ ×ˢ F))) :=
    hcap.isCompact.image continuous_fst
  have heq : Prod.fst '' ({z : D × Y | z.2 = f z.1} ∩ (Set.univ ×ˢ F)) = f ⁻¹' F := by
    ext d
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod,
      Set.mem_univ, true_and, Set.mem_preimage, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨hb, hbF⟩, rfl⟩; rw [hb] at hbF; exact hbF
    · intro h; exact ⟨d, f d, ⟨rfl, h⟩, rfl⟩
  rw [heq] at hproj
  exact hproj.isClosed

/-- **Uniqueness closes the graph.** If a closed relation `R` contains the graph of `f`
(`hf : ∀ d, R (d, f d)`) and selects each value uniquely (`huniq : ∀ d y, R (d, y) → y = f d`), then
the graph `{z | z.2 = f z.1}` is closed, being equal to `R`. -/
theorem isClosed_graph_of_isClosed_relation_of_unique
    {D Y : Type*} [TopologicalSpace D] [TopologicalSpace Y]
    (R : Set (D × Y)) (hR : IsClosed R)
    (f : D → Y)
    (hf : ∀ d, R (d, f d))
    (huniq : ∀ d y, R (d, y) → y = f d) :
    IsClosed {z : D × Y | z.2 = f z.1} := by
  have hset : {z : D × Y | z.2 = f z.1} = R := by
    ext z
    obtain ⟨d, y⟩ := z
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => h ▸ hf d, fun h => huniq d y h⟩
  rw [hset]; exact hR

end NRR.EMP.VariableBody
