/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CanonicalCell
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.HalfspaceCoefficients
/-!
# `NRR.EMP.VariableBody.CanonicalCellGraph` — one-sided closedness of the cell graph

We record the one-sided closed-graph property of the canonical power cell: the relation

```
{z | (z.2.body : Set Plane) ⊆ (canonicalCell sites hA hn z.1 i).body}
```

over `(BodySpace K A × X) × ConvexSubbody K` is closed. Concretely, if a sequence of subbodies
`D_m` contained in the canonical cell at parameters `z_m` converges (in the Hausdorff metric) to
`D`, while `z_m → z`, then `D` is contained in the canonical cell at `z`.

The proof is the sequential closed-set criterion. A point `y ∈ D` is approximated by points
`y_m ∈ D_m` (`ConvexSubbody.exists_tendsto_points`); each `y_m` lies in the moving cell, so it lies
in the moving parent body and satisfies every off-diagonal power-halfspace inequality. Parent
membership passes to the limit via `ConvexSubbody.mem_limit_of_tendsto`; each halfspace inequality
passes to the limit by continuity of the separating normal (in the sites) and offset (in the sites
and the selected weight, through `continuous_normalizedWeight_compactFamily`) together with
closedness of `≤`. Hence `y` lies in the limiting cell.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody
open scoped RealInnerProductSpace
open Filter Topology

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

omit [CompactSpace X] in
/-- **Halfspace membership characterization of the canonical cell.** A point lies in the canonical
power cell iff it lies in the parent body and satisfies every off-diagonal power-halfspace
inequality. -/
theorem mem_canonicalCell_iff
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (z : BodySpace K A × X) (i : Fin n) (y : Plane) :
    y ∈ ((canonicalCell sites hA hn z i).body : Set Plane) ↔
      y ∈ (z.1.body : Set Plane) ∧
      ∀ j : {j : Fin n // j ≠ i},
        ⟪sepNormal (sites z.2) i j.1, y⟫ ≤
          sepOffset (sites z.2) (normalizedWeight hA hn z.1 (sites z.2)) i j.1 := by
  rw [canonicalCell_carrier, cellSet_eq_offDiag_halfspaces]
  simp only [Set.mem_inter_iff, Set.mem_iInter, Geometry.mem_lowerClosedHalfspace]

/-- The **one-sided (lower) canonical-cell graph**: parameter–subbody pairs `(z, D)` where the
subbody `D` is contained in the canonical power cell of site `i` at `z`. -/
def CanonicalCellLowerGraph
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (i : Fin n) :
    Set ((BodySpace K A × X) × ConvexSubbody K) :=
  {z | (z.2.body : Set Plane) ⊆
       (canonicalCell sites hA hn z.1 i).body}

/-
**One-sided closedness of the canonical-cell graph.** Every Hausdorff limit of subbodies
contained in canonical cells is contained in the canonical cell of the limiting parameter.
-/
theorem isClosed_canonicalCellLowerGraph
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (i : Fin n) :
    IsClosed (CanonicalCellLowerGraph (K := K) sites hA hn i) := by
  refine' isSeqClosed_iff_isClosed.mp _;
  intro f hf a hlim y hy;
  -- By `ConvexSubbody.exists_tendsto_points`, obtain a sequence of points `yseq` in the
  -- approximating subbodies converging to `y`.
  obtain ⟨yseq, hyseq⟩ : ∃ yseq : ℕ → Plane, (∀ m, yseq m ∈ ((f m).2.body : Set Plane)) ∧
    Filter.Tendsto yseq Filter.atTop (nhds y) := by
    convert ConvexSubbody.exists_tendsto_points ( show Filter.Tendsto ( fun m => ( f m |>.2 ) )
      Filter.atTop ( nhds hf.2 ) from ?_ ) hy;
    exact continuousAt_snd.tendsto.comp hlim;
  -- By `mem_canonicalCell_iff`, we need to show that `y` is in the parent body and satisfies the
  -- wall inequalities.
  have h_parent : y ∈ (hf.1.1.body : Set Plane) := by
    have h_parent : Filter.Tendsto (fun m => ((f m).1.1).body) Filter.atTop (nhds (hf.1.1).body)
      := by
      exact ( BodySpace.continuous_body.tendsto _ ).comp ( continuous_fst.tendsto _ |>
        Filter.Tendsto.comp <| continuous_fst.tendsto _ |> Filter.Tendsto.comp <| hlim );
    apply ConvexSubbody.mem_limit_of_tendsto h_parent hyseq.2;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm;
    exact ( a m ) ( hyseq.1 m ) |> fun h => by simpa using h.1;
  refine' mem_canonicalCell_iff sites hA hn hf.1 i y |>.2 ⟨ h_parent, _ ⟩;
  intro j
  have h_wall : ∀ m, ⟪sepNormal (sites (f m).1.2) i j.1, yseq m⟫ ≤ sepOffset (sites (f m).1.2)
    (normalizedWeight hA hn (f m).1.1 (sites (f m).1.2)) i j.1 := by
    intro m
    have h_wall : yseq m ∈ ((canonicalCell sites hA hn (f m).1 i).body : Set Plane) := by
      exact a m ( hyseq.1 m );
    exact ( mem_canonicalCell_iff sites hA hn ( f m |>.1 ) i ( yseq m ) ) |>.1 h_wall |>.2 j;
  refine' le_of_tendsto_of_tendsto' ( Filter.Tendsto.inner ( _ ) hyseq.2 ) ( _ ) fun m => h_wall m;
  · exact Continuous.continuousAt ( continuous_sepNormal i j ) |> fun h => h.tendsto.comp (
      Continuous.continuousAt ( sites.continuous ) |> fun h => h.tendsto.comp (
      continuous_snd.continuousAt.tendsto.comp ( continuous_fst.continuousAt.tendsto.comp hlim )
      ) );
  · convert Filter.Tendsto.comp
        (continuous_sepOffset i j.1 |>.tendsto
          (sites hf.1.2, normalizedWeight hA hn hf.1.1 (sites hf.1.2)))
        (Filter.Tendsto.prodMk_nhds
          (Filter.Tendsto.comp (sites.continuous.tendsto hf.1.2)
            (continuous_snd.comp continuous_fst |>.continuousAt |>.tendsto.comp hlim))
          (Filter.Tendsto.comp
            (continuous_normalizedWeight_compactFamily sites hA hn |>.tendsto hf.1)
            (continuous_fst |>.continuousAt |>.tendsto.comp hlim))) using 1
    funext m
    rfl

end NRR.EMP.VariableBody
