/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CanonicalCellGraph
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.ClosedGraph
import LeanPool.NandakumarRamanaRao.NRR.BodySpace.AreaRigidity

/-!
# `NRR.EMP.VariableBody.CanonicalCellContinuity` — closed graph and continuity of cells

We upgrade the one-sided closed-graph result `isClosed_canonicalCellLowerGraph` to the *exact* graph
of the canonical power cell and deduce continuity of each cell and of the finite family.

* `CanonicalCellGraph` — the exact relation `{z | z.2 = canonicalCell sites hA hn z.1 i}`.
* `isClosed_canonicalCellGraph` — the exact graph is closed.
* `continuous_canonicalCell` — each canonical cell varies continuously in the Hausdorff hyperspace.
* `continuous_canonicalCells` — the finite family of cells varies continuously.

The exact-graph closedness combines the one-sided lower-graph inclusion with area continuity and the
convex-area rigidity of `ConvexSubbody.eq_of_subset_of_area_eq`: a Hausdorff limit `D` of the cells is contained in the limiting
canonical cell, both have the common target area `z.1.body.area / n` (positive since `0 < A` and
`0 < n`), so `ConvexSubbody.eq_of_subset_of_area_eq` forces equality. Continuity then follows from the
compact closed-graph criterion `continuous_of_isClosed_graph_of_compact` (both the parameter space
`BodySpace K A × X` and the codomain `ConvexSubbody K` are compact Hausdorff metric spaces), and the
family continuity from `continuous_pi`.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody
open Filter Topology

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- The **exact canonical-cell graph**: parameter–subbody pairs `(z, D)` where the subbody `D`
equals the canonical power cell of site `i` at `z`. -/
def CanonicalCellGraph
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (i : Fin n) :
    Set ((BodySpace K A × X) × ConvexSubbody K) :=
  {z | z.2 = canonicalCell sites hA hn z.1 i}

/-- **Exact closedness of the canonical-cell graph.** The relation identifying a subbody with the
canonical power cell of its parameter is closed. -/
theorem isClosed_canonicalCellGraph
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (i : Fin n) :
    IsClosed (CanonicalCellGraph (K := K) sites hA hn i) := by
  refine isSeqClosed_iff_isClosed.mp ?_
  intro f a hf hlim
  -- `hf m : (f m).2 = canonicalCell sites hA hn (f m).1 i`.
  -- Step 1: the limit body is contained in the limiting canonical cell (lower-graph closedness).
  have hlower : a ∈ CanonicalCellLowerGraph (K := K) sites hA hn i := by
    refine (isClosed_canonicalCellLowerGraph sites hA hn i).isSeqClosed ?_ hlim
    intro m
    have : (f m).2 = canonicalCell sites hA hn (f m).1 i := hf m
    exact fun y hy => by rw [this] at hy; exact hy
  have hsubset : ((a.2).body : Set Plane) ⊆
      (canonicalCell sites hA hn a.1 i).body := hlower
  -- Step 2: the areas of the cells converge to `a.2.area`.
  have hTsnd : Tendsto (fun m => (f m).2) atTop (𝓝 a.2) :=
    (continuous_snd.tendsto a).comp hlim
  have hT1 : Tendsto (fun m => (f m).2.area) atTop (𝓝 a.2.area) :=
    ConvexSubbody.tendsto_area hTsnd
  -- Each cell area equals the target area of its parent body.
  have hrw : ∀ m, (f m).2.area = targetArea (f m).1.1 n := by
    intro m
    rw [hf m, canonicalCell_area_eq_target]
    rfl
  have hT2 : Tendsto (fun m => (f m).2.area) atTop (𝓝 (targetArea a.1.1 n)) := by
    have hcont : Continuous fun w : BodySpace K A × X => targetArea w.1 n :=
      continuous_targetArea.comp continuous_fst
    have htarget : Tendsto (fun m => targetArea (f m).1.1 n) atTop
        (𝓝 (targetArea a.1.1 n)) :=
      (hcont.tendsto a.1).comp ((continuous_fst.tendsto a).comp hlim)
    exact (tendsto_congr hrw).mpr htarget
  -- Step 3: identify areas and conclude equality via convex-area rigidity.
  have harea_target : a.2.area = targetArea a.1.1 n := tendsto_nhds_unique hT1 hT2
  have hcanon_target : (canonicalCell sites hA hn a.1 i).area = targetArea a.1.1 n := by
    rw [canonicalCell_area_eq_target]; rfl
  have harea : a.2.area = (canonicalCell sites hA hn a.1 i).area := by
    rw [harea_target, hcanon_target]
  have hpos : 0 < (canonicalCell sites hA hn a.1 i).area := by
    rw [hcanon_target, targetArea]
    exact div_pos (BodySpace.area_pos hA a.1.1) (by exact_mod_cast hn)
  show a.2 = canonicalCell sites hA hn a.1 i
  exact ConvexSubbody.eq_of_subset_of_area_eq hsubset harea hpos

/-- **Continuity of the canonical cell.** Each canonical power cell depends continuously on the
parameter, valued in the compact Hausdorff hyperspace `ConvexSubbody K`. -/
theorem continuous_canonicalCell
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n)
    (i : Fin n) :
    Continuous fun z : BodySpace K A × X =>
      canonicalCell sites hA hn z i :=
  continuous_of_isClosed_graph_of_compact _ (isClosed_canonicalCellGraph sites hA hn i)

/-- **Continuity of the finite cell family.** The whole finite family of canonical power cells
depends continuously on the parameter. -/
theorem continuous_canonicalCells
    (sites : SiteFamily X n) (hA : 0 < A) (hn : 0 < n) :
    Continuous fun z : BodySpace K A × X =>
      fun i => canonicalCell sites hA hn z i :=
  continuous_pi (fun i => continuous_canonicalCell sites hA hn i)

end NRR.EMP.VariableBody
