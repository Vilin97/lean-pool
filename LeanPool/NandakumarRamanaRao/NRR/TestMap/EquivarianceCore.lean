/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerPartitionPerimeter
import LeanPool.NandakumarRamanaRao.NRR.ConfigurationSpace

/-!
# `NRR.TestMap.EquivarianceCore` — power-partition relabelling

This module proves that the canonical normalized weights, power-partition pieces, perimeter vector,
and perimeter deviation commute with relabelling of sites.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

/--
**Power cell relabeling.** Precomposing both the sites and the weights by `σ.symm`
reindexes the power cell: the `i`-th cell of the relabeled data is the `σ.symm i`-th cell of
the original data. This is because `powerDist (t∘σ.symm) (u∘σ.symm) i x = powerDist t u (σ.symm i) x`
and the universally-quantified `j` in the cell condition ranges bijectively via `σ.symm`.
-/
theorem PowerDiagram.cell_relabel
    (σ : Equiv.Perm (Fin n)) (t : Fin n → E2) (u : Fin n → ℝ) (i : Fin n) :
    PowerDiagram.cell (fun j => t (σ.symm j)) (fun j => u (σ.symm j)) i
      = PowerDiagram.cell t u (σ.symm i) := by
  convert Set.ext _;
  intro x; constructor <;> intro hx <;> simp_all +decide [ cell, PowerDiagram.powerDist ];
  exact fun j => by simpa using hx ( σ j );

/--
**Restricted power cell relabeling.** The restricted cell (intersection with the body `K`)
relabels by `σ.symm`, inheriting the relabeling of the underlying power cell.
-/
theorem PowerDiagram.bodyCellSet_relabel
    (K : Geometry.ConvexBody Plane) (σ : Equiv.Perm (Fin n))
    (t : Fin n → Plane) (u : Fin n → ℝ) (i : Fin n) :
    PowerDiagram.bodyCellSet K (fun j => t (σ.symm j)) (fun j => u (σ.symm j)) i
      = PowerDiagram.bodyCellSet K t u (σ.symm i) := by
  exact congr_arg₂ _ rfl ( PowerDiagram.cell_relabel σ t u i )

/--
**Normalized equal-area weight relabeling.** The canonical normalized equal-area weight of
the relabeled configuration equals the original normalized weight reindexed by `σ.symm`.
Proved by `EMP.normalizedWeight_unique`: the reindexed weight `w ∘ σ.symm` is again equal-area
(via `PowerDiagram.bodyCellSet_relabel`, hence each restricted cell area is unchanged) and
normalized (the sum is invariant under reindexing), so by uniqueness it is *the* normalized
weight of the relabeled configuration.
-/
theorem EMP.normalizedWeight_relabel
    (K : Geometry.ConvexBody Plane) (hn : 0 < n)
    (σ : Equiv.Perm (Fin n)) (s : Config n) :
    EMP.normalizedWeight K (Config.relabel σ s).pts hn (Config.relabel σ s).injective_pts
      = fun i => EMP.normalizedWeight K s.pts hn s.injective_pts (σ.symm i) := by
  refine' ( EMP.normalizedWeight_unique _ _ _ _ _ _ ).symm
  generalize_proofs at *;
  · intro i;
    convert EMP.normalizedWeight_isEqualArea K s.pts hn s.injective_pts ( σ.symm i ) using 1
    generalize_proofs at *;
    unfold areaVec PowerDiagram.areaVec PowerDiagram.bodyCellArea PowerDiagram.bodyCellSet
    generalize_proofs at *;
    exact PowerDiagram.cell_relabel σ s.pts _ _ ▸ rfl;
  · rw [ EMP.WeightNormalized_iff ];
    rw [ Equiv.sum_comp σ.symm ]; exact EMP.normalizedWeight_normalized K s.pts hn s.injective_pts;

/--
**Power-partition perimeter-vector relabelling.** The canonical equal-area power-partition
perimeter vector relabels by `σ.symm`: the perimeter vector of the relabeled configuration is
the original perimeter vector precomposed with `σ.symm`.

This theorem is proved and is the main input to test-map equivariance.

Proof outline: expand the perimeter vector to the perimeter of the `i`-th power-partition
piece, whose carrier is a restricted power cell of the canonical normalized weight. By
`EMP.normalizedWeight_relabel` the weight of the relabeled configuration reindexes by `σ.symm`,
and by `PowerDiagram.bodyCellSet_relabel` the restricted cell of the relabeled configuration
coincides with the `σ.symm i`-th restricted cell of the original configuration. Since the planar
perimeter depends only on the underlying set (`NRR.Geometry.planarPerimeter_congr`),
the perimeters agree.
-/
theorem EMP.powerPartitionPerimeterVec_relabel
    (K : Geometry.ConvexBody Plane) (hn : 0 < n) (hK : 0 < K.area)
    (σ : Equiv.Perm (Fin n)) (s : Config n) :
    EMP.powerPartitionPerimeterVec K (Config.relabel σ s) hn hK
      = fun i => EMP.powerPartitionPerimeterVec K s hn hK (σ.symm i) := by
  ext i
  unfold EMP.powerPartitionPerimeterVec ConvexPartition.perimeterVec
  rw [NRR.Geometry.ConvexBody.perimeter_def]
  apply NRR.Geometry.planarPerimeter_congr
  rw [EMP.powerPartition_piece_carrier, EMP.powerPartition_piece_carrier,
    EMP.normalizedWeight_relabel K hn σ s]
  exact PowerDiagram.bodyCellSet_relabel K σ s.pts
    (EMP.normalizedWeight K s.pts hn s.injective_pts) i

end NRR
