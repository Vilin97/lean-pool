/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.Statement
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Metric consequences of a finite diameter

The comparison argument controls the induced Riemannian distance.  This file
records the final, purely metric implication separately: once Hopf--Rinow has
supplied properness for the complete finite-dimensional Riemannian metric, the
diameter estimate makes the whole manifold compact.
-/

noncomputable section

open Set
open scoped ENNReal Topology

namespace BonnetMyersEntry

theorem compactSpace_of_ediam_univ_le
    {M : Type*} [PseudoMetricSpace M] [ProperSpace M]
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : Metric.ediam (Set.univ : Set M) ≤ ENNReal.ofReal C) :
    CompactSpace M := by
  apply Metric.compactSpace_iff_isBounded_univ.mpr
  refine Metric.isBounded_iff.mpr ⟨C, ?_⟩
  intro x hx y hy
  apply (ENNReal.ofReal_le_ofReal_iff hC0).mp
  rw [← edist_dist]
  exact le_trans (Metric.edist_le_ediam_of_mem hx hy) hC

theorem dist_le_of_ediam_univ_le
    {M : Type*} [PseudoEMetricSpace M]
    {C : ℝ≥0∞} (hC : Metric.ediam (Set.univ : Set M) ≤ C)
    (x y : M) : edist x y ≤ C := by
  exact le_trans (Metric.edist_le_ediam_of_mem (s := (Set.univ : Set M))
    (mem_univ x) (mem_univ y)) hC

end BonnetMyersEntry
