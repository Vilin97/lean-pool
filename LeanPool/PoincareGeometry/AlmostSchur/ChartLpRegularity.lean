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

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartL2Pullback
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integrability of actual-volume L² representatives in charts

The compact-coordinate `MemLp` result follows from the actual representative
identity in `exists_chartL2Pullback`, using Mathlib's `Lp.memLp` and `memLp_congr_ae`.
Finite Euclidean measure on compact sets then permits `MemLp.integrable`.
Interior closed balls provide neighborhoods for `LocallyIntegrableOn`; no global
integrability on the whole chart target or regularity of the L² representative is
assumed.
-/

@[expose] public noncomputable section

open Bundle Set MeasureTheory Metric
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]

/-- The chosen representative of any actual-volume L² class is L² in coordinates
on every compact subset of a chart target. -/
theorem memLp_chart_comp_on_compact (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (u : Lp ℝ 2 (riemannianVolume (I := I))) :
    MemLp ((u : M → ℝ) ∘ (extChartAt I c).symm) 2 ((volume : Measure E).restrict K) := by
  obtain ⟨_, _, T, _, hT⟩ := exists_chartL2Pullback (I := I) c hK hKt
  exact (memLp_congr_ae (hT u)).mp (Lp.memLp (T u))

/-- Compact-coordinate L² representatives are integrable for coordinate volume. -/
theorem integrableOn_chart_comp_on_compact (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (u : Lp ℝ 2 (riemannianVolume (I := I))) :
    IntegrableOn ((u : M → ℝ) ∘ (extChartAt I c).symm) K volume := by
  let : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (memLp_chart_comp_on_compact c hK hKt u).integrable (by norm_num)

/-- Any actual-volume L² class has a locally integrable coordinate representative
on the full chart target. The proof only uses compact interior closed balls. -/
theorem locallyIntegrableOn_chart_comp_lp (c : M)
    (u : Lp ℝ 2 (riemannianVolume (I := I))) :
    LocallyIntegrableOn ((u : M → ℝ) ∘ (extChartAt I c).symm)
      (extChartAt I c).target volume := by
  intro z hz
  obtain ⟨d, hd, hdT⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) c) z hz
  have hK : closedBall z (d / 2) ⊆ (extChartAt I c).target :=
    (closedBall_subset_ball (by linarith : d / 2 < d)).trans hdT
  refine ⟨closedBall z (d / 2), nhdsWithin_le_nhds (closedBall_mem_nhds z (by positivity)), ?_⟩
  exact integrableOn_chart_comp_on_compact c (isCompact_closedBall _ _) hK u

end AlmostSchur
