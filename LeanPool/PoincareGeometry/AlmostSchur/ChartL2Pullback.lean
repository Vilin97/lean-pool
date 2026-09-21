/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DensityComparison
public import LeanPool.PoincareGeometry.RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul

/-! # Bounded local pullback of actual-volume L² classes -/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ENNReal

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]

/-- Pullback to a compact coordinate set is bounded on L² equivalence classes.
The constant is the square-root measure-domination factor, written as an
ENNReal power. The representative identity holds for every L² class. -/
theorem exists_chartL2Pullback (c : M) {K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ (extChartAt I c).target) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧
      ∃ T : Lp ℝ 2 (riemannianVolume (I := I)) →L[ℝ]
          Lp ℝ 2 ((volume : Measure E).restrict K),
        (∀ u, ‖T u‖ ≤ (A ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖u‖) ∧
        ∀ u, (T u : E → ℝ) =ᵐ[(volume : Measure E).restrict K]
          (u : M → ℝ) ∘ (extChartAt I c).symm := by
  classical
  let e := extChartAt I c
  let ν : Measure M := riemannianVolume (I := I)
  let μ := (volume : Measure E).restrict K
  let g : E → M := e.target.piecewise e.symm (fun _ => c)
  have hg : Measurable g :=
    (continuousOn_extChartAt_symm c).measurable_piecewise
      continuous_const.continuousOn (isOpen_extChartAt_target c).measurableSet
  have he : AEMeasurable e (ν.restrict e.source) :=
    aemeasurable_restrict_of_measurable_subtype
      (isOpen_extChartAt_source c).measurableSet
      (continuousOn_extChartAt c).domRestrict.measurable
  have hback : Measure.map g (Measure.map e (ν.restrict e.source)) =
      ν.restrict e.source := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable he]
    calc
      Measure.map (g ∘ e) (ν.restrict e.source) =
          Measure.map id (ν.restrict e.source) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem (isOpen_extChartAt_source c).measurableSet]
          with x hx
        simp [g, e.map_source hx, e.left_inv hx]
      _ = _ := Measure.map_id
  obtain ⟨A, B, hA, _, hdom, _⟩ := chartPushforward_measure_comparison c hK hsub
  have hμ : Measure.map g μ ≤ A • ν := by
    calc
      Measure.map g μ ≤ Measure.map g
          (A • (Measure.map e (ν.restrict e.source)).restrict K) :=
        Measure.map_mono hdom hg
      _ = A • Measure.map g ((Measure.map e (ν.restrict e.source)).restrict K) :=
        Measure.map_smul A _ g
      _ ≤ A • Measure.map g (Measure.map e (ν.restrict e.source)) :=
        smul_le_smul_left A (Measure.map_mono Measure.restrict_le_self hg)
      _ = A • ν.restrict e.source := by rw [hback]
      _ ≤ A • ν := smul_le_smul_left A Measure.restrict_le_self
  let S := Lp.changeMeasureL (E := ℝ) (p := 2) hA hμ (by norm_num)
  have hp : MeasurePreserving g μ (Measure.map g μ) := ⟨hg, rfl⟩
  let P := (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ g hp).toContinuousLinearMap
  refine ⟨A, hA, P.comp S, ?_, ?_⟩
  · intro u
    change ‖Lp.compMeasurePreserving g hp (S u)‖ ≤ _
    rw [Lp.norm_compMeasurePreserving]
    exact Lp.vendorMeasureTheoryFunctionLpSpaceChangeMeasureLeSmul_norm_changeMeasureFun_le
      hA hμ u (by norm_num)
  · intro u
    have h₁ := Lp.coeFn_compMeasurePreserving (S u) hp
    have h₂ := ae_of_ae_map hg.aemeasurable
      (Lp.changeMeasureL_coeFn_ae_eq hA hμ (by norm_num) u)
    filter_upwards [h₁, h₂, ae_restrict_mem hK.measurableSet] with z hz hz' hzK
    have hzT : z ∈ e.target := hsub hzK
    exact hz.trans (hz'.trans (by simp only [g, Set.piecewise_eq_of_mem _ _ _ hzT]; rfl))

end AlmostSchur
