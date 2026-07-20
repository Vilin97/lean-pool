/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.LocalizationH2

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.H2`

Define a scalar `H²` space on a compact manifold relative to finite chart data.

Given `d : FiniteChartData` and a finite measure `μ` on `M`, we define a manifold `H²` space as the
topological closure of the range of a chartwise graph map into

`L²(E, μᵢ) × (L²(E, μᵢ;E) × L²(E, μᵢ; E →L E))`

where `μᵢ` is the pushforward chart measure (`chartMeasure`) and the graph map is obtained by:

1. localizing a `C²` function `f : M → ℝ` to a chart (extend-by-zero outside the chart target);
2. viewing it as an element of Euclidean `C²_c`;
3. applying the Euclidean `H²` graph map.

## Main definitions

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.C2`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.h2`
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Topology
open scoped ENNReal MeasureTheory
open MeasureTheory
open scoped _root_.Manifold

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
variable [I.Boundaryless]
variable [T2Space M] [CompactSpace M]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEH2 : MeasurableSpace E := borel E
local instance instBorelSpaceEH2 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEH2 : OpensMeasurableSpace E := by infer_instance

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMH2 : MeasurableSpace M := borel M
local instance instBorelSpaceMH2 : BorelSpace M := ⟨rfl⟩

namespace FiniteChartData

/-- `C²` scalar functions `M → ℝ` (in the manifold sense), as a submodule of `M → ℝ`. -/
def C2 : Submodule ℝ (M → ℝ) where
  carrier := {f | ContMDiff I (𝓘(ℝ, ℝ)) 2 f}
  zero_mem' := by
    exact (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (2 : WithTop ℕ∞)) (c := (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    simpa using (hf.add hg)
  smul_mem' := by
    intro c f hf
    have hc :
        ContMDiff I (𝓘(ℝ, ℝ)) 2 (fun _ : M => c) := by
      simpa using
        (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (2 : WithTop ℕ∞)) (c := c))
    -- Scalar multiplication on `ℝ` is multiplication.
    simpa [Pi.mul_def, Pi.smul_def, smul_eq_mul] using (hc.mul hf)

variable (d : FiniteChartData (H := H) (M := M) I)
variable (μ : Measure M) [IsFiniteMeasure μ]

/-! ### Target types -/

/-- The chartwise target type `L² × (L²(E) × L²(E →L E))` used to define manifold `H²`. -/
abbrev h2TargetE (μ : Measure M) (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) ×
    (↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) ×
      ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)))

/-- The product-of-charts target type used to define manifold `H²`. -/
abbrev h2Target (μ : Measure M) : Type _ := ∀ i : d.ι, h2TargetE (d := d) (I := I) μ i

private abbrev chartMeasureE (i : d.ι) : Measure E :=
  chartMeasure (d := d) (I := I) μ i

private abbrev L2ℝ (i : d.ι) : Type _ := ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] ℝ)
private abbrev L2E (i : d.ι) : Type _ := ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] E)
private abbrev L2EE (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasureE (d := d) (I := I) (μ := μ) i] (E →L[ℝ] E))

private abbrev H2TargetE (i : d.ι) : Type _ :=
  L2ℝ (d := d) (I := I) (μ := μ) i ×
    (L2E (d := d) (I := I) (μ := μ) i ×
      L2EE (d := d) (I := I) (μ := μ) i)

private abbrev H2Target : Type _ := ∀ i : d.ι, H2TargetE (d := d) (I := I) (μ := μ) i

private noncomputable def localizeToC2c (i : d.ι) :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C2c (E := E)) where
  toFun f :=
    ⟨localize (d := d) f.1 i, localize_mem_C2c (d := d) (I := I) (f := f.1) f.2 i⟩
  map_add' f g := by
    ext y
    by_cases hy : y ∈ (extChartAt I (d.center i)).target
    · have hfg :
          localize (d := d) (f.1 + g.1) i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              (f.1 + g.1) ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (f.1 + g.1) ((extChartAt I (d.center i)).symm y)) hy)
      have hf :
          localize (d := d) f.1 i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              f.1 ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      have hg :
          localize (d := d) g.1 i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              g.1 ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                g.1 ((extChartAt I (d.center i)).symm y))
            hy)
      simp [hfg, hf, hg, mul_add]
    · have hfg : localize (d := d) (f.1 + g.1) i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (f.1 + g.1)
                  ((extChartAt I (d.center i)).symm y))
            hy)
      have hf : localize (d := d) f.1 i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      have hg : localize (d := d) g.1 i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                g.1 ((extChartAt I (d.center i)).symm y))
            hy)
      simp [hfg, hf, hg]
  map_smul' c f := by
    ext y
    by_cases hy : y ∈ (extChartAt I (d.center i)).target
    · have hcf :
          localize (d := d) (c • f.1) i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              (c • f.1)
                ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (c • f.1)
                  ((extChartAt I (d.center i)).symm y))
            hy)
      have hf :
          localize (d := d) f.1 i y =
            d.ρ i ((extChartAt I (d.center i)).symm y) *
              f.1 ((extChartAt I (d.center i)).symm y) := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_mem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      have key :
          d.ρ i ((extChartAt I (d.center i)).symm y) *
              (c • f.1) ((extChartAt I (d.center i)).symm y) =
            c * (d.ρ i ((extChartAt I (d.center i)).symm y) *
              f.1 ((extChartAt I (d.center i)).symm y)) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      simp only [SetLike.val_smul, RingHom.id_apply,
        Pi.smul_apply, smul_eq_mul, hcf, hf]
      simpa only [smul_eq_mul, Pi.smul_apply] using key
    · have hcf : localize (d := d) (c • f.1) i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                (c • f.1)
                  ((extChartAt I (d.center i)).symm y))
            hy)
      have hf : localize (d := d) f.1 i y = 0 := by
        simpa [FiniteChartData.localize] using
          (Set.indicator_of_notMem
            (s := (extChartAt I (d.center i)).target) (a := y)
            (f := fun y =>
              d.ρ i ((extChartAt I (d.center i)).symm y) *
                f.1 ((extChartAt I (d.center i)).symm y))
            hy)
      simp [hcf, hf]

/-- The per-chart graph map `C²(M) →ₗ h2TargetE` obtained by localization to chart `i` and the
Euclidean `H²` graph construction. -/
noncomputable def h2GraphChart (i : d.ι) :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h2TargetE (d := d) (I := I) μ i :=
  (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph2
      (μ := chartMeasureE (d := d) (I := I) (μ := μ) i) (E := E)).comp
    (localizeToC2c (d := d) (I := I) i)

/-- The product-of-charts graph map `C²(M) →ₗ ∀ i, h2TargetE i` used to define manifold `H²`. -/
noncomputable def h2Graph :
    ↥(C2 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h2Target (d := d) (I := I) μ := by
  classical
  refine LinearMap.pi fun i => h2GraphChart (d := d) (I := I) (μ := μ) i

private instance instContinuousConstSMulH2TargetE (i : d.ι) :
    ContinuousConstSMul ℝ (h2TargetE (d := d) (I := I) μ i) :=
  inferInstanceAs
    (ContinuousConstSMul ℝ
      (↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) ×
        (↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) ×
          ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)))))

private instance instContinuousConstSMulH2Target :
    ContinuousConstSMul ℝ (h2Target (d := d) (I := I) μ) :=
  inferInstanceAs
    (ContinuousConstSMul ℝ (∀ i : d.ι, h2TargetE (d := d) (I := I) μ i))

/-- The `H²` submodule defined by chart localizations and the Euclidean `H²` graph construction. -/
noncomputable def h2 : Submodule ℝ (h2Target (d := d) (I := I) μ) :=
  (LinearMap.range (h2Graph (d := d) (I := I) (μ := μ))).topologicalClosure

omit [IsManifold I (1 : WithTop ℕ∞) M] [T2Space M] in
theorem isClosed_h2 :
    IsClosed (h2 (d := d) (I := I) (μ := μ) : Set (h2Target (d := d) (I := I) μ)) := by
  simp [h2]

/-- `H²` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpaceh2 : CompleteSpace (↥(h2 (d := d) (I := I) (μ := μ))) := by
  classical
  exact (isClosed_h2 (d := d) (I := I) (μ := μ)).isComplete.completeSpace_coe

/-- The continuous projection `H² →` chartwise
`L² × (L²(E) × L²(E →L E))` for a fixed chart index. -/
noncomputable def h2ToChart (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] h2TargetE (d := d) (I := I) μ i :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp (Submodule.subtypeL (h2 (d := d) (I := I) (μ := μ)))

/-- The continuous chartwise `L²` map extracted from `H²`. -/
noncomputable def h2ToChartL2 (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i)

/-- The continuous chartwise gradient map `H² → L²(E)` extracted from `H²`. -/
noncomputable def h2ToChartL2Grad (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i))

/-- The continuous chartwise Hessian map `H² → L²(E →L E)` extracted from `H²`. -/
noncomputable def h2ToChartL2Hess (i : d.ι) :
    (↥(h2 (d := d) (I := I) (μ := μ))) →L[ℝ]
      ↥(E →₂[chartMeasure (d := d) (I := I) μ i] (E →L[ℝ] E)) :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (h2ToChart (d := d) (I := I) (μ := μ) i))

end FiniteChartData

end

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
