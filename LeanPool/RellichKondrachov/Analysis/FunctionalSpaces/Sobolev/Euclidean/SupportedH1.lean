/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.SupportedH1`

Supported Euclidean `H¹` subspaces for a general measure.

This file defines the `H¹` subspace of functions whose `L²` component is (a.e.) supported in a
measurable set `K`, modeled as membership in the closed range of the extension-by-zero map
`Lp (μ.restrict K) →ₗᵢ Lp μ`.

These definitions match the volume-specialized `h1On` construction used by
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`, but are stated for an
arbitrary measure `μ`. Compactness results are proven elsewhere.

## Main definitions

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnMeasure`
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2Measure`
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceSupportedH1 : MeasurableSpace E := borel E
local instance instBorelSpaceSupportedH1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceSupportedH1 : OpensMeasurableSpace E := by
  infer_instance
local instance instFactOneLeTwoSobolevEuclideanSupportedH1 : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ] {K : Set E} (hKm : MeasurableSet K)

/-! ## Range characterization for extension-by-zero -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [IsFiniteMeasureOnCompacts μ] in
/-- If a function is supported in `K`, then its `Lp` class belongs to the range of `extendByZeroₗᵢ`
from the restricted measure `μ.restrict K`. -/
lemma mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) μ) (hK : tsupport f ⊆ K) :
    (hf.toLp f) ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
  classical
  -- Define the restricted `Lp` class and show its extension by zero matches `hf.toLp f`.
  have hfK : MeasureTheory.MemLp f (2 : ℝ≥0∞) (μ.restrict K) := hf.restrict K
  let u : MeasureTheory.Lp F (2 : ℝ≥0∞) (μ.restrict K) := hfK.toLp f
  refine ⟨u, ?_⟩
  refine MeasureTheory.Lp.ext (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) ?_
  have hu_ae_restrict : (u : E → F) =ᵐ[μ.restrict K] f :=
    (MeasureTheory.MemLp.coeFn_toLp (μ := μ.restrict K) (p := (2 : ℝ≥0∞)) (f := f) hfK)
  have hu_ae_on :
      ∀ᵐ x ∂μ, x ∈ K → (u : E → F) x = f x := by
    exact (ae_restrict_iff' (μ := μ) (s := K) hKm).1 hu_ae_restrict
  have hExt_ae :
      (((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μ) (E := F) (p := (2 : ℝ≥0∞))
              (s := K) hKm) u :
            MeasureTheory.Lp F (2 : ℝ≥0∞) μ) :
            E → F) =ᵐ[μ] K.indicator fun x : E => (u : E → F) x := by
    simpa using
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  have hf_ae : ((hf.toLp f : MeasureTheory.Lp F (2 : ℝ≥0∞) μ) : E → F) =ᵐ[μ] f :=
    (MeasureTheory.MemLp.coeFn_toLp (μ := μ) (p := (2 : ℝ≥0∞)) (f := f) hf)
  -- Combine: on `K` use `hu_ae_on`; off `K` use pointwise support control.
  filter_upwards [hExt_ae, hf_ae, hu_ae_on] with x hxExt hxLp hxOn
  by_cases hxK : x ∈ K
  · -- on `K`, the indicator is `u`, and `u = f`.
    calc
      ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μ) (E := F) (p := (2 : ℝ≥0∞)) (s := K) hKm) u : E → F) x =
          (K.indicator (fun y : E => (u : E → F) y)) x := hxExt
      _ = (u : E → F) x := by simp [hxK]
      _ = f x := hxOn hxK
      _ = (hf.toLp f : E → F) x := by simpa using hxLp.symm
  · -- off `K`, the indicator is `0`, and `f x = 0`.
    have hfx : f x = 0 := by
      have : x ∉ tsupport f := by
        exact fun hx' => hxK (hK hx')
      simpa using (image_eq_zero_of_notMem_tsupport (f := f) this)
    simp [hxK, hxExt, hxLp, hfx]

/-- The subspace of `H¹(μ)` whose `L²` component is (a.e.) supported in `K`.

We model “supported in `K`” as belonging to the closed range of the extension-by-zero map
`Lp(μ.restrict K) →ₗᵢ Lp(μ)`. -/
noncomputable def h1OnMeasure :
    Submodule ℝ (↥(h1 (μ := μ) (E := E))) :=
  Submodule.comap
    (h1ToL2 (μ := μ) (E := E)).toLinearMap
    (LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := μ) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))

/-- The inclusion `h1OnMeasure μ K → L²(μ)` as a continuous linear map. -/
noncomputable def h1OnToL2Measure :
    ↥(h1OnMeasure (μ := μ) hKm) →L[ℝ] (E →₂[μ] ℝ) :=
  (h1ToL2 (μ := μ) (E := E)).comp (h1OnMeasure (μ := μ) hKm).subtypeL

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
