/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.ChartMeasure
import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.Localization

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.H1`

Define a scalar `H¹` space on a compact manifold relative to finite chart data.

Given `d : FiniteChartData` and a finite measure `μ` on `M`, we:

- define the submodule `C1` of `C¹` scalar functions `M → ℝ` (in the manifold sense);
- define the per-chart graph map obtained by localizing into Euclidean `C1c` and then applying the
  Euclidean `H¹` graph `C1c →ₗ L² × L²(E)`;
- define `h1` as the topological closure of the range of the product-of-charts graph map.

## Main definitions

- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.C1`
- `RellichKondrachov.Geometry.Manifold.Sobolev.FiniteChartData.h1`
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
local instance instMeasurableSpaceEH1 : MeasurableSpace E := borel E
local instance instBorelSpaceEH1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEH1 : OpensMeasurableSpace E := by infer_instance

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMH1 : MeasurableSpace M := borel M
local instance instBorelSpaceMH1 : BorelSpace M := ⟨rfl⟩

namespace FiniteChartData

/-- `C¹` scalar functions `M → ℝ` (in the manifold sense), as a submodule of `M → ℝ`. -/
def C1 : Submodule ℝ (M → ℝ) where
  carrier := {f | ContMDiff I (𝓘(ℝ, ℝ)) 1 f}
  zero_mem' := by
    -- `0` is (locally) constant, hence `C¹`.
    exact (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (1 : WithTop ℕ∞)) (c := (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    simpa using (hf.add hg)
  smul_mem' := by
    intro c f hf
    -- Scalar multiplication on `ℝ` is multiplication.
    have hc :
        ContMDiff I (𝓘(ℝ, ℝ)) 1 (fun _ : M => c) := by
      simpa using
        (contMDiff_const (I := I) (I' := (𝓘(ℝ, ℝ))) (n := (1 : WithTop ℕ∞)) (c := c))
    -- `c • f = (fun _ => c) * f`.
    simpa [Pi.mul_def, Pi.smul_def, smul_eq_mul] using (hc.mul hf)

variable (d : FiniteChartData (H := H) (M := M) I)

variable (μ : Measure M) [IsFiniteMeasure μ]

private noncomputable def localizeToC1c (i : d.ι) :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E)) where
  toFun f :=
    ⟨localize (d := d) f.1 i, localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩
  map_add' f g := by
    ext y
    by_cases hy : y ∈ (extChartAt I (d.center i)).target
    · -- On the chart target, `indicator` is the identity.
      have hfg :
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
      -- Now use distributivity in `ℝ`.
      simp [hfg, hf, hg, mul_add]
    · -- Outside the chart target, all indicator terms vanish.
      have hfg : localize (d := d) (f.1 + g.1) i y = 0 := by
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
              (c • f.1) ((extChartAt I (d.center i)).symm y) := by
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
      -- Scalar multiplication is multiplication; use commutativity in `ℝ`.
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

/-! ### Target types -/

/-- The chartwise target type `L² × L²(E)` used to define manifold `H¹`. -/
abbrev h1TargetE (μ : Measure M) (i : d.ι) : Type _ :=
  ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) × ↥(E →₂[chartMeasure (d := d) (I := I) μ i] E)

/-- The product-of-charts target type used to define manifold `H¹`. -/
abbrev h1Target (μ : Measure M) : Type _ := ∀ i : d.ι, h1TargetE (d := d) (I := I) μ i

/-- The per-chart graph map `C¹(M) →ₗ (L² × L²(E))` obtained by localization to chart `i` and the
Euclidean `H¹` graph construction. -/
noncomputable def h1GraphChart (i : d.ι) :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h1TargetE (d := d) (I := I) μ i :=
  (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
      (μ := chartMeasure (d := d) (I := I) μ i) (E := E)).comp
    (localizeToC1c (d := d) (I := I) i)

omit [T2Space M] in
lemma h1GraphChart_mem_range_euclidean_graph (i : d.ι)
    (f : ↥(C1 (E := E) (H := H) (M := M) (I := I))) :
    h1GraphChart (d := d) (I := I) (μ := μ) i f ∈
      LinearMap.range
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := chartMeasure (d := d) (I := I) μ i) (E := E)) := by
  classical
  refine ⟨localizeToC1c (d := d) (I := I) i f, rfl⟩

/-!
### Unfolding lemmas

These lemmas expose the chartwise `L²` and `L²(E)` components of `h1GraphChart` in terms of the
underlying localized function `localize (d := d) f i`. They are used downstream to control supports.
-/

omit [T2Space M] in
/-- The scalar `L²` component of `h1GraphChart` is the `L²` class of `localize f i`. -/
lemma h1GraphChart_fst (i : d.ι) (f : ↥(C1 (E := E) (H := H) (M := M) (I := I))) :
    (h1GraphChart (d := d) (I := I) (μ := μ) i f).1 =
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
        (μ := chartMeasure (d := d) (I := I) μ i)
        (E := E)
        ⟨localize (d := d) f.1 i, localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  simp [h1GraphChart, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph,
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Linear, localizeToC1c]

omit [T2Space M] in
/-- The gradient `L²(E)` component of `h1GraphChart` is the `L²(E)` class
of `grad (localize f i)`. -/
lemma h1GraphChart_snd (i : d.ι) (f : ↥(C1 (E := E) (H := H) (M := M) (I := I))) :
    (h1GraphChart (d := d) (I := I) (μ := μ) i f).2 =
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
        (μ := chartMeasure (d := d) (I := I) μ i)
        (E := E)
        ⟨localize (d := d) f.1 i, localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  simp [h1GraphChart, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph,
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2GradLinear, localizeToC1c]

/-- The product-of-charts graph map `C¹(M) →ₗ ∀ i, (L² × L²(E))` used to define manifold `H¹`. -/
noncomputable def h1Graph :
    ↥(C1 (E := E) (H := H) (M := M) (I := I)) →ₗ[ℝ] h1Target (d := d) (I := I) μ := by
  classical
  -- Assemble the per-chart graph maps into a product map.
  refine LinearMap.pi fun i => h1GraphChart (d := d) (I := I) (μ := μ) i

/-- The `H¹` submodule defined by chart localizations and the Euclidean `H¹` graph construction. -/
noncomputable def h1 : Submodule ℝ (h1Target (d := d) (I := I) μ) :=
  (LinearMap.range (h1Graph (d := d) (I := I) (μ := μ))).topologicalClosure

omit [T2Space M] in
theorem isClosed_h1 :
    IsClosed (h1 (d := d) (I := I) (μ := μ) : Set (h1Target (d := d) (I := I) μ)) := by
  exact Submodule.isClosed_topologicalClosure (LinearMap.range (h1Graph (d := d) (I := I) (μ := μ)))

/-- `H¹` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpaceh1 : CompleteSpace (↥(h1 (d := d) (I := I) (μ := μ))) := by
  classical
  exact (isClosed_h1 (d := d) (I := I) (μ := μ)).isComplete.completeSpace_coe

/-- The continuous projection `H¹ →` chartwise `L² × L²(E)` for a fixed chart index. -/
noncomputable def h1ToChart (i : d.ι) :
    (↥(h1 (d := d) (I := I) (μ := μ))) →L[ℝ] h1TargetE (d := d) (I := I) μ i :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp (Submodule.subtypeL (h1 (d := d) (I := I) (μ := μ)))

/-- The continuous chartwise `L²` map extracted from `H¹`. -/
noncomputable def h1ToChartL2 (i : d.ι) :
    (↥(h1 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (h1ToChart (d := d) (I := I) (μ := μ) i)

/-- The continuous chartwise gradient map `H¹ → L²(E)` extracted from `H¹`. -/
noncomputable def h1ToChartL2Grad (i : d.ι) :
    (↥(h1 (d := d) (I := I) (μ := μ))) →L[ℝ] ↥(E →₂[chartMeasure (d := d) (I := I) μ i] E) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (h1ToChart (d := d) (I := I) (μ := μ) i)

end FiniteChartData

end

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
