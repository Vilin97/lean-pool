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

public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
public import LeanPool.PoincareGeometry.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovDensity.Transport

/-! # Chartwise -/

@[expose] public section

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson

Adaptation: generic finite-measure, two-sided local-density comparison version,
derived from RellichKondrachovRiemannian at upstream commit
70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23 and its local Lean 4.33 migration.
The original support, graph-closure, and compactness proofs are retained;
Riemannian/Hausdorff-specific comparison constants are replaced by explicit
finite bounds on the compact localization supports. No measure equality,
compactness hypothesis, or Poincare inequality is assumed.
-/

/-! # Compactness by transport of both scalar and derivative graph components -/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped BigOperators ENNReal MeasureTheory Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

local notation "n∞" => (↑(⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

local instance densityChartwiseInstance0 : MeasurableSpace M := borel M
local instance densityChartwiseInstance1 : BorelSpace M := ⟨rfl⟩
local instance densityChartwiseInstance2 : MeasurableSpace E := borel E
local instance densityChartwiseInstance3 : BorelSpace E := ⟨rfl⟩
local instance densityChartwiseInstance4 : OpensMeasurableSpace E := by infer_instance

namespace Density
variable (d : FiniteChartData (H := H) (M := M) I)
  (μ : Measure M) [IsFiniteMeasure μ]

variable (hcomp : LocalMeasureComparison d μ)
include μ hcomp

/-!
## Chartwise compactness for locally comparable finite measures

This section uses Euclidean Rellich compactness on Lebesgue `volume` and transports it to the
chart pushforward measures via the `L²` range equivalences developed above.
-/

section ChartwiseCompactness

open RellichKondrachov.Analysis.FunctionalSpaces

variable (i : d.ι)

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (i : d.ι)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := μchart) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) ≃L[ℝ]
        ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) :=
  l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := F)

/-!
### Range-codomain restricted chart maps

We will work with codomain restrictions into the closed `extendByZero` range to make the transport
between `μchart` and `volume` explicit and purely `L²`-level.
-/

noncomputable def h1ToChartL2Range :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  refine
    (FiniteChartData.h1ToChartL2 (d := d) (I := I) (μ := μM) i).codRestrict
      (LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) ?_
  intro x
  simpa using! (h1ToChartL2_mem_extendByZero_range (d := d) (μ := μ) (I := I) i x)

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartL2GradRange :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  refine
    (FiniteChartData.h1ToChartL2Grad (d := d) (I := I) (μ := μM) i).codRestrict
      (LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) ?_
  intro x
  simpa using! (h1ToChartL2Grad_mem_extendByZero_range (d := d) (μ := μ) (I := I) i x)

/-!
### Volume-side supported `H¹` map and compactness

We now transport the chartwise `H¹` element to Lebesgue `volume` on `K`, apply Euclidean Rellich
compactness there, and transport the compactness statement back to the chart measure.
-/

noncomputable def h1ToChartL2RangeVol :
    let μM :=
      μ
    let _μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  have e :
      ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) ≃L[ℝ]
          ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) := by
    simpa using! (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ))
  exact e.toContinuousLinearMap.comp (h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i))

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartL2GradRangeVol :
    let μM :=
      μ
    let _μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := E) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  have e :
      ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) ≃L[ℝ]
          ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)) := by
    simpa using! (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := E))
  exact e.toContinuousLinearMap.comp (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartL2GradRange (d := d) (μ := μ) (I := I) (i := i))

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1Target :
    let μM :=
      μ
    let _μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) := by
  classical
  intro μM μchart K
  let f :
      ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ] ↥(E →₂[(volume : Measure E)] ℝ) :=
    ((LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)).subtypeL).comp
      (h1ToChartL2RangeVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i))
  let g :
      ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ] ↥(E →₂[(volume : Measure E)] E) :=
    ((LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)).subtypeL).comp
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartL2GradRangeVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i))
  exact f.prod g

/-!
### A volume-side chart target map defined on the ambient `H¹` target

For the closure argument showing membership in Euclidean `H¹(volume)`, it is convenient to have a
continuous linear map defined on the *ambient* chart `H¹` target
`L²(μchart) × L²(μchart;E)`, rather than only on the `extendByZero` range.

We implement this by restricting to `K`, applying the restricted `L²` change-of-measure equivalence,
and extending by zero back to `L²(volume)`.
-/

omit μ hcomp in
lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_restrict_le_one_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    μ.restrict s ≤ (1 : ℝ≥0∞) • μ := by
  simpa [one_smul] using! (Measure.restrict_le_self (μ := μ) (s := s))

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (i : d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(E →₂[μchart] F) →L[ℝ] ↥(E →₂[(volume : Measure E)] F) := by
  classical
  intro μM μchart K
  -- Restrict `L²(μchart)` to `L²(μchart.restrict K)` via the identity map (since `μchart.restrict K ≤ μchart`).
  let r :
      (E →₂[μchart] F) →L[ℝ] (E →₂[μchart.restrict K] F) :=
    MeasureTheory.Lp.changeMeasureL
      (μ := μchart) (ν := μchart.restrict K) (E := F) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
      (by simpa using! (one_ne_top : (1 : ℝ≥0∞) ≠ ∞)) (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_restrict_le_one_smul (μ := μchart) (s := K))
      (by simpa using! (ENNReal.coe_ne_top (2 : ℕ)))
  -- Change measure on the restricted spaces.
  let e : (E →₂[μchart.restrict K] F) ≃L[ℝ] (E →₂[(volume : Measure E).restrict K] F) :=
    l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := F)
  -- Extend back to `L²(volume)` by zero outside `K`.
  let ez :
      (E →₂[(volume : Measure E).restrict K] F) →ₗᵢ[ℝ] (E →₂[(volume : Measure E)] F) :=
    MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
      (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)
  exact (ez.toContinuousLinearMap).comp (e.toContinuousLinearMap.comp r)

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget (i : d.ι) :
    let μM :=
      μ
    let _μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    (FiniteChartData.h1TargetE (d := d) (I := I) μM i) →L[ℝ]
      (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) := by
  classical
  intro μM μchart K
  -- Map each component `L²(μchart)` / `L²(μchart;E)` into `L²(volume)` / `L²(volume;E)` using
  -- `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage`.
  let f :
      (FiniteChartData.h1TargetE (d := d) (I := I) μM i) →L[ℝ] ↥(E →₂[(volume : Measure E)] ℝ) :=
    (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)).comp
      (ContinuousLinearMap.fst ℝ (↥(E →₂[μchart] ℝ)) (↥(E →₂[μchart] E)))
  let g :
      (FiniteChartData.h1TargetE (d := d) (I := I) μM i) →L[ℝ] ↥(E →₂[(volume : Measure E)] E) :=
    (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := E)).comp
      (ContinuousLinearMap.snd ℝ (↥(E →₂[μchart] ℝ)) (↥(E →₂[μchart] E)))
  exact f.prod g

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (i : d.ι) :
    let μM :=
      μ
    let _μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    (FiniteChartData.h1Target (d := d) (I := I) μM) →L[ℝ]
      (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) := by
  classical
  intro μM μchart K
  let proj :
      (FiniteChartData.h1Target (d := d) (I := I) μM) →L[ℝ]
        (FiniteChartData.h1TargetE (d := d) (I := I) μM i) :=
    ContinuousLinearMap.proj (R := ℝ) i
  exact (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)).comp proj

/-!
### Graph compatibility (C¹c generators)

To use Euclidean Rellich compactness for `volume`, we need to know that the volume-side map
`vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget` respects the Euclidean graph generators induced by
`FiniteChartData.localize`.
-/

omit μ hcomp in
lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_support_subset_of_tsupport_subset {F : Type*} [Zero F]
    (g : E → F) {K : Set E} (h : tsupport g ⊆ K) : Function.support g ⊆ K := by
  -- `tsupport g = closure (support g)` by definition.
  have hsupp : Function.support g ⊆ tsupport g := by
    simpa [tsupport] using! (subset_closure : Function.support g ⊆ closure (Function.support g))
  exact hsupp.trans h

omit μ hcomp in
lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_indicator_ae_eq_of_ae_eq_restrict
    {F : Type*} [MeasurableSpace F] [Zero F] [MeasurableEq F]
    {μ : Measure E} {K : Set E} {f g : E → F}
    (hf : AEMeasurable f (μ.restrict K)) (hg : AEMeasurable g (μ.restrict K))
    (hfg : f =ᵐ[μ.restrict K] g) (hsupp : Function.support g ⊆ K) :
    K.indicator f =ᵐ[μ] g := by
  have hEq : ∀ᵐ x ∂μ.restrict K, f x = g x := hfg
  have h0 : (μ.restrict K) {x | f x ≠ g x} = 0 := by
    -- Convert AE equality to a measure-zero inequality set.
    have h0' : (μ.restrict K) {x | ¬f x = g x} = 0 := (MeasureTheory.ae_iff).1 hEq
    simpa [ne_eq] using! h0'
  have hnullEq : NullMeasurableSet {x | f x = g x} (μ.restrict K) :=
    nullMeasurableSet_eq_fun (μ := μ.restrict K) hf hg
  have hnullNe : NullMeasurableSet {x | f x ≠ g x} (μ.restrict K) := by
    -- Complement of the equality set.
    simpa [Set.compl_setOf, ne_eq] using! hnullEq.compl
  have hK0 : μ ({x | f x ≠ g x} ∩ K) = 0 := by
    -- Use the restriction formula on a null-measurable set.
    have hEqRestr :
        (μ.restrict K) {x | f x ≠ g x} = μ ({x | f x ≠ g x} ∩ K) :=
      Measure.restrict_apply₀ (μ := μ) (s := K) (t := {x | f x ≠ g x}) hnullNe
    simpa [hEqRestr] using! h0
  have hsubset :
      {x | K.indicator f x ≠ g x} ⊆ {x | f x ≠ g x} ∩ K := by
    intro x hx
    have hxK : x ∈ K := by
      by_contra hxK
      have hg0 : g x = 0 := by
        have hxnsupp : x ∉ Function.support g := by
          intro hxSupp
          exact hxK (hsupp hxSupp)
        -- `x ∉ support g` means `g x = 0`.
        simpa [Function.support, Set.mem_setOf_eq] using! hxnsupp
      have hfx0 : K.indicator f x = 0 := by simp [hxK]
      exact hx (by simpa [hfx0, hg0])
    have hne : f x ≠ g x := by
      -- On `K`, the indicator is the identity.
      simpa [Set.indicator_of_mem hxK] using! hx
    exact ⟨hne, hxK⟩
  have hbad0 : μ {x | K.indicator f x ≠ g x} = 0 :=
    measure_mono_null hsubset hK0
  have : ∀ᵐ x ∂μ, K.indicator f x = g x := by
    -- `ae_iff` expects a negated predicate set; rewrite it to the inequality set.
    refine (MeasureTheory.ae_iff).2 ?_
    simpa [ne_eq] using! hbad0
  exact this

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2EquivVolumeOnRhoSupportImage'_coeFn_ae_eq (i : d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f :
      E →₂[
        (FiniteChartData.chartMeasure (d := d) (I := I)
              (μ) i).restrict
          (FiniteChartData.rhoSupportImage (d := d) (I := I) i)
      ] F) :
    ((l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := F)) f : E → F) =ᵐ[
        (volume : Measure E).restrict (FiniteChartData.rhoSupportImage (d := d) (I := I) i)
      ] f := by
  classical
  let μM :=
    μ
  let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
  let cChartVol : ℝ≥0∞ := hcomp.chartToVolume i
  let cVolChart : ℝ≥0∞ := hcomp.volumeToChart i
  have hμ_le : μchart.restrict K ≤ cChartVol • (volume : Measure E).restrict K := by
    simpa [μM, μchart, K, cChartVol] using!
      chartMeasure_restrict_rhoSupportImage_le_volume (d := d) (μ := μ) (hcomp := hcomp) (I := I) i
  have hvol_le : (volume : Measure E).restrict K ≤ cVolChart • μchart.restrict K := by
    simpa [μM, μchart, K, cVolChart] using!
      volume_restrict_rhoSupportImage_le_chartMeasure (d := d) (μ := μ) (hcomp := hcomp) (I := I) i
  have hcChartVol : cChartVol ≠ ∞ :=
    chartMeasure_volume_constant_ne_top (d := d) (μ := μ) (hcomp := hcomp) (I := I) (E := E) i
  have hcVolChart : cVolChart ≠ ∞ :=
    volume_chartMeasure_constant_ne_top (d := d) (μ := μ) (hcomp := hcomp) (I := I) (E := E) i
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by simp
  -- Unfold and apply the general `changeMeasureEquiv` coherence lemma.
  simpa [l2EquivVolumeOnRhoSupportImage', μM, μchart, K, cVolChart, cChartVol] using!
    (MeasureTheory.Lp.changeMeasureEquiv_coeFn_ae_eq
      (μ := μchart.restrict K) (ν := (volume : Measure E).restrict K) (E := F) (p := (2 : ℝ≥0∞))
      (c₁ := cVolChart) (c₂ := cChartVol) hcVolChart hcChartVol hvol_le hμ_le hp f)

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage_toL2_of_tsupport_subset (i : d.ι)
    (g : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    tsupport g.1 ⊆ K →
      vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2 (μ := μchart) (E := E) g) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2 (μ := (volume : Measure E)) (E := E) g := by
  classical
  intro μM μchart K htsupp
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  have hsupp : Function.support g.1 ⊆ K :=
    vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_support_subset_of_tsupport_subset (g := g.1) (K := K) htsupp
  -- Abbreviate the chart- and volume-side `L²` elements of `g`.
  let x : E →₂[μchart] ℝ :=
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2 (μ := μchart) (E := E) g
  let y : E →₂[(volume : Measure E)] ℝ :=
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2 (μ := (volume : Measure E)) (E := E) g
  -- `x` is represented by `g` a.e. under `μchart`, hence also under `μchart.restrict K`.
  have hx : (x : E → ℝ) =ᵐ[μchart] g.1 := by
    have hxmem : MeasureTheory.MemLp g.1 (2 : ℝ≥0∞) μchart := by
      simpa using!
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
          (μ := μchart) (E := E) (f := g.1) g.2)
    simpa [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2] using! hxmem.coeFn_toLp
  have hxK : (x : E → ℝ) =ᵐ[μchart.restrict K] g.1 :=
    MeasureTheory.ae_restrict_of_ae (s := K) hx
  -- Expand `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage` and chase AE equalities.
  dsimp [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage]
  -- `r : L²(μchart) → L²(μchart.restrict K)` is `changeMeasureL`.
  have hν_le : μchart.restrict K ≤ (1 : ℝ≥0∞) • μchart := by
    simpa using! (Measure.restrict_le_self (μ := μchart) (s := K))
  let r :
      (E →₂[μchart] ℝ) →L[ℝ] (E →₂[μchart.restrict K] ℝ) :=
    MeasureTheory.Lp.changeMeasureL
      (μ := μchart) (ν := μchart.restrict K) (E := ℝ) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
      (by simp) (by simpa using! (Measure.restrict_le_self (μ := μchart) (s := K))) (by simp)
  let e : (E →₂[μchart.restrict K] ℝ) ≃L[ℝ] (E →₂[(volume : Measure E).restrict K] ℝ) :=
    l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)
  let ez :
      (E →₂[(volume : Measure E).restrict K] ℝ) →ₗᵢ[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hr : (r x : E → ℝ) =ᵐ[μchart.restrict K] (x : E → ℝ) := by
    simpa [r] using!
      (MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq (μ := μchart) (ν := μchart.restrict K) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp) hν_le (by simp) x)
  have hrg : (r x : E → ℝ) =ᵐ[μchart.restrict K] g.1 :=
    hr.trans hxK
  have hvol_le : (volume : Measure E).restrict K ≤
      hcomp.volumeToChart i • μchart.restrict K := by
    simpa [μM, μchart, K] using!
      volume_restrict_rhoSupportImage_le_chartMeasure (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
  have habs : (volume : Measure E).restrict K ≪ μchart.restrict K :=
    Measure.absolutelyContinuous_of_le_smul hvol_le
  have hrgVol : (r x : E → ℝ) =ᵐ[(volume : Measure E).restrict K] g.1 :=
    habs.ae_le hrg
  have he : (e (r x) : E → ℝ) =ᵐ[(volume : Measure E).restrict K] (r x : E → ℝ) := by
    -- Use the specialized lemma for `l2EquivVolumeOnRhoSupportImage'`.
    simpa [e, μM, μchart, K] using!
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2EquivVolumeOnRhoSupportImage'_coeFn_ae_eq (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ) (f := r x))
  have heg : (e (r x) : E → ℝ) =ᵐ[(volume : Measure E).restrict K] g.1 :=
    he.trans hrgVol
  have hInd :
      K.indicator (fun z : E => (e (r x) : E → ℝ) z) =ᵐ[(volume : Measure E)] g.1 := by
    refine vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_indicator_ae_eq_of_ae_eq_restrict (μ := (volume : Measure E)) (K := K)
        (f := fun z : E => (e (r x) : E → ℝ) z) (g := g.1) ?_ ?_ heg hsupp
    · exact (MeasureTheory.Lp.aestronglyMeasurable (e (r x))).aemeasurable
    · have hgmem : MeasureTheory.MemLp g.1 (2 : ℝ≥0∞) ((volume : Measure E).restrict K) := by
        simpa using!
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
            (μ := (volume : Measure E).restrict K) (E := E) (f := g.1) g.2)
      exact hgmem.aestronglyMeasurable.aemeasurable
  have hez :
      ((ez (e (r x)) : E →₂[(volume : Measure E)] ℝ) : E → ℝ) =ᵐ[(volume : Measure E)]
        K.indicator fun z : E => (e (r x) : E → ℝ) z := by
    simpa [ez] using!
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
        (s := K) (hs := hKm) (f := e (r x)))
  -- Conclude by `Lp.ext` on `volume`.
  apply Lp.ext
  have hy : (y : E → ℝ) =ᵐ[(volume : Measure E)] g.1 := by
    have hymem : MeasureTheory.MemLp g.1 (2 : ℝ≥0∞) (volume : Measure E) := by
      simpa using!
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
          (μ := (volume : Measure E)) (E := E) (f := g.1) g.2)
    simpa [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2] using! hymem.coeFn_toLp
  have hT :
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ) x : E → ℝ) =ᵐ[
          (volume : Measure E)
        ] K.indicator fun z : E => (e (r x) : E → ℝ) z := by
    -- This is definitional: `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage` is `ez ∘ e ∘ r`.
    simpa [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage, r, e, ez] using! hez
  exact hT.trans (hInd.trans hy.symm)

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage_toL2Grad_of_tsupport_subset (i : d.ι)
    (g : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E))) :
    let μM :=
      μ
    let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    tsupport g.1 ⊆ K →
      vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := E)
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad (μ := μchart) (E := E) g) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad (μ := (volume : Measure E)) (E := E) g := by
  classical
  intro μM μchart K htsupp
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  -- Support of the gradient is contained in `K`.
  have htsuppGrad :
      tsupport
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1) ⊆ K := by
    exact
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset
          (E := E) (f := g.1)).trans
        htsupp
  have hsuppGrad : Function.support
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1) ⊆ K :=
    vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_support_subset_of_tsupport_subset (g :=
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1) (K := K) htsuppGrad
  let x : E →₂[μchart] E :=
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad (μ := μchart) (E := E) g
  let y : E →₂[(volume : Measure E)] E :=
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad (μ := (volume : Measure E)) (E := E) g
  have hx : (x : E → E) =ᵐ[μchart]
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1 := by
    have hxmem :
        MeasureTheory.MemLp
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1)
          (2 : ℝ≥0∞) μchart := by
      simpa using!
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
          (μ := μchart) (E := E) (f := g.1) g.2)
    simpa [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad] using! hxmem.coeFn_toLp
  have hxK :
      (x : E → E) =ᵐ[μchart.restrict K]
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1 :=
    MeasureTheory.ae_restrict_of_ae (s := K) hx
  have hν_le : μchart.restrict K ≤ (1 : ℝ≥0∞) • μchart := by
    simpa using! (Measure.restrict_le_self (μ := μchart) (s := K))
  let r :
      (E →₂[μchart] E) →L[ℝ] (E →₂[μchart.restrict K] E) :=
    MeasureTheory.Lp.changeMeasureL
      (μ := μchart) (ν := μchart.restrict K) (E := E) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
      (by simp) (by simpa using! (Measure.restrict_le_self (μ := μchart) (s := K))) (by simp)
  let e : (E →₂[μchart.restrict K] E) ≃L[ℝ] (E →₂[(volume : Measure E).restrict K] E) :=
    l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := E)
  let ez :
      (E →₂[(volume : Measure E).restrict K] E) →ₗᵢ[ℝ] (E →₂[(volume : Measure E)] E) :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := E) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hr : (r x : E → E) =ᵐ[μchart.restrict K] (x : E → E) := by
    simpa [r] using!
      (MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq (μ := μchart) (ν := μchart.restrict K) (E := E)
        (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp) hν_le (by simp) x)
  have hrg :
      (r x : E → E) =ᵐ[μchart.restrict K]
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1 :=
    hr.trans hxK
  have hvol_le : (volume : Measure E).restrict K ≤
      hcomp.volumeToChart i • μchart.restrict K := by
    simpa [μM, μchart, K] using!
      volume_restrict_rhoSupportImage_le_chartMeasure (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
  have habs : (volume : Measure E).restrict K ≪ μchart.restrict K :=
    Measure.absolutelyContinuous_of_le_smul hvol_le
  have hrgVol :
      (r x : E → E) =ᵐ[(volume : Measure E).restrict K]
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1 :=
    habs.ae_le hrg
  have he : (e (r x) : E → E) =ᵐ[(volume : Measure E).restrict K] (r x : E → E) := by
    simpa [e, μM, μchart, K] using!
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2EquivVolumeOnRhoSupportImage'_coeFn_ae_eq (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := E) (f := r x))
  have heg :
      (e (r x) : E → E) =ᵐ[(volume : Measure E).restrict K]
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1 :=
    he.trans hrgVol
  have hInd :
      K.indicator (fun z : E => (e (r x) : E → E) z) =ᵐ[(volume : Measure E)]
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1 := by
    refine vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_indicator_ae_eq_of_ae_eq_restrict (μ := (volume : Measure E)) (K := K)
        (f := fun z : E => (e (r x) : E → E) z)
        (g := RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1) ?_ ?_ heg hsuppGrad
    · exact (MeasureTheory.Lp.aestronglyMeasurable (e (r x))).aemeasurable
    · have hgmem :
          MeasureTheory.MemLp
            (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1)
            (2 : ℝ≥0∞) ((volume : Measure E).restrict K) := by
        simpa using!
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
            (μ := (volume : Measure E).restrict K) (E := E) (f := g.1) g.2)
      exact hgmem.aestronglyMeasurable.aemeasurable
  have hez :
      ((ez (e (r x)) : E →₂[(volume : Measure E)] E) : E → E) =ᵐ[(volume : Measure E)]
        K.indicator fun z : E => (e (r x) : E → E) z := by
    simpa [ez] using!
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
        (s := K) (hs := hKm) (f := e (r x)))
  apply Lp.ext
  have hy : (y : E → E) =ᵐ[(volume : Measure E)]
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1 := by
    have hymem :
        MeasureTheory.MemLp
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad (E := E) g.1)
          (2 : ℝ≥0∞) (volume : Measure E) := by
      simpa using!
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
          (μ := (volume : Measure E)) (E := E) (f := g.1) g.2)
    simpa [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad] using! hymem.coeFn_toLp
  have hT :
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := E) x : E → E) =ᵐ[
          (volume : Measure E)
        ] K.indicator fun z : E => (e (r x) : E → E) z := by
    simpa [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage, r, e, ez] using! hez
  exact hT.trans (hInd.trans hy.symm)

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget_h1GraphChart (i : d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      μ
    vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
        (FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f) =
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph (μ := (volume : Measure E)) (E := E))
        ⟨FiniteChartData.localize (d := d) (I := I) f.1 i,
          FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
  let g :
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E)) :=
    ⟨FiniteChartData.localize (d := d) (I := I) f.1 i,
      FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩
  have htsupp : tsupport g.1 ⊆ K := by
    simpa [g, K] using!
      (FiniteChartData.tsupport_localize_subset_rhoSupportImage (d := d) (I := I) (f := f.1) i)
  -- Compare componentwise, keeping goals in `L²` (avoid `ext` on `Lp`, which produces AE goals).
  refine Prod.ext ?_ ?_
  · -- Scalar component.
    have hfst :
        ((FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f).1) =
          RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2 (μ := μchart) (E := E) g := by
      simpa [μchart, μM, K, g] using!
        (FiniteChartData.h1GraphChart_fst (d := d) (I := I) (μ := μM) i f)
    -- Reduce to the `L²` transport lemma.
    simpa [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget, g,
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph,
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Linear,
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2GradLinear,
      hfst] using!
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage_toL2_of_tsupport_subset (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) g htsupp)
  · -- Gradient component.
    have hsnd :
        ((FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f).2) =
          RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad (μ := μchart) (E := E) g := by
      simpa [μchart, μM, K, g] using!
        (FiniteChartData.h1GraphChart_snd (d := d) (I := I) (μ := μM) i f)
    simpa [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget, g,
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph,
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Linear,
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2GradLinear,
      hsnd] using!
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage_toL2Grad_of_tsupport_subset (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) g htsupp)

/-!
### Closure argument: chartwise volume image lies in Euclidean `H¹(volume)` and `h1On`

We use the graph compatibility lemma above to show that the volume-side projection map sends the
defining dense range of `FiniteChartData.h1` into the Euclidean graph range on `volume`, and thus
extends to a map `H¹(M) → H¹(volume)` (and further into `h1On K`).

This sets up the application of Euclidean Rellich compactness on `volume` in later steps.
-/

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget_h1Graph (i : d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      μ
    vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
        (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM) f) =
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph (μ := (volume : Measure E)) (E := E))
        ⟨FiniteChartData.localize (d := d) (I := I) f.1 i,
          FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
  -- `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget` is `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget ∘ proj`, and `h1Graph` is `pi` of `h1GraphChart`.
  have hproj :
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
            (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM) f)) =
        vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
          ((FiniteChartData.h1Graph (d := d) (I := I) (μ := μM) f) i) := by
    simp [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget, ContinuousLinearMap.proj_apply]
  -- Rewrite the `i`-th component of `h1Graph`.
  have hi :
      (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM) f) i =
        FiniteChartData.h1GraphChart (d := d) (I := I) (μ := μM) i f := by
    simp [FiniteChartData.h1Graph]
  -- Conclude using graph compatibility on `h1GraphChart`.
  simpa [hproj, hi, μchart, K] using!
    (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget_h1GraphChart (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) f)

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget_mem_euclidean_h1 (i : d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := d) (I := I)
            (μ :=
              μ))) :
    let μM :=
      μ
    let _μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM) ∈
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := (volume : Measure E)) (E := E) : Set _) := by
  classical
  intro μM μchart K
  let A : Set (FiniteChartData.h1Target (d := d) (I := I) μM) :=
    (LinearMap.range (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM)) : Set _)
  have hx_closure : (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM) ∈ closure A := by
    simpa [FiniteChartData.h1, Submodule.topologicalClosure_coe, A] using! x.2
  let T :
      (FiniteChartData.h1Target (d := d) (I := I) μM) →L[ℝ]
        (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) :=
    vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
  have hTmem : T x.1 ∈ closure (Set.image T A) :=
    mem_closure_image (f := T) (s := A) (x := x.1) (T.continuous.continuousAt) hx_closure
  have hImage :
      Set.image T A ⊆
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := (volume : Measure E)) (E := E) : Set _) := by
    intro y hy
    rcases hy with ⟨z, hzA, rfl⟩
    rcases hzA with ⟨f, rfl⟩
    -- Use the graph compatibility lemma for `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget` on generators.
    have :
        T (FiniteChartData.h1Graph (d := d) (I := I) (μ := μM) f) ∈
          LinearMap.range
            (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph (μ := (volume : Measure E)) (E := E)) := by
      let g :
          ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c (E := E)) :=
        ⟨FiniteChartData.localize (d := d) (I := I) f.1 i,
          FiniteChartData.localize_mem_C1c (d := d) (I := I) (f := f.1) f.2 i⟩
      refine ⟨g, ?_⟩
      simpa [T, g, μM, μchart, K] using!
        (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget_h1Graph (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) f).symm
    exact (Submodule.le_topologicalClosure _ ) this
  have hClosed :
      IsClosed
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := (volume : Measure E)) (E := E) :
          Set (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E))) := by
    simpa using!
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isClosed_h1 (μ := (volume : Measure E)) (E := E))
  have hx_closure_h1 :
      T x.1 ∈
        closure
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := (volume : Measure E)) (E := E) :
            Set (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E))) :=
    (closure_mono hImage) hTmem
  have :
      T x.1 ∈
        (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := (volume : Measure E)) (E := E) :
          Set (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E))) := by
    simpa [hClosed.closure_eq] using! hx_closure_h1
  simpa [T] using! this

lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget_fst_mem_extendByZero_range (i : d.ι)
    (y :
      FiniteChartData.h1Target (d := d) (I := I)
        (μ)) :
    (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) y).1 ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
              (s := FiniteChartData.rhoSupportImage (d := d) (I := I) i)
              (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap) := by
  classical
  let μM :=
    μ
  let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  let u : (E →₂[μchart] ℝ) := (y i).1
  have hfst :
      (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) y).1 =
        vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ) u := by
    simp [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget, vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget, u, ContinuousLinearMap.proj_apply]
  -- Exhibit the restricted `L²` witness used by `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage`.
  let w : E →₂[(volume : Measure E).restrict K] ℝ :=
    (l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ))
      (MeasureTheory.Lp.changeMeasureL
          (μ := μchart) (ν := μchart.restrict K) (E := ℝ) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
          (by simpa using! (one_ne_top : (1 : ℝ≥0∞) ≠ ∞)) (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_restrict_le_one_smul (μ := μchart) (s := K))
          (by simpa using! (ENNReal.coe_ne_top (2 : ℕ))) u)
  have hmem :
      vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ) u ∈
        LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap) := by
    refine ⟨w, ?_⟩
    -- Expand the construction and discharge the remaining proof-term mismatch using
    -- `changeMeasureL_congr`.
    simp [w, vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage]
  simpa [hfst, u] using! hmem

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1 (i : d.ι) :
    let μM :=
      μ
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := (volume : Measure E)) (E := E)) := by
  classical
  intro μM
  let T :
      ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
        (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) :=
    (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)).comp
      (Submodule.subtypeL (FiniteChartData.h1 (d := d) (I := I) (μ := μM)))
  refine
    T.codRestrict
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1 (μ := (volume : Measure E)) (E := E)) ?_
  intro x
  -- Use the closure lemma on `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget` and rewrite through `T`.
  simpa [T] using! (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget_mem_euclidean_h1 (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) x)

noncomputable def vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1On (i : d.ι) :
    let μM :=
      μ
    let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
    ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ]
      ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On (E := E) K
          (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)) := by
  classical
  intro μM K
  let T := vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1 (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
  -- Codomain-restrict using the defining `h1On` condition.
  refine
    T.codRestrict
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On (E := E) K
        (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)) ?_
  intro x
  -- Unfold `h1On` membership: it is a `comap` condition on `h1ToL2`.
  dsimp [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On]
  -- `h1ToL2` is the first projection, so it suffices to show the scalar component lies in the extend-by-zero range.
  change
      ((RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2
              (μ := (volume : Measure E)) (E := E)).toLinearMap (T x)) ∈
        LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).toLinearMap)
  -- Compute `h1ToL2 (T x)` and apply the range lemma for `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget`.
  have :
      ((RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2
              (μ := (volume : Measure E)) (E := E)).toLinearMap (T x)) =
        (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM)).1 := by
    -- `T` is the codomain-restricted version of `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget ∘ subtypeL`, and `h1ToL2` is `fst`.
    simp [T, vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2]
  -- Rewrite and apply the range lemma.
  simpa [this, K] using!
    (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget_fst_mem_extendByZero_range (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
      (y := (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM)))

 lemma vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol_h1ToChartL2Range_coe (i : d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := d) (I := I)
            (μ :=
              μ))) :
    let μM :=
      μ
    ↑((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ))
        ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x)) =
      ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM))).1 := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
  -- Abbreviations for the relevant `extendByZero` maps.
  let eChart :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
      (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)
  let eVol :=
    MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
      (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)
  -- The chartwise `L²` component.
  let u : (E →₂[μchart] ℝ) := (FiniteChartData.h1ToChartL2 (d := d) (I := I) (μ := μM) i) x
  -- `h1ToChartL2Range` is a codomain restriction of `h1ToChartL2`, so its underlying value is `u`.
  have hz_coe :
      ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x : (E →₂[μchart] ℝ)) = u := by
    -- `simp` can unfold the codomain restriction, but we also unfold `μM` so both sides match.
    simp [h1ToChartL2Range, u, μM]
  -- Identify the preimage in the restricted `L²` space corresponding to `u` under `extendByZero`.
  let uK : (E →₂[μchart.restrict K] ℝ) :=
    (LinearIsometry.equivRange eChart).symm ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x)
  have heChart_uK : (eChart uK : (E →₂[μchart] ℝ)) = u := by
    -- Use `apply_symm_apply` in the range equivalence.
    have :
        (LinearIsometry.equivRange eChart) uK =
          (h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x := by
      simpa [uK] using!
        (LinearIsometry.equivRange eChart).apply_symm_apply
          ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x)
    -- Coerce to `L²(μchart)` and simplify.
    have := congrArg Subtype.val this
    simpa [eChart] using! this
  -- The `changeMeasureL` used in `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage` from `μchart` to `μchart.restrict K`.
  let cm :
      (E →₂[μchart] ℝ) →L[ℝ] (E →₂[μchart.restrict K] ℝ) :=
    MeasureTheory.Lp.changeMeasureL
      (μ := μchart) (ν := μchart.restrict K) (E := ℝ) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
      (by simpa using! (one_ne_top : (1 : ℝ≥0∞) ≠ ∞)) (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_restrict_le_one_smul (μ := μchart) (s := K))
      (by simpa using! (ENNReal.coe_ne_top (2 : ℕ)))
  -- `uK` is the same as `changeMeasureL` applied to `u`, since `u` is supported in `K`.
  have huK_eq : uK = cm u := by
    -- Show `uK =ᵐ[μchart.restrict K] u` (by restricting the `extendByZero` AE equality), then compare
    -- to `cm u =ᵐ[μchart.restrict K] u`.
    have hu_indicator :
        (u : E → ℝ) =ᵐ[μchart] K.indicator fun x => uK x := by
      -- `extendByZero` is `indicator` a.e.
      have hAE :
          ((eChart uK : (E →₂[μchart] ℝ)) : E → ℝ) =ᵐ[μchart]
            K.indicator fun x => uK x := by
        simpa [eChart] using!
          (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
            (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i) uK)
      -- Rewrite `eChart uK` as `u`.
      have hu_eq : ((eChart uK : (E →₂[μchart] ℝ)) : E → ℝ) =ᵐ[μchart] u := by
        -- `heChart_uK` is equality in `L²`, hence a.e. equality.
        simpa [heChart_uK] using! (MeasureTheory.Lp.coeFn_ae_eq (μ := μchart) (f := (eChart uK)) (g := u) heChart_uK)
      -- Combine.
      exact hu_eq.symm.trans hAE
    have hu_on : ∀ᵐ x : E ∂μchart, x ∈ K → u x = uK x := by
      filter_upwards [hu_indicator] with x hx hxK
      have : K.indicator (fun y => uK y) x = uK x := by simp [Set.indicator_of_mem, hxK]
      -- On `K`, the indicator equals the function itself.
      simpa [this] using! hx
    have hu_restrict : (u : E → ℝ) =ᵐ[μchart.restrict K] fun x => uK x :=
      (ae_restrict_iff' (μ := μchart) (s := K)
        (rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i)).2 hu_on
    have hcm_ae :
        (cm u : E → ℝ) =ᵐ[μchart.restrict K] u :=
      MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq (μ := μchart) (ν := μchart.restrict K) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
        (by simpa using! (one_ne_top : (1 : ℝ≥0∞) ≠ ∞))
        (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_restrict_le_one_smul (μ := μchart) (s := K))
        (by simpa using! (ENNReal.coe_ne_top (2 : ℕ))) u
    refine MeasureTheory.Lp.ext (μ := μchart.restrict K) (E := ℝ) (p := (2 : ℝ≥0∞)) ?_
    -- Compare almost everywhere representatives on the restricted measure.
    have : (uK : E → ℝ) =ᵐ[μchart.restrict K] (cm u : E → ℝ) :=
      hu_restrict.symm.trans hcm_ae.symm
    exact this
  -- Compute both sides as `extendByZero` of the same restricted-volume witness.
  -- Left side: unfold the range equivalence and use `huK_eq` to identify the restricted witness.
  have hL :
      (↑((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ))
            ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x)) : (E →₂[(volume : Measure E)] ℝ)) =
        eVol
          ((l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)) uK) := by
    -- Unfold the definition of the `extendByZero`-range equivalence.
    -- The resulting expression is exactly `extendByZero` after `l2EquivVolumeOnRhoSupportImage'` applied to the
    -- canonical `equivRange` preimage `uK`.
    simp [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol, l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage',
      MeasureTheory.Lp.extendByZeroRangeEquivOfRestrictChangeMeasureEquiv, eChart, eVol, uK,
      l2EquivVolumeOnRhoSupportImage']
    all_goals rfl
  -- Right side: `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget` is `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget ∘ proj`, and the scalar component is
  -- exactly `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage` applied to the chartwise `L²` value `u`.
  have hR :
      ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM))).1 =
        eVol
          ((l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)) (cm u)) := by
    -- Reduce to the definition of `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage` applied to the chartwise scalar component.
    have hu' : ((x.1 : FiniteChartData.h1Target (d := d) (I := I) μM) i).1 = u := by
      -- `u` is exactly the `i`-th scalar coordinate of `x`.
      simp [u, FiniteChartData.h1ToChartL2, FiniteChartData.h1ToChart, ContinuousLinearMap.proj_apply]
    -- Expand `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget` and rewrite the scalar component using `hu'`.
    -- Then unfold `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage` and align the `changeMeasureL` proof terms via
    -- `changeMeasureL_congr`.
    simp [vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget, vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget, vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_chartTargetToVolumeTarget, hu', vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_l2ChartToVolumeOnRhoSupportImage, cm]
    -- Discharge the remaining definitional mismatch in `changeMeasureL`.
    refine congrArg
      eVol ?_
    refine congrArg (l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)) ?_
    -- `changeMeasureL` is independent of proof arguments.
    exact
      congrArg (fun T => T u)
        (MeasureTheory.Lp.changeMeasureL_congr (μ := μchart) (ν := μchart.restrict K) (E := ℝ)
          (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
          (hc₁ := (by simpa using! (one_ne_top : (1 : ℝ≥0∞) ≠ ∞)))
          (hc₂ := _)
          (hν₁ := vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_restrict_le_one_smul (μ := μchart) (s := K))
          (hν₂ := _)
          (hp₁ := (by simpa using! (ENNReal.coe_ne_top (2 : ℕ))))
          (hp₂ := _))
  -- Combine: align the restricted witness and conclude.
  calc
    ↑((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ))
          ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x)) =
        eVol
          ((l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)) uK) := by
          simpa [hL]
    _ =
        eVol
          ((l2EquivVolumeOnRhoSupportImage' (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)) (cm u)) := by
          simpa [huK_eq]
    _ = ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)
          (x.1 : FiniteChartData.h1Target (d := d) (I := I) μM))).1 := by
          exact hR.symm

/-!
### Compactness: chartwise `H¹ → L²` contribution

We now apply Euclidean Rellich compactness on Lebesgue `volume` (supported in `K`) and transport
compactness back to the chart measure using! the `extendByZero`-range equivalence.
-/

theorem isCompactOperator_h1ToChartL2Range (i : d.ι) :
    let μM :=
      μ
    IsCompactOperator
      (h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i) :
        ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →L[ℝ] _) := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (d := d) (μ := μ) (I := I) i
  have hK : IsCompact K := FiniteChartData.isCompact_rhoSupportImage (d := d) (I := I) i
  -- Euclidean Rellich compactness into the `extendByZero` range for `volume`.
  let volRange :
      Submodule ℝ (E →₂[(volume : Measure E)] ℝ) :=
    LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
            (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)
  have hcompVol :
      IsCompactOperator
        (Set.codRestrict
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2 (E := E) K hKm)
          volRange
          (by
            intro x
            have hxmem :
                (x : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                    (μ := (volume : Measure E)) (E := E))) ∈
                  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On (E := E) K hKm :=
              x.property
            dsimp [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On] at hxmem
            -- `h1OnToL2` is `h1ToL2` on the underlying `H¹` element.
            -- Avoid `simp` using `x.property` (which can rewrite the goal to `True`).
            change
                ((RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2
                    (μ := (volume : Measure E)) (E := E)).toLinearMap
                      (x : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                        (μ := (volume : Measure E)) (E := E)))) ∈
                  volRange
            -- `hxmem` is exactly the unfolded membership.
            exact hxmem)) := by
    -- The theorem in the Euclidean file is stated with `LinearMap.range` directly; this `volRange`
    -- is definitional (unification fills the proof term).
    simpa [volRange] using!
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2_codRestrict_range_extendByZero
        (E := E) (K := K) hK hKm)
  -- Precompose by the manifold-to-Euclidean supported `H¹` map.
  have hcompVol' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) =>
        (Set.codRestrict
          (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2 (E := E) K hKm)
          volRange
          (by
            intro y
            have hymem :
                (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                    (μ := (volume : Measure E)) (E := E))) ∈
                  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On (E := E) K hKm :=
              y.property
            dsimp [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On] at hymem
            change
                ((RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2
                    (μ := (volume : Measure E)) (E := E)).toLinearMap
                      (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                        (μ := (volume : Measure E)) (E := E)))) ∈
                  volRange
            exact hymem))
          ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1On (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)) x) :=
    hcompVol.comp_clm (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1On (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i))
  -- Transport the compactness statement back to the chart measure using the range equivalence.
  have hcompVol'' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) =>
        (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)).symm
          ((Set.codRestrict
                (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2 (E := E) K hKm)
                volRange
                (by
                  intro y
                  have hymem :
                      (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                          (μ := (volume : Measure E)) (E := E))) ∈
                        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On (E := E) K hKm :=
                    y.property
                  dsimp [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On] at hymem
                  change
                      ((RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2
                          (μ := (volume : Measure E)) (E := E)).toLinearMap
                            (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                              (μ := (volume : Measure E)) (E := E)))) ∈
                        volRange
                  exact hymem)
                ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1On (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)) x))) :=
    (hcompVol'.clm_comp (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)).symm.toContinuousLinearMap)
  -- Finally, identify this transported compact operator with the actual codomain-restricted chart map.
  -- This is the only nontrivial point: it asserts that `h1ToChartL2Range` is obtained by conjugating
  -- the volume-side supported `H¹` inclusion.
  -- We prove it by applying `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol` and simplifying.
  have hEq :
      (h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i) :
          ↥(FiniteChartData.h1 (d := d) (I := I) (μ := μM)) →
            ↥(LinearMap.range
              ((MeasureTheory.Lp.extendByZeroₗᵢ
                    (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))) =
        fun x =>
          ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)).symm
              (Set.codRestrict
                (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2 (E := E) K hKm)
                volRange
                (by
                  intro y
                  have hymem :
                      (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                          (μ := (volume : Measure E)) (E := E))) ∈
                        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On (E := E) K hKm :=
                    y.property
                  dsimp [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On] at hymem
                  change
                      ((RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2
                          (μ := (volume : Measure E)) (E := E)).toLinearMap
                            (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                              (μ := (volume : Measure E)) (E := E)))) ∈
                        volRange
                  exact hymem)
                ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1On (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)) x))) := by
    -- Apply the forward equivalence and simplify via `h1ToChartL2RangeVol`.
    funext x
    -- It suffices to prove equality after applying the forward equivalence.
    -- (This avoids unpacking the `symm` explicitly.)
    have :
        (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ))
            ((h1ToChartL2Range (d := d) (μ := μ) (I := I) (i := i)) x) =
          (Set.codRestrict
              (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2 (E := E) K hKm)
              volRange
              (by
                intro y
                have hymem :
                    (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                        (μ := (volume : Measure E)) (E := E))) ∈
                      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On (E := E) K hKm :=
                  y.property
                dsimp [RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On] at hymem
                change
                    ((RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2
                        (μ := (volume : Measure E)) (E := E)).toLinearMap
                          (y : ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1
                            (μ := (volume : Measure E)) (E := E)))) ∈
                      volRange
                exact hymem)
              ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1On (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i)) x)) := by
      -- The left-hand side is the definition of `h1ToChartL2RangeVol`.
      -- Prove equality by unfolding both sides and reducing to the explicit `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget`
      -- computation of the scalar component.
      -- (The heavy lifting is encapsulated in the `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_h1ToChartVolH1On` construction.)
      -- We use `Subtype.ext` and compute the underlying `L²(volume)` value.
      ext1
      -- Identify the transported chartwise `L²` component with the `vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_projToVolumeTarget` scalar output.
      simpa using! (vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol_h1ToChartL2Range_coe (d := d) (μ := μ) (hcomp := hcomp) (I := I) (E := E) (i := i) x)
    -- Now cancel the forward equivalence.
    -- (`simp` uses `ContinuousLinearEquiv.apply_symm_apply`.)
    simpa using! congrArg ((vendorGeometryManifoldSobolevRellichKondrachovDensityChartwise_eL2RangeChartVol (d := d) (μ := μ) (hcomp := hcomp) (I := I) (i := i) (F := ℝ)).symm) this
  -- Rewrite the goal using the identification and apply the established compactness.
  simpa [hEq] using! hcompVol''


end ChartwiseCompactness



end Density
end
end Sobolev
end Manifold
end Geometry
end RellichKondrachov
