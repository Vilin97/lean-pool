/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Transport
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
import LeanPool.RellichKondrachov.Geometry.Manifold.Riemannian.VolumeMeasure.Finiteness

/-!
# `RellichKondrachov.Geometry.Manifold.Sobolev.RellichKondrachovRiemannian.Chartwise`

Chartwise compactness discharge for the manifold Rellich–Kondrachov theorem on compact Riemannian
manifolds.

This module sets up the `L²`-range codomain restrictions and applies Euclidean Rellich compactness
(on Lebesgue `volume`) after transporting along the `L²` equivalences from
`RellichKondrachovRiemannian.Transport`.
-/

public section

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Sobolev

open Set Filter Topology
open scoped BigOperators ENNReal MeasureTheory _root_.Manifold NNReal
open MeasureTheory
open _root_.Manifold _root_.Bundle

local notation "n∞" => (⊤ : WithTop ℕ∞)

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [I.Boundaryless]
  [T3Space M]
  [T2Space M] [CompactSpace M]

/-- Borel σ-algebra on the manifold `M`. -/
local instance instMeasurableSpaceMChartwise :
    MeasurableSpace M := borel M
local instance instBorelSpaceMChartwise : BorelSpace M := ⟨rfl⟩

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEChartwise :
    MeasurableSpace E := borel E
local instance instBorelSpaceEChartwise : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceChartwise :
    OpensMeasurableSpace E := by
  infer_instance

-- On compact manifolds, the Riemannian volume measure is finite.
local instance instIsFiniteMeasureriemannianVolumeMeasureChartwise :
    IsFiniteMeasure
        (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure
          (I := I) (M := M)) :=
  RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure_isFiniteMeasure
    (I := I) (M := M)

namespace RiemannianFiniteChartData

variable (dR : RiemannianFiniteChartData (H := H) (M := M) I)

/-!
## Chartwise compactness discharge (Riemannian volume)

This section uses Euclidean Rellich compactness on Lebesgue `volume` and transports it to the
chart pushforward measures via the `L²` range equivalences developed above.
-/

section ChartwiseCompactness

open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

variable (i : dR.d.ι)

/-- Embed the local square-integrable range using the chart volume measure. -/
noncomputable def eL2RangeChartVol (i : dR.d.ι)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := μchart) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) ≃L[ℝ]
        ↥(LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) :=
  l2ExtendByZeroRangeEquivVolumeOnRhoSupportImage' (dR := dR) (I := I) (i := i) (F := F)

/-!
### Range-codomain restricted chart maps

We will work with codomain restrictions into the closed `extendByZero` range to make the transport
between `μchart` and `volume` explicit and purely `L²`-level.
-/

omit [T2Space M] in
/-- The chartwise `H¹ → L²` projection with codomain restricted to the Euclidean `H¹` range,
for the chart pushforward of the Riemannian volume measure. -/
noncomputable def h1ToChartL2Range :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  refine
    (FiniteChartData.h1ToChartL2 (d := dR.d) (I := I) (μ := μM) i).codRestrict
      (LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) ?_
  intro x
  simpa using (h1ToChartL2_mem_extendByZero_range (dR := dR) (I := I) i x)

omit [T2Space M] in
private noncomputable def h1ToChartL2GradRange :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  refine
    (FiniteChartData.h1ToChartL2Grad (d := dR.d) (I := I) (μ := μM) i).codRestrict
      (LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := μchart) (E := E) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) ?_
  intro x
  simpa using (h1ToChartL2Grad_mem_extendByZero_range (dR := dR) (I := I) i x)

/-!
### Volume-side supported `H¹` map and compactness

We now transport the chartwise `H¹` element to Lebesgue `volume` on `K`, apply Euclidean Rellich
compactness there, and transport the compactness statement back to the chart measure.
-/

omit [T2Space M] in
/-- The chartwise `H¹ → L²` projection into the Euclidean `H¹` range, transported to Lebesgue
`volume` on the fixed compact support. -/
noncomputable def h1ToChartL2RangeVol :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let _μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  have e :
      ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) ≃L[ℝ]
          ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) := by
    simpa using (eL2RangeChartVol (dR := dR) (I := I) (i := i) (F := ℝ))
  exact e.toContinuousLinearMap.comp (h1ToChartL2Range (dR := dR) (I := I) (i := i))

omit [T2Space M] in
private noncomputable def h1ToChartL2GradRangeVol :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let _μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := E) (p := (2 : ℝ≥0∞))
              (s := K) (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) := by
  classical
  intro μM μchart K
  have e :
      ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := μchart) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) ≃L[ℝ]
          ↥(LinearMap.range
            ((MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
                  (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)) := by
    simpa using (eL2RangeChartVol (dR := dR) (I := I) (i := i) (F := E))
  exact e.toContinuousLinearMap.comp (h1ToChartL2GradRange (dR := dR) (I := I) (i := i))

omit [T2Space M] in
private noncomputable def h1ToChartVolH1Target :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let _μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) := by
  classical
  intro μM μchart K
  let f :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ] ↥(E →₂[(volume : Measure E)] ℝ) :=
    ((LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)).subtypeL).comp
      (h1ToChartL2RangeVol (dR := dR) (I := I) (i := i))
  let g :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ] ↥(E →₂[(volume : Measure E)] E) :=
    ((LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := E) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)).subtypeL).comp
      (h1ToChartL2GradRangeVol (dR := dR) (I := I) (i := i))
  exact f.prod g

/-!
### A volume-side chart target map defined on the ambient `H¹` target

For the closure argument showing membership in Euclidean `H¹(volume)`, it is convenient to have a
continuous linear map defined on the *ambient* chart `H¹` target
`L²(μchart) × L²(μchart;E)`, rather than only on the `extendByZero` range.

We implement this by restricting to `K`, applying the restricted `L²` change-of-measure equivalence,
and extending by zero back to `L²(volume)`.
-/

private lemma restrict_le_one_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    μ.restrict s ≤ (1 : ℝ≥0∞) • μ := by
  simpa [one_smul] using (Measure.restrict_le_self (μ := μ) (s := s))

private noncomputable def l2ChartToVolumeOnRhoSupportImage (i : dR.d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(E →₂[μchart] F) →L[ℝ] ↥(E →₂[(volume : Measure E)] F) := by
  classical
  intro μM μchart K
  -- Restrict `L²(μchart)` to `L²(μchart.restrict K)` via the identity map (since `μchart.restrict K
  -- ≤ μchart`).
  let r :
      (E →₂[μchart] F) →L[ℝ] (E →₂[μchart.restrict K] F) :=
    MeasureTheory.Lp.changeMeasureL
      (μ := μchart) (ν := μchart.restrict K) (E := F) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
      (by simp) (restrict_le_one_smul (μ := μchart) (s := K))
      (by simp)
  -- Change measure on the restricted spaces.
  let e : (E →₂[μchart.restrict K] F) ≃L[ℝ] (E →₂[(volume : Measure E).restrict K] F) :=
    l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) (i := i) (F := F)
  -- Extend back to `L²(volume)` by zero outside `K`.
  let ez :
      (E →₂[(volume : Measure E).restrict K] F) →ₗᵢ[ℝ] (E →₂[(volume : Measure E)] F) :=
    MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure E)) (E := F) (p := (2 : ℝ≥0∞)) (s := K)
      (rhoSupportImage_measurable (dR := dR) (I := I) i)
  exact (ez.toContinuousLinearMap).comp (e.toContinuousLinearMap.comp r)

private noncomputable def chartTargetToVolumeTarget (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let _μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i) →L[ℝ]
      (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) := by
  classical
  intro μM μchart K
  -- Map each component `L²(μchart)` / `L²(μchart;E)` into `L²(volume)` / `L²(volume;E)` using
  -- `l2ChartToVolumeOnRhoSupportImage`.
  let f :
      (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i) →L[ℝ] ↥(E →₂[(volume : Measure E)] ℝ) :=
    (l2ChartToVolumeOnRhoSupportImage (dR := dR) (I := I) (i := i) (F := ℝ)).comp
      (ContinuousLinearMap.fst ℝ (↥(E →₂[μchart] ℝ)) (↥(E →₂[μchart] E)))
  let g :
      (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i) →L[ℝ] ↥(E →₂[(volume : Measure E)] E) :=
    (l2ChartToVolumeOnRhoSupportImage (dR := dR) (I := I) (i := i) (F := E)).comp
      (ContinuousLinearMap.snd ℝ (↥(E →₂[μchart] ℝ)) (↥(E →₂[μchart] E)))
  exact f.prod g

private noncomputable def projToVolumeTarget (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let _μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    (FiniteChartData.h1Target (d := dR.d) (I := I) μM) →L[ℝ]
      (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) := by
  classical
  intro μM μchart K
  let proj :
      (FiniteChartData.h1Target (d := dR.d) (I := I) μM) →L[ℝ]
        (FiniteChartData.h1TargetE (d := dR.d) (I := I) μM i) :=
    ContinuousLinearMap.proj (R := ℝ) i
  exact (chartTargetToVolumeTarget (dR := dR) (I := I) (i := i)).comp proj

/-!
### Graph compatibility (C¹c generators)

To use Euclidean Rellich compactness for `volume`, we need to know that the volume-side map
`chartTargetToVolumeTarget` respects the Euclidean graph generators induced by
`FiniteChartData.localize`.
-/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma support_subset_of_tsupport_subset {F : Type*} [Zero F]
    (g : E → F) {K : Set E} (h : tsupport g ⊆ K) : Function.support g ⊆ K := by
  -- `tsupport g = closure (support g)` by definition.
  have hsupp : Function.support g ⊆ tsupport g := by
    simpa [tsupport] using (subset_closure : Function.support g ⊆ closure (Function.support g))
  exact hsupp.trans h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma indicator_ae_eq_of_ae_eq_restrict
    {F : Type*} [MeasurableSpace F] [Zero F] [MeasurableEq F]
    {μ : Measure E} {K : Set E} {f g : E → F}
    (hf : AEMeasurable f (μ.restrict K)) (hg : AEMeasurable g (μ.restrict K))
    (hfg : f =ᵐ[μ.restrict K] g) (hsupp : Function.support g ⊆ K) :
    K.indicator f =ᵐ[μ] g := by
  have hEq : ∀ᵐ x ∂μ.restrict K, f x = g x := hfg
  have h0 : (μ.restrict K) {x | f x ≠ g x} = 0 := by
    -- Convert AE equality to a measure-zero inequality set.
    have h0' : (μ.restrict K) {x | ¬f x = g x} = 0 := (MeasureTheory.ae_iff).1 hEq
    simpa [ne_eq] using h0'
  have hnullEq : NullMeasurableSet {x | f x = g x} (μ.restrict K) :=
    nullMeasurableSet_eq_fun (μ := μ.restrict K) hf hg
  have hnullNe : NullMeasurableSet {x | f x ≠ g x} (μ.restrict K) := by
    -- Complement of the equality set.
    simpa [Set.compl_ofPred, ne_eq] using hnullEq.compl
  have hK0 : μ ({x | f x ≠ g x} ∩ K) = 0 := by
    -- Use the restriction formula on a null-measurable set.
    have hEqRestr :
        (μ.restrict K) {x | f x ≠ g x} = μ ({x | f x ≠ g x} ∩ K) :=
      Measure.restrict_apply₀ (μ := μ) (s := K) (t := {x | f x ≠ g x}) hnullNe
    simpa [hEqRestr] using h0
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
        simpa [Function.support, Set.mem_ofPred_eq] using hxnsupp
      have hfx0 : K.indicator f x = 0 := by simp [hxK]
      exact hx (by simp [hfx0, hg0])
    have hne : f x ≠ g x := by
      -- On `K`, the indicator is the identity.
      simpa [Set.indicator_of_mem hxK] using hx
    exact ⟨hne, hxK⟩
  have hbad0 : μ {x | K.indicator f x ≠ g x} = 0 :=
    measure_mono_null hsubset hK0
  have : ∀ᵐ x ∂μ, K.indicator f x = g x := by
    -- `ae_iff` expects a negated predicate set; rewrite it to the inequality set.
    refine (MeasureTheory.ae_iff).2 ?_
    simpa [ne_eq] using hbad0
  exact this

omit [T2Space M] [I.Boundaryless] in
private lemma l2EquivVolumeOnRhoSupportImage'_coeFn_ae_eq (i : dR.d.ι) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →₂[(FiniteChartData.chartMeasure (d := dR.d) (I := I)
          (Riemannian.riemannianVolumeMeasure (I := I) (M := M)) i).restrict
        (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)] F) :
    ((l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) (i := i) (F := F)) f : E → F) =ᵐ[
        (volume : Measure E).restrict (FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)
      ] f := by
  classical
  let μM :=
    RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  let cChartVol : ℝ≥0∞ :=
    (((dR.C i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)) *
          ((μH[(Module.finrank ℝ E : ℝ)] (Metric.closedBall (0 : E) 1)) /
            ((volume : Measure E) (Metric.closedBall (0 : E) 1))))
  let cVolChart : ℝ≥0∞ :=
    ((((volume : Measure E) (Metric.closedBall (0 : E) 1)) /
              ((μH[(Module.finrank ℝ E : ℝ)] : Measure E) (Metric.closedBall (0 : E) 1))) *
            ((dR.Cfwd i : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ)))
  have hμ_le : μchart.restrict K ≤ cChartVol • (volume : Measure E).restrict K := by
    simpa [μM, μchart, K, cChartVol] using
      chartMeasure_restrict_rhoSupportImage_le_volume (dR := dR) (I := I) i
  have hvol_le : (volume : Measure E).restrict K ≤ cVolChart • μchart.restrict K := by
    simpa [μM, μchart, K, cVolChart] using
      volume_restrict_rhoSupportImage_le_chartMeasure (dR := dR) (I := I) i
  have hcChartVol : cChartVol ≠ ∞ :=
    RiemannianFiniteChartData.chartMeasure_volume_constant_ne_top (dR := dR) (I := I) (E := E) i
  have hcVolChart : cVolChart ≠ ∞ :=
    RiemannianFiniteChartData.volume_chartMeasure_constant_ne_top (dR := dR) (I := I) (E := E) i
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by simp
  -- Unfold and apply the general `changeMeasureEquiv` coherence lemma.
  simpa [l2EquivVolumeOnRhoSupportImage', μM, μchart, K, cVolChart, cChartVol] using
    (MeasureTheory.Lp.changeMeasureEquiv_coeFn_ae_eq
      (μ := μchart.restrict K) (ν := (volume : Measure E).restrict K) (E := F) (p := (2 : ℝ≥0∞))
      (c₁ := cVolChart) (c₂ := cChartVol) hcVolChart hcChartVol hvol_le hμ_le hp f)

omit [T2Space M] [I.Boundaryless] in
private lemma l2ChartToVolumeOnRhoSupportImage_eq_of_support_subset (i : dR.d.ι)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) :
    let μM := Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ∀ (x : E →₂[μchart] F) (y : E →₂[(volume : Measure E)] F),
      (x : E → F) =ᵐ[μchart] g → (y : E → F) =ᵐ[(volume : Measure E)] g →
      Function.support g ⊆ K →
      l2ChartToVolumeOnRhoSupportImage (dR := dR) (I := I) i F x = y := by
  classical
  intro μM μchart K x y hx hy hsupp
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  let r : (E →₂[μchart] F) →L[ℝ] (E →₂[μchart.restrict K] F) :=
    Lp.changeMeasureL (μ := μchart) (ν := μchart.restrict K) (E := F)
      (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (restrict_le_one_smul μchart K) (by simp)
  let e := l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) (i := i) (F := F)
  let ez := Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := F)
    (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hr : (r x : E → F) =ᵐ[μchart.restrict K] g :=
    (Lp.changeMeasureL_coeFn_ae_eq (μ := μchart) (ν := μchart.restrict K) (E := F)
      (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
      (restrict_le_one_smul μchart K) (by simp) x).trans (ae_restrict_of_ae hx)
  have habs : (volume : Measure E).restrict K ≪ μchart.restrict K :=
    Measure.absolutelyContinuous_of_le_smul
      (volume_restrict_rhoSupportImage_le_chartMeasure (dR := dR) (I := I) i)
  have he : (e (r x) : E → F) =ᵐ[(volume : Measure E).restrict K] g :=
    (l2EquivVolumeOnRhoSupportImage'_coeFn_ae_eq (dR := dR) (I := I) i F (r x)).trans
      (habs.ae_le hr)
  have hInd : K.indicator (fun z => (e (r x) : E → F) z) =ᵐ[(volume : Measure E)] g := by
    filter_upwards [ae_imp_of_ae_restrict he] with z hz
    by_cases hzK : z ∈ K
    · simpa only [Set.indicator_of_mem hzK] using hz hzK
    · rw [Set.indicator_of_notMem hzK]
      exact (Function.notMem_support.mp (fun hzSupp => hzK (hsupp hzSupp))).symm
  have hez : (ez (e (r x)) : E → F) =ᵐ[(volume : Measure E)]
      K.indicator fun z => (e (r x) : E → F) z :=
    Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
      (s := K) (hs := hKm) (f := e (r x))
  exact Lp.ext (hez.trans (hInd.trans hy.symm))

omit [T2Space M] [I.Boundaryless] in
private lemma l2ChartToVolumeOnRhoSupportImage_toL2_of_tsupport_subset (i : dR.d.ι)
    (g : ↥(C1c (E := E))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    tsupport g.1 ⊆ K →
      l2ChartToVolumeOnRhoSupportImage (dR := dR) (I := I) (i := i) (F := ℝ)
          (toL2 (μ := μchart) (E := E) g) =
        toL2 (μ := (volume : Measure E)) (E := E) g := by
  intro μM μchart K htsupp
  exact l2ChartToVolumeOnRhoSupportImage_eq_of_support_subset (dR := dR) (I := I) i g.1
    _ _ (memLp_of_mem_C1c (μ := μchart) g.2).coeFn_toLp
    (memLp_of_mem_C1c (μ := (volume : Measure E)) g.2).coeFn_toLp
    (support_subset_of_tsupport_subset g.1 htsupp)

omit [T2Space M] [I.Boundaryless] in
private lemma l2ChartToVolumeOnRhoSupportImage_toL2Grad_of_tsupport_subset (i : dR.d.ι)
    (g : ↥(C1c (E := E))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    tsupport g.1 ⊆ K →
      l2ChartToVolumeOnRhoSupportImage (dR := dR) (I := I) (i := i) (F := E)
          (toL2Grad (μ := μchart) (E := E) g) =
        toL2Grad (μ := (volume : Measure E)) (E := E) g := by
  intro μM μchart K htsupp
  exact l2ChartToVolumeOnRhoSupportImage_eq_of_support_subset (dR := dR) (I := I) i
    (grad (E := E) g.1) _ _ (memLp_grad_of_mem_C1c (μ := μchart) g.2).coeFn_toLp
    (memLp_grad_of_mem_C1c (μ := (volume : Measure E)) g.2).coeFn_toLp
    (support_subset_of_tsupport_subset _ ((tsupport_grad_subset (f := g.1)).trans htsupp))

omit [T2Space M] in
private lemma chartTargetToVolumeTarget_h1GraphChart (i : dR.d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    chartTargetToVolumeTarget (dR := dR) (I := I) (i := i)
        (FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f) =
      (graph (μ := (volume : Measure E)) (E := E))
        ⟨FiniteChartData.localize (d := dR.d) (I := I) f.1 i,
          FiniteChartData.localize_mem_C1c (d := dR.d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  let g :
      ↥(C1c (E := E)) :=
    ⟨FiniteChartData.localize (d := dR.d) (I := I) f.1 i,
      FiniteChartData.localize_mem_C1c (d := dR.d) (I := I) (f := f.1) f.2 i⟩
  have htsupp : tsupport g.1 ⊆ K := by
    simpa [g, K] using
      (FiniteChartData.tsupport_localize_subset_rhoSupportImage (d := dR.d) (I := I) (f := f.1) i)
  -- Compare componentwise, keeping goals in `L²` (avoid `ext` on `Lp`, which produces AE goals).
  refine Prod.ext ?_ ?_
  · -- Scalar component.
    have hfst :
        ((FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f).1) =
          toL2 (μ := μchart) (E := E) g := by
      simpa [μchart, μM, K, g] using
        (FiniteChartData.h1GraphChart_fst (d := dR.d) (I := I) (μ := μM) i f)
    -- Reduce to the `L²` transport lemma.
    simpa [chartTargetToVolumeTarget, g,
      graph,
      toL2Linear,
      toL2GradLinear,
      hfst] using
      (l2ChartToVolumeOnRhoSupportImage_toL2_of_tsupport_subset (dR := dR) (I := I) (i := i) g
        htsupp)
  · -- Gradient component.
    have hsnd :
        ((FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f).2) =
          toL2Grad (μ := μchart) (E := E) g := by
      simpa [μchart, μM, K, g] using
        (FiniteChartData.h1GraphChart_snd (d := dR.d) (I := I) (μ := μM) i f)
    simpa [chartTargetToVolumeTarget, g,
      graph,
      toL2Linear,
      toL2GradLinear,
      hsnd] using
      (l2ChartToVolumeOnRhoSupportImage_toL2Grad_of_tsupport_subset (dR := dR) (I := I) (i := i) g
        htsupp)

/-!
### Closure argument: chartwise volume image lies in Euclidean `H¹(volume)` and `h1On`

We use the graph compatibility lemma above to show that the volume-side projection map sends the
defining dense range of `FiniteChartData.h1` into the Euclidean graph range on `volume`, and thus
extends to a map `H¹(M) → H¹(volume)` (and further into `h1On K`).

This sets up the application of Euclidean Rellich compactness on `volume` in later steps.
-/

omit [T2Space M] in
private lemma projToVolumeTarget_h1Graph (i : dR.d.ι)
    (f : ↥(FiniteChartData.C1 (I := I) (E := E) (H := H) (M := M))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    projToVolumeTarget (dR := dR) (I := I) (i := i)
        (FiniteChartData.h1Graph (d := dR.d) (I := I) (μ := μM) f) =
      (graph (μ := (volume : Measure E)) (E := E))
        ⟨FiniteChartData.localize (d := dR.d) (I := I) f.1 i,
          FiniteChartData.localize_mem_C1c (d := dR.d) (I := I) (f := f.1) f.2 i⟩ := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  -- `projToVolumeTarget` is `chartTargetToVolumeTarget ∘ proj`, and `h1Graph` is `pi` of
  -- `h1GraphChart`.
  have hproj :
      (projToVolumeTarget (dR := dR) (I := I) (i := i)
            (FiniteChartData.h1Graph (d := dR.d) (I := I) (μ := μM) f)) =
        chartTargetToVolumeTarget (dR := dR) (I := I) (i := i)
          ((FiniteChartData.h1Graph (d := dR.d) (I := I) (μ := μM) f) i) := by
    simp [projToVolumeTarget, ContinuousLinearMap.proj_apply]
  -- Rewrite the `i`-th component of `h1Graph`.
  have hi :
      (FiniteChartData.h1Graph (d := dR.d) (I := I) (μ := μM) f) i =
        FiniteChartData.h1GraphChart (d := dR.d) (I := I) (μ := μM) i f := by
    simp [FiniteChartData.h1Graph]
  -- Conclude using graph compatibility on `h1GraphChart`.
  simpa [hproj, hi, μchart, K] using
    (chartTargetToVolumeTarget_h1GraphChart (dR := dR) (I := I) (i := i) f)

omit [T2Space M] in
private lemma projToVolumeTarget_mem_euclidean_h1 (i : dR.d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I)
            (μ :=
              RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                (M := M)))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let _μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
    let _K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    projToVolumeTarget (dR := dR) (I := I) (i := i) (x.1 : FiniteChartData.h1Target (d := dR.d) (I
      := I) μM) ∈
      (h1 (μ := (volume : Measure E)) (E := E) : Set _) := by
  intro μM μchart K
  let T := projToVolumeTarget (dR := dR) (I := I) i
  have hClosed := (isClosed_h1 (μ := (volume : Measure E)) (E := E)).preimage T.continuous
  refine closure_minimal ?_ hClosed x.2
  rintro _ ⟨f, rfl⟩
  apply Submodule.le_topologicalClosure
  exact ⟨_, (projToVolumeTarget_h1Graph (dR := dR) (I := I) i f).symm⟩

omit [T2Space M] [I.Boundaryless] in
private lemma projToVolumeTarget_fst_mem_extendByZero_range (i : dR.d.ι)
    (y :
      FiniteChartData.h1Target (d := dR.d) (I := I)
        (RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)))
          :
    (projToVolumeTarget (dR := dR) (I := I) (i := i) y).1 ∈
      LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
              (s := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i)
              (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap) := by
  classical
  let μM :=
    RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  let u : (E →₂[μchart] ℝ) := (y i).1
  have hfst :
      (projToVolumeTarget (dR := dR) (I := I) (i := i) y).1 =
        l2ChartToVolumeOnRhoSupportImage (dR := dR) (I := I) (i := i) (F := ℝ) u := by
    simp [projToVolumeTarget, chartTargetToVolumeTarget, u, ContinuousLinearMap.proj_apply]
  -- Exhibit the restricted `L²` witness used by `l2ChartToVolumeOnRhoSupportImage`.
  let w : E →₂[(volume : Measure E).restrict K] ℝ :=
    (l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) (i := i) (F := ℝ))
      (MeasureTheory.Lp.changeMeasureL
          (μ := μchart) (ν := μchart.restrict K) (E := ℝ) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞))
          (by simp) (restrict_le_one_smul (μ := μchart) (s :=
            K))
          (by simp) u)
  have hmem :
      l2ChartToVolumeOnRhoSupportImage (dR := dR) (I := I) (i := i) (F := ℝ) u ∈
        LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap) := by
    refine ⟨w, ?_⟩
    -- Expand the construction and discharge the remaining proof-term mismatch using
    -- `changeMeasureL_congr`.
    simp [w, l2ChartToVolumeOnRhoSupportImage]
  simpa [hfst, u] using hmem

omit [T2Space M] in
private noncomputable def h1ToChartVolH1 (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(h1 (μ := (volume : Measure E)) (E := E)) := by
  classical
  intro μM
  let T :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
        (↥(E →₂[(volume : Measure E)] ℝ) × ↥(E →₂[(volume : Measure E)] E)) :=
    (projToVolumeTarget (dR := dR) (I := I) (i := i)).comp
      (Submodule.subtypeL (FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)))
  refine
    T.codRestrict
      (h1 (μ := (volume : Measure E)) (E := E)) ?_
  intro x
  -- Use the closure lemma on `projToVolumeTarget` and rewrite through `T`.
  simpa [T] using (projToVolumeTarget_mem_euclidean_h1 (dR := dR) (I := I) (i := i) x)

omit [T2Space M] in
private noncomputable def h1ToChartVolH1On (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
    ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ]
      ↥(h1On (E := E) K
          (rhoSupportImage_measurable (dR := dR) (I := I) i)) := by
  classical
  intro μM K
  let T := h1ToChartVolH1 (dR := dR) (I := I) (i := i)
  -- Codomain-restrict using the defining `h1On` condition.
  refine
    T.codRestrict
      (h1On (E := E) K
        (rhoSupportImage_measurable (dR := dR) (I := I) i)) ?_
  intro x
  -- Unfold `h1On` membership: it is a `comap` condition on `h1ToL2`.
  dsimp [h1On]
  -- `h1ToL2` is the first projection, so it suffices to show the scalar component lies in the
  -- extend-by-zero range.
  change
      ((h1ToL2
              (μ := (volume : Measure E)) (E := E)).toLinearMap (T x)) ∈
        LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K)
                (rhoSupportImage_measurable (dR := dR) (I := I) i)).toLinearMap)
  -- Compute `h1ToL2 (T x)` and apply the range lemma for `projToVolumeTarget`.
  have :
      ((h1ToL2
              (μ := (volume : Measure E)) (E := E)).toLinearMap (T x)) =
        (projToVolumeTarget (dR := dR) (I := I) (i := i) (x.1 : FiniteChartData.h1Target (d :=
          dR.d) (I := I) μM)).1 := by
    -- `T` is the codomain-restricted version of `projToVolumeTarget ∘ subtypeL`, and `h1ToL2` is
    -- `fst`.
    simp [T, h1ToChartVolH1, h1ToL2]
  -- Rewrite and apply the range lemma.
  simpa [this, K] using
    (projToVolumeTarget_fst_mem_extendByZero_range (dR := dR) (I := I) (i := i)
      (y := (x.1 : FiniteChartData.h1Target (d := dR.d) (I := I) μM)))

omit [T2Space M] in
 private lemma eL2RangeChartVol_h1ToChartL2Range_coe (i : dR.d.ι)
    (x :
      ↥(FiniteChartData.h1 (d := dR.d) (I := I)
            (μ :=
              RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I)
                (M := M)))) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    ↑((eL2RangeChartVol (dR := dR) (I := I) (i := i) (F := ℝ))
        ((h1ToChartL2Range (dR := dR) (I := I) (i := i)) x)) =
      ((projToVolumeTarget (dR := dR) (I := I) (i := i) (x.1 : FiniteChartData.h1Target (d := dR.d)
        (I := I) μM))).1 := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  let eChart := Lp.extendByZeroₗᵢ (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm
  let eVol := Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ)
    (p := (2 : ℝ≥0∞)) (s := K) hKm
  let z := h1ToChartL2Range (dR := dR) (I := I) i x
  let uK := (LinearIsometry.equivRange eChart).symm z
  let cm := Lp.changeMeasureL (μ := μchart) (ν := μchart.restrict K) (E := ℝ)
    (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
    (restrict_le_one_smul μchart K) (by simp)
  have heChart_uK : eChart uK = (z : E →₂[μchart] ℝ) :=
    congrArg Subtype.val ((LinearIsometry.equivRange eChart).apply_symm_apply z)
  have huK_eq : uK = cm (z : E →₂[μchart] ℝ) := by
    have hz : ((z : E →₂[μchart] ℝ) : E → ℝ) =ᵐ[μchart] K.indicator (fun t => uK t) := by
      rw [← heChart_uK]
      exact Lp.extendByZeroₗᵢ_ae_eq hKm uK
    have hzK : ((z : E →₂[μchart] ℝ) : E → ℝ) =ᵐ[μchart.restrict K] uK :=
      Filter.EventuallyEq.trans (ae_restrict_of_ae hz) (indicator_ae_eq_restrict hKm)
    exact Lp.ext (hzK.symm.trans
      (Lp.changeMeasureL_coeFn_ae_eq (μ := μchart) (ν := μchart.restrict K) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (c := (1 : ℝ≥0∞)) (by simp)
        (restrict_le_one_smul μchart K) (by simp) (z : E →₂[μchart] ℝ)).symm)
  change eVol (l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) i ℝ uK) =
    eVol (l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) i ℝ
      (cm (z : E →₂[μchart] ℝ)))
  exact congrArg (fun u => eVol (l2EquivVolumeOnRhoSupportImage' (dR := dR) (I := I) i ℝ u))
    huK_eq

/-!
### Compactness: chartwise `H¹ → L²` contribution

We now apply Euclidean Rellich compactness on Lebesgue `volume` (supported in `K`) and transport
compactness back to the chart measure using the `extendByZero`-range equivalence.
-/

omit [T2Space M] in
theorem isCompactOperator_h1ToChartL2Range (i : dR.d.ι) :
    let μM :=
      RellichKondrachov.Geometry.Manifold.Riemannian.riemannianVolumeMeasure (I := I) (M := M)
    IsCompactOperator
      (h1ToChartL2Range (dR := dR) (I := I) (i := i) :
        ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →L[ℝ] _) := by
  classical
  intro μM
  let μchart := FiniteChartData.chartMeasure (d := dR.d) (I := I) μM i
  let K : Set E := FiniteChartData.rhoSupportImage (d := dR.d) (I := I) i
  have hKm : MeasurableSet K := rhoSupportImage_measurable (dR := dR) (I := I) i
  have hK : IsCompact K := FiniteChartData.isCompact_rhoSupportImage (d := dR.d) (I := I) i
  -- Euclidean Rellich compactness into the `extendByZero` range for `volume`.
  let volRange :
      Submodule ℝ (E →₂[(volume : Measure E)] ℝ) :=
    LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
            (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap)
  have hcompVol :
      IsCompactOperator
        (Set.codRestrict
          (h1OnToL2 (E := E) K hKm)
          volRange
          (by
            intro x
            have hxmem :
                (x : ↥(h1
                    (μ := (volume : Measure E)) (E := E))) ∈
                  h1On (E := E) K hKm :=
              x.property
            dsimp [h1On] at hxmem
            -- `h1OnToL2` is `h1ToL2` on the underlying `H¹` element.
            -- Avoid `simp` using `x.property` (which can rewrite the goal to `True`).
            change
                ((h1ToL2
                    (μ := (volume : Measure E)) (E := E)).toLinearMap
                      (x : ↥(h1
                        (μ := (volume : Measure E)) (E := E)))) ∈
                  volRange
            -- `hxmem` is exactly the unfolded membership.
            exact hxmem)) := by
    -- The theorem in the Euclidean file is stated with `LinearMap.range` directly; this `volRange`
    -- is definitional (unification fills the proof term).
    simpa [volRange] using
      (isCompactOperator_h1OnToL2_codRestrict_range_extendByZero
        (E := E) (K := K) hK hKm)
  -- Precompose by the manifold-to-Euclidean supported `H¹` map.
  have hcompVol' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
        (Set.codRestrict
          (h1OnToL2 (E := E) K hKm)
          volRange
          (by
            intro y
            have hymem :
                (y : ↥(h1
                    (μ := (volume : Measure E)) (E := E))) ∈
                  h1On (E := E) K hKm :=
              y.property
            dsimp [h1On] at hymem
            change
                ((h1ToL2
                    (μ := (volume : Measure E)) (E := E)).toLinearMap
                      (y : ↥(h1
                        (μ := (volume : Measure E)) (E := E)))) ∈
                  volRange
            exact hymem))
          ((h1ToChartVolH1On (dR := dR) (I := I) (i := i)) x) :=
    hcompVol.comp_clm (h1ToChartVolH1On (dR := dR) (I := I) (i := i))
  -- Transport the compactness statement back to the chart measure using the range equivalence.
  have hcompVol'' :
      IsCompactOperator fun x : ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) =>
        (eL2RangeChartVol (dR := dR) (I := I) (i := i) (F := ℝ)).symm
          ((Set.codRestrict
                (h1OnToL2 (E := E) K hKm)
                volRange
                (by
                  intro y
                  have hymem :
                      (y : ↥(h1
                          (μ := (volume : Measure E)) (E := E))) ∈
                        h1On (E := E) K hKm :=
                    y.property
                  dsimp [h1On] at hymem
                  change
                      ((h1ToL2
                          (μ := (volume : Measure E)) (E := E)).toLinearMap
                            (y : ↥(h1
                              (μ := (volume : Measure E)) (E := E)))) ∈
                        volRange
                  exact hymem)
                ((h1ToChartVolH1On (dR := dR) (I := I) (i := i)) x))) :=
    (hcompVol'.clm_comp (eL2RangeChartVol (dR := dR) (I := I) (i := i) (F :=
      ℝ)).symm.toContinuousLinearMap)
  -- Finally, identify this transported compact operator with the actual codomain-restricted chart
  -- map.
  -- This is the only nontrivial point: it asserts that `h1ToChartL2Range` is obtained by
  -- conjugating
  -- the volume-side supported `H¹` inclusion.
  -- We prove it by applying `eL2RangeChartVol` and simplifying.
  have hEq :
      (h1ToChartL2Range (dR := dR) (I := I) (i := i) :
          ↥(FiniteChartData.h1 (d := dR.d) (I := I) (μ := μM)) →
            ↥(LinearMap.range
              ((MeasureTheory.Lp.extendByZeroₗᵢ
                    (μ := μchart) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))) =
        fun x =>
          ((eL2RangeChartVol (dR := dR) (I := I) (i := i) (F := ℝ)).symm
              (Set.codRestrict
                (h1OnToL2 (E := E) K hKm)
                volRange
                (by
                  intro y
                  have hymem :
                      (y : ↥(h1
                          (μ := (volume : Measure E)) (E := E))) ∈
                        h1On (E := E) K hKm :=
                    y.property
                  dsimp [h1On] at hymem
                  change
                      ((h1ToL2
                          (μ := (volume : Measure E)) (E := E)).toLinearMap
                            (y : ↥(h1
                              (μ := (volume : Measure E)) (E := E)))) ∈
                        volRange
                  exact hymem)
                ((h1ToChartVolH1On (dR := dR) (I := I) (i := i)) x))) := by
    -- Apply the forward equivalence and simplify via `h1ToChartL2RangeVol`.
    funext x
    -- It suffices to prove equality after applying the forward equivalence.
    -- (This avoids unpacking the `symm` explicitly.)
    have :
        (eL2RangeChartVol (dR := dR) (I := I) (i := i) (F := ℝ))
            ((h1ToChartL2Range (dR := dR) (I := I) (i := i)) x) =
          (Set.codRestrict
              (h1OnToL2 (E := E) K hKm)
              volRange
              (by
                intro y
                have hymem :
                    (y : ↥(h1
                        (μ := (volume : Measure E)) (E := E))) ∈
                      h1On (E := E) K hKm :=
                  y.property
                dsimp [h1On] at hymem
                change
                    ((h1ToL2
                        (μ := (volume : Measure E)) (E := E)).toLinearMap
                          (y : ↥(h1
                            (μ := (volume : Measure E)) (E := E)))) ∈
                      volRange
                exact hymem)
              ((h1ToChartVolH1On (dR := dR) (I := I) (i := i)) x)) := by
      -- The left-hand side is the definition of `h1ToChartL2RangeVol`.
      -- Prove equality by unfolding both sides and reducing to the explicit `projToVolumeTarget`
      -- computation of the scalar component.
      -- (The heavy lifting is encapsulated in the `h1ToChartVolH1On` construction.)
      -- We use `Subtype.ext` and compute the underlying `L²(volume)` value.
      ext1
      -- Identify the transported chartwise `L²` component with `projToVolumeTarget`.
      rw [eL2RangeChartVol_h1ToChartL2Range_coe (dR := dR) (I := I) (E := E) (i := i) x]
      rfl
    -- Now cancel the forward equivalence.
    -- (`simp` uses `ContinuousLinearEquiv.apply_symm_apply`.)
    simpa using congrArg ((eL2RangeChartVol (dR := dR) (I := I) (i := i) (F := ℝ)).symm) this
  -- Rewrite the goal using the identification and apply the established compactness.
  simpa [hEq] using hcompVol''

end ChartwiseCompactness

end RiemannianFiniteChartData

end

end Sobolev
end Manifold
end Geometry
end RellichKondrachov
