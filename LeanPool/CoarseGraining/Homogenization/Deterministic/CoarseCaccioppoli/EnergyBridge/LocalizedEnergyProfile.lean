/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Basic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff

/-! # Localized Energy Profile -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Localized energy profiles for coarse Caccioppoli

This file starts the Phase 3 `hlower` bridge.  The LaTeX proof uses a radius
profile obtained by averaging the energy over the inner scaled cube.  The
lemmas here isolate the purely order-theoretic/cutoff part: once `F rho` is
defined as this localized profile, the lower-bound hypothesis follows from
the canonical cutoff being `1` on the inner scaled cube and nonnegative
elsewhere.
-/

/-- Localized cube-average energy over the closed scaled inner cube. -/
def coarseCaccioppoliLocalizedEnergyProfile {d : ℕ} (Q : TriadicCube d)
    (ρ : ℝ) (energy : Vec d → ℝ) : ℝ :=
  cubeAverage Q ((scaledClosedCubeSet Q ρ).indicator energy)

/-- Indicator localization preserves cube integrability. -/
theorem integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) {energy : Vec d → ℝ}
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      ((scaledClosedCubeSet Q ρ).indicator energy)
      (cubeSet Q) MeasureTheory.volume := by
  exact henergy_int.indicator (isClosed_scaledClosedCubeSet Q ρ).measurableSet

/-- On a cube contained in the scaled closed cube, the localized indicator has
the same cube average as the original energy density. -/
theorem cubeAverage_indicator_scaledClosedCubeSet_eq_cubeAverage_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} (ρ : ℝ) (energy : Vec d → ℝ)
    (hsub : cubeSet R ⊆ scaledClosedCubeSet Q ρ) :
    cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy) =
      cubeAverage R energy := by
  apply cubeAverage_congr_on_cubeSet
  intro x hxR
  simp [Set.indicator_of_mem (hsub hxR)]

/-- Flux-energy controls may be localized by an outer indicator on a cube
contained in the localization region. -/
theorem CoarseCaccioppoliFluxEnergyControls.indicator_scaledClosedCubeSet_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} (ρ : ℝ)
    {a : CoeffField d} {s : ℝ} {flux : Vec d → Vec d} {energy : Vec d → ℝ}
    (hctrl : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hsub : cubeSet R ⊆ scaledClosedCubeSet Q ρ) :
    CoarseCaccioppoliFluxEnergyControls R a s flux
      ((scaledClosedCubeSet Q ρ).indicator energy) := by
  rcases hctrl with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  refine ⟨?_, ?_, ?_, hsum1, hsumS⟩
  · intro x hxR
    simpa [Set.indicator_of_mem (hsub hxR)] using henergy_nonneg x hxR
  · exact henergy_int.indicator (isClosed_scaledClosedCubeSet Q ρ).measurableSet
  · intro n S hS
    have hSsub : cubeSet S ⊆ scaledClosedCubeSet Q ρ :=
      (cubeSet_subset_of_mem_descendantsAtDepth hS).trans hsub
    have havg :
        cubeAverage S ((scaledClosedCubeSet Q ρ).indicator energy) =
          cubeAverage S energy :=
      cubeAverage_indicator_scaledClosedCubeSet_eq_cubeAverage_of_cubeSet_subset
        (Q := Q) (R := S) ρ energy hSsub
    simpa [havg] using hfluxCtrl n S hS

/-- Multiplication by the canonical cutoff preserves cube integrability. -/
theorem integrableOn_canonicalCutoff_mul_of_integrableOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} {energy : Vec d → ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun x => QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x * energy x)
      (cubeSet Q) MeasureTheory.volume := by
  have hcut_meas :
      MeasureTheory.AEStronglyMeasurable
        (QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂)
        (MeasureTheory.volume.restrict (cubeSet Q)) :=
    (QuantitativeCubeCutoff.canonicalFun_smooth Q hρ₁ hρ₁₂).continuous.aestronglyMeasurable
  have hcut_bound :
      ∀ᵐ x ∂MeasureTheory.volume.restrict (cubeSet Q),
        ‖QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x‖ ≤ 1 := by
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact
        abs_le.mpr
          ⟨by
            linarith [QuantitativeCubeCutoff.canonicalFun_nonneg Q ρ₁ ρ₂ x],
           QuantitativeCubeCutoff.canonicalFun_le_one Q ρ₁ ρ₂ x⟩
  exact henergy_int.bdd_mul hcut_meas hcut_bound

/-- Monotonicity of `cubeAverage` from a pointwise comparison on the cube. -/
theorem cubeAverage_le_cubeAverage_of_le_on {d : ℕ} (Q : TriadicCube d)
    {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume)
    (hg : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hfg : ∀ x ∈ cubeSet Q, f x ≤ g x) :
    cubeAverage Q f ≤ cubeAverage Q g := by
  have hmono :
      ∫ x in cubeSet Q, f x ∂MeasureTheory.volume ≤
        ∫ x in cubeSet Q, g x ∂MeasureTheory.volume := by
    exact
      MeasureTheory.integral_mono_ae hf hg <|
        (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
          Filter.Eventually.of_forall hfg
  unfold cubeAverage
  exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (cubeVolume_nonneg Q))

/-- Radius of the note's local Caccioppoli patch `x + rho * cu_{m-1}` when the
parent cube has radius `cubeRadius Q`. -/
def coarseCaccioppoliLocalPatchRadius {d : ℕ} (Q : TriadicCube d)
    (rho : ℝ) : ℝ :=
  rho * (cubeRadius Q / 3)

/-- Closed local cube used in the boundary Caccioppoli radius profile.  Unlike
`scaledClosedCubeSet`, this is centered at the boundary-patch center, not at
the parent cube center, and has base scale one triadic level smaller than the
parent. -/
def coarseCaccioppoliLocalClosedCube {d : ℕ} (Q : TriadicCube d)
    (center : Vec d) (rho : ℝ) : Set (Vec d) :=
  {y | ∀ i, |y i - center i| ≤ coarseCaccioppoliLocalPatchRadius Q rho}

/-- Open local cube used for support cutoffs in the boundary Caccioppoli
argument. -/
def coarseCaccioppoliLocalOpenCube {d : ℕ} (Q : TriadicCube d)
    (center : Vec d) (rho : ℝ) : Set (Vec d) :=
  {y | ∀ i, |y i - center i| < coarseCaccioppoliLocalPatchRadius Q rho}

/-- The note-facing local boundary patch: the local cube intersected with the
ambient parent cube.  For the normalized parent `cu_0`, this is
`(center + rho cu_{-1}) ∩ cu_0`. -/
def coarseCaccioppoliLocalClosedPatch {d : ℕ} (Q : TriadicCube d)
    (center : Vec d) (rho : ℝ) : Set (Vec d) :=
  openCubeSet Q ∩ coarseCaccioppoliLocalClosedCube Q center rho

/-- Open version of the local boundary patch. -/
def coarseCaccioppoliLocalOpenPatch {d : ℕ} (Q : TriadicCube d)
    (center : Vec d) (rho : ℝ) : Set (Vec d) :=
  openCubeSet Q ∩ coarseCaccioppoliLocalOpenCube Q center rho

theorem isClosed_coarseCaccioppoliLocalClosedCube {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) :
    IsClosed (coarseCaccioppoliLocalClosedCube Q center rho) := by
  classical
  unfold coarseCaccioppoliLocalClosedCube
  rw [show
      {y : Vec d | ∀ i, |y i - center i| ≤ coarseCaccioppoliLocalPatchRadius Q rho} =
        ⋂ i : Fin d,
          {y : Vec d | |y i - center i| ≤ coarseCaccioppoliLocalPatchRadius Q rho} by
    ext y
    simp]
  exact isClosed_iInter fun i =>
    isClosed_Iic.preimage
      ((continuous_abs.comp ((continuous_apply i).sub continuous_const)))

theorem measurableSet_coarseCaccioppoliLocalClosedCube {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) :
    MeasurableSet (coarseCaccioppoliLocalClosedCube Q center rho) :=
  (isClosed_coarseCaccioppoliLocalClosedCube Q center rho).measurableSet

theorem measurableSet_coarseCaccioppoliLocalClosedPatch {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) :
    MeasurableSet (coarseCaccioppoliLocalClosedPatch Q center rho) := by
  exact
    (measurableSet_openCubeSet Q).inter
      (measurableSet_coarseCaccioppoliLocalClosedCube Q center rho)

theorem coarseCaccioppoliLocalClosedPatch_subset_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) :
    coarseCaccioppoliLocalClosedPatch Q center rho ⊆ openCubeSet Q := by
  intro x hx
  exact hx.1

theorem coarseCaccioppoliLocalOpenCube_subset_closedCube {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) :
    coarseCaccioppoliLocalOpenCube Q center rho ⊆
      coarseCaccioppoliLocalClosedCube Q center rho := by
  intro x hx i
  exact le_of_lt (hx i)

theorem coarseCaccioppoliLocalOpenPatch_subset_closedPatch {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) :
    coarseCaccioppoliLocalOpenPatch Q center rho ⊆
      coarseCaccioppoliLocalClosedPatch Q center rho := by
  intro x hx
  exact ⟨hx.1, coarseCaccioppoliLocalOpenCube_subset_closedCube Q center rho hx.2⟩

/-- Local-patch cube-average energy profile with the parent-cube normalization
used by the deterministic radius-iteration backbone. -/
def coarseCaccioppoliLocalEnergyProfile {d : ℕ} (Q : TriadicCube d)
    (center : Vec d) (rho : ℝ) (energy : Vec d → ℝ) : ℝ :=
  cubeAverage Q ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)

/-- Indicator localization to the local closed cube preserves cube
integrability. -/
theorem integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
    {d : ℕ} (Q : TriadicCube d) (center : Vec d) (rho : ℝ)
    {energy : Vec d → ℝ}
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
      (cubeSet Q) MeasureTheory.volume := by
  exact
    henergy_int.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube Q center rho)

/-- Indicator localization to the note's local open-parent patch preserves cube
integrability. -/
theorem integrableOn_indicator_coarseCaccioppoliLocalClosedPatch_of_integrableOn_cubeSet
    {d : ℕ} (Q : TriadicCube d) (center : Vec d) (rho : ℝ)
    {energy : Vec d → ℝ}
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      ((coarseCaccioppoliLocalClosedPatch Q center rho).indicator energy)
      (cubeSet Q) MeasureTheory.volume := by
  exact
    henergy_int.indicator
      (measurableSet_coarseCaccioppoliLocalClosedPatch Q center rho)

/-- On a cube contained in the local closed cube, the localized indicator has
the same cube average as the original energy density. -/
theorem
    cubeAverage_indicator_coarseCaccioppoliLocalClosedCube_eq_cubeAverage_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} (center : Vec d) (rho : ℝ)
    (energy : Vec d → ℝ)
    (hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedCube Q center rho) :
    cubeAverage R ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy) =
      cubeAverage R energy := by
  apply cubeAverage_congr_on_cubeSet
  intro x hxR
  simp [Set.indicator_of_mem (hsub hxR)]

/-- On a cube contained in the local Caccioppoli patch, the localized indicator
has the same cube average as the original energy density. -/
theorem
    cubeAverage_indicator_coarseCaccioppoliLocalClosedPatch_eq_cubeAverage_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} (center : Vec d) (rho : ℝ)
    (energy : Vec d → ℝ)
    (hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedPatch Q center rho) :
    cubeAverage R ((coarseCaccioppoliLocalClosedPatch Q center rho).indicator energy) =
      cubeAverage R energy := by
  apply cubeAverage_congr_on_cubeSet
  intro x hxR
  simp [Set.indicator_of_mem (hsub hxR)]

/-- Flux-energy controls may be localized by a local-closed-cube indicator on a
cube contained in the local cube. -/
theorem
    CoarseCaccioppoliFluxEnergyControls.indicator_coarseCaccioppoliLocalClosedCube_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} (center : Vec d) (rho : ℝ)
    {a : CoeffField d} {s : ℝ} {flux : Vec d → Vec d} {energy : Vec d → ℝ}
    (hctrl : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedCube Q center rho) :
    CoarseCaccioppoliFluxEnergyControls R a s flux
      ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy) := by
  rcases hctrl with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  refine ⟨?_, ?_, ?_, hsum1, hsumS⟩
  · intro x hxR
    simpa [Set.indicator_of_mem (hsub hxR)] using henergy_nonneg x hxR
  · exact
      henergy_int.indicator
        (measurableSet_coarseCaccioppoliLocalClosedCube Q center rho)
  · intro n S hS
    have hSsub : cubeSet S ⊆ coarseCaccioppoliLocalClosedCube Q center rho :=
      (cubeSet_subset_of_mem_descendantsAtDepth hS).trans hsub
    have havg :
        cubeAverage S
            ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy) =
          cubeAverage S energy :=
      cubeAverage_indicator_coarseCaccioppoliLocalClosedCube_eq_cubeAverage_of_cubeSet_subset
        (Q := Q) (R := S) center rho energy hSsub
    simpa [havg] using hfluxCtrl n S hS

/-- Flux-energy controls may be localized by a local-patch indicator on a cube
contained in the patch. -/
theorem
    CoarseCaccioppoliFluxEnergyControls.indicator_coarseCaccioppoliLocalClosedPatch_of_cubeSet_subset
    {d : ℕ} {Q R : TriadicCube d} (center : Vec d) (rho : ℝ)
    {a : CoeffField d} {s : ℝ} {flux : Vec d → Vec d} {energy : Vec d → ℝ}
    (hctrl : CoarseCaccioppoliFluxEnergyControls R a s flux energy)
    (hsub : cubeSet R ⊆ coarseCaccioppoliLocalClosedPatch Q center rho) :
    CoarseCaccioppoliFluxEnergyControls R a s flux
      ((coarseCaccioppoliLocalClosedPatch Q center rho).indicator energy) := by
  rcases hctrl with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  refine ⟨?_, ?_, ?_, hsum1, hsumS⟩
  · intro x hxR
    simpa [Set.indicator_of_mem (hsub hxR)] using henergy_nonneg x hxR
  · exact
      henergy_int.indicator
        (measurableSet_coarseCaccioppoliLocalClosedPatch Q center rho)
  · intro n S hS
    have hSsub : cubeSet S ⊆ coarseCaccioppoliLocalClosedPatch Q center rho :=
      (cubeSet_subset_of_mem_descendantsAtDepth hS).trans hsub
    have havg :
        cubeAverage S
            ((coarseCaccioppoliLocalClosedPatch Q center rho).indicator energy) =
          cubeAverage S energy :=
      cubeAverage_indicator_coarseCaccioppoliLocalClosedPatch_eq_cubeAverage_of_cubeSet_subset
        (Q := Q) (R := S) center rho energy hSsub
    simpa [havg] using hfluxCtrl n S hS

/-- The local-patch profile is nonnegative when the energy is nonnegative on
the parent cube. -/
theorem coarseCaccioppoliLocalEnergyProfile_nonneg {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x) :
    0 ≤ coarseCaccioppoliLocalEnergyProfile Q center rho energy := by
  apply cubeAverage_nonneg_of_nonneg_on (Q := Q)
  intro x hxQ
  by_cases hxinner : x ∈ coarseCaccioppoliLocalClosedCube Q center rho
  · simpa [Set.indicator_of_mem hxinner] using henergy_nonneg x hxQ
  · simp [Set.indicator_of_notMem hxinner]

/-- The local-patch profile is bounded above by the full parent-cube average. -/
theorem coarseCaccioppoliLocalEnergyProfile_le_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rho : ℝ) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    coarseCaccioppoliLocalEnergyProfile Q center rho energy ≤ cubeAverage Q energy := by
  unfold coarseCaccioppoliLocalEnergyProfile
  apply cubeAverage_le_cubeAverage_of_le_on Q
    (integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
      Q center rho henergy_int)
    henergy_int
  intro x hxQ
  by_cases hxinner : x ∈ coarseCaccioppoliLocalClosedCube Q center rho
  · simp [Set.indicator_of_mem hxinner]
  · rw [Set.indicator_of_notMem hxinner]
    exact henergy_nonneg x hxQ

/-- Unary radius profile for the note's arbitrary-center local patch. -/
def coarseCaccioppoliLocalEnergyRadiusProfile {d : ℕ} (Q : TriadicCube d)
    (center : Vec d) (energy : Vec d → ℝ) : ℝ → ℝ :=
  fun rho => coarseCaccioppoliLocalEnergyProfile Q center rho energy

/-- The arbitrary-center local radius profile supplies the nonnegativity
hypothesis used by radius iteration. -/
theorem coarseCaccioppoliLocalEnergyRadiusProfile_nonneg {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x) :
    ∀ ⦃rho : ℝ⦄, (1 / 3 : ℝ) ≤ rho → rho ≤ 1 →
      0 ≤ coarseCaccioppoliLocalEnergyRadiusProfile Q center energy rho := by
  intro rho _ _
  exact coarseCaccioppoliLocalEnergyProfile_nonneg Q center rho henergy_nonneg

/-- The arbitrary-center local radius profile is bounded above by the full
parent-cube energy average. -/
theorem coarseCaccioppoliLocalEnergyRadiusProfile_boundedAbove {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    CoarseCaccioppoliRadiusBoundedAbove
      (coarseCaccioppoliLocalEnergyRadiusProfile Q center energy) := by
  refine ⟨cubeAverage Q energy, ?_⟩
  intro rho _ _
  exact
    coarseCaccioppoliLocalEnergyProfile_le_cubeAverage
      Q center rho henergy_nonneg henergy_int

/-- The localized inner energy is bounded by the canonical cutoff-weighted
energy.  This is the reusable core of the eventual `hlower` discharge. -/
theorem coarseCaccioppoliLocalizedEnergyProfile_le_canonicalCutoffEnergy
    {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (energy : Vec d → ℝ)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (hprofile_int :
      MeasureTheory.IntegrableOn
        ((scaledClosedCubeSet Q ρ₁).indicator energy)
        (cubeSet Q) MeasureTheory.volume)
    (hweighted_int :
      MeasureTheory.IntegrableOn
        (fun x => QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x * energy x)
        (cubeSet Q) MeasureTheory.volume) :
    coarseCaccioppoliLocalizedEnergyProfile Q ρ₁ energy ≤
      cubeAverage Q
        (fun x => QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x * energy x) := by
  unfold coarseCaccioppoliLocalizedEnergyProfile
  apply cubeAverage_le_cubeAverage_of_le_on Q hprofile_int hweighted_int
  intro x hxQ
  by_cases hxinner : x ∈ scaledClosedCubeSet Q ρ₁
  · have hη :
      QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x = 1 :=
        QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner hρ₁ hρ₁₂ hxinner
    simp [Set.indicator_of_mem hxinner, hη]
  · have hη_nonneg :
        0 ≤ QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x :=
      QuantitativeCubeCutoff.canonicalFun_nonneg Q ρ₁ ρ₂ x
    rw [Set.indicator_of_notMem hxinner]
    exact mul_nonneg hη_nonneg (henergy_nonneg x hxQ)

/-- Integrability-free localized-energy lower bound using the canonical cutoff. -/
theorem coarseCaccioppoliLocalizedEnergyProfile_le_canonicalCutoffEnergy_of_integrable
    {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (energy : Vec d → ℝ)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    coarseCaccioppoliLocalizedEnergyProfile Q ρ₁ energy ≤
      cubeAverage Q
        (fun x => QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x * energy x) := by
  exact
    coarseCaccioppoliLocalizedEnergyProfile_le_canonicalCutoffEnergy
      Q energy hρ₁ hρ₁₂ henergy_nonneg
      (integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet Q ρ₁ henergy_int)
      (integrableOn_canonicalCutoff_mul_of_integrableOn_cubeSet Q hρ₁ hρ₁₂ henergy_int)

/-- The localized profile is nonnegative when the energy is nonnegative on
the cube. -/
theorem coarseCaccioppoliLocalizedEnergyProfile_nonneg {d : ℕ}
    (Q : TriadicCube d) (ρ : ℝ) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x) :
    0 ≤ coarseCaccioppoliLocalizedEnergyProfile Q ρ energy := by
  apply cubeAverage_nonneg_of_nonneg_on (Q := Q)
  intro x hxQ
  by_cases hxinner : x ∈ scaledClosedCubeSet Q ρ
  · simpa [Set.indicator_of_mem hxinner] using henergy_nonneg x hxQ
  · simp [Set.indicator_of_notMem hxinner]

/-- The localized profile is bounded above by the full cube average. -/
theorem coarseCaccioppoliLocalizedEnergyProfile_le_cubeAverage
    {d : ℕ} (Q : TriadicCube d) (ρ : ℝ) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    coarseCaccioppoliLocalizedEnergyProfile Q ρ energy ≤ cubeAverage Q energy := by
  unfold coarseCaccioppoliLocalizedEnergyProfile
  apply cubeAverage_le_cubeAverage_of_le_on Q
    (integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet Q ρ henergy_int)
    henergy_int
  intro x hxQ
  by_cases hxinner : x ∈ scaledClosedCubeSet Q ρ
  · simp [Set.indicator_of_mem hxinner]
  · rw [Set.indicator_of_notMem hxinner]
    exact henergy_nonneg x hxQ

/-- Unary radius profile obtained by localizing a fixed energy density. -/
def coarseCaccioppoliLocalizedEnergyRadiusProfile {d : ℕ} (Q : TriadicCube d)
    (energy : Vec d → ℝ) : ℝ → ℝ :=
  fun ρ => coarseCaccioppoliLocalizedEnergyProfile Q ρ energy

/-- The fixed-energy localized radius profile supplies the nonnegativity
hypothesis used by radius iteration. -/
theorem coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg {d : ℕ}
    (Q : TriadicCube d) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x) :
    ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 →
      0 ≤ coarseCaccioppoliLocalizedEnergyRadiusProfile Q energy ρ := by
  intro ρ _ _
  exact coarseCaccioppoliLocalizedEnergyProfile_nonneg Q ρ henergy_nonneg

/-- The fixed-energy localized radius profile is bounded above by the full
cube energy average. -/
theorem coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove {d : ℕ}
    (Q : TriadicCube d) {energy : Vec d → ℝ}
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    CoarseCaccioppoliRadiusBoundedAbove
      (coarseCaccioppoliLocalizedEnergyRadiusProfile Q energy) := by
  refine ⟨cubeAverage Q energy, ?_⟩
  intro ρ _ _
  exact coarseCaccioppoliLocalizedEnergyProfile_le_cubeAverage Q ρ henergy_nonneg henergy_int

/-- A concrete localized-radius profile control, stated at the exact arity of
the Caccioppoli radius bridge. -/
def CoarseCaccioppoliLocalizedEnergyProfileLowerControls {d : ℕ}
    (Q : TriadicCube d) (F : ℝ → ℝ) (energy : ℝ → ℝ → Vec d → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    F ρ₁ ≤ coarseCaccioppoliLocalizedEnergyProfile Q ρ₁ (energy ρ₁ ρ₂)

/-- Localized-radius profile controls produce the exact `hlower` family needed
by the weak-testing bridge. -/
theorem
    CoarseCaccioppoliLocalizedEnergyProfileLowerControls.to_canonicalCutoffLower
    {d : ℕ} {Q : TriadicCube d} {F : ℝ → ℝ}
    {energy : ℝ → ℝ → Vec d → ℝ}
    (hprofile : CoarseCaccioppoliLocalizedEnergyProfileLowerControls Q F energy)
    (henergy_nonneg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ cubeSet Q, 0 ≤ energy ρ₁ ρ₂ x)
    (henergy_int :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.IntegrableOn (energy ρ₁ ρ₂) (cubeSet Q) MeasureTheory.volume) :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      F ρ₁ ≤
        cubeAverage Q
          (fun x => QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x * energy ρ₁ ρ₂ x) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  exact
    (hprofile hρ₁ hlt hρ₂).trans
      (coarseCaccioppoliLocalizedEnergyProfile_le_canonicalCutoffEnergy_of_integrable
        Q (energy ρ₁ ρ₂)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hρ₁) hlt
        (henergy_nonneg hρ₁ hlt hρ₂) (henergy_int hρ₁ hlt hρ₂))

/-- Build localized lower controls for a fixed radius profile from a
pointwise comparison with the pair-dependent energy on each inner cube. -/
theorem
    CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_le_pairEnergy
    {d : ℕ} (Q : TriadicCube d) {baseEnergy : Vec d → ℝ}
    {pairEnergy : ℝ → ℝ → Vec d → ℝ}
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hpair_int :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.IntegrableOn (pairEnergy ρ₁ ρ₂) (cubeSet Q) MeasureTheory.volume)
    (hpoint :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁, baseEnergy x ≤ pairEnergy ρ₁ ρ₂ x) :
    CoarseCaccioppoliLocalizedEnergyProfileLowerControls Q
      (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      pairEnergy := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  unfold coarseCaccioppoliLocalizedEnergyRadiusProfile
  unfold coarseCaccioppoliLocalizedEnergyProfile
  apply cubeAverage_le_cubeAverage_of_le_on Q
    (integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet Q ρ₁ hbase_int)
    (integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet Q ρ₁
      (hpair_int hρ₁ hlt hρ₂))
  intro x hxQ
  by_cases hxinner : x ∈ scaledClosedCubeSet Q ρ₁
  · simpa [Set.indicator_of_mem hxinner] using
      hpoint (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂ x hxinner
  · simp [Set.indicator_of_notMem hxinner]

/-- Equality on each inner cube is a convenient way to supply the fixed-profile
lower-control comparison. -/
theorem
    CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_eq_pairEnergy
    {d : ℕ} (Q : TriadicCube d) {baseEnergy : Vec d → ℝ}
    {pairEnergy : ℝ → ℝ → Vec d → ℝ}
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hpair_int :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        MeasureTheory.IntegrableOn (pairEnergy ρ₁ ρ₂) (cubeSet Q) MeasureTheory.volume)
    (hpoint :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁, baseEnergy x = pairEnergy ρ₁ ρ₂ x) :
    CoarseCaccioppoliLocalizedEnergyProfileLowerControls Q
      (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)
      pairEnergy := by
  exact
    CoarseCaccioppoliLocalizedEnergyProfileLowerControls.of_fixedEnergy_le_pairEnergy
      Q hbase_int hpair_int
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ x hx =>
        le_of_eq (hpoint (ρ₁ := ρ₁) (ρ₂ := ρ₂) hρ₁ hlt hρ₂ x hx))

end

end Homogenization
