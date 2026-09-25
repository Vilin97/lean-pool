/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalizedEnergyProfile
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Local Patch Cutoff -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Arbitrary-center local cutoffs for coarse Caccioppoli

The boundary Caccioppoli proof in the notes uses cutoffs on
`(center + rho cu_{m-1}) ∩ cu_m`, with arbitrary patch center `center`.
The older deterministic stack used only cutoffs centered at the parent cube
center.  This file reuses the canonical cube cutoff on the origin cube of
scale `Q.scale - 1`, translated to the desired local center.
-/

/-- Reference origin cube with the scale of `cu_{m-1}` when `Q` has scale
`m`. -/
def coarseCaccioppoliLocalReferenceCube {d : ℕ} (Q : TriadicCube d) :
    TriadicCube d :=
  originCube d (Q.scale - 1)

theorem cubeCenter_coarseCaccioppoliLocalReferenceCube {d : ℕ}
    (Q : TriadicCube d) :
    cubeCenter (coarseCaccioppoliLocalReferenceCube Q) = 0 := by
  ext i
  simp [coarseCaccioppoliLocalReferenceCube, cubeCenter, originCube]

theorem cubeRadius_coarseCaccioppoliLocalReferenceCube {d : ℕ}
    (Q : TriadicCube d) :
    cubeRadius (coarseCaccioppoliLocalReferenceCube Q) = cubeRadius Q / 3 := by
  unfold coarseCaccioppoliLocalReferenceCube cubeRadius cubeScaleFactor originCube
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num
  ring

theorem sub_center_mem_scaledClosedCubeSet_localReference_iff {d : ℕ}
    (Q : TriadicCube d) (center x : Vec d) (rho : ℝ) :
    x - center ∈ scaledClosedCubeSet (coarseCaccioppoliLocalReferenceCube Q) rho ↔
      x ∈ coarseCaccioppoliLocalClosedCube Q center rho := by
  constructor
  · intro hx i
    have hxi := hx i
    simpa [scaledClosedCubeSet, coarseCaccioppoliLocalClosedCube,
      coarseCaccioppoliLocalPatchRadius, Pi.sub_apply,
      cubeCenter_coarseCaccioppoliLocalReferenceCube,
      cubeRadius_coarseCaccioppoliLocalReferenceCube] using hxi
  · intro hx i
    have hxi := hx i
    simpa [scaledClosedCubeSet, coarseCaccioppoliLocalClosedCube,
      coarseCaccioppoliLocalPatchRadius, Pi.sub_apply,
      cubeCenter_coarseCaccioppoliLocalReferenceCube,
      cubeRadius_coarseCaccioppoliLocalReferenceCube] using hxi

theorem sub_center_mem_scaledOpenCubeSet_localReference_iff {d : ℕ}
    (Q : TriadicCube d) (center x : Vec d) (rho : ℝ) :
    x - center ∈ scaledOpenCubeSet (coarseCaccioppoliLocalReferenceCube Q) rho ↔
      x ∈ coarseCaccioppoliLocalOpenCube Q center rho := by
  constructor
  · intro hx i
    have hxi := hx i
    simpa [scaledOpenCubeSet, coarseCaccioppoliLocalOpenCube,
      coarseCaccioppoliLocalPatchRadius, Pi.sub_apply,
      cubeCenter_coarseCaccioppoliLocalReferenceCube,
      cubeRadius_coarseCaccioppoliLocalReferenceCube] using hxi
  · intro hx i
    have hxi := hx i
    simpa [scaledOpenCubeSet, coarseCaccioppoliLocalOpenCube,
      coarseCaccioppoliLocalPatchRadius, Pi.sub_apply,
      cubeCenter_coarseCaccioppoliLocalReferenceCube,
      cubeRadius_coarseCaccioppoliLocalReferenceCube] using hxi

/-- If a descendant cube touches an inner local cube and is smaller than the
local radial buffer, then it is contained in the outer local cube. -/
theorem cubeSet_subset_coarseCaccioppoliLocalClosedCube_of_intersects_of_scaleFactor_le_gap
    {d : ℕ} {Q R : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (hgap : cubeScaleFactor R ≤ (rhoOuter - rhoInner) * (cubeRadius Q / 3))
    (hinter :
      ∃ y ∈ cubeSet R, y ∈ coarseCaccioppoliLocalClosedCube Q center rhoInner) :
    cubeSet R ⊆ coarseCaccioppoliLocalClosedCube Q center rhoOuter := by
  rcases hinter with ⟨y, hyR, hyinner⟩
  intro x hxR i
  have hxy_norm : ‖x - y‖ ≤ cubeScaleFactor R :=
    norm_sub_le_cubeScaleFactor_of_mem_cubeSet R hxR hyR
  have hxy_coord : |x i - y i| ≤ cubeScaleFactor R := by
    calc
      |x i - y i| = ‖(x - y) i‖ := by
        simp [Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i
      _ ≤ cubeScaleFactor R := hxy_norm
  have htri :
      |x i - center i| ≤ |x i - y i| + |y i - center i| := by
    have hdecomp :
        x i - center i = (x i - y i) + (y i - center i) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |x i - center i|
        ≤ |x i - y i| + |y i - center i| := htri
    _ ≤ coarseCaccioppoliLocalPatchRadius Q rhoInner + cubeScaleFactor R := by
          linarith [hxy_coord, hyinner i]
    _ ≤ coarseCaccioppoliLocalPatchRadius Q rhoInner +
          (rhoOuter - rhoInner) * (cubeRadius Q / 3) := by
          linarith [hgap]
    _ = coarseCaccioppoliLocalPatchRadius Q rhoOuter := by
          unfold coarseCaccioppoliLocalPatchRadius
          ring

/-- Canonical local cutoff centered at an arbitrary patch center. -/
def coarseCaccioppoliLocalCanonicalFun {d : ℕ} (Q : TriadicCube d)
    (center : Vec d) (rhoInner rhoOuter : ℝ) : Vec d → ℝ :=
  fun x =>
    QuantitativeCubeCutoff.canonicalFun
      (coarseCaccioppoliLocalReferenceCube Q) rhoInner rhoOuter (x - center)

theorem coarseCaccioppoliLocalCanonicalFun_smooth {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    ContDiff ℝ (⊤ : ℕ∞)
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) := by
  have hcanonical :
      ContDiff ℝ (⊤ : ℕ∞)
        (QuantitativeCubeCutoff.canonicalFun
          (coarseCaccioppoliLocalReferenceCube Q) rhoInner rhoOuter) :=
    QuantitativeCubeCutoff.canonicalFun_smooth
      (coarseCaccioppoliLocalReferenceCube Q) hinner hinnerOuter
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => x - center) :=
    contDiff_id.sub contDiff_const
  simpa [coarseCaccioppoliLocalCanonicalFun] using! hcanonical.comp hshift

theorem coarseCaccioppoliLocalCanonicalFun_nonneg {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rhoInner rhoOuter : ℝ)
    (x : Vec d) :
    0 ≤ coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x :=
  QuantitativeCubeCutoff.canonicalFun_nonneg
    (coarseCaccioppoliLocalReferenceCube Q) rhoInner rhoOuter (x - center)

theorem coarseCaccioppoliLocalCanonicalFun_le_one {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) (rhoInner rhoOuter : ℝ)
    (x : Vec d) :
    coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x ≤ 1 :=
  QuantitativeCubeCutoff.canonicalFun_le_one
    (coarseCaccioppoliLocalReferenceCube Q) rhoInner rhoOuter (x - center)

theorem coarseCaccioppoliLocalCanonicalFun_hasCompactSupport {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    HasCompactSupport
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) := by
  have hbase :
      HasCompactSupport
        (QuantitativeCubeCutoff.canonicalFun
          (coarseCaccioppoliLocalReferenceCube Q) rhoInner rhoOuter) :=
    QuantitativeCubeCutoff.canonicalFun_hasCompactSupport
      (coarseCaccioppoliLocalReferenceCube Q) hinner hinnerOuter
  show
    HasCompactSupport
      ((QuantitativeCubeCutoff.canonicalFun
          (coarseCaccioppoliLocalReferenceCube Q) rhoInner rhoOuter) ∘
        Homeomorph.subRight center)
  simpa [coarseCaccioppoliLocalCanonicalFun, Function.comp] using
    hbase.comp_homeomorph (Homeomorph.subRight center)

/-- Multiplication by the translated local canonical cutoff preserves
parent-cube integrability. -/
theorem integrableOn_localCanonicalCutoff_mul_of_integrableOn_cubeSet {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    {energy : Vec d → ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun x =>
        coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x * energy x)
      (cubeSet Q) MeasureTheory.volume := by
  have hcut_meas :
      MeasureTheory.AEStronglyMeasurable
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
        (MeasureTheory.volume.restrict (cubeSet Q)) :=
    ((coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter).continuous).aestronglyMeasurable
  have hcut_bound :
      ∀ᵐ x ∂MeasureTheory.volume.restrict (cubeSet Q),
        ‖coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x‖ ≤ 1 := by
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact
        abs_le.mpr
          ⟨by
            linarith
              [coarseCaccioppoliLocalCanonicalFun_nonneg
                Q center rhoInner rhoOuter x],
           coarseCaccioppoliLocalCanonicalFun_le_one
             Q center rhoInner rhoOuter x⟩
  exact henergy_int.bdd_mul hcut_meas hcut_bound

theorem coarseCaccioppoliLocalCanonicalFun_eq_one_on_inner {d : ℕ}
    {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    {x : Vec d} (hx : x ∈ coarseCaccioppoliLocalClosedCube Q center rhoInner) :
    coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x = 1 := by
  have hxref :
      x - center ∈
        scaledClosedCubeSet (coarseCaccioppoliLocalReferenceCube Q) rhoInner :=
    (sub_center_mem_scaledClosedCubeSet_localReference_iff Q center x rhoInner).2 hx
  exact
    QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner
      hinner hinnerOuter hxref

/-- The local inner energy is bounded by the translated canonical
cutoff-weighted energy. -/
theorem coarseCaccioppoliLocalEnergyProfile_le_localCanonicalCutoffEnergy
    {d : ℕ} (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (energy : Vec d → ℝ)
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (hprofile_int :
      MeasureTheory.IntegrableOn
        ((coarseCaccioppoliLocalClosedCube Q center rhoInner).indicator energy)
        (cubeSet Q) MeasureTheory.volume)
    (hweighted_int :
      MeasureTheory.IntegrableOn
        (fun x =>
          coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x * energy x)
        (cubeSet Q) MeasureTheory.volume) :
    coarseCaccioppoliLocalEnergyProfile Q center rhoInner energy ≤
      cubeAverage Q
        (fun x =>
          coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x *
            energy x) := by
  unfold coarseCaccioppoliLocalEnergyProfile
  apply cubeAverage_le_cubeAverage_of_le_on Q hprofile_int hweighted_int
  intro x hxQ
  by_cases hxinner : x ∈ coarseCaccioppoliLocalClosedCube Q center rhoInner
  · have hη :
      coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x = 1 :=
        coarseCaccioppoliLocalCanonicalFun_eq_one_on_inner
          hinner hinnerOuter hxinner
    simp [Set.indicator_of_mem hxinner, hη]
  · have hη_nonneg :
        0 ≤ coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x :=
      coarseCaccioppoliLocalCanonicalFun_nonneg Q center rhoInner rhoOuter x
    rw [Set.indicator_of_notMem hxinner]
    exact mul_nonneg hη_nonneg (henergy_nonneg x hxQ)

/-- Integrability-free local lower bound using the translated canonical
cutoff. -/
theorem coarseCaccioppoliLocalEnergyProfile_le_localCanonicalCutoffEnergy_of_integrable
    {d : ℕ} (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (energy : Vec d → ℝ)
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    coarseCaccioppoliLocalEnergyProfile Q center rhoInner energy ≤
      cubeAverage Q
        (fun x =>
          coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter x *
            energy x) := by
  exact
    coarseCaccioppoliLocalEnergyProfile_le_localCanonicalCutoffEnergy
      Q center energy hinner hinnerOuter henergy_nonneg
      (integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
        Q center rhoInner henergy_int)
      (integrableOn_localCanonicalCutoff_mul_of_integrableOn_cubeSet
        Q center hinner hinnerOuter henergy_int)

theorem coarseCaccioppoliLocalCanonicalFun_support_subset_localOpenCube {d : ℕ}
    {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    Function.support
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) ⊆
      coarseCaccioppoliLocalOpenCube Q center rhoOuter := by
  intro x hx
  have hxref :
      x - center ∈
        Function.support
          (QuantitativeCubeCutoff.canonicalFun
            (coarseCaccioppoliLocalReferenceCube Q) rhoInner rhoOuter) := by
    simpa [coarseCaccioppoliLocalCanonicalFun] using hx
  exact
    (sub_center_mem_scaledOpenCubeSet_localReference_iff Q center x rhoOuter).1
      (QuantitativeCubeCutoff.canonicalFun_support_subset hinner hinnerOuter hxref)

theorem coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube {d : ℕ}
    {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    tsupport
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) ⊆
      coarseCaccioppoliLocalClosedCube Q center rhoOuter := by
  have hsupp :
      Function.support
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) ⊆
        coarseCaccioppoliLocalClosedCube Q center rhoOuter :=
    (coarseCaccioppoliLocalCanonicalFun_support_subset_localOpenCube
      hinner hinnerOuter).trans
      (coarseCaccioppoliLocalOpenCube_subset_closedCube Q center rhoOuter)
  simpa [tsupport] using
    closure_minimal hsupp
      (isClosed_coarseCaccioppoliLocalClosedCube Q center rhoOuter)

theorem coarseCaccioppoliLocalCanonicalFun_tsupport_subset_openCubeSet
    {d : ℕ} {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hsub : coarseCaccioppoliLocalClosedCube Q center rhoOuter ⊆ openCubeSet Q) :
    tsupport
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) ⊆
      openCubeSet Q :=
  (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
      hinner hinnerOuter).trans hsub

theorem coarseCaccioppoliLocalClosedCube_subset_localOpenCube_one_of_lt_one
    {d : ℕ} {Q : TriadicCube d} {center : Vec d} {rho : ℝ} (hrho : rho < 1) :
    coarseCaccioppoliLocalClosedCube Q center rho ⊆
      coarseCaccioppoliLocalOpenCube Q center 1 := by
  intro x hx i
  have hxi := hx i
  have hbase_pos : 0 < cubeRadius Q / 3 := by
    exact div_pos (cubeRadius_pos Q) (by norm_num)
  have hrad_lt :
      coarseCaccioppoliLocalPatchRadius Q rho <
        coarseCaccioppoliLocalPatchRadius Q 1 := by
    dsimp [coarseCaccioppoliLocalPatchRadius]
    exact mul_lt_mul_of_pos_right hrho hbase_pos
  exact lt_of_le_of_lt hxi hrad_lt

theorem support_scalarCutoffGradientField_coarseCaccioppoliLocalCanonicalFun_subset_localClosedCube
    {d : ℕ} {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    Function.support
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)) ⊆
      coarseCaccioppoliLocalClosedCube Q center rhoOuter :=
  (support_scalarCutoffGradientField_subset_tsupport
      (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)).trans
    (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
      hinner hinnerOuter)

theorem scalarCutoffGradientField_coarseCaccioppoliLocalCanonicalFun_eq_zero_of_notMem_localClosedCube
    {d : ℕ} {Q : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    {x : Vec d}
    (hx : x ∉ coarseCaccioppoliLocalClosedCube Q center rhoOuter) :
    scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x = 0 := by
  exact
    scalarCutoffGradientField_eq_zero_of_notMem_tsupport
      (fun hx_support =>
        hx
          (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
            hinner hinnerOuter hx_support))

theorem coarseCaccioppoliLocalCanonicalFun_gradient_bound {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (x : Vec d) :
    ‖fderiv ℝ
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x‖ ≤
      quantitativeCubeCutoffGradientConst d /
        ((rhoOuter - rhoInner) * (cubeRadius Q / 3)) := by
  let Qloc : TriadicCube d := coarseCaccioppoliLocalReferenceCube Q
  have hbase :
      ‖fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Qloc rhoInner rhoOuter)
          (x - center)‖ ≤
        quantitativeCubeCutoffGradientConst d /
          ((rhoOuter - rhoInner) * cubeRadius Qloc) :=
    (QuantitativeCubeCutoff.canonical Qloc rhoInner rhoOuter hinner hinnerOuter).gradient_bound
      (x - center)
  have hshift :
      fderiv ℝ (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x =
        fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Qloc rhoInner rhoOuter)
          (x - center) := by
    simpa [coarseCaccioppoliLocalCanonicalFun, Qloc] using!
      (fderiv_comp_sub (𝕜 := ℝ)
        (f := QuantitativeCubeCutoff.canonicalFun Qloc rhoInner rhoOuter)
        (x := x) center)
  rw [hshift]
  simpa [Qloc, cubeRadius_coarseCaccioppoliLocalReferenceCube] using hbase

theorem coarseCaccioppoliLocalCanonicalFun_hessian_bound {d : ℕ}
    (Q : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (x : Vec d) :
    ‖iteratedFDeriv ℝ 2
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x‖ ≤
      quantitativeCubeCutoffHessianConst d /
        (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2) := by
  let Qloc : TriadicCube d := coarseCaccioppoliLocalReferenceCube Q
  have hbase :
      ‖iteratedFDeriv ℝ 2
          (QuantitativeCubeCutoff.canonicalFun Qloc rhoInner rhoOuter)
          (x - center)‖ ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * cubeRadius Qloc) ^ 2) :=
    (QuantitativeCubeCutoff.canonical Qloc rhoInner rhoOuter hinner hinnerOuter).hessian_bound
      (x - center)
  have hshift :
      iteratedFDeriv ℝ 2
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x =
        iteratedFDeriv ℝ 2
          (QuantitativeCubeCutoff.canonicalFun Qloc rhoInner rhoOuter)
          (x - center) := by
    simpa [coarseCaccioppoliLocalCanonicalFun, Qloc] using!
      (iteratedFDeriv_comp_sub (𝕜 := ℝ)
        (f := QuantitativeCubeCutoff.canonicalFun Qloc rhoInner rhoOuter)
        2 center x)
  rw [hshift]
  simpa [Qloc, cubeRadius_coarseCaccioppoliLocalReferenceCube] using hbase

theorem coarseCaccioppoliLocalCanonicalFun_memLp_top_gradientField_on_cube
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    MeasureTheory.MemLp
      (scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
      ∞ (normalizedCubeMeasure R) := by
  refine
    memLp_top_scalarCutoffGradientField_of_bound_on_cubeSet
      (Q := R)
      (η := coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
      (Xi :=
        quantitativeCubeCutoffGradientConst d /
          ((rhoOuter - rhoInner) * (cubeRadius Q / 3)))
      (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter) ?_
  intro z _hz
  exact coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center hinner hinnerOuter z

theorem coarseCaccioppoliLocalCanonicalFun_cubeLpNorm_infty_gradientField_le_on_cube
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    cubeLpNorm R ∞
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)) ≤
      quantitativeCubeCutoffGradientConst d /
        ((rhoOuter - rhoInner) * (cubeRadius Q / 3)) := by
  have hden_nonneg :
      0 ≤ (rhoOuter - rhoInner) * (cubeRadius Q / 3) := by
    have hgap_nonneg : 0 ≤ rhoOuter - rhoInner := sub_nonneg.mpr hinnerOuter.le
    have hrad_nonneg : 0 ≤ cubeRadius Q / 3 := by
      nlinarith [cubeRadius_pos Q]
    exact mul_nonneg hgap_nonneg hrad_nonneg
  have hconst_nonneg : 0 ≤ quantitativeCubeCutoffGradientConst d := by
    unfold quantitativeCubeCutoffGradientConst
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      smoothTransitionProfile.derivBound_nonneg
  refine cubeLpNorm_infty_scalarCutoffGradientField_le_of_bound_on_cubeSet R
    (hXi := div_nonneg hconst_nonneg hden_nonneg) ?_
  intro z _hz
  exact coarseCaccioppoliLocalCanonicalFun_gradient_bound Q center hinner hinnerOuter z

theorem coarseCaccioppoliLocalCanonicalFun_component_fderiv_bound_on_cubeSet
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter) :
    ∀ i : Fin d, ∀ z ∈ cubeSet R,
      ‖fderiv ℝ
          (fun x =>
            scalarCutoffGradientField
              (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter) x i) z‖ ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2) := by
  exact
    scalarCutoffGradientField_component_fderiv_bound_on_cubeSet_of_hessian_bound
      R
      (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter)
      (fun z _hz =>
        coarseCaccioppoliLocalCanonicalFun_hessian_bound Q center hinner hinnerOuter z)

theorem CoarseCaccioppoliVectorCutoffControls.of_localCanonicalCutoff_on_cube
    {d : ℕ} (Q R : TriadicCube d) (center : Vec d) (s : ℝ)
    {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (energy : Vec d → ℝ)
    {Acirc1 AcircS C : ℝ}
    (hB :
      0 ≤
        quantitativeCubeCutoffHessianConst d /
          (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
    (hAcircS : 0 ≤ AcircS)
    (hBgConst :
      0 ≤
        coarseCaccioppoliConstantCutoffSize R u
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2)))
    (hBgCent :
      0 ≤
        coarseCaccioppoliCenteredCutoffSize R s
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
          Acirc1 AcircS
          (Real.sqrt (cubeAverage R energy))
          (quantitativeCubeCutoffHessianConst d /
            (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
          ((Fintype.card (Fin d) : ℝ) * C))
    (hC : 0 ≤ C)
    (hproj : ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C (cubeFluctuation R u) G N)
    (hGcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
        Acirc1 * Real.sqrt (cubeAverage R energy))
    (hGcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage R energy)) :
    CoarseCaccioppoliVectorCutoffControls R s u G
      (scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter))
      energy Acirc1 AcircS
      (quantitativeCubeCutoffHessianConst d /
        (((rhoOuter - rhoInner) * (cubeRadius Q / 3)) ^ 2))
      C := by
  refine
    ⟨hB, hAcircS, hBgConst, hBgCent, hC, hproj, ?_, ?_, hGcirc1, hGcircS⟩
  · intro i
    exact
      contDiff_scalarCutoffGradientField_component
        (coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter) i
  · exact
      coarseCaccioppoliLocalCanonicalFun_component_fderiv_bound_on_cubeSet
        Q R center hinner hinnerOuter

end

end Homogenization
