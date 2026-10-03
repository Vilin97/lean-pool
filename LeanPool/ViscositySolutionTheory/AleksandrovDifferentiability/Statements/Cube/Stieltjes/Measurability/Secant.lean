/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Secant approximations for clamped coordinate-slice right derivatives

This file proves measurability of fixed coordinate-slice secant slopes and the source-local
secant approximation identity for the clamped right derivative.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem coordinateSliceConvexSourceSecantSlopeValue_measurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) (s h : ℝ) (hpos : 0 < h) (hlt : h < 1) :
    CoordinateSliceConvexSourceSecantSlopeValueAtMeasurable u hu i s h := by
  classical
  let c := sourceDerivativeClamp s
  let p0 : SourceCubeSpace n → SourceCubeSpace n :=
    fun y => coordinateLinePoint i (coordinateLineBase i y) c
  let p1 : SourceCubeSpace n → SourceCubeSpace n :=
    fun y => coordinateLinePoint i (coordinateLineBase i y) (c + h)
  have hc : c ∈ Set.Ioo (-3 : ℝ) 3 := by
    simpa [c] using sourceDerivativeClamp_mem_Ioo_three s
  have hch : c + h ∈ Set.Ioo (-3 : ℝ) 3 := by
    simpa [c] using sourceDerivativeClamp_add_mem_Ioo_three (s := s) hpos hlt
  have hp0_cont : Continuous p0 := by
    convert (continuous_coordinateLineBase i).add (continuous_const :
      Continuous fun _ : SourceCubeSpace n => c • sourceCoordinateVector i) using 1
    funext y
    rfl
  have hp1_cont : Continuous p1 := by
    convert (continuous_coordinateLineBase i).add (continuous_const :
      Continuous fun _ : SourceCubeSpace n => (c + h) • sourceCoordinateVector i) using 1
    funext y
    rfl
  have hp0_maps : Set.MapsTo p0 (sourceOpenCube n 1) (sourceOpenCube n 3) := by
    intro y hy
    have hline :
        c ∈ lineDomain (sourceOpenCube n 3) (coordinateLineBase i y)
          (sourceCoordinateVector i) := by
      simpa [coordinateLineDomain_sourceOpenCube_three_of_mem_sourceOpenCube_one hy] using hc
    simpa [p0, lineDomain, coordinateLinePoint] using hline
  have hp1_maps : Set.MapsTo p1 (sourceOpenCube n 1) (sourceOpenCube n 3) := by
    intro y hy
    have hline :
        c + h ∈ lineDomain (sourceOpenCube n 3) (coordinateLineBase i y)
          (sourceCoordinateVector i) := by
      simpa [coordinateLineDomain_sourceOpenCube_three_of_mem_sourceOpenCube_one hy] using hch
    simpa [p1, lineDomain, coordinateLinePoint] using hline
  have hu_cont : ContinuousOn u (sourceOpenCube n 3) :=
    hu.continuousOn (isOpen_sourceOpenCube (n := n) 3)
  have h0_cont : ContinuousOn (fun y : SourceCubeSpace n => u (p0 y)) (sourceOpenCube n 1) :=
    hu_cont.comp hp0_cont.continuousOn hp0_maps
  have h1_cont : ContinuousOn (fun y : SourceCubeSpace n => u (p1 y)) (sourceOpenCube n 1) :=
    hu_cont.comp hp1_cont.continuousOn hp1_maps
  have hden : c + h - c ≠ 0 := by linarith
  have hslope_cont :
      ContinuousOn
        (fun y : SourceCubeSpace n =>
          slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)) c
            (c + h))
        (sourceOpenCube n 1) := by
    have hquot :
        ContinuousOn
          (fun y : SourceCubeSpace n => (u (p1 y) - u (p0 y)) / (c + h - c))
          (sourceOpenCube n 1) :=
      (h1_cont.sub h0_cont).div_const (c + h - c)
    simpa [slope_def_field, lineRestriction, p0, p1, coordinateLinePoint] using hquot
  have hzero_cont :
      ContinuousOn (fun _ : SourceCubeSpace n => (0 : ℝ)) (sourceOpenCube n 1)ᶜ :=
    continuous_const.continuousOn
  have hpiece :
      Measurable
        ((sourceOpenCube n 1).piecewise
          (fun y : SourceCubeSpace n =>
            slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)) c
              (c + h))
          (fun _ : SourceCubeSpace n => (0 : ℝ))) :=
    hslope_cont.measurable_piecewise hzero_cont
      (isOpen_sourceOpenCube (n := n) 1).measurableSet
  change Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceSecantSlopeValue u hu i s h y
  rw [show
      (fun y : SourceCubeSpace n =>
        coordinateSliceConvexSourceSecantSlopeValue u hu i s h y) =
        (sourceOpenCube n 1).piecewise
          (fun y : SourceCubeSpace n =>
            slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)) c
              (c + h))
          (fun _ : SourceCubeSpace n => (0 : ℝ)) by
    ext y
    by_cases hy : y ∈ sourceOpenCube n 1
    · simp [coordinateSliceConvexSourceSecantSlopeValue, Set.piecewise, hy, c]
    · simp [coordinateSliceConvexSourceSecantSlopeValue, Set.piecewise, hy]]
  exact hpiece

/-- The standard forward secant step is positive. -/
theorem sourceForwardSecantStep_pos (m : ℕ) : 0 < sourceForwardSecantStep m := by
  unfold sourceForwardSecantStep
  positivity

/-- The standard forward secant step is smaller than one. -/
theorem sourceForwardSecantStep_lt_one (m : ℕ) : sourceForwardSecantStep m < 1 := by
  unfold sourceForwardSecantStep
  have hm : (1 : ℝ) < ((m + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos m)
  exact inv_lt_one_of_one_lt₀ hm

/-- The standard forward secant steps tend to zero. -/
theorem tendsto_sourceForwardSecantStep : Tendsto sourceForwardSecantStep atTop (nhds 0) := by
  have h :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  convert h using 1
  ext m
  norm_num [sourceForwardSecantStep, one_div, Nat.cast_add, add_assoc, add_comm, add_left_comm]

/-- The standard forward secant steps are decreasing. -/
theorem antitone_sourceForwardSecantStep : Antitone sourceForwardSecantStep := by
  intro m k hmk
  unfold sourceForwardSecantStep
  have hden : ((m + 2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hmk 2
  exact inv_anti₀ (by positivity : (0 : ℝ) < ((m + 2 : ℕ) : ℝ)) hden

/-- For a one-dimensional convex function, the project-local right derivative at an interior
point is the infimum of the standard forward secant slopes, provided the forward points stay in
the convexity set. -/
theorem ConvexOn.rightDeriv_eq_iInf_slope_sourceForwardSecantStep
    {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ} (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hstep : ∀ m : ℕ, x + sourceForwardSecantStep m ∈ S) :
    rightDeriv f x = ⨅ m : ℕ, slope f x (x + sourceForwardSecantStep m) := by
  have hderiv :
      Tendsto (slope f x) (nhdsWithin x (Set.Ioi x)) (nhds (rightDeriv f x)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Set.Ioi x)).mp
      (AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_rightDeriv
        (S := S) (f := f) (x := x) hf hx)
  have harg :
      Tendsto (fun m : ℕ => x + sourceForwardSecantStep m) atTop
        (nhdsWithin x (Set.Ioi x)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using tendsto_const_nhds.add tendsto_sourceForwardSecantStep
    · filter_upwards with m
      have hm : 0 < sourceForwardSecantStep m := sourceForwardSecantStep_pos m
      exact show x < x + sourceForwardSecantStep m from lt_add_of_pos_right x hm
  have hseq :
      Tendsto (fun m : ℕ => slope f x (x + sourceForwardSecantStep m)) atTop
        (nhds (rightDeriv f x)) :=
    hderiv.comp harg
  have hanti : Antitone fun m : ℕ => slope f x (x + sourceForwardSecantStep m) := by
    intro m k hmk
    have hm_pos : 0 < sourceForwardSecantStep m := sourceForwardSecantStep_pos m
    have hk_pos : 0 < sourceForwardSecantStep k := sourceForwardSecantStep_pos k
    have hk_le_hm : sourceForwardSecantStep k ≤ sourceForwardSecantStep m :=
      antitone_sourceForwardSecantStep hmk
    have hm_lt : x < x + sourceForwardSecantStep m := by linarith
    have hk_lt : x < x + sourceForwardSecantStep k := by linarith
    have hk_le : x + sourceForwardSecantStep k ≤ x + sourceForwardSecantStep m := by
      linarith
    have hm_mem : x + sourceForwardSecantStep m ∈ {y | y ∈ S ∧ x < y} :=
      ⟨hstep m, hm_lt⟩
    have hk_mem : x + sourceForwardSecantStep k ∈ {y | y ∈ S ∧ x < y} :=
      ⟨hstep k, hk_lt⟩
    exact (hf.monotoneOn_slope_gt (interior_subset hx)) hk_mem hm_mem
      hk_le
  have hbdd :
      BddBelow (Set.range fun m : ℕ => slope f x (x + sourceForwardSecantStep m)) := by
    refine ⟨rightDeriv f x, ?_⟩
    rintro _ ⟨m, rfl⟩
    have hm_lt : x < x + sourceForwardSecantStep m := by
      have hm_pos : 0 < sourceForwardSecantStep m := sourceForwardSecantStep_pos m
      linarith
    exact AleksandrovDifferentiability.ConvexOn.rightDeriv_le_slope
      (S := S) (f := f) (x := x) (y := x + sourceForwardSecantStep m)
      hf hx (hstep m) hm_lt
  exact tendsto_nhds_unique hseq (tendsto_atTop_ciInf hanti hbdd)

/-- The standard forward secant slopes are measurable. -/
theorem coordinateSliceConvexSourceSecantSlopeValue_standard_measurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (i : Fin n) (s : ℝ) (m : ℕ) :
    CoordinateSliceConvexSourceSecantSlopeValueAtMeasurable
      u hu i s (sourceForwardSecantStep m) :=
  coordinateSliceConvexSourceSecantSlopeValue_measurable i s (sourceForwardSecantStep m)
    (sourceForwardSecantStep_pos m) (sourceForwardSecantStep_lt_one m)

/-- The secant approximation identity reduces clamped right-derivative extension measurability to
the already proved measurability of fixed forward secant slopes. -/
theorem CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable.of_secantApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    (happrox : CoordinateSliceConvexSourceRightDerivExtensionValueSecantApprox u hu) :
    CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu := by
  intro i s
  have hseq :
      Measurable fun y : SourceCubeSpace n =>
        ⨅ m : ℕ,
          coordinateSliceConvexSourceSecantSlopeValue u hu i s (sourceForwardSecantStep m) y :=
    Measurable.iInf fun m =>
      coordinateSliceConvexSourceSecantSlopeValue_standard_measurable i s m
  change Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivExtensionValue u hu i s y
  convert hseq using 1
  ext y
  exact happrox i s y

/-- Concrete convex coordinate slices satisfy the standard secant approximation identity for the
clamped right-derivative extension. -/
theorem coordinateSliceConvexSourceRightDerivExtensionValue_secantApprox
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u} :
    CoordinateSliceConvexSourceRightDerivExtensionValueSecantApprox u hu := by
  intro i s y
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · let c := sourceDerivativeClamp s
    let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
    have hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v :=
      ConvexOn.coordinateLineRestriction_sourceCube_three hu i hy
    have hc : c ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
      simpa [(isOpen_Ioo : IsOpen (Set.Ioo (-3 : ℝ) 3)).interior_eq, c]
        using sourceDerivativeClamp_mem_Ioo_three s
    have hstep : ∀ m : ℕ, c + sourceForwardSecantStep m ∈ Set.Ioo (-3 : ℝ) 3 := by
      intro m
      simpa [c] using sourceDerivativeClamp_add_mem_Ioo_three (s := s)
        (sourceForwardSecantStep_pos m) (sourceForwardSecantStep_lt_one m)
    have hright :=
      ConvexOn.rightDeriv_eq_iInf_slope_sourceForwardSecantStep
        (S := Set.Ioo (-3 : ℝ) 3) (f := v) (x := c) hv hc hstep
    calc
      coordinateSliceConvexSourceRightDerivExtensionValue u hu i s y =
          rightDeriv v c := by
        simp [coordinateSliceConvexSourceRightDerivExtensionValue, sourceRightDerivExtension,
          hy, c, v]
      _ = ⨅ m : ℕ, slope v c (c + sourceForwardSecantStep m) := hright
      _ = ⨅ m : ℕ,
            coordinateSliceConvexSourceSecantSlopeValue u hu i s
              (sourceForwardSecantStep m) y := by
        simp [coordinateSliceConvexSourceSecantSlopeValue, hy, c, v]
  · simp [coordinateSliceConvexSourceRightDerivExtensionValue,
      coordinateSliceConvexSourceSecantSlopeValue, hy]

/-- Fixed clamped right-derivative extension evaluations of concrete convex coordinate slices are
measurable. -/
theorem coordinateSliceConvexSourceRightDerivExtensionValue_measurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u} :
    CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable u hu :=
  CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable.of_secantApprox
    coordinateSliceConvexSourceRightDerivExtensionValue_secantApprox

end AleksandrovDifferentiability
