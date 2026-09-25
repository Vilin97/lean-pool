/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.BoundedSliceDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelTime
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanZeroInitialOperator
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderInterpolation
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Uniqueness for the bounded Euclidean heat equation

This file proves the missing injective half of the finite-cylinder Euclidean
heat operator. It first packages every positive-time slice of an arbitrary
parabolic four-jet as genuine bounded C² data.
-/

@[expose] public section

@[expose] public noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RicciFlow
namespace AnalyticPDE

section CompatibleRealModule

attribute [-instance] Semiring.toModule

namespace FiniteParabolicC2AlphaBanach

variable {n : ℕ} {t₀ T α : ℝ}

private def coordinateUpdateDerivative (k : Fin n) : Fin n → ℝ :=
  Pi.single k 1

private theorem hasDerivAt_coordinateUpdate
    (x : Fin n → ℝ) (k : Fin n) :
    HasDerivAt (fun a : ℝ => Function.update x k a)
      (coordinateUpdateDerivative k) (x k) := by
  unfold coordinateUpdateDerivative
  convert! (hasFDerivAt_update x (x k)).hasDerivAt
  ext z j
  rw [Pi.single, Function.update_apply]
  split_ifs with hj
  · simp [hj]
  · simp [Pi.single_eq_of_ne hj]

/-- First coordinate derivative of a positive-time finite-cylinder slice,
as a bounded continuous scalar function. -/
def scalarFirstSlice
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T) (k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ) (coordinateUpdateDerivative k))
    |>.compLeftContinuousBounded (Fin n → ℝ)
      (ParabolicC0AlphaBanach.finiteTimeSlice hα
        (spaceDerivComponentL u) t)

@[simp]
theorem scalarFirstSlice_apply
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T)
    (k : Fin n) (x : Fin n → ℝ) :
    scalarFirstSlice hα u t k x =
      spaceDeriv u ((t : ℝ), x) (coordinateUpdateDerivative k) := by
  change (ParabolicC0AlphaBanach.evalCLM ((t : ℝ), x)
      (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
      (spaceDerivComponentL u)) (coordinateUpdateDerivative k) = _
  rw [evalCLM_spaceDerivComponentL]

/-- One coordinate Hessian entry of a positive-time finite-cylinder slice,
as a bounded continuous scalar function. -/
def scalarSecondSlice
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T)
    (j k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  (((ContinuousLinearMap.apply ℝ ℝ) (coordinateUpdateDerivative k)).comp
      ((ContinuousLinearMap.apply ℝ ((Fin n → ℝ) →L[ℝ] ℝ))
        (coordinateUpdateDerivative j)))
    |>.compLeftContinuousBounded (Fin n → ℝ)
      (ParabolicC0AlphaBanach.finiteTimeSlice hα
        (spaceSecondDerivComponentL u) t)

@[simp]
theorem scalarSecondSlice_apply
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T)
    (j k : Fin n) (x : Fin n → ℝ) :
    scalarSecondSlice hα u t j k x =
      spaceSecondDeriv u ((t : ℝ), x)
        (coordinateUpdateDerivative j) (coordinateUpdateDerivative k) := by
  change ((ParabolicC0AlphaBanach.evalCLM ((t : ℝ), x)
      (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
      (spaceSecondDerivComponentL u)) (coordinateUpdateDerivative j))
        (coordinateUpdateDerivative k) = _
  rw [evalCLM_spaceSecondDerivComponentL]

/-- Every positive-time slice of an arbitrary finite parabolic four-jet is
genuine bounded Euclidean C² data. -/
def boundedC2DataOfSlice
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T) :
    EuclideanBoundedC2Data n where
  value := ParabolicC0AlphaBanach.finiteTimeSlice hα
    (valueComponentL u) t
  first := scalarFirstSlice hα u t
  second := scalarSecondSlice hα u t
  hasDeriv_value := by
    intro k x
    have hbase := hasFDerivAt_space u
      (show (t : ℝ) ∈ Ioc t₀ T from ⟨t.2, t.1.2.2⟩) x
    have hbase' : HasFDerivAt (fun y => value u ((t : ℝ), y))
        (spaceDeriv u ((t : ℝ), x)) (Function.update x k (x k)) := by
      simpa using hbase
    have h := hbase'.comp_hasDerivAt (x k)
      (hasDerivAt_coordinateUpdate x k)
    have hfun : (fun a : ℝ =>
        (ParabolicC0AlphaBanach.finiteTimeSlice hα
          (valueComponentL u) t) (Function.update x k a)) =
        ((fun y => value u ((t : ℝ), y)) ∘ Function.update x k) := by
      funext a
      rw [Function.comp_apply,
        ParabolicC0AlphaBanach.finiteTimeSlice_apply,
        evalCLM_valueComponentL]
    rw [hfun]
    simpa only [scalarFirstSlice_apply] using h
  hasDeriv_first := by
    intro j k x
    have hbase := hasFDerivAt_spaceDeriv u
      (show (t : ℝ) ∈ Ioc t₀ T from ⟨t.2, t.1.2.2⟩) x
    have hbase' : HasFDerivAt (fun y => spaceDeriv u ((t : ℝ), y))
        (spaceSecondDeriv u ((t : ℝ), x)) (Function.update x j (x j)) := by
      simpa using hbase
    have hline := hbase'.comp_hasDerivAt (x j)
      (hasDerivAt_coordinateUpdate x j)
    have h := ((ContinuousLinearMap.apply ℝ ℝ)
      (coordinateUpdateDerivative k)).hasFDerivAt.comp_hasDerivAt
        (x j) hline
    have hfun : (fun a : ℝ =>
        scalarFirstSlice hα u t k (Function.update x j a)) =
        ((ContinuousLinearMap.apply ℝ ℝ) (coordinateUpdateDerivative k) ∘
          (fun y => spaceDeriv u ((t : ℝ), y)) ∘ Function.update x j) := by
      funext a
      simp only [Function.comp_apply, scalarFirstSlice_apply,
        ContinuousLinearMap.apply_apply]
    rw [hfun]
    simpa only [scalarSecondSlice_apply,
      ContinuousLinearMap.apply_apply] using h

@[simp]
theorem boundedC2DataOfSlice_value
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T)
    (x : Fin n → ℝ) :
    (boundedC2DataOfSlice hα u t).value x = value u ((t : ℝ), x) := by
  unfold boundedC2DataOfSlice
  change ParabolicC0AlphaBanach.evalCLM ((t : ℝ), x)
      (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
      (valueComponentL u) = _
  rw [evalCLM_valueComponentL]

@[simp]
theorem boundedC2DataOfSlice_second
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T)
    (j k : Fin n) (x : Fin n → ℝ) :
    (boundedC2DataOfSlice hα u t).second j k x =
      spaceSecondDeriv u ((t : ℝ), x)
        (coordinateUpdateDerivative j) (coordinateUpdateDerivative k) := by
  unfold boundedC2DataOfSlice
  exact scalarSecondSlice_apply hα u t j k x

/-- The spatial Laplacian of a positive-time scalar slice, bundled as a
bounded continuous function. -/
def scalarLaplacianSlice
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ∑ k : Fin n, scalarSecondSlice hα u t k k

@[simp]
theorem scalarLaplacianSlice_apply
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T)
    (x : Fin n → ℝ) :
    scalarLaplacianSlice hα u t x =
      ∑ k : Fin n, spaceSecondDeriv u ((t : ℝ), x)
        (coordinateUpdateDerivative k) (coordinateUpdateDerivative k) := by
  unfold scalarLaplacianSlice
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
      rw [Finset.sum_insert hks, Finset.sum_insert hks,
        BoundedContinuousFunction.add_apply, scalarSecondSlice_apply, ih]

/-- On a genuine bounded C² slice, the heat-kernel Laplacian is the heat
semigroup applied to the actual finite trace of the Hessian. -/
theorem heatSemigroupLaplacianND_boundedC2DataOfSlice_eq
    (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (t : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T)
    {τ : ℝ} (hτ : 0 < τ) (x : Fin n → ℝ) :
    heatSemigroupLaplacianND τ (boundedC2DataOfSlice hα u t).value x =
      heatSemigroupND τ (scalarLaplacianSlice hα u t) x := by
  rw [heatSemigroupLaplacianND]
  calc
    (∑ k : Fin n, heatHessianCoordConvolutionND τ
        (boundedC2DataOfSlice hα u t).value k x) =
        ∑ k : Fin n, heatSemigroupND τ
          ((boundedC2DataOfSlice hα u t).second k k) x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show heatHessianCoordConvolutionND τ
          (boundedC2DataOfSlice hα u t).value k x =
          heatHessianEntryConvolutionND τ
            (boundedC2DataOfSlice hα u t).value k k x by
        rw [heatHessianCoordConvolutionND, heatHessianEntryConvolutionND]
        simp only [heatHessianKernelEntryND_diag]]
      exact (boundedC2DataOfSlice hα u t).heatHessianEntryConvolutionND_eq hτ k k x
    _ = heatSemigroupND τ (scalarLaplacianSlice hα u t) x := by
      unfold scalarLaplacianSlice
      change (∑ k : Fin n,
          (heatSemigroupNDclm hτ
            ((boundedC2DataOfSlice hα u t).second k k)) x) =
        (heatSemigroupNDclm hτ
          (∑ k : Fin n, (boundedC2DataOfSlice hα u t).second k k)) x
      rw [map_sum]
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty => simp
      | @insert k s hks ih =>
          rw [Finset.sum_insert hks, Finset.sum_insert hks,
            BoundedContinuousFunction.add_apply, ih]

end FiniteParabolicC2AlphaBanach

section MovingHeatFlow

variable {n : ℕ}

/-- In a moving heat flow, the part caused by a differentiable change of
datum has the expected derivative.  The semigroup need only be strongly
continuous: its contraction estimate controls the moving difference
quotient uniformly. -/
theorem hasDerivAt_heatFlowPathBcf_movingIncrement
    (F : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (F' : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {s t : ℝ} (hst : s < t)
    (hF : HasDerivAt F F' s) (x : Fin n → ℝ) :
    HasDerivAt
      (fun r => heatFlowPathBcf (F r - F s) (t - r) x)
      (heatSemigroupND (t - s) F' x) s := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hτ : 0 < t - s := sub_pos.mpr hst
  have hQ : Tendsto (slope F s) (𝓝[≠] s) (𝓝 F') := hF.tendsto_slope
  have htime : Tendsto (fun r : ℝ => t - r) (𝓝[≠] s) (𝓝 (t - s)) :=
    ((continuousAt_const.sub continuousAt_id).tendsto.mono_left inf_le_left)
  have hheat : Tendsto (fun r : ℝ => heatFlowPathBcf F' (t - r))
      (𝓝[≠] s) (𝓝 (heatFlowPathBcf F' (t - s))) :=
    (continuousAt_heatFlowPathBcf F' hτ).tendsto.comp htime
  have hpos : ∀ᶠ r in 𝓝[≠] s, 0 < t - r := by
    filter_upwards [htime.eventually (Ioi_mem_nhds hτ)] with r hr
    exact hr
  have hslope : ∀ᶠ r in 𝓝[≠] s,
      slope (fun a => heatFlowPathBcf (F a - F s) (t - a) x) s r =
        heatFlowPathBcf (slope F s r) (t - r) x := by
    filter_upwards [hpos] with r hrpos
    rw [slope_def_module, slope_def_module,
      heatFlowPathBcf_of_pos _ hrpos,
      heatFlowPathBcf_of_pos _ hτ]
    have hzero : heatSemigroupNDbcf hτ (F s - F s) = 0 := by
      change heatSemigroupNDclm hτ (F s - F s) = 0
      rw [sub_self, map_zero]
    rw [hzero]
    rw [show (0 : BoundedContinuousFunction (Fin n → ℝ) ℝ) x = 0 by rfl,
      sub_zero, heatFlowPathBcf_of_pos _ hrpos]
    change (r - s)⁻¹ • heatSemigroupNDbcf hrpos (F r - F s) x =
      heatSemigroupNDbcf hrpos ((r - s)⁻¹ • (F r - F s)) x
    rw [
      ← BoundedContinuousFunction.smul_apply,
      ← heatSemigroupNDbcf_smul]
  apply (tendsto_congr' hslope).2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hQε := (Metric.tendsto_nhds.1 hQ) (ε / 2) hε2
  have hHε := (Metric.tendsto_nhds.1 hheat) (ε / 2) hε2
  filter_upwards [hQε, hHε, hpos] with r hQr hHr hrpos
  rw [heatFlowPathBcf_of_pos _ hrpos,
    heatFlowPathBcf_of_pos _ hτ] at hHr
  rw [heatFlowPathBcf_of_pos _ hrpos]
  change dist (heatSemigroupNDbcf hrpos (slope F s r) x)
    (heatSemigroupNDbcf hτ F' x) < ε
  calc
    dist (heatSemigroupNDbcf hrpos (slope F s r) x)
        (heatSemigroupND (t - s) F' x)
        ≤ dist (heatSemigroupNDbcf hrpos (slope F s r) x)
            (heatSemigroupNDbcf hrpos F' x) +
          dist (heatSemigroupNDbcf hrpos F' x)
            (heatSemigroupNDbcf hτ F' x) := dist_triangle _ _ _
    _ ≤ dist (slope F s r) F' +
          dist (heatSemigroupNDbcf hrpos F')
            (heatSemigroupNDbcf hτ F') := by
      gcongr
      calc
        dist (heatSemigroupNDbcf hrpos (slope F s r) x)
            (heatSemigroupNDbcf hrpos F' x)
            = ‖(heatSemigroupNDbcf hrpos (slope F s r) -
                heatSemigroupNDbcf hrpos F') x‖ := by
              simp only [dist_eq_norm, BoundedContinuousFunction.sub_apply]
        _ ≤ ‖heatSemigroupNDbcf hrpos (slope F s r) -
                heatSemigroupNDbcf hrpos F'‖ :=
              (heatSemigroupNDbcf hrpos (slope F s r) -
                heatSemigroupNDbcf hrpos F').norm_coe_le_norm x
        _ ≤ ‖slope F s r - F'‖ :=
              norm_heatSemigroupNDbcf_sub_le hrpos _ _
        _ = dist (slope F s r) F' := by rw [dist_eq_norm]
      calc
        dist (heatSemigroupNDbcf hrpos F' x)
            (heatSemigroupNDbcf hτ F' x) =
            ‖(heatSemigroupNDbcf hrpos F' -
              heatSemigroupNDbcf hτ F') x‖ := by
                simp only [dist_eq_norm, BoundedContinuousFunction.sub_apply]
        _ ≤ ‖heatSemigroupNDbcf hrpos F' -
              heatSemigroupNDbcf hτ F'‖ :=
            (heatSemigroupNDbcf hrpos F' -
              heatSemigroupNDbcf hτ F').norm_coe_le_norm x
        _ = dist (heatSemigroupNDbcf hrpos F')
              (heatSemigroupNDbcf hτ F') := by rw [dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add hQr hHr
    _ = ε := by ring

/-- Backward heat evolution of a fixed bounded C² datum has derivative the
negative heat Laplacian. -/
theorem EuclideanBoundedC2Data.hasDerivAt_backwardHeatFlow
    (D : EuclideanBoundedC2Data n) {s t : ℝ} (hst : s < t)
    (x : Fin n → ℝ) :
    HasDerivAt (fun r => heatFlowPathBcf D.value (t - r) x)
      (-heatSemigroupLaplacianND (t - s) D.value x) s := by
  have hτ : 0 < t - s := sub_pos.mpr hst
  have hbase := hasDerivAt_heatSemigroupND_time_eq_laplacian hτ D.value x
  have hinner0 := (hasDerivAt_const (x := s) t).sub (hasDerivAt_id s)
  have hcomp := hbase.comp s hinner0
  have heq : (fun r : ℝ => heatFlowPathBcf D.value (t - r) x) =ᶠ[𝓝 s]
      (fun r : ℝ => heatSemigroupND (t - r) D.value x) := by
    have htime : Tendsto (fun r : ℝ => t - r) (𝓝 s) (𝓝 (t - s)) :=
      (continuousAt_const.sub continuousAt_id).tendsto
    filter_upwards [htime.eventually (Ioi_mem_nhds hτ)] with r hr
    rw [heatFlowPathBcf_of_pos D.value hr, heatSemigroupNDbcf_apply]
  have h := hcomp.congr_of_eventuallyEq heq
  simpa only [zero_sub, mul_neg, mul_one] using h

/-- Variation-of-constants differential identity for a moving bounded datum
at a strictly earlier time than the fixed final time. -/
theorem hasDerivAt_backwardHeatFlow_movingData
    (F : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (F' : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (D : EuclideanBoundedC2Data n)
    {s t : ℝ} (hst : s < t) (hF : HasDerivAt F F' s)
    (hD : D.value = F s) (x : Fin n → ℝ) :
    HasDerivAt (fun r => heatFlowPathBcf (F r) (t - r) x)
      (heatSemigroupND (t - s) F' x -
        heatSemigroupLaplacianND (t - s) D.value x) s := by
  have hinc := hasDerivAt_heatFlowPathBcf_movingIncrement F F' hst hF x
  have hfix := D.hasDerivAt_backwardHeatFlow hst x
  have hfix' : HasDerivAt (fun r => heatFlowPathBcf (F s) (t - r) x)
      (-heatSemigroupLaplacianND (t - s) D.value x) s := by
    simpa only [← hD] using hfix
  have hsum := hinc.add hfix'
  have hτ : 0 < t - s := sub_pos.mpr hst
  have htime : Tendsto (fun r : ℝ => t - r) (𝓝 s) (𝓝 (t - s)) :=
    (continuousAt_const.sub continuousAt_id).tendsto
  have heq : (fun r : ℝ =>
      heatFlowPathBcf (F r - F s) (t - r) x +
        heatFlowPathBcf (F s) (t - r) x) =ᶠ[𝓝 s]
      (fun r : ℝ => heatFlowPathBcf (F r) (t - r) x) := by
    filter_upwards [htime.eventually (Ioi_mem_nhds hτ)] with r hr
    rw [heatFlowPathBcf_of_pos _ hr, heatFlowPathBcf_of_pos _ hr,
      heatFlowPathBcf_of_pos _ hr]
    change (heatSemigroupNDclm hr (F r - F s) +
      heatSemigroupNDclm hr (F s)) x = heatSemigroupNDclm hr (F r) x
    rw [← map_add]
    congr 2
    abel
  have h := hsum.congr_of_eventuallyEq heq.symm
  simpa only [sub_eq_add_neg] using h

/-- At nonnegative heat time the total heat-flow path is nonexpansive in
its datum, including the defined value at heat time zero. -/
theorem dist_heatFlowPathBcf_le_of_nonneg
    (f g : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    dist (heatFlowPathBcf f τ) (heatFlowPathBcf g τ) ≤ dist f g := by
  rcases eq_or_lt_of_le hτ with rfl | hτpos
  · simp [heatFlowPathBcf]
  · rw [heatFlowPathBcf_of_pos f hτpos,
      heatFlowPathBcf_of_pos g hτpos, dist_eq_norm, dist_eq_norm]
    exact norm_heatSemigroupNDbcf_sub_le hτpos f g

/-- Joint continuity of backward heat flow away from its zero heat-time
face.  Strong continuity for a fixed datum and nonexpansiveness in the datum
replace any false operator-norm continuity claim. -/
theorem continuousAt_backwardHeatFlowPath_of_lt
    (F : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {s t : ℝ} (hst : s < t) (hF : ContinuousAt F s) :
    ContinuousAt (fun r => heatFlowPathBcf (F r) (t - r)) s := by
  have hτ : 0 < t - s := sub_pos.mpr hst
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rw [Metric.continuousAt_iff] at hF
  obtain ⟨δF, hδF, hFδ⟩ := hF (ε / 2) hε2
  have hfixed : ContinuousAt (fun r : ℝ => heatFlowPathBcf (F s) (t - r)) s :=
    (continuousAt_heatFlowPathBcf (F s) hτ).comp
      (continuousAt_const.sub continuousAt_id)
  rw [Metric.continuousAt_iff] at hfixed
  obtain ⟨δH, hδH, hHδ⟩ := hfixed (ε / 2) hε2
  refine ⟨min δF (min δH ((t - s) / 2)), by positivity, ?_⟩
  intro r hr
  have hrF : dist r s < δF := hr.trans_le (min_le_left _ _)
  have hrH : dist r s < δH :=
    hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrτ : 0 ≤ t - r := by
    have hrs : |r - s| < (t - s) / 2 := by
      simpa [Real.dist_eq] using
        hr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [abs_lt] at hrs
    linarith
  calc
    dist (heatFlowPathBcf (F r) (t - r))
        (heatFlowPathBcf (F s) (t - s)) ≤
      dist (heatFlowPathBcf (F r) (t - r))
          (heatFlowPathBcf (F s) (t - r)) +
        dist (heatFlowPathBcf (F s) (t - r))
          (heatFlowPathBcf (F s) (t - s)) := dist_triangle _ _ _
    _ ≤ dist (F r) (F s) +
        dist (heatFlowPathBcf (F s) (t - r))
          (heatFlowPathBcf (F s) (t - s)) := by
      gcongr
      exact dist_heatFlowPathBcf_le_of_nonneg _ _ hrτ
    _ < ε / 2 + ε / 2 := add_lt_add (hFδ hrF) (hHδ hrH)
    _ = ε := by ring

/-- Joint continuity at the zero heat-time face for a moving datum whose
limiting spatial function is globally Lipschitz. -/
theorem continuousWithinAt_backwardHeatFlowPath_terminal
    (F : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (t : ℝ) (hF : ContinuousAt F t)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |F t a - F t b| ≤ L * ‖a - b‖) :
    ContinuousWithinAt (fun r => heatFlowPathBcf (F r) (t - r))
      (Iic t) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rw [Metric.continuousAt_iff] at hF
  obtain ⟨δF, hδF, hFδ⟩ := hF (ε / 2) hε2
  have hfixed : ContinuousWithinAt
      (fun r : ℝ => heatFlowPathBcf (F t) (t - r)) (Iic t) t := by
    have hc := (continuousWithinAt_heatFlowPathBcf_zero (F t) hL hlip).comp_of_eq
      (f := fun r : ℝ => t - r) (s := Iic t)
      (t := Ici (0 : ℝ)) (x := t)
      (continuous_const.sub continuous_id).continuousWithinAt
      (by
        intro r hr
        exact sub_nonneg.mpr (show r ≤ t from hr))
      (by ring)
    convert hc using 1
    funext r
    rfl
  rw [Metric.continuousWithinAt_iff] at hfixed
  obtain ⟨δH, hδH, hHδ⟩ := hfixed (ε / 2) hε2
  refine ⟨min δF δH, lt_min hδF hδH, ?_⟩
  intro r hrmem hr
  have hrF : dist r t < δF := hr.trans_le (min_le_left _ _)
  have hrH : dist r t < δH := hr.trans_le (min_le_right _ _)
  have hrτ : 0 ≤ t - r := sub_nonneg.mpr hrmem
  have hzero : heatFlowPathBcf (F t) (t - t) = F t := by
    simp [heatFlowPathBcf]
  rw [hzero]
  calc
    dist (heatFlowPathBcf (F r) (t - r)) (F t) ≤
      dist (heatFlowPathBcf (F r) (t - r))
          (heatFlowPathBcf (F t) (t - r)) +
        dist (heatFlowPathBcf (F t) (t - r)) (F t) := dist_triangle _ _ _
    _ ≤ dist (F r) (F t) +
        dist (heatFlowPathBcf (F t) (t - r)) (F t) := by
      gcongr
      exact dist_heatFlowPathBcf_le_of_nonneg _ _ hrτ
    _ < ε / 2 + ε / 2 := add_lt_add (hFδ hrF) (by
      have hh := hHδ hrmem hrH
      simpa [heatFlowPathBcf] using hh)
    _ = ε := by ring

/-- A classical finite-cylinder solution of the homogeneous Euclidean heat
equation makes the backward heat flow constant to first order. -/
theorem hasDerivAt_backwardHeatFlow_eq_zero_of_euclideanHeatCauchy_eq_zero
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (hu : euclideanHeatCauchyL n t₀ T α u = 0)
    {s t : ℝ} (hs : s ∈ Ioo t₀ T) (hst : s < t)
    (x : Fin n → ℝ) :
    HasDerivAt (fun r => heatFlowPathBcf
        (FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u r)
        (t - r) x) 0 s := by
  let ss : ParabolicC0AlphaBanach.positiveTimeInIcc t₀ T :=
    ⟨⟨s, hs.1.le, hs.2.le⟩, hs.1⟩
  let F := FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u
  let F' := FiniteParabolicC2AlphaBanach.clampedTimeDerivSlicePath hT hα u
  let D := FiniteParabolicC2AlphaBanach.boundedC2DataOfSlice hα u ss
  have hFderiv : HasDerivAt F (F' s) s := by
    exact FiniteParabolicC2AlphaBanach.hasDerivAt_clampedValueSlicePath
      hT hα u hs
  have hD : D.value = F s := by
    apply BoundedContinuousFunction.ext
    intro y
    rw [show D.value y = FiniteParabolicC2AlphaBanach.value u (s, y) by
      exact FiniteParabolicC2AlphaBanach.boundedC2DataOfSlice_value hα u ss y]
    exact (FiniteParabolicC2AlphaBanach.clampedValueSlicePath_apply_of_mem
      hT hα u ⟨hs.1, hs.2.le⟩ y).symm
  have hslice : F' s =
      FiniteParabolicC2AlphaBanach.scalarLaplacianSlice hα u ss := by
    apply BoundedContinuousFunction.ext
    intro y
    rw [show F' s y = FiniteParabolicC2AlphaBanach.timeDeriv u (s, y) by
      exact FiniteParabolicC2AlphaBanach.clampedTimeDerivSlicePath_apply_of_mem
        hT hα u ⟨hs.1, hs.2.le⟩ y]
    rw [FiniteParabolicC2AlphaBanach.scalarLaplacianSlice_apply]
    have hz := evalCLM_euclideanHeatCauchyL u (s, y)
      (show (s, y) ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T from
        ⟨⟨hs.1, hs.2.le⟩, Set.mem_univ y⟩)
    have hz' : 0 = FiniteParabolicC2AlphaBanach.timeDeriv u (s, y) -
        ∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv u (s, y)
          (Pi.single k 1) (Pi.single k 1) := by
      calc
        0 = ParabolicC0AlphaBanach.evalCLM (s, y)
            (show (s, y) ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T from
              ⟨⟨hs.1, hs.2.le⟩, Set.mem_univ y⟩)
            (euclideanHeatCauchyL n t₀ T α u) := by rw [hu, map_zero]
        _ = _ := hz
    simpa only [FiniteParabolicC2AlphaBanach.coordinateUpdateDerivative] using
      (sub_eq_zero.mp hz'.symm)
  have hmove := hasDerivAt_backwardHeatFlow_movingData
    F (F' s) D hst hFderiv hD x
  have hlap :=
    FiniteParabolicC2AlphaBanach.heatSemigroupLaplacianND_boundedC2DataOfSlice_eq
      hα u ss (sub_pos.mpr hst) x
  rw [hslice, hlap] at hmove
  simpa only [sub_self] using hmove

/-- Every positive-time value slice of a finite parabolic jet is globally
Lipschitz, with the norm of the stored first-derivative component as a valid
constant. -/
theorem clampedValueSlicePath_lipschitz
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    {t : ℝ} (ht : t ∈ Ioc t₀ T) (a b : Fin n → ℝ) :
    |FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u t a -
        FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u t b| ≤
      ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL u‖ * ‖a - b‖ := by
  let B := ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL u‖
  have hB : 0 ≤ B := norm_nonneg _
  have hDb : ParabolicBoundedWith B
      (FiniteParabolicC2AlphaBanach.spaceDeriv u)
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    intro z hz
    rw [← FiniteParabolicC2AlphaBanach.evalCLM_spaceDerivComponentL u z hz]
    calc
      ‖ParabolicC0AlphaBanach.evalCLM z hz
          (FiniteParabolicC2AlphaBanach.spaceDerivComponentL u)‖ ≤
          ‖ParabolicC0AlphaBanach.evalCLM
            (E := (Fin n → ℝ) →L[ℝ] ℝ) z hz‖ *
            ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL u‖ :=
        (ParabolicC0AlphaBanach.evalCLM
          (E := (Fin n → ℝ) →L[ℝ] ℝ) z hz).le_opNorm _
      _ ≤ 1 * ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL u‖ := by
        gcongr
        exact ParabolicC0AlphaBanach.norm_evalCLM_le z hz
      _ = B := by simp [B]
  have hv := FiniteParabolicC2AlphaBanach.value_spatial_lipschitz
    u hB hDb ht a b
  rw [FiniteParabolicC2AlphaBanach.clampedValueSlicePath_apply_of_mem
      hT hα u ht a,
    FiniteParabolicC2AlphaBanach.clampedValueSlicePath_apply_of_mem
      hT hα u ht b]
  simpa only [B, Real.norm_eq_abs] using hv

/-- The backward heat-flow path of a finite parabolic jet is continuous on
the full closed interval ending at a positive target time. -/
theorem continuousOn_backwardHeatFlowPath_finite
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    {t : ℝ} (ht : t ∈ Ioc t₀ T) :
    ContinuousOn (fun r => heatFlowPathBcf
        (FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u r)
        (t - r)) (Icc t₀ t) := by
  let F := FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u
  have hF : Continuous F :=
    FiniteParabolicC2AlphaBanach.continuous_clampedValueSlicePath hT hα u
  intro s hs
  rcases eq_or_lt_of_le hs.2 with rfl | hst
  · exact (continuousWithinAt_backwardHeatFlowPath_terminal F s hF.continuousAt
      (norm_nonneg _)
      (clampedValueSlicePath_lipschitz hT hα u ht)).mono
        (fun _ hr => hr.2)
  · exact (continuousAt_backwardHeatFlowPath_of_lt F hst hF.continuousAt).continuousWithinAt

@[simp]
theorem clampedValueSlicePath_initial
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α) :
    FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u t₀ =
      FiniteParabolicC2AlphaBanach.initialTraceL hT hα u := by
  apply BoundedContinuousFunction.ext
  intro x
  unfold FiniteParabolicC2AlphaBanach.clampedValueSlicePath
  rw [ParabolicC0AlphaBanach.globalTimeSlice_apply,
    ParabolicC0AlphaBanach.eval_finiteSourceExtension]
  change ParabolicC0AlphaBanach.finiteClosedTimeSlice hT hα
      (FiniteParabolicC2AlphaBanach.valueComponentL u)
      (Set.projIcc t₀ T hT.le t₀) x = _
  rw [Set.projIcc_of_mem hT.le (show t₀ ∈ Icc t₀ T from ⟨le_rfl, hT.le⟩)]
  rfl

/-- The backward heat flow of a homogeneous classical solution has the same
value at the final and initial ends of every positive finite interval. -/
theorem backwardHeatFlow_value_eq_initial_of_euclideanHeatCauchy_eq_zero
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (hu : euclideanHeatCauchyL n t₀ T α u = 0)
    {t : ℝ} (ht : t ∈ Ioc t₀ T) (x : Fin n → ℝ) :
    heatFlowPathBcf
        (FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u t)
        (t - t) x =
      heatFlowPathBcf
        (FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u t₀)
        (t - t₀) x := by
  let φ : ℝ → ℝ := fun r => heatFlowPathBcf
    (FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u r)
    (t - r) x
  have hcontB := continuousOn_backwardHeatFlowPath_finite hT hα u ht
  have hcont : ContinuousOn φ (Icc t₀ t) := by
    have hc := (continuous_eval_const x).comp_continuousOn hcontB
    convert hc using 1
    funext r
    rfl
  let m : ℝ := (t₀ + t) / 2
  have hm : m ∈ Ioo t₀ t := by
    dsimp only [m]
    constructor <;> linarith [ht.1]
  have heqInterior : EqOn φ (fun _ => φ m) (Ioo t₀ t) := by
    intro r hr
    rcases le_total r m with hrm | hmr
    · have hconst := constant_of_has_deriv_right_zero
          (f := φ) (a := r) (b := m)
          (hcont.mono (Icc_subset_Icc hr.1.le hm.2.le))
          (fun s hs =>
            (hasDerivAt_backwardHeatFlow_eq_zero_of_euclideanHeatCauchy_eq_zero
              (t := t) hT hα u hu
              ⟨hr.1.trans_le hs.1, hs.2.trans (hm.2.trans_le ht.2)⟩
              (hs.2.trans hm.2) x).hasDerivWithinAt)
      exact (hconst m ⟨hrm, le_rfl⟩).symm
    · have hconst := constant_of_has_deriv_right_zero
          (f := φ) (a := m) (b := r)
          (hcont.mono (Icc_subset_Icc hm.1.le hr.2.le))
          (fun s hs =>
            (hasDerivAt_backwardHeatFlow_eq_zero_of_euclideanHeatCauchy_eq_zero
              (t := t) hT hα u hu
              ⟨hm.1.trans_le hs.1, hs.2.trans (hr.2.trans_le ht.2)⟩
              (hs.2.trans hr.2) x).hasDerivWithinAt)
      exact hconst r ⟨hmr, le_rfl⟩
  have heqClosed : EqOn φ (fun _ => φ m) (Icc t₀ t) :=
    heqInterior.of_subset_closure hcont continuousOn_const
      (Ioo_subset_Icc_self)
      (by
        rw [closure_Ioo ht.1.ne])
  exact (heqClosed ⟨ht.1.le, le_rfl⟩).trans
    (heqClosed ⟨le_rfl, ht.1.le⟩).symm

/-- Genuine uniqueness for the bounded classical Euclidean heat equation:
zero Cauchy data and zero initial trace force the entire compatible
parabolic jet to vanish. -/
theorem eq_zero_of_euclideanHeatCauchy_eq_zero_of_initialTrace_eq_zero
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (hu : euclideanHeatCauchyL n t₀ T α u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = 0) :
    u = 0 := by
  apply FiniteParabolicC2AlphaBanach.ext_value hα hT
  rintro ⟨t, x⟩ hz
  have ht : t ∈ Ioc t₀ T := by
    simpa [parabolicFiniteCylinder] using hz
  have hb := backwardHeatFlow_value_eq_initial_of_euclideanHeatCauchy_eq_zero
    hT hα u hu ht x
  have hlhs : heatFlowPathBcf
      (FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u t)
      (t - t) x = FiniteParabolicC2AlphaBanach.value u (t, x) := by
    rw [sub_self]
    simp only [heatFlowPathBcf, lt_self_iff_false, ↓reduceDIte]
    exact FiniteParabolicC2AlphaBanach.clampedValueSlicePath_apply_of_mem
      hT hα u ht x
  have hrhs : heatFlowPathBcf
      (FiniteParabolicC2AlphaBanach.clampedValueSlicePath hT hα u t₀)
      (t - t₀) x = 0 := by
    rw [clampedValueSlicePath_initial, hu0]
    rw [heatFlowPathBcf_of_pos _ (sub_pos.mpr ht.1)]
    change (heatSemigroupNDclm (sub_pos.mpr ht.1)
      (0 : BoundedContinuousFunction (Fin n → ℝ) ℝ)) x = 0
    rw [map_zero]
    rfl
  rw [hlhs, hrhs] at hb
  simpa only [FiniteParabolicC2AlphaBanach.value_zero] using hb

end MovingHeatFlow

end CompatibleRealModule

end AnalyticPDE
end RicciFlow
