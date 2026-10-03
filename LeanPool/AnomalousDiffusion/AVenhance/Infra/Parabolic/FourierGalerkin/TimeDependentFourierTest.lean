/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Smooth time coefficients of spatial Fourier cutoffs

The Fourier cutoff of a smooth periodic spacetime test is a finite Fourier sum whose scalar
coefficients are smooth time tests. The coefficients are written as cell integrals so their
time regularity follows by differentiation under the integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance timeFourierTestMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance timeFourierTestMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance timeFourierTestProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance timeFourierTestProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

local instance timeFourierTestCellFinite :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def TimeDependentFourierTest.timeFourierTestCellClosure : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem TimeDependentFourierTest.timeFourierTestCellClosure_compact :
    IsCompact TimeDependentFourierTest.timeFourierTestCellClosure := by
  simpa [TimeDependentFourierTest.timeFourierTestCellClosure] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem TimeDependentFourierTest.timeFourierTestCell_subset_closure :
    AVenhance.unitCube ⊆ TimeDependentFourierTest.timeFourierTestCellClosure := by
  intro x hx
  simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ,
    forall_true_left] at hx ⊢
  intro i _
  exact ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

theorem TimeDependentFourierTest.timeFourierTestCell_measurable : MeasurableSet AVenhance.unitCube
    := by
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

/-- A jointly continuous integrand on a bounded spatial cell has a continuous cell integral in
time. The compact closure supplies a locally uniform integrable majorant. -/
theorem continuous_cell_integral_of_joint
    {F : ℝ × Vec 2 → ℝ} (hF : Continuous F) :
    Continuous (fun t => ∫ x in AVenhance.unitCube, F (t, x)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let K : Set (ℝ × Vec 2) := Metric.closedBall t 1 ×ˢ
      TimeDependentFourierTest.timeFourierTestCellClosure
  have hK : IsCompact K := (isCompact_closedBall t 1).prod
    TimeDependentFourierTest.timeFourierTestCellClosure_compact
  have himageBound : Bornology.IsBounded (F '' K) := hK.image hF |>.isBounded
  obtain ⟨C, hCpos, hC⟩ := himageBound.subset_ball_lt 0 0
  have hbound : ∀ x ∈ TimeDependentFourierTest.timeFourierTestCellClosure, ∀ s ∈ Metric.ball t 1,
      ‖F (s, x)‖ ≤ C := by
    intro x hx s hs
    have hp : (s, x) ∈ K :=
      ⟨Metric.mem_closedBall.mpr (le_of_lt hs), hx⟩
    have hb := hC ⟨(s, x), hp, rfl⟩
    have hb' : ‖F (s, x)‖ < C := by
      simpa [Metric.mem_ball, dist_eq_norm] using hb
    exact hb'.le
  have hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x => F (s, x))
        (volume.restrict AVenhance.unitCube) := by
    filter_upwards with s
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hboundAE : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ‖F (s, x)‖ ≤ C := by
    filter_upwards [Metric.ball_mem_nhds t zero_lt_one] with s hs
    filter_upwards [ae_restrict_mem TimeDependentFourierTest.timeFourierTestCell_measurable] with
        x hx
    exact hbound x (TimeDependentFourierTest.timeFourierTestCell_subset_closure hx) s hs
  have hCint : Integrable (fun _ : Vec 2 => C)
      (volume.restrict AVenhance.unitCube) := integrable_const C
  have hcont : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ContinuousAt (fun s => F (s, x)) t := by
    filter_upwards with x
    exact hF.continuousAt.comp (continuous_id.prodMk continuous_const).continuousAt
  have h := continuousAt_of_dominated hFmeas hboundAE hCint hcont
  simpa using h

/-- The time derivative of a smooth spacetime test, in joint-coordinate form. -/
def TimeDependentFourierTest.smoothTestTimePartial (φ : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p (1, 0)

theorem TimeDependentFourierTest.smoothTestTimePartial_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (TimeDependentFourierTest.smoothTestTimePartial φ) := by
  exact (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem TimeDependentFourierTest.smoothTestTimePartial_eq_deriv {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (t : ℝ) (x : Vec 2) :
    TimeDependentFourierTest.smoothTestTimePartial φ (t, x) = deriv (fun s => φ s x) t := by
  have hline : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hcomp :=
    (hφ.differentiable (by norm_num) (t, x)).hasFDerivAt.comp_hasDerivAt t hline
  simpa [TimeDependentFourierTest.smoothTestTimePartial, Function.comp_def] using hcomp.deriv.symm

/-- The time derivative of a smooth spacetime test, as a spacetime function. -/
def spacetimeTestTimeDerivative (φ : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun t x => deriv (fun s => φ s x) t

theorem spacetimeTestTimeDerivative_contDiff {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => spacetimeTestTimeDerivative φ p.1 p.2) := by
  have hfderiv : ContDiff ℝ (⊤ : ℕ∞)
      (fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2)) := hφ.fderiv_right (by norm_num)
  have hEq : (fun p : ℝ × Vec 2 => spacetimeTestTimeDerivative φ p.1 p.2) =
      TimeDependentFourierTest.smoothTestTimePartial φ := by
    funext p
    exact (TimeDependentFourierTest.smoothTestTimePartial_eq_deriv hφ p.1 p.2).symm
  rw [hEq]
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × Vec 2 => (fderiv ℝ
      (fun q : ℝ × Vec 2 => φ q.1 q.2) p) (1, 0))
  exact hfderiv.clm_apply contDiff_const

theorem spacetimeTestTimeDerivative_periodic {φ : ℝ → Vec 2 → ℝ}
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (t : ℝ) :
    AVenhance.IsZ2Periodic (spacetimeTestTimeDerivative φ t) := by
  intro k x
  have hfun : (fun s => φ s (x + AVenhance.latticeShift k)) = fun s => φ s x := by
    funext s
    exact hperiodic s k x
  exact congrArg (fun f : ℝ → ℝ => deriv f t) hfun

/-- The cell coefficient of one ambient real Fourier mode in a time-dependent test. -/
def spacetimeRealFourierCoefficient (φ : ℝ → Vec 2 → ℝ) (N : ℕ)
    (j : Fin (RealFourierDimension N)) (t : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube,
    φ t x * realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x

theorem TimeDependentFourierTest.spacetimeRealFourierCoefficient_eq_projectionCoefficient
    {φ : ℝ → Vec 2 → ℝ}
    (N : ℕ) (j : Fin (RealFourierDimension N)) (t : ℝ) :
    spacetimeRealFourierCoefficient φ N j t =
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (φ t))) j := by
  let m : Vec 2 → ℝ := fun x =>
    realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x
  have hmode := realFourierModeFin_eq_periodicToTorus N j
  have hproduct : (fun y : Torus =>
      AVenhance.Infra.Torus.periodicToTorus
        (fun x => φ t x * m x) y) =
      fun y => AVenhance.Infra.Torus.periodicToTorus (φ t) y *
        realFourierModeFin N j y := by
    funext y
    rw [hmode]
    rfl
  calc
    spacetimeRealFourierCoefficient φ N j t =
        ∫ x in AVenhance.unitCube, φ t x * m x := rfl
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, φ t x * m x :=
      (AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _).symm
    _ = ∫ y : Torus,
        AVenhance.Infra.Torus.periodicToTorus
          (fun x => φ t x * m x) y :=
      (AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell
        (d := 2) (fun x => φ t x * m x)).symm
    _ = ∫ y : Torus,
        AVenhance.Infra.Torus.periodicToTorus (φ t) y *
          realFourierModeFin N j y := by rw [hproduct]
    _ = (modeProjectionCoefficients (RealFourierDimension N)
        (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (φ t))) j := by
          simp [modeProjectionCoefficients]

/-- Differentiation under the cell integral identifies the derivative of a time-dependent
Fourier coefficient with the same coefficient of the time derivative. -/
theorem spacetimeRealFourierCoefficient_deriv
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (N : ℕ) (j : Fin (RealFourierDimension N)) (t : ℝ) :
    deriv (spacetimeRealFourierCoefficient φ N j) t =
      ∫ x in AVenhance.unitCube,
        deriv (fun s => φ s x) t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x := by
  let m : Vec 2 → ℝ := fun x =>
    realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x
  have hmcont : Continuous m := (realFourierModeAmbient_contDiff N
    ((realFourierIndexEquivFin N).symm j)).continuous
  let F : ℝ × Vec 2 → ℝ := fun p => φ p.1 p.2 * m p.2
  let F' : ℝ × Vec 2 → ℝ := fun p => TimeDependentFourierTest.smoothTestTimePartial φ p * m p.2
  have hFcont : Continuous F := hφ.continuous.mul (hmcont.comp continuous_snd)
  have hF'cont : Continuous F' :=
    (TimeDependentFourierTest.smoothTestTimePartial_continuous hφ).mul (hmcont.comp continuous_snd)
  have hFhas : ∀ s, HasDerivAt
      (fun r => ∫ x in AVenhance.unitCube, F (r, x))
      (∫ x in AVenhance.unitCube, F' (s, x)) s := by
    intro s
    let K : Set (ℝ × Vec 2) :=
      Metric.closedBall s 1 ×ˢ TimeDependentFourierTest.timeFourierTestCellClosure
    have hK : IsCompact K := (isCompact_closedBall s 1).prod
      TimeDependentFourierTest.timeFourierTestCellClosure_compact
    have himageBound : Bornology.IsBounded (F' '' K) := hK.image hF'cont |>.isBounded
    obtain ⟨C, hCpos, hC⟩ := himageBound.subset_ball_lt 0 0
    have hbound : ∀ x ∈ TimeDependentFourierTest.timeFourierTestCellClosure, ∀ r ∈ Metric.ball s 1,
        ‖F' (r, x)‖ ≤ C := by
      intro x hx r hr
      have hp : (r, x) ∈ K := ⟨Metric.mem_closedBall.mpr (le_of_lt hr), hx⟩
      have hb := hC ⟨(r, x), hp, rfl⟩
      have hb' : ‖F' (r, x)‖ < C := by
        simpa [Metric.mem_ball, dist_eq_norm] using hb
      exact hb'.le
    have hFmeas : ∀ᶠ r in 𝓝 s,
        AEStronglyMeasurable (fun x => F (r, x))
          (volume.restrict AVenhance.unitCube) := by
      filter_upwards with r
      exact (hFcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hFint : Integrable (fun x => F (s, x))
        (volume.restrict AVenhance.unitCube) := by
      exact bridge_continuous_integrable_cube
        ((hφ.continuous.comp (continuous_const.prodMk continuous_id)).mul hmcont)
    have hF'meas : AEStronglyMeasurable (fun x => F' (s, x))
        (volume.restrict AVenhance.unitCube) := by
      exact (hF'cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hboundAE : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
        ∀ r ∈ Metric.ball s 1, ‖F' (r, x)‖ ≤ C := by
      filter_upwards [ae_restrict_mem TimeDependentFourierTest.timeFourierTestCell_measurable]
          with x hx
      intro r hr
      exact hbound x (TimeDependentFourierTest.timeFourierTestCell_subset_closure hx) r hr
    have hCint : Integrable (fun _ : Vec 2 => C)
        (volume.restrict AVenhance.unitCube) := integrable_const C
    have hdiff : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ r ∈ Metric.ball s 1,
        HasDerivAt (fun q => F (q, x)) (F' (r, x)) r := by
      filter_upwards [ae_restrict_mem TimeDependentFourierTest.timeFourierTestCell_measurable]
          with x _
      intro r _
      have hline : HasDerivAt (fun q : ℝ => (q, x)) (1, 0) r :=
        (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
      have hcompose :=
        (hφ.differentiable (by norm_num) (r, x)).hasFDerivAt.comp_hasDerivAt r hline
      have htime : HasDerivAt (fun q => φ q x) (TimeDependentFourierTest.smoothTestTimePartial φ
          (r, x)) r := by
        simpa [TimeDependentFourierTest.smoothTestTimePartial, Function.comp_def] using hcompose
      simpa [F, F'] using htime.mul_const (m x)
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds s zero_lt_one) hFmeas hFint hF'meas hboundAE hCint hdiff
    simpa [F, F'] using hderiv.2
  have hEq : (fun s => ∫ x in AVenhance.unitCube, F (s, x)) =
      spacetimeRealFourierCoefficient φ N j := by
    funext s
    rfl
  have hderivEq : deriv (spacetimeRealFourierCoefficient φ N j) t =
      ∫ x in AVenhance.unitCube, F' (t, x) := by
    have h := hFhas t
    rw [hEq] at h
    exact h.deriv
  rw [hderivEq]
  apply setIntegral_congr_fun TimeDependentFourierTest.timeFourierTestCell_measurable
  intro x hx
  change TimeDependentFourierTest.smoothTestTimePartial φ (t, x) * m x = _
  rw [TimeDependentFourierTest.smoothTestTimePartial_eq_deriv hφ]

theorem spacetimeRealFourierCoefficient_deriv_eq_timeDerivativeCoefficient
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (N : ℕ) (j : Fin (RealFourierDimension N)) (t : ℝ) :
    deriv (spacetimeRealFourierCoefficient φ N j) t =
      spacetimeRealFourierCoefficient (spacetimeTestTimeDerivative φ) N j t := by
  rw [spacetimeRealFourierCoefficient_deriv hφ]
  rfl

/-- Every time coefficient of the finite spatial Fourier cutoff is continuously differentiable,
and its derivative is the same coefficient applied to the time derivative of the test. -/
theorem spacetimeRealFourierCoefficient_contDiff_one
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (N : ℕ) (j : Fin (RealFourierDimension N)) :
    ContDiff ℝ 1 (spacetimeRealFourierCoefficient φ N j) := by
  let m : Vec 2 → ℝ := fun x =>
    realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x
  have hmcont : Continuous m := (realFourierModeAmbient_contDiff N
    ((realFourierIndexEquivFin N).symm j)).continuous
  let F : ℝ × Vec 2 → ℝ := fun p => φ p.1 p.2 * m p.2
  have hFcont : Continuous F := by
    exact hφ.continuous.mul (hmcont.comp continuous_snd)
  let F' : ℝ × Vec 2 → ℝ := fun p => TimeDependentFourierTest.smoothTestTimePartial φ p * m p.2
  have hF'cont : Continuous F' := by
    exact (TimeDependentFourierTest.smoothTestTimePartial_continuous hφ).mul (hmcont.comp
        continuous_snd)
  have hFhas : ∀ t, HasDerivAt
      (fun s => ∫ x in AVenhance.unitCube, F (s, x))
      (∫ x in AVenhance.unitCube, F' (t, x)) t := by
    intro t
    let K : Set (ℝ × Vec 2) :=
      Metric.closedBall t 1 ×ˢ TimeDependentFourierTest.timeFourierTestCellClosure
    have hK : IsCompact K := (isCompact_closedBall t 1).prod
      TimeDependentFourierTest.timeFourierTestCellClosure_compact
    have himageBound : Bornology.IsBounded (F' '' K) := hK.image hF'cont |>.isBounded
    obtain ⟨C, hCpos, hC⟩ := himageBound.subset_ball_lt 0 0
    have hbound : ∀ x ∈ TimeDependentFourierTest.timeFourierTestCellClosure, ∀ s ∈ Metric.ball t 1,
        ‖F' (s, x)‖ ≤ C := by
      intro x hx s hs
      have hp : (s, x) ∈ K := ⟨Metric.mem_closedBall.mpr (le_of_lt hs), hx⟩
      have hb := hC ⟨(s, x), hp, rfl⟩
      have hb' : ‖F' (s, x)‖ < C := by
        simpa [Metric.mem_ball, dist_eq_norm] using hb
      exact hb'.le
    have hFmeas : ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable (fun x => F (s, x))
          (volume.restrict AVenhance.unitCube) := by
      filter_upwards with s
      exact (hFcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hFint : Integrable (fun x => F (t, x))
        (volume.restrict AVenhance.unitCube) := by
      exact bridge_continuous_integrable_cube
        ((hφ.continuous.comp (continuous_const.prodMk continuous_id)).mul hmcont)
    have hF'meas : AEStronglyMeasurable (fun x => F' (t, x))
        (volume.restrict AVenhance.unitCube) := by
      exact (hF'cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hboundAE : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
        ∀ s ∈ Metric.ball t 1, ‖F' (s, x)‖ ≤ C := by
      filter_upwards [ae_restrict_mem TimeDependentFourierTest.timeFourierTestCell_measurable]
          with x hx
      intro s hs
      exact hbound x (TimeDependentFourierTest.timeFourierTestCell_subset_closure hx) s hs
    have hCint : Integrable (fun _ : Vec 2 => C)
        (volume.restrict AVenhance.unitCube) := integrable_const C
    have hdiff : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ s ∈ Metric.ball t 1,
        HasDerivAt (fun r => F (r, x)) (F' (s, x)) s := by
      filter_upwards [ae_restrict_mem TimeDependentFourierTest.timeFourierTestCell_measurable]
          with x _
      intro s _
      have hline : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
      have hFderiv := (hφ.differentiable (by norm_num) (s, x)).hasFDerivAt
      have hcompose := hFderiv.comp_hasDerivAt s hline
      have htime : HasDerivAt (fun r => φ r x) (TimeDependentFourierTest.smoothTestTimePartial φ
          (s, x)) s := by
        simpa [TimeDependentFourierTest.smoothTestTimePartial, Function.comp_def] using hcompose
      simpa [F, F'] using htime.mul_const (m x)
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds t zero_lt_one) hFmeas hFint hF'meas hboundAE hCint hdiff
    simpa [F, F'] using hderiv.2
  have hEtaContinuous : Continuous (spacetimeRealFourierCoefficient φ N j) := by
    change Continuous (fun t => ∫ x in AVenhance.unitCube, F (t, x))
    exact continuous_cell_integral_of_joint hFcont
  have hEtaDerivContinuous : Continuous (fun t =>
      ∫ x in AVenhance.unitCube, F' (t, x)) :=
    continuous_cell_integral_of_joint hF'cont
  rw [contDiff_one_iff_deriv]
  constructor
  · intro t
    have h := hFhas t
    have hEq : (fun s => ∫ x in AVenhance.unitCube, F (s, x)) =
        spacetimeRealFourierCoefficient φ N j := by
      funext s
      rfl
    rw [hEq] at h
    exact h.differentiableAt
  · have hderivEq : deriv (spacetimeRealFourierCoefficient φ N j) =
        fun t => ∫ x in AVenhance.unitCube, F' (t, x) := by
      funext t
      have h := hFhas t
      have hEq : (fun s => ∫ x in AVenhance.unitCube, F (s, x)) =
          spacetimeRealFourierCoefficient φ N j := by
        funext s
        rfl
      rw [hEq] at h
      exact h.deriv
    rw [hderivEq]
    exact hEtaDerivContinuous

/-- The time-dependent spatial cutoff is the finite Fourier sum with the smooth coefficient
functions defined above. -/
theorem spacetimeTestFourierCutoff_expansion
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t))
    (N : ℕ) (t : ℝ) :
    ∀ x : Vec 2,
      AVenhance.Infra.Section5.testFourierCutoff (φ t) N x =
        ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j t *
            realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
      contDiff_prodMk_right t
    exact hφ.comp hmap
  intro x
  calc
    AVenhance.Infra.Section5.testFourierCutoff (φ t) N x =
        ∑ j : Fin (RealFourierDimension N),
          (modeProjectionCoefficients (RealFourierDimension N)
            (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus (φ t))) j *
            realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x :=
      testFourierCutoff_ambientExpansion_coeff hslice (hperiodic t) N x
    _ = ∑ j : Fin (RealFourierDimension N),
          spacetimeRealFourierCoefficient φ N j t *
            realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← TimeDependentFourierTest.spacetimeRealFourierCoefficient_eq_projectionCoefficient]

/-- Differentiating a time-dependent spatial cutoff differentiates only its finite scalar
coefficients. -/
theorem spacetimeTestFourierCutoff_timeDerivative
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t))
    (N : ℕ) (t : ℝ) (x : Vec 2) :
    deriv (fun s => AVenhance.Infra.Section5.testFourierCutoff (φ s) N x) t =
      ∑ j : Fin (RealFourierDimension N),
        deriv (spacetimeRealFourierCoefficient φ N j) t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x := by
  let term : Fin (RealFourierDimension N) → ℝ → ℝ := fun j s =>
    spacetimeRealFourierCoefficient φ N j s *
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x
  have hfunction : (fun s => AVenhance.Infra.Section5.testFourierCutoff (φ s) N x) =
      fun s => ∑ j : Fin (RealFourierDimension N), term j s := by
    funext s
    simpa [term] using spacetimeTestFourierCutoff_expansion hφ hperiodic N s x
  have hsum : HasDerivAt (fun s => ∑ j : Fin (RealFourierDimension N), term j s)
      (∑ j : Fin (RealFourierDimension N),
        deriv (spacetimeRealFourierCoefficient φ N j) t *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact ((spacetimeRealFourierCoefficient_contDiff_one hφ N j).differentiable
      (by norm_num) t).hasDerivAt.mul_const
        (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x)
  have hderiv := congrArg (fun f : ℝ → ℝ => deriv f t) hfunction
  rw [hsum.deriv] at hderiv
  simpa [term] using hderiv

theorem spacetimeTestFourierCutoff_timeDerivative_eq_spatialCutoff
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t))
    (N : ℕ) (t : ℝ) (x : Vec 2) :
    deriv (fun s => AVenhance.Infra.Section5.testFourierCutoff (φ s) N x) t =
      AVenhance.Infra.Section5.testFourierCutoff
        (spacetimeTestTimeDerivative φ t) N x := by
  rw [spacetimeTestFourierCutoff_timeDerivative hφ hperiodic]
  simp_rw [spacetimeRealFourierCoefficient_deriv_eq_timeDerivativeCoefficient hφ]
  exact (spacetimeTestFourierCutoff_expansion
    (spacetimeTestTimeDerivative_contDiff hφ)
    (spacetimeTestTimeDerivative_periodic hperiodic) N t x).symm

/-- Terminal vanishing of a test is retained by every spatial Fourier coefficient. -/
theorem spacetimeRealFourierCoefficient_terminal
    {φ : ℝ → Vec 2 → ℝ} (hterminal : ∀ x, φ 1 x = 0)
    (N : ℕ) (j : Fin (RealFourierDimension N)) :
    spacetimeRealFourierCoefficient φ N j 1 = 0 := by
  simp [spacetimeRealFourierCoefficient, hterminal]

/-- Every time coefficient of a smooth spacetime test is smooth in time. Repeated differentiation
commutes with its cell Fourier integral. -/
theorem spacetimeRealFourierCoefficient_contDiff
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (N : ℕ) (j : Fin (RealFourierDimension N)) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeRealFourierCoefficient φ N j) := by
  have hnat : ∀ n : ℕ, ∀ ψ : ℝ → Vec 2 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2) →
      ContDiff ℝ n (spacetimeRealFourierCoefficient ψ N j) := by
    intro n
    induction n with
    | zero =>
        intro ψ hψ
        exact (spacetimeRealFourierCoefficient_contDiff_one hψ N j).of_le (by norm_num)
    | succ n ih =>
        intro ψ hψ
        change ContDiff ℝ ((n : ℕ∞) + 1)
          (spacetimeRealFourierCoefficient ψ N j)
        rw [contDiff_succ_iff_deriv]
        refine ⟨(spacetimeRealFourierCoefficient_contDiff_one hψ N j).differentiable
          (by norm_num), ?_, ?_⟩
        · intro hn
          exact False.elim (by simp at hn)
        · have hderiv : deriv (spacetimeRealFourierCoefficient ψ N j) =
              spacetimeRealFourierCoefficient (spacetimeTestTimeDerivative ψ) N j := by
            funext t
            exact spacetimeRealFourierCoefficient_deriv_eq_timeDerivativeCoefficient
              hψ N j t
          rw [hderiv]
          exact ih (spacetimeTestTimeDerivative ψ)
            (spacetimeTestTimeDerivative_contDiff hψ)
  rw [contDiff_iff_forall_nat_le]
  intro n hn
  exact hnat n φ hφ

/-- The joint time-space Fourier cutoff of a smooth periodic spacetime test is itself smooth. -/
theorem spacetimeTestFourierCutoff_contDiff_top
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) := by
  let sumFun : ℝ × Vec 2 → ℝ := fun p =>
    ∑ j : Fin (RealFourierDimension N),
      spacetimeRealFourierCoefficient φ N j p.1 *
        realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) p.2
  have hterm (j : Fin (RealFourierDimension N)) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        spacetimeRealFourierCoefficient φ N j p.1 *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) p.2) := by
    let m : Vec 2 → ℝ :=
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)
    have hm : ContDiff ℝ (↑(⊤ : ℕ∞)) m := by
      exact (realFourierModeAmbient_contDiff N
        ((realFourierIndexEquivFin N).symm j)).of_le (by simp)
    have hproj : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun p : ℝ × Vec 2 => p.2) := contDiff_snd
    have hmode : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
        m p.2) := by
      simpa only [Function.comp_def] using hm.comp hproj
    exact (spacetimeRealFourierCoefficient_contDiff hφ N j).comp contDiff_fst |>.mul
      (by simpa only [Function.comp_def] using hmode)
  have hsum : ContDiff ℝ (⊤ : ℕ∞) sumFun := by
    unfold sumFun
    exact ContDiff.sum (fun j _ => hterm j)
  have heq (p : ℝ × Vec 2) :
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2 = sumFun p := by
    simpa [sumFun] using spacetimeTestFourierCutoff_expansion hφ hperiodic N p.1 p.2
  have hfun : (fun p : ℝ × Vec 2 =>
      AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) = sumFun := by
    funext p
    exact heq p
  rw [hfun]
  exact hsum

end AVenhance.Infra.Parabolic.FourierGalerkin

end
