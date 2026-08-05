/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.NormalizationClosure
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Parameterized analytic division

This file develops the several-variable Hadamard-division input needed by Poincaré's
normalization.  The homotopy `(mass, phase) ↦ (t * mass, phase)` reduces division by the mass
coordinate to integration of the mass partial derivative along `0 ≤ t ≤ 1`.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody
open TopologicalSpace
open scoped Interval

abbrev ParameterPhase := ℝ × PhaseSpace

/-- Scale the mass coordinate while leaving every phase coordinate fixed. -/
def massScale (t : ℝ) : ParameterPhase →L[ℝ] ParameterPhase :=
  (t • ContinuousLinearMap.fst ℝ ℝ PhaseSpace).prod
    (ContinuousLinearMap.snd ℝ ℝ PhaseSpace)

@[simp] theorem massScale_apply (t : ℝ) (z : ℝ × PhaseSpace) :
    massScale t z = (t * z.1, z.2) := by
  simp [massScale]

theorem continuous_massScale : Continuous massScale := by
  change Continuous (fun t ↦
    ContinuousLinearMap.prodₗᵢ ℝ
      (t • ContinuousLinearMap.fst ℝ ℝ PhaseSpace,
        ContinuousLinearMap.snd ℝ ℝ PhaseSpace))
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
    ((continuous_id.smul continuous_const).prodMk continuous_const)

/-- The distinguished unit direction in the mass coordinate. -/
def massDirection : ParameterPhase := (1, 0)

@[simp] theorem massDirection_fst : massDirection.1 = 1 := rfl

@[simp] theorem massDirection_snd : massDirection.2 = 0 := rfl

@[simp] theorem norm_massDirection : ‖massDirection‖ = 1 := by
  simp [massDirection, Prod.norm_def]

/-- On the unit interval, the mass-scaling homotopy is norm nonexpanding. -/
theorem norm_massScale_le_one {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖massScale t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  rw [massScale_apply]
  simp only [Prod.norm_def, Real.norm_eq_abs]
  rw [abs_mul]
  have habs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  simpa only [one_mul] using
    (max_le
      ((mul_le_mul_of_nonneg_right habs (abs_nonneg z.1)).trans
        (le_max_left _ _))
      (le_max_right _ _))

/-- The power series of the mass partial derivative after applying the mass-scaling homotopy to
its input variables. -/
noncomputable def massPartialSeries
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ) (t : ℝ) :
    FormalMultilinearSeries ℝ ParameterPhase ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ massDirection).compFormalMultilinearSeries
    (p.derivSeries.compContinuousLinearMap (massScale t))

theorem massPartialSeries_apply
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ) (t : ℝ)
    (n : ℕ) (v : Fin n → ParameterPhase) :
    massPartialSeries p t n v =
      p.derivSeries n (fun i ↦ massScale t (v i)) massDirection :=
  rfl

theorem continuous_massPartialSeries_coeff
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ) (n : ℕ) :
    Continuous (fun t ↦ massPartialSeries p t n) := by
  have hmaps : Continuous (fun t ↦
      (fun _ : Fin n ↦ massScale t)) :=
    continuous_pi (fun _ ↦ continuous_massScale)
  have hcomposition : Continuous (fun maps : Fin n →
      (ParameterPhase →L[ℝ] ParameterPhase) ↦
      (p.derivSeries n).compContinuousLinearMap maps) := by
    exact (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin n ↦ ParameterPhase) (fun _ : Fin n ↦ ParameterPhase)
        (ParameterPhase →L[ℝ] ℝ)).cont.clm_apply continuous_const
  have hcomp : Continuous (fun t ↦
      (p.derivSeries n).compContinuousLinearMap
        (fun _ : Fin n ↦ massScale t)) :=
    hcomposition.comp hmaps
  change Continuous (fun t ↦
    (ContinuousLinearMap.apply ℝ ℝ massDirection).compContinuousMultilinearMap
      ((p.derivSeries n).compContinuousLinearMap
        (fun _ : Fin n ↦ massScale t)))
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin n ↦ ParameterPhase) (ParameterPhase →L[ℝ] ℝ) ℝ)
      (ContinuousLinearMap.apply ℝ ℝ massDirection)).continuous.comp hcomp

/-- One evaluated coefficient, bundled as a continuous function of the homotopy parameter. -/
noncomputable def massPartialTerm
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ)
    (x : ParameterPhase) (n : ℕ) : C(ℝ, ℝ) where
  toFun t := massPartialSeries p t n (fun _ ↦ x)
  continuous_toFun :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ ParameterPhase) ℝ
      (fun _ ↦ x)).continuous.comp (continuous_massPartialSeries_coeff p n)

@[simp] theorem massPartialTerm_apply
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ)
    (x : ParameterPhase) (n : ℕ) (t : ℝ) :
    massPartialTerm p x n t = massPartialSeries p t n (fun _ ↦ x) :=
  rfl

def unitIntervalCompact : Compacts ℝ :=
  ⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩

noncomputable def massPartialTermUnit
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ)
    (x : ParameterPhase) (n : ℕ) : C(unitIntervalCompact, ℝ) :=
  (massPartialTerm p x n).restrict unitIntervalCompact

/-- Uniform coefficient bound along the unit homotopy interval. -/
theorem norm_massPartialSeries_le
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ) (n : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖massPartialSeries p t n‖ ≤ ‖p.derivSeries n‖ := by
  have heval : ‖ContinuousLinearMap.apply ℝ ℝ massDirection‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro derivative
    simpa using derivative.le_opNorm massDirection
  have hscale := FormalMultilinearSeries.norm_compContinuousLinearMap_le
    p.derivSeries (massScale t) n
  calc
    ‖massPartialSeries p t n‖ ≤
        ‖ContinuousLinearMap.apply ℝ ℝ massDirection‖ *
          ‖p.derivSeries.compContinuousLinearMap (massScale t) n‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖p.derivSeries.compContinuousLinearMap (massScale t) n‖ := by
      gcongr
    _ ≤ 1 * (‖p.derivSeries n‖ * ‖massScale t‖ ^ n) := by
      gcongr
    _ ≤ ‖p.derivSeries n‖ := by
      rw [one_mul]
      calc
        ‖p.derivSeries n‖ * ‖massScale t‖ ^ n ≤
            ‖p.derivSeries n‖ * 1 ^ n := by
          gcongr
          exact norm_massScale_le_one ht
        _ = ‖p.derivSeries n‖ := by simp

theorem norm_massPartialTerm_restrict_le
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ)
    (x : ParameterPhase) (n : ℕ) :
    ‖massPartialTermUnit p x n‖ ≤
      ‖p.derivSeries n‖ * ‖x‖ ^ n := by
  apply (ContinuousMap.norm_le
    (f := massPartialTermUnit p x n)
    (mul_nonneg (norm_nonneg (p.derivSeries n))
      (pow_nonneg (norm_nonneg x) n))).2
  intro t
  change ‖massPartialSeries p t.1 n (fun _ ↦ x)‖ ≤ _
  calc
    ‖massPartialSeries p t.1 n (fun _ ↦ x)‖ ≤
        ‖massPartialSeries p t.1 n‖ * ‖x‖ ^ n := by
      simpa using (massPartialSeries p t.1 n).le_opNorm (fun _ ↦ x)
    _ ≤ ‖p.derivSeries n‖ * ‖x‖ ^ n := by
      gcongr
      apply norm_massPartialSeries_le p n
      have ht : (t.1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := t.2
      rwa [Set.uIcc_of_le zero_le_one] at ht

theorem summable_norm_massPartialTerm_restrict
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ)
    {x : ParameterPhase} (hx : x ∈ Metric.eball (0 : ParameterPhase) p.derivSeries.radius) :
    Summable (fun n ↦ ‖massPartialTermUnit p x n‖) := by
  have hradius : ENNReal.ofNNReal ‖x‖₊ < p.derivSeries.radius := by
    simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hx
  have hs : Summable (fun n : ℕ ↦ ‖p.derivSeries n‖ * ‖x‖ ^ n) := by
    simpa using p.derivSeries.summable_norm_mul_pow hradius
  exact hs.of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_massPartialTerm_restrict_le p x n)

/-- Integrating the mass-partial series along the scaling homotopy gives the formal series for
the removable mass quotient. -/
noncomputable def integratedMassPartialSeries
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ) :
    FormalMultilinearSeries ℝ ParameterPhase ℝ :=
  fun n ↦ ∫ t in (0 : ℝ)..1, massPartialSeries p t n

theorem integratedMassPartialSeries_apply
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ)
    (n : ℕ) (v : Fin n → ParameterPhase) :
    integratedMassPartialSeries p n v =
      ∫ t in (0 : ℝ)..1, massPartialSeries p t n v := by
  unfold integratedMassPartialSeries
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ ParameterPhase) ℝ v
    |>.intervalIntegral_comp_comm
      ((continuous_massPartialSeries_coeff p n).intervalIntegrable 0 1)).symm

theorem hasSum_integratedMassPartialSeries
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ)
    {x : ParameterPhase} (hx : x ∈ Metric.eball (0 : ParameterPhase) p.derivSeries.radius) :
    HasSum
      (fun n ↦ integratedMassPartialSeries p n (fun _ ↦ x))
      (∫ t in (0 : ℝ)..1, ∑' n, massPartialTerm p x n t) := by
  have hsum := intervalIntegral.hasSum_intervalIntegral_of_summable_norm
    (a := (0 : ℝ)) (b := 1) (f := fun n ↦ massPartialTerm p x n)
    (summable_norm_massPartialTerm_restrict p hx)
  simpa only [integratedMassPartialSeries_apply, massPartialTerm_apply] using hsum

/-- Homotopy formula for the removable quotient: integrate the mass partial derivative from the
zero-mass slice to the requested mass while keeping the phase coordinates fixed. -/
noncomputable def parameterizedMassIntegral
    (f : ParameterPhase → ℝ) (base z : ParameterPhase) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    fderiv ℝ f (base + massScale t (z - base)) massDirection

theorem HasFPowerSeriesOnBall.tsum_massPartialTerm_eq_massDerivative
    {f : ParameterPhase → ℝ} {p : FormalMultilinearSeries ℝ ParameterPhase ℝ}
    {base : ParameterPhase} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p base r)
    {x : ParameterPhase} (hx : x ∈ Metric.eball (0 : ParameterPhase) r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑' n, massPartialTerm p x n t =
      fderiv ℝ f (base + massScale t x) massDirection := by
  have hnorm : ‖massScale t x‖ ≤ ‖x‖ := by
    calc
      ‖massScale t x‖ ≤ ‖massScale t‖ * ‖x‖ := (massScale t).le_opNorm x
      _ ≤ 1 * ‖x‖ := by
        gcongr
        exact norm_massScale_le_one ht
      _ = ‖x‖ := one_mul _
  have hy : massScale t x ∈ Metric.eball (0 : ParameterPhase) r := by
    rw [Metric.mem_eball, edist_zero_right] at hx ⊢
    exact lt_of_le_of_lt (by
      simpa only [enorm_eq_nnnorm, ENNReal.coe_le_coe] using (show ‖massScale t x‖₊ ≤ ‖x‖₊ by
        exact_mod_cast hnorm)) hx
  have hsum := (hp.fderiv.hasSum hy).mapL
    (ContinuousLinearMap.apply ℝ ℝ massDirection)
  simpa only [massPartialTerm_apply, massPartialSeries_apply,
    ContinuousLinearMap.apply_apply] using hsum.tsum_eq

theorem HasFPowerSeriesOnBall.hasSum_parameterizedMassIntegral
    {f : ParameterPhase → ℝ} {p : FormalMultilinearSeries ℝ ParameterPhase ℝ}
    {base : ParameterPhase} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p base r)
    {x : ParameterPhase} (hx : x ∈ Metric.eball (0 : ParameterPhase) r) :
    HasSum
      (fun n ↦ integratedMassPartialSeries p n (fun _ ↦ x))
      (parameterizedMassIntegral f base (base + x)) := by
  have hxderiv : x ∈ Metric.eball (0 : ParameterPhase) p.derivSeries.radius :=
    by
      rw [Metric.mem_eball] at hx ⊢
      exact hx.trans_le (hp.r_le.trans p.radius_le_radius_derivSeries)
  have hsum := hasSum_integratedMassPartialSeries p hxderiv
  have hintegral :
      (∫ t in (0 : ℝ)..1, ∑' n, massPartialTerm p x n t) =
        parameterizedMassIntegral f base (base + x) := by
    unfold parameterizedMassIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    change (∑' n, massPartialTerm p x n t) =
      fderiv ℝ f (base + massScale t (base + x - base)) massDirection
    rw [HasFPowerSeriesOnBall.tsum_massPartialTerm_eq_massDerivative hp hx]
    · congr 3
      abel
    · rw [← Set.uIcc_of_le zero_le_one]
      exact ht
  rwa [hintegral] at hsum

/-- Integration over the unit interval does not reduce the convergence radius supplied by the
derivative series. -/
theorem norm_integratedMassPartialSeries_le
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ) (n : ℕ) :
    ‖integratedMassPartialSeries p n‖ ≤ ‖p.derivSeries n‖ := by
  unfold integratedMassPartialSeries
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t ↦ massPartialSeries p t n)
    (C := ‖p.derivSeries n‖) (a := (0 : ℝ)) (b := 1) (fun t ht ↦ by
      apply norm_massPartialSeries_le p n
      rw [← Set.uIcc_of_le zero_le_one]
      exact Set.uIoc_subset_uIcc ht)
  simpa using hbound

theorem derivSeries_radius_le_integratedMassPartialSeries_radius
    (p : FormalMultilinearSeries ℝ ParameterPhase ℝ) :
    p.derivSeries.radius ≤ (integratedMassPartialSeries p).radius :=
  FormalMultilinearSeries.radius_le_of_le
    (fun n ↦ norm_integratedMassPartialSeries_le p n)

/-- The homotopy integral has the integrated derivative series as a genuine power series on the
same ball as the original analytic function. -/
theorem HasFPowerSeriesOnBall.parameterizedMassIntegral
    {f : ParameterPhase → ℝ} {p : FormalMultilinearSeries ℝ ParameterPhase ℝ}
    {base : ParameterPhase} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p base r) :
    HasFPowerSeriesOnBall (parameterizedMassIntegral f base)
      (integratedMassPartialSeries p) base r where
  r_le := hp.r_le.trans <| p.radius_le_radius_derivSeries.trans <|
    derivSeries_radius_le_integratedMassPartialSeries_radius p
  r_pos := hp.r_pos
  hasSum := HasFPowerSeriesOnBall.hasSum_parameterizedMassIntegral hp

/-- Parameterized analytic Hadamard lemma in integral form. -/
theorem AnalyticAt.analyticAt_parameterizedMassIntegral
    {f : ParameterPhase → ℝ} {base : ParameterPhase}
    (hf : AnalyticAt ℝ f base) :
    AnalyticAt ℝ (parameterizedMassIntegral f base) base := by
  rcases hf with ⟨p, r, hp⟩
  exact ⟨integratedMassPartialSeries p, r,
    HasFPowerSeriesOnBall.parameterizedMassIntegral hp⟩

/-- The derivative of a mass slice is the joint derivative in the pure mass direction. -/
theorem deriv_curry_left_at
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : ℝ × B → ℝ} {mass : ℝ} {b : B}
    (hG : DifferentiableAt ℝ G (mass, b)) :
    deriv (fun m ↦ G (m, b)) mass = fderiv ℝ G (mass, b) (1, 0) := by
  have hembedding := hasFDerivAt_prodMk_left (𝕜 := ℝ) mass b
  have hcomposition := hG.hasFDerivAt.comp mass hembedding
  have hderivative := hcomposition.fderiv
  change fderiv ℝ (G ∘ fun m ↦ (m, b)) mass 1 = _
  rw [hderivative]
  rfl

/-- Fundamental-theorem identity behind parameterized division. -/
theorem HasFPowerSeriesOnBall.mass_mul_parameterizedMassIntegral
    {f : ParameterPhase → ℝ} {p : FormalMultilinearSeries ℝ ParameterPhase ℝ}
    {baseState : PhaseSpace} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p (0, baseState) r)
    {x : ParameterPhase} (hx : x ∈ Metric.eball (0 : ParameterPhase) r) :
    x.1 * LeanPool.PoincareThreeBody.parameterizedMassIntegral
        f (0, baseState) ((0, baseState) + x) =
      f ((0, baseState) + x) - f ((0, baseState) + (0, x.2)) := by
  let g : ℝ → ℝ := fun mass ↦ f (mass, baseState + x.2)
  let g' : ℝ → ℝ := fun mass ↦
    fderiv ℝ f (mass, baseState + x.2) massDirection
  have hpath (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (0, baseState) + massScale t x ∈ Metric.eball (0, baseState) r := by
    have hnorm : ‖massScale t x‖ ≤ ‖x‖ := by
      calc
        ‖massScale t x‖ ≤ ‖massScale t‖ * ‖x‖ := (massScale t).le_opNorm x
        _ ≤ 1 * ‖x‖ := by
          gcongr
          exact norm_massScale_le_one ht
        _ = ‖x‖ := one_mul _
    rw [Metric.mem_eball, edist_eq_enorm_sub] at hx ⊢
    apply lt_of_le_of_lt _ hx
    simpa only [add_sub_cancel_left, sub_zero, enorm_eq_nnnorm, ENNReal.coe_le_coe] using
      (show ‖massScale t x‖₊ ≤ ‖x‖₊ by exact_mod_cast hnorm)
  have hcurve : Continuous (fun t : ℝ ↦ (0, baseState) + massScale t x) := by
    exact continuous_const.add (continuous_massScale.clm_apply continuous_const)
  have hmaps : Set.MapsTo (fun t : ℝ ↦ (0, baseState) + massScale t x)
      (Set.Icc 0 1) (Metric.eball (0, baseState) r) := hpath
  have hderivativeContinuous : ContinuousOn
      (fun t : ℝ ↦ fderiv ℝ f ((0, baseState) + massScale t x) massDirection)
      (Set.Icc 0 1) := by
    have hcomposed : ContinuousOn
        (fun t : ℝ ↦ fderiv ℝ f ((0, baseState) + massScale t x)) (Set.Icc 0 1) :=
      hp.fderiv.continuousOn.comp hcurve.continuousOn hmaps
    exact hcomposed.clm_apply continuousOn_const
  have hderivative (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt g (g' (t * x.1)) (t * x.1) := by
    have hpoint := hpath t ht
    have hpoint' : (t * x.1, baseState + x.2) ∈ Metric.eball (0, baseState) r := by
      simpa only [massScale_apply, Prod.mk_add_mk, zero_add] using hpoint
    have hjoint : AnalyticAt ℝ f (t * x.1, baseState + x.2) :=
      hp.analyticAt_of_mem hpoint'
    have hslice : AnalyticAt ℝ g (t * x.1) := by
      exact hjoint.comp (f := fun mass : ℝ ↦ (mass, baseState + x.2))
        (analyticAt_id.prod analyticAt_const)
    apply hslice.differentiableAt.hasDerivAt.congr_deriv
    simpa only [g', massDirection] using
      (deriv_curry_left_at (G := f) hjoint.differentiableAt)
  have hfundamental := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f := g) (f' := g') (z₀ := (0 : ℝ)) (z₁ := x.1)
    (by
      simpa only [g', zero_add, smul_eq_mul, massScale_apply, Prod.mk_add_mk]
        using hderivativeContinuous)
    (by intro t ht; simpa only [zero_add, smul_eq_mul] using hderivative t ht)
  have hbase_add_x : (0, baseState) + x = (x.1, baseState + x.2) := by
    ext <;> simp
  unfold LeanPool.PoincareThreeBody.parameterizedMassIntegral
  rw [hbase_add_x]
  simpa only [g, g', zero_add, zero_smul, one_smul, smul_eq_mul,
    massScale_apply, Prod.mk_add_mk, Prod.mk_sub_mk, sub_zero,
    add_sub_cancel_left] using hfundamental

/-- The parameterized integral supplies the removable analytic extension of the normalized
residual at every collision-free point of the mass-zero slice. -/
theorem analyticAt_uncurry_domainMassNormalizedCandidate_mass_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (henergy : ∀ energy, AnalyticAt ℝ energyFunction energy)
    (hcancel : ∀ state, (0, state) ∈ collisionFree →
      F 0 state = energyFunction (hamiltonian 0 state))
    {state : PhaseSpace} (hcollision : (0, state) ∈ collisionFree) :
    AnalyticAt ℝ
      (Function.uncurry (domainMassNormalizedCandidate F energyFunction)) (0, state) := by
  let residual : ParameterPhase → ℝ :=
    Function.uncurry (normalizationResidual F energyFunction)
  have hbaseDomain : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hresidual : AnalyticAt ℝ residual (0, state) := by
    exact (hanalytic (0, state) hbaseDomain).sub
      ((henergy (hamiltonian 0 state)).comp
        (f := Function.uncurry hamiltonian) (hamiltonian_analyticAt hcollision))
  rcases hresidual with ⟨p, r, hp⟩
  have hintegral : AnalyticAt ℝ
      (parameterizedMassIntegral residual (0, state)) (0, state) :=
    AnalyticAt.analyticAt_parameterizedMassIntegral ⟨p, r, hp⟩
  apply hintegral.congr
  have hball : ∀ᶠ z in nhds (0, state),
      z - (0, state) ∈ Metric.eball (0 : ParameterPhase) r := by
    filter_upwards [Metric.eball_mem_nhds (0, state) hp.r_pos] with z hz
    rw [Metric.mem_eball, edist_eq_enorm_sub] at hz ⊢
    simpa only [sub_zero] using hz
  have hfirst : ∀ᶠ z in nhds ((0 : ℝ), state),
      firstPrimaryDistanceSq 0 z.2 ≠ 0 := by
    exact (show ContinuousAt
      (fun z : ParameterPhase ↦ firstPrimaryDistanceSq 0 z.2) ((0 : ℝ), state) by
        simp only [firstPrimaryDistanceSq]
        fun_prop).eventually_ne hcollision.1
  have hsecond : ∀ᶠ z in nhds ((0 : ℝ), state),
      secondPrimaryDistanceSq 0 z.2 ≠ 0 := by
    exact (show ContinuousAt
      (fun z : ParameterPhase ↦ secondPrimaryDistanceSq 0 z.2) ((0 : ℝ), state) by
        simp only [secondPrimaryDistanceSq]
        fun_prop).eventually_ne hcollision.2
  filter_upwards [hball, hfirst, hsecond] with z hzBall hzFirst hzSecond
  have hzCollision : (0, z.2) ∈ collisionFree := ⟨hzFirst, hzSecond⟩
  have hresidualZero : residual (0, z.2) = 0 := by
    simp only [residual, Function.uncurry_apply_pair, normalizationResidual,
      hcancel z.2 hzCollision, sub_self]
  have hmul := HasFPowerSeriesOnBall.mass_mul_parameterizedMassIntegral
    hp hzBall
  have hrestore : (0, state) + (z - (0, state)) = z := by
    abel
  have hzeroRestore : ((0 : ℝ), state) + (0, (z - (0, state)).2) = (0, z.2) := by
    apply Prod.ext
    · simp
    · simp only [Prod.snd_add, Prod.snd_sub]
      abel
  have hresidualZeroRestore :
      residual ((0, state) + (0, (z - (0, state)).2)) = 0 := by
    exact (congrArg residual hzeroRestore).trans hresidualZero
  have hmul' : z.1 * parameterizedMassIntegral residual (0, state) z = residual z := by
    rw [hrestore, hresidualZeroRestore, sub_zero] at hmul
    simpa only [Prod.fst_sub, sub_zero] using hmul
  by_cases hmass : z.1 = 0
  · rcases z with ⟨mass, phase⟩
    simp only at hmass
    subst mass
    have hzDomain : (0, phase) ∈ parameterDomain δ :=
      ⟨by simpa using hδ, hzCollision⟩
    rw [Function.uncurry_apply_pair, domainMassNormalizedCandidate_zero,
      massNormalizedCandidate_zero_eq_parameterCoefficient
        hanalytic hzDomain (henergy (hamiltonian 0 phase))]
    unfold parameterizedMassIntegral parameterCoefficient
    have hstate : state + (phase - state) = phase := by abel
    simp only [Prod.mk_sub_mk, sub_zero, massScale_apply, mul_zero,
      Prod.mk_add_mk, zero_add, hstate, massDirection,
      intervalIntegral.integral_const, sub_zero, one_smul]
    rfl
  · rw [Function.uncurry_apply_pair,
      domainMassNormalizedCandidate_eq_div hmass]
    apply (eq_div_iff hmass).2
    change parameterizedMassIntegral residual (0, state) z * z.1 = residual z
    simpa only [mul_comm] using hmul'

/-- Analytic Hadamard division by the mass parameter, with cancellation required only on the
actual collision-free mass-zero domain. -/
theorem jointAnalyticMassDivisionPrinciple : JointAnalyticMassDivisionPrinciple := by
  rw [jointAnalyticMassDivisionPrinciple_iff_massZero]
  intro δ F energyFunction hδ hanalytic henergy hcancel state hcollision
  exact analyticAt_uncurry_domainMassNormalizedCandidate_mass_zero
    hδ hanalytic henergy hcancel hcollision

end LeanPool.PoincareThreeBody
