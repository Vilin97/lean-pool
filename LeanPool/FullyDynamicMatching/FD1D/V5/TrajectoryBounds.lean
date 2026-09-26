/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.InitialProcess
public import LeanPool.FullyDynamicMatching.FD1D.V5.CostBounds

/-! # Trajectory Bounds -/

@[expose] public section

namespace FD1D.V5.ContinuousProcess

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal ProbabilityTheory Topology

variable {L m : ℕ}

/-- Cauchy--Schwarz converts the concrete one-period second moment into an
upper bound for its expected distance. -/
theorem expected_cost_le_sqrt_expected_squared_cost
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedCost (L := L) a hm fallback t ≤
      Real.sqrt (trajectoryExpectedSquaredCost (L := L) a hm fallback t) := by
  let P := trajectoryLaw (L := L) a fallback
  let f : (ℕ → ProcessState m) → ℝ := fun path =>
    processCost L a (SupplyConfiguration.canonicalFallback hm) (path t)
  have hf_nonneg : 0 ≤ᵐ[P] f := by
    filter_upwards with path
    exact processCost_nonneg L a
      (SupplyConfiguration.canonicalFallback hm) (path t)
  have h1_nonneg :
      0 ≤ᵐ[P] (fun _ : ℕ → ProcessState m => (1 : ℝ)) :=
    Filter.Eventually.of_forall (fun _ => by norm_num)
  have hf : MemLp f (ENNReal.ofReal 2) P := by
    apply MemLp.of_bound
      ((processCost_measurable L a
        (SupplyConfiguration.canonicalFallback hm)).comp
          (measurable_pi_apply t)).aestronglyMeasurable 1
    filter_upwards with path
    change |f path| ≤ 1
    rw [abs_of_nonneg (processCost_nonneg L a
      (SupplyConfiguration.canonicalFallback hm) (path t))]
    exact processCost_le_one L a
      (SupplyConfiguration.canonicalFallback hm) (path t)
  have h1 : MemLp (fun _ : ℕ → ProcessState m => (1 : ℝ))
      (ENNReal.ofReal 2) P := by
    apply MemLp.of_bound measurable_const.aestronglyMeasurable 1
    simp
  have hpq : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    hf_nonneg h1_nonneg hf h1
  unfold trajectoryExpectedCost trajectoryExpectedSquaredCost
  simp_rw [processSquaredCost_eq_sq]
  change (∫ path, f path ∂P) ≤ Real.sqrt (∫ path, f path ^ 2 ∂P)
  simpa only [mul_one, one_pow, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul, one_div,
    OfNat.ofNat_eq_ofNat, invOf_eq_inv, Real.sqrt_eq_rpow,
    Real.one_rpow, Real.rpow_natCast, Real.rpow_two] using h

theorem trajectoryExpectedSquaredCost_nonneg
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) :
    0 ≤ trajectoryExpectedSquaredCost (L := L) a hm fallback t := by
  unfold trajectoryExpectedSquaredCost
  exact integral_nonneg fun path =>
    processSquaredCost_nonneg L a
      (SupplyConfiguration.canonicalFallback hm) (path t)

/-- The iid spatial initialization projects the concrete squared cost to the
refreshed finite count chain. -/
theorem trajectoryExpectedSquaredCost_le_refreshedEnvelope
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedSquaredCost (L := L) a hm fallback t ≤
      ((Dynamics.kernel (L := L) (m := m) a ha hm).iterate t
        (refreshedLaw L m)).expect
          (Transport.stateSquaredCostEnvelope a) := by
  exact trajectoryExpectedSquaredCostFrom_le_envelope
    (initialSpatialLaw m) (refreshedLaw L m)
    (map_spatialCount_initialSpatialLaw L m)
    a ha hm fallback t

/-- Per-period RMS cost of the parameterized policy from a fixed arbitrary
initial inventory. -/
def trajectoryRMSCostFromState
    (m : ℕ) (hm : 1 ≤ m) (s₀ : SpatialState m) (t : ℕ) : ℝ :=
  Real.sqrt
    (trajectoryExpectedSquaredCostFromState
      (L := treeDepth m) s₀ (parameterA m : ℝ) (by omega)
      (SupplyConfiguration.canonicalFallback (by omega)) t)

theorem trajectoryRMSCostFromState_le_envelope
    {m : ℕ} (hm : 1 ≤ m) (s₀ : SpatialState m) (t : ℕ) :
    trajectoryRMSCostFromState m hm s₀ t ≤
      rmsSquaredCostExpectation m hm
        (FiniteLaw.dirac (spatialCount (treeDepth m) s₀)) t := by
  unfold trajectoryRMSCostFromState rmsSquaredCostExpectation
  rw [show parameterizedSquaredCostEnvelope m =
    Transport.stateSquaredCostEnvelope (parameterA m : ℝ) by rfl]
  apply Real.sqrt_le_sqrt
  simpa [parameterizedKernel] using
    (trajectoryExpectedSquaredCostFromState_le_envelope
      (L := treeDepth m) s₀ (parameterA m : ℝ)
      (parameterA_cast_pos hm) (by omega)
      (SupplyConfiguration.canonicalFallback (by omega)) t)

/-- Manuscript part (i), with the explicit proof constant `8.5`. -/
theorem limsup_trajectoryRMSCostFromState_le
    {m : ℕ} (hm : 1 ≤ m) (s₀ : SpatialState m) :
    Filter.limsup (trajectoryRMSCostFromState m hm s₀) atTop ≤
      (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
  let mu0 := FiniteLaw.dirac (spatialCount (treeDepth m) s₀)
  obtain ⟨pi, _hpi, hconv, hstationary⟩ :=
    exists_stationary_rmsSquaredCost_tendsto hm mu0
  have hx_cobounded :
      atTop.IsCoboundedUnder (· ≤ ·)
        (trajectoryRMSCostFromState m hm s₀) :=
    Filter.isCoboundedUnder_le_of_le atTop
      (fun _ => Real.sqrt_nonneg _)
  have hy_bounded :
      atTop.IsBoundedUnder (· ≤ ·)
        (rmsSquaredCostExpectation m hm mu0) :=
    hconv.isBoundedUnder_le
  calc
    Filter.limsup (trajectoryRMSCostFromState m hm s₀) atTop ≤
        Filter.limsup (rmsSquaredCostExpectation m hm mu0) atTop :=
      Filter.limsup_le_limsup
        (Filter.Eventually.of_forall
          (trajectoryRMSCostFromState_le_envelope hm s₀))
        hx_cobounded hy_bounded
    _ = Real.sqrt (pi.expect (parameterizedSquaredCostEnvelope m)) :=
      hconv.limsup_eq
    _ ≤ (17 / 2) * (parameterA m : ℝ) / (m : ℝ) :=
      hstationary

/-- The concrete refreshed trajectory inherits the count-chain average RMS
bound. -/
theorem refreshed_average_expected_squared_cost_rms_le
    {m T : ℕ} (hm : 1 ≤ m) (hT : m ^ 2 ≤ T) :
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          trajectoryExpectedSquaredCost
            (L := treeDepth m) (m := m) (parameterA m : ℝ) (by omega)
            (SupplyConfiguration.canonicalFallback (by omega)) t) /
          (T : ℝ)) ≤
      (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
  apply le_trans (Real.sqrt_le_sqrt ?_)
    (refreshed_average_rms_squaredCostEnvelope_le hm hT)
  apply div_le_div_of_nonneg_right
  · apply Finset.sum_le_sum
    intro t _ht
    rw [show parameterizedSquaredCostEnvelope m =
      Transport.stateSquaredCostEnvelope (parameterA m : ℝ) by rfl]
    simpa [refreshedIterate, parameterizedKernel] using
      (trajectoryExpectedSquaredCost_le_refreshedEnvelope
        (L := treeDepth m) (m := m) (parameterA m : ℝ)
        (parameterA_cast_pos hm) (by omega)
        (SupplyConfiguration.canonicalFallback (by omega)) t)
  · positivity

/-- Average expected distance is bounded by the refreshed average RMS second
moment. -/
theorem refreshed_average_expected_cost_le
    {m T : ℕ} (hm : 1 ≤ m) (hT : m ^ 2 ≤ T) :
    (∑ t ∈ Finset.range T,
        trajectoryExpectedCost
          (L := treeDepth m) (m := m) (parameterA m : ℝ) (by omega)
          (SupplyConfiguration.canonicalFallback (by omega)) t) /
        (T : ℝ) ≤
      (17 / 2) * (parameterA m : ℝ) / (m : ℝ) := by
  have hTpos : 0 < T := by
    have hmpos : 0 < m := by omega
    have : 0 < m ^ 2 := pow_pos hmpos 2
    omega
  calc
    (∑ t ∈ Finset.range T,
        trajectoryExpectedCost
          (L := treeDepth m) (m := m) (parameterA m : ℝ) (by omega)
          (SupplyConfiguration.canonicalFallback (by omega)) t) /
        (T : ℝ) ≤
      (∑ t ∈ Finset.range T,
        Real.sqrt (trajectoryExpectedSquaredCost
          (L := treeDepth m) (m := m) (parameterA m : ℝ) (by omega)
          (SupplyConfiguration.canonicalFallback (by omega)) t)) /
        (T : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact Finset.sum_le_sum fun t _ht =>
          expected_cost_le_sqrt_expected_squared_cost
            (L := treeDepth m) (m := m) (parameterA m : ℝ) (by omega)
            (SupplyConfiguration.canonicalFallback (by omega)) t
      · positivity
    _ ≤ Real.sqrt
        ((∑ t ∈ Finset.range T,
          trajectoryExpectedSquaredCost
            (L := treeDepth m) (m := m) (parameterA m : ℝ) (by omega)
            (SupplyConfiguration.canonicalFallback (by omega)) t) /
          (T : ℝ)) := by
      apply finite_average_sqrt_le_sqrt_average hTpos
      intro t _ht
      exact trajectoryExpectedSquaredCost_nonneg
        (L := treeDepth m) (m := m) (parameterA m : ℝ) (by omega)
        (SupplyConfiguration.canonicalFallback (by omega)) t
    _ ≤ (17 / 2) * (parameterA m : ℝ) / (m : ℝ) :=
      refreshed_average_expected_squared_cost_rms_le hm hT

end

end FD1D.V5.ContinuousProcess
