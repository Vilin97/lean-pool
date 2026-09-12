/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
public import LeanPool.NavierStokesAndEuler.ForMathlib.FiniteDimensionalBumps
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.RingTheory.Finiteness.Prod

/-! Expanding spatial cutoffs and transport cancellation for noncompact fields on the cylinder. -/

@[expose] public section

attribute [local instance] FiniteDimensional.hasContDiffBump

noncomputable section

namespace EulerNoncompactTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport

open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A fixed smooth spatial cutoff equal to one on the unit ball. -/
def spatialBump : ContDiffBump (0 : Vector3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The reciprocal spatial scale in the expanding cutoff sequence. -/
def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

/-- Smooth expanding cutoffs on the cylinder; the angular variable is unchanged. -/
def spatialCutoff (n : ℕ) (x : LiftDomain period) : ℝ :=
  spatialBump (cutoffScale n • x.1)

omit [Fact (0 < period)] in
theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  exact inv_pos.mpr (by positivity)

omit [Fact (0 < period)] in
theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (by have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

omit [Fact (0 < period)] in
theorem cutoffScale_tendsto : Filter.Tendsto cutoffScale Filter.atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop)

omit [Fact (0 < period)] in
theorem spatialCutoff_bounds (n : ℕ) (x : LiftDomain period) :
    0 ≤ spatialCutoff period n x ∧ spatialCutoff period n x ≤ 1 :=
  ⟨spatialBump.nonneg, spatialBump.le_one⟩

omit [Fact (0 < period)] in
theorem spatialCutoff_smooth (n : ℕ) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localLift period (spatialCutoff period n) x) := by
  exact spatialBump.contDiff.comp ((contDiff_const.add contDiff_fst).const_smul _)

omit [Fact (0 < period)] in
theorem spatialCutoff_tendsto (x : LiftDomain period) :
    Filter.Tendsto (fun n => spatialCutoff period n x) Filter.atTop (𝓝 1) := by
  have h := spatialBump.continuous.continuousAt.tendsto.comp
    (cutoffScale_tendsto.smul_const x.1)
  have hb : spatialBump 0 = 1 := spatialBump.one_of_mem_closedBall (by simp [spatialBump])
  convert h using 1 <;> simp [spatialCutoff, hb, Function.comp_def]

theorem spatialCutoff_compact (n : ℕ) : HasCompactSupport (spatialCutoff period n) := by
  apply HasCompactSupport.intro
    ((isCompact_closedBall (0 : Vector3) (2 * ((n : ℝ) + 1))).prod
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle period))))
  intro x hx
  have hnorm : 2 * ((n : ℝ) + 1) < ‖x.1‖ := by
    simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, Set.mem_univ,
      and_true, not_le] using hx
  apply spatialBump.zero_of_le_dist
  change 2 ≤ dist (cutoffScale n • x.1) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n)]
  change 2 ≤ ((n : ℝ) + 1)⁻¹ * ‖x.1‖
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact hnorm.le

omit [Fact (0 < period)] in
theorem spatialCutoff_fderiv (n : ℕ) (x : LiftDomain period) (v : LiftTangent) :
    fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v =
      fderiv ℝ spatialBump (cutoffScale n • x.1) (cutoffScale n • v.1) := by
  have hi : HasFDerivAt (fun h : LiftTangent => cutoffScale n • (x.1 + h.1))
      (cutoffScale n • ContinuousLinearMap.fst ℝ Vector3 ℝ) 0 := by
    convert ((ContinuousLinearMap.fst ℝ Vector3 ℝ).hasFDerivAt.const_add x.1).const_smul
      (cutoffScale n) using 1 <;> rfl
  have ho := ((spatialBump.contDiff : ContDiff ℝ ∞ spatialBump).differentiable
    (by simp)).differentiableAt.hasFDerivAt (x := cutoffScale n • (x.1 + (0 : LiftTangent).1))
  have h := ho.comp 0 hi
  have heq := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L v) h.fderiv
  simpa +unfoldPartialApp [spatialCutoff, localLift, Function.comp_def] using heq

omit [Fact (0 < period)] in
/-- The cutoff derivatives have a uniform constant times their reciprocal spatial scale. -/
theorem spatialCutoff_derivative_bound : ∃ M : ℝ, 0 < M ∧ ∀ n x v,
    ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v‖ ≤
      M * cutoffScale n * ‖v‖ := by
  obtain ⟨M, hM, hbound⟩ :=
    ((spatialBump.hasCompactSupport.fderiv ℝ).isCompact_range
      ((spatialBump.contDiff : ContDiff ℝ ∞ spatialBump).continuous_fderiv (by
          simp))).isBounded.exists_pos_norm_le
  refine ⟨M, hM, fun n x v => ?_⟩
  rw [spatialCutoff_fderiv]
  calc
    _ ≤ ‖fderiv ℝ spatialBump (cutoffScale n • x.1)‖ * ‖cutoffScale n • v.1‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * (cutoffScale n * ‖v‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n)]
      exact mul_le_mul (hbound _ (Set.mem_range_self _))
        (mul_le_mul_of_nonneg_left (norm_fst_le v) (cutoffScale_pos n).le)
        (mul_nonneg (cutoffScale_pos n).le (norm_nonneg _)) hM.le
    _ = _ := by ring

omit [Fact (0 < period)] in
theorem spatialCutoff_derivative_tendsto (x : LiftDomain period) (v : LiftTangent) :
    Filter.Tendsto (fun n => fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v)
      Filter.atTop (𝓝 0) := by
  obtain ⟨M, _, hM⟩ := spatialCutoff_derivative_bound period
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => hM n x v)
  simpa using (tendsto_const_nhds.mul cutoffScale_tendsto).mul_const (‖v‖ : ℝ)

omit [Fact (0 < period)] in
theorem cutoff_product_transport (κ : ℝ) (m : Vector3) (n : ℕ)
    (φ : LiftDomain period → ℝ) (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x))
    (x : LiftDomain period) (v : Vector3) :
    ⟪liftedGradient period κ m (fun y => spatialCutoff period n y * φ y) x, v⟫_ℝ =
      spatialCutoff period n x * fderiv ℝ (localLift period φ x) 0 (transportDirection κ m v) +
      φ x * fderiv ℝ (localLift period (spatialCutoff period n) x) 0 (transportDirection κ m v) :=
          by
  rw [liftedGradient_eq_vectorOfLinear, vectorOfLinear_inner]
  have hc := ((spatialCutoff_smooth period n x).differentiable (by
      simp)).differentiableAt.hasFDerivAt
    (x := 0)
  have hf := ((hφ x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have h := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L (transportDirection κ m v))
    (hc.mul hf).fderiv
  simpa +unfoldPartialApp [localLift, Pi.mul_def] using h

/-- Smooth scalar weak-divergence tests extend to integrable noncompact energies. -/
theorem weak_divergence_integral_noncompact (κ : ℝ) (m : Vector3)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (B : ℝ) (_hB : 0 ≤ B) (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (φ : LiftDomain period → ℝ) (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x))
    (hφI : Integrable φ (liftMeasure period))
    (hflux : Integrable (fun x => fderiv ℝ (localLift period φ x) 0
      (transportDirection κ m (z x))) (liftMeasure period)) :
    ∫ x, fderiv ℝ (localLift period φ x) 0 (transportDirection κ m (z x))
      ∂liftMeasure period = 0 := by
  obtain ⟨M, hM, hMb⟩ := spatialCutoff_derivative_bound period
  let C := M * (|κ| + ‖m‖) * B
  let flux := fun x => fderiv ℝ (localLift period φ x) 0 (transportDirection κ m (z x))
  let F := fun n x => ⟪liftedGradient period κ m (fun y => spatialCutoff period n y * φ y) x, z x⟫_ℝ
  have hs : ∀ n x, ContDiff ℝ ∞ (localLift period (fun y => spatialCutoff period n y * φ y) x) :=
    fun n x => (spatialCutoff_smooth period n x).mul (hφ x)
  have hc : ∀ n, HasCompactSupport (fun y => spatialCutoff period n y * φ y) :=
    fun n => (spatialCutoff_compact period n).mul_right
  have hF0 : ∀ n, ∫ x, F n x ∂liftMeasure period = 0 :=
    fun n => weak_divergence_test_integral period κ m hz _ ⟨hc n, hs n⟩
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (liftMeasure period) := by
    intro n
    exact (liftedGradient_continuous period κ m _ (hs n)).aestronglyMeasurable.inner
      (Lp.aestronglyMeasurable z)
  have hbound : ∀ n, ∀ᵐ x ∂liftMeasure period, ‖F n x‖ ≤ ‖flux x‖ + C * ‖φ x‖ := by
    intro n
    filter_upwards [hzB] with x hx
    have hcut := spatialCutoff_bounds period n x
    have hv : ‖transportDirection κ m (z x)‖ ≤ (|κ| + ‖m‖) * B :=
      (transportDirection_norm_le κ m (z x)).trans
        (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
    have hd : ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0
        (transportDirection κ m (z x))‖ ≤ C := by
      calc
        _ ≤ M * cutoffScale n * ‖transportDirection κ m (z x)‖ := hMb n x _
        _ ≤ M * 1 * ((|κ| + ‖m‖) * B) := by
          gcongr
          exact cutoffScale_le_one n
        _ = C := by dsimp [C]; ring
    dsimp [F]
    rw [cutoff_product_transport period κ m n φ hφ]
    calc
      _ ≤ ‖spatialCutoff period n x * flux x‖ +
          ‖φ x * fderiv ℝ (localLift period (spatialCutoff period n) x) 0
            (transportDirection κ m (z x))‖ := norm_add_le _ _
      _ = ‖spatialCutoff period n x‖ * ‖flux x‖ + ‖φ x‖ *
          ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0
            (transportDirection κ m (z x))‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖flux x‖ + ‖φ x‖ * C := by
        gcongr
        simpa only [Real.norm_eq_abs, abs_of_nonneg hcut.1] using hcut.2
      _ = _ := by simp only [Real.norm_eq_abs]; ring
  have hlim : ∀ᵐ x ∂liftMeasure period, Filter.Tendsto (fun n => F n x)
      Filter.atTop (𝓝 (flux x)) := by
    apply Filter.Eventually.of_forall
    intro x
    simp_rw [F, cutoff_product_transport period κ m _ φ hφ]
    convert ((spatialCutoff_tendsto period x).mul_const (flux x)).add
      ((spatialCutoff_derivative_tendsto period x (transportDirection κ m (z x))).const_mul
        (φ x)) using 1
    simp
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖flux x‖ + C * ‖φ x‖)
    hmeas (hflux.norm.add (hφI.norm.const_mul C)) hbound hlim
  have heq : (fun n => ∫ x, F n x ∂liftMeasure period) = fun _ : ℕ => 0 := by
    funext n
    exact hF0 n
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Integration by parts for a noncompact smooth metric energy with integrable terms. -/
theorem metric_transport_noncompact_by_parts (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (B : ℝ) (hB : 0 ≤ B) (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (hE : Integrable (metricEnergy period K e) (liftMeasure period))
    (hT : Integrable (fun x => ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ) (liftMeasure period))
    (hQ : Integrable (fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period)) :
    (∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period) =
    -(∫ x, (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ ∂liftMeasure period) := by
  have hf : Integrable (fun x => fderiv ℝ (localLift period (metricEnergy period K e) x) 0
      (transportDirection κ m (z x))) (liftMeasure period) := by
    simp only [metricEnergy_fderiv period K e hK he hsym]
    exact hT.add hQ
  have hz0 := weak_divergence_integral_noncompact period κ m hz B hB hzB
    (metricEnergy period K e) (metricEnergy_smooth period K e hK he) hE hf
  simp only [metricEnergy_fderiv period K e hK he hsym] at hz0
  rw [integral_add hT hQ] at hz0
  exact eq_neg_of_add_eq_zero_left hz0

theorem aestronglyMeasurable_apply {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : LiftDomain period → V →L[ℝ] W} {u : LiftDomain period → V}
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hu : AEStronglyMeasurable u (liftMeasure period)) :
    AEStronglyMeasurable (fun x => A x (u x)) (liftMeasure period) :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hu)

/-- Bounded metrics have integrable quadratic energy on every actual L² field. -/
theorem metricEnergy_integrable (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period)) (he : MemLp e 2 (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C) :
    Integrable (metricEnergy period K e) (liftMeasure period) := by
  apply (he.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * C)).mono'
  · exact aestronglyMeasurable_const.mul ((aestronglyMeasurable_apply period hK
      he.aestronglyMeasurable).inner
      he.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  have hKe : ‖K x (e x)‖ ≤ (C : ℝ) * ‖e x‖ :=
    ((K x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪K x (e x), e x⟫_ℝ‖ := by dsimp [metricEnergy]; rw [abs_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖K x (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((C : ℝ) * ‖e x‖) * ‖e x‖) := by gcongr
    _ = _ := by ring

/-- The actual lifted transport velocity of an L² field is measurable. -/
theorem transportDirection_aestronglyMeasurable (κ : ℝ) (m : Vector3) (z : LiftL2 period) :
    AEStronglyMeasurable (fun x => transportDirection κ m (z x)) (liftMeasure period) := by
  exact ((Lp.aestronglyMeasurable z).const_smul κ).prodMk
    (aestronglyMeasurable_const.inner (Lp.aestronglyMeasurable z))

/-- The principal transport pairing is integrable for smooth H¹ fields and bounded velocity. -/
theorem metricTransport_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period))
    (he : MemLp e 2 (liftMeasure period))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period e x) 0) 2 (liftMeasure period))
    (C B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C) (z : LiftL2 period)
    (hz : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    Integrable (fun x => ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ) (liftMeasure period) := by
  apply ((he.norm.integrable_mul hDe.norm).const_mul ((C : ℝ) * B)).mono'
  · exact (aestronglyMeasurable_apply period hK he.aestronglyMeasurable).inner
      (aestronglyMeasurable_apply period hDe.aestronglyMeasurable
        (transportDirection_aestronglyMeasurable period κ m z))
  filter_upwards [hz] with x hx
  have hKe : ‖K x (e x)‖ ≤ (C : ℝ) * ‖e x‖ :=
    ((K x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hDv : ‖fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))‖ ≤
      ‖fderiv ℝ (localFieldLift period e x) 0‖ * B :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  calc
    _ ≤ ‖K x (e x)‖ * ‖fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ((C : ℝ) * ‖e x‖) * (‖fderiv ℝ (localFieldLift period e x) 0‖ * B) :=
      mul_le_mul hKe hDv (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Pi.mul_apply]; ring

omit [Fact (0 < period)] in
theorem metricCorrection_pointwise_bound
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (D B : ℝ≥0) (x : LiftDomain period) (v : LiftTangent)
    (hD : ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D) (hv : ‖v‖ ≤ B) :
    ‖(1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ‖ ≤
      (1 / 2 : ℝ) * D * B * ‖e x‖ ^ 2 := by
  have hL : ‖fderiv ℝ (localFieldLift period K x) 0 v‖ ≤ (D : ℝ) * B :=
    ((fderiv ℝ (localFieldLift period K x) 0).le_opNorm _).trans
      (mul_le_mul hD hv (norm_nonneg _) D.coe_nonneg)
  have hLe : ‖(fderiv ℝ (localFieldLift period K x) 0 v) (e x)‖ ≤ (D : ℝ) * B * ‖e x‖ :=
    ((fderiv ℝ (localFieldLift period K x) 0 v).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ‖ := by
      rw [norm_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ (localFieldLift period K x) 0 v) (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((D : ℝ) * B * ‖e x‖) * ‖e x‖) := by gcongr
    _ = _ := by ring

/-- The metric correction is integrable for L² fields and bounded metric derivative and velocity. -/
theorem metricCorrection_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hDK : AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period K x) 0)
      (liftMeasure period)) (he : MemLp e 2 (liftMeasure period))
    (D B : ℝ≥0) (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (z : LiftL2 period) (hz : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    Integrable (fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period) := by
  apply (he.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * D * B)).mono'
  · exact aestronglyMeasurable_const.mul
      ((aestronglyMeasurable_apply period
        (aestronglyMeasurable_apply period hDK (transportDirection_aestronglyMeasurable period κ m
            z))
          he.aestronglyMeasurable).inner he.aestronglyMeasurable)
  filter_upwards [hz] with x hx
  exact metricCorrection_pointwise_bound period K e D B x _ (hD x) hx

/-- The genuine noncompact H¹ metric transport estimate; no cancellation is assumed. -/
theorem metric_transport_H1_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (heLp : MemLp e 2 (liftMeasure period))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period e x) 0) 2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
  let β : ℝ≥0 := ⟨(|κ| + ‖m‖) * B,
    mul_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _)) B.coe_nonneg⟩
  have hv : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ β := by
    filter_upwards [hzB] with x hx
    exact (transportDirection_norm_le κ m (z x)).trans
      (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  have hKm : AEStronglyMeasurable K (liftMeasure period) :=
    (smoothField_continuous period K hK).aestronglyMeasurable
  have hDKm : AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period K x) 0)
      (liftMeasure period) :=
    (localFDeriv_continuous period K hK).aestronglyMeasurable
  have hT := metricTransport_integrable period κ m K e hKm heLp hDe C β hC z hv
  have hQ := metricCorrection_integrable period κ m K e hDKm heLp D β hD z hv
  rw [metric_transport_noncompact_by_parts period κ m K e hK he hsym hz B B.coe_nonneg hzB
    (metricEnergy_integrable period K e hKm heLp C hC) hT hQ, abs_neg]
  have hbound := norm_integral_le_of_norm_le
    (heLp.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * D * β))
    (f := fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ?_
  · have hβ : (β : ℝ) = (|κ| + ‖m‖) * B := rfl
    rw [hβ] at hbound
    simpa only [Real.norm_eq_abs, integral_const_mul] using hbound
  filter_upwards [hv] with x hx
  exact metricCorrection_pointwise_bound period K e D β x _ (hD x) hx

/-- The noncompact transport estimate expressed in the genuine L² Hilbert norm. -/
theorem metric_transport_L2_H1_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftL2 period)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e y) x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period (fun y => e y) x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ‖e‖ ^ 2 := by
  have hn : (∫ x, ‖e x‖ ^ 2 ∂liftMeasure period) = ‖e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simpa only [hn] using metric_transport_H1_bound period κ m K (fun x => e x)
    hK he (Lp.memLp e) hDe hsym hz C D B hC hD hzB

end EulerNoncompactTransport
