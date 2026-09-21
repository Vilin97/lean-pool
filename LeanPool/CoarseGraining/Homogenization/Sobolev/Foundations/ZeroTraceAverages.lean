/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
import LeanPool.CoarseGraining.Homogenization.Multiscale.CubeAverage
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.H10Function
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.MeanZero
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal

/-! # Zero Trace Averages -/

namespace Homogenization

theorem IsPotentialZeroTraceOn.integral_eq_zero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {f : Vec d → Vec d} (hf : IsPotentialZeroTraceOn U f) :
    (fun i => ∫ x in U, f x i ∂MeasureTheory.volume) = 0 := by
  rcases hf with ⟨u, rfl⟩
  ext i
  let μ := MeasureTheory.volume.restrict U
  let D : ℕ → Vec d → ℝ := fun m x => (fderiv ℝ (u.approx m) x) (basisVec i)
  have hD_integrable : ∀ m, MeasureTheory.Integrable (D m) MeasureTheory.volume := by
    intro m
    have hcont : Continuous (D m) := by
      simpa [D] using
        ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply continuous_const
    have hcomp : HasCompactSupport (D m) := by
      simpa [D] using (u.approx_hasCompactSupport m).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact hcont.integrable_of_hasCompactSupport hcomp
  have hD_integrable_restrict :
      ∀ᶠ m in Filter.atTop, MeasureTheory.Integrable (D m) μ := by
    refine Filter.Eventually.of_forall ?_
    intro m
    simpa [MeasureTheory.IntegrableOn, μ] using (hD_integrable m).integrableOn (s := U)
  have hD_zero : ∀ m, ∫ x, D m x ∂μ = 0 := by
    intro m
    have happrox_integrable : MeasureTheory.Integrable (u.approx m) MeasureTheory.volume := by
      exact (u.approx_smooth m).continuous.integrable_of_hasCompactSupport
        (u.approx_hasCompactSupport m)
    have hfull :
        ∫ x, D m x ∂MeasureTheory.volume = 0 := by
      have h :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (μ := MeasureTheory.volume)
          (f := fun _ : Vec d => (1 : ℝ))
          (g := u.approx m)
          (v := basisVec i)
          (by simp)
          (by simpa [D] using hD_integrable m)
          (by simpa using happrox_integrable)
          (fun x _ => (differentiable_const (1 : ℝ)).differentiableAt)
          (fun x _ => (u.approx_smooth m).differentiable (by simp) x)
      simpa [D] using h
    have hzero_off : ∀ x, x ∉ U → D m x = 0 := by
      intro x hx
      have hnot : x ∉ tsupport (u.approx m) := fun hx' => hx (u.approx_support_subset m hx')
      have hfderiv : fderiv ℝ (u.approx m) x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
      simpa [D] using congrArg (fun L => L (basisVec i)) hfderiv
    have hset :
        ∫ x in U, D m x ∂MeasureTheory.volume =
          ∫ x, D m x ∂MeasureTheory.volume :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_off
    simpa [μ] using hset.trans hfull
  have hfi : MeasureTheory.Integrable (fun x => u.toH1Function.grad x i) μ := by
    simpa [μ] using
      (u.toH1Function.gradMemL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hDiffMeas :
      ∀ m, MeasureTheory.AEStronglyMeasurable (fun x => D m x - u.toH1Function.grad x i) μ := by
    intro m
    have hDm :
        MeasureTheory.AEStronglyMeasurable (D m) μ := by
      have hInt : MeasureTheory.Integrable (D m) μ := by
        simpa [MeasureTheory.IntegrableOn, μ] using (hD_integrable m).integrableOn (s := U)
      exact hInt.aestronglyMeasurable
    exact hDm.sub (u.toH1Function.gradMemL2 i).aestronglyMeasurable
  have hL1_bound :
      ∀ m,
        MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 1 μ ≤
          MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 2 μ *
            μ Set.univ ^ ((1 : ℝ) - 1 / 2) := by
    intro m
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ)
        (f := fun x => D m x - u.toH1Function.grad x i)
        (p := (1 : ENNReal))
        (q := (2 : ENNReal))
        (by norm_num)
        (hDiffMeas m))
  have hConst_ne_top : μ Set.univ ^ ((1 : ℝ) - 1 / 2) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_).ne
    simpa [μ] using (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hL1 :
      Filter.Tendsto
        (fun m => MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 1 μ)
        Filter.atTop (nhds 0) := by
    have hscaled :
        Filter.Tendsto
          (fun m =>
            MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 2 μ *
              μ Set.univ ^ ((1 : ℝ) - 1 / 2))
          Filter.atTop
          (nhds (0 * (μ Set.univ ^ ((1 : ℝ) - 1 / 2)))) := by
      exact ENNReal.Tendsto.mul_const (u.tendsto_approx_grad i) (Or.inr hConst_ne_top)
    have hscaled0 :
        Filter.Tendsto
          (fun m =>
            MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 2 μ *
              μ Set.univ ^ ((1 : ℝ) - 1 / 2))
          Filter.atTop (nhds 0) := by
      simpa [zero_mul] using hscaled
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hscaled0
      (fun _ => zero_le)
      hL1_bound
  have hconv :
      Filter.Tendsto
        (fun m => ∫ x, D m x ∂μ)
        Filter.atTop
        (nhds (∫ x, u.toH1Function.grad x i ∂μ)) :=
    MeasureTheory.tendsto_integral_of_L1'
      (μ := μ)
      (f := fun x => u.toH1Function.grad x i)
      hfi.aestronglyMeasurable
      hD_integrable_restrict
      hL1
  have hEq : (fun m => ∫ x, D m x ∂μ) = fun _ => (0 : ℝ) := by
    funext m
    exact hD_zero m
  have hzero_tendsto :
      Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (∫ x, u.toH1Function.grad x i ∂μ)) := by
    simpa [hEq] using hconv
  have hIntegralZero : ∫ x, u.toH1Function.grad x i ∂μ = 0 :=
    tendsto_nhds_unique hzero_tendsto tendsto_const_nhds
  change ∫ x in U, u.toH1Function.grad x i ∂MeasureTheory.volume = 0
  simpa [μ] using hIntegralZero

namespace H10Function

/-- Zero-trace `H¹` functions have vanishing componentwise average gradient. -/
theorem averageGradient_eq_zero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H10Function U) :
    u.toH1Function.averageGradient = 0 := by
  exact H1Function.averageGradient_eq_zero_of_integral_eq_zero u.toH1Function
    (IsPotentialZeroTraceOn.integral_eq_zero u.isPotentialZeroTraceOn)

/-- Domain-regularity wrapper for `H10Function.averageGradient_eq_zero`. -/
theorem averageGradient_eq_zero_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (_hU : IsSobolevRegularDomain U) (u : H10Function U) :
    u.toH1Function.averageGradient = 0 := by
  simpa using u.averageGradient_eq_zero

end H10Function

private theorem fderiv_centeredCoord_apply_basisVec
    {d : ℕ} (Q : TriadicCube d) (i j : Fin d) (x : Vec d) :
    (fderiv ℝ (fun y : Vec d => y i - cubeCenter Q i) x) (basisVec j) =
      basisVec j i := by
  have hcoord :
      fderiv ℝ (fun y : Vec d => y i) x =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) := by
    exact ContinuousLinearMap.fderiv (𝕜 := ℝ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
  have hconst :
      fderiv ℝ (fun _ : Vec d => cubeCenter Q i) x = 0 := by
    simp
  have hd :
      fderiv ℝ ((fun y : Vec d => y i) - (fun _ : Vec d => cubeCenter Q i)) x =
        fderiv ℝ (fun y : Vec d => y i) x -
          fderiv ℝ (fun _ : Vec d => cubeCenter Q i) x := by
    exact fderiv_sub
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).differentiableAt)
      (differentiableAt_const (c := cubeCenter Q i))
  change
    (fderiv ℝ ((fun y : Vec d => y i) - (fun _ : Vec d => cubeCenter Q i)) x)
      (basisVec j) = basisVec j i
  rw [hd, hcoord, hconst]
  simp

private theorem fderiv_centeredCoord_apply_basisVec_self
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    (fderiv ℝ (fun y : Vec d => y i - cubeCenter Q i) x) (basisVec i) = 1 := by
  simpa [basisVec] using fderiv_centeredCoord_apply_basisVec Q i i x

private theorem centeredCoord_memLp_top_cubeSet
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) :
    MeasureTheory.MemLp (fun x : Vec d => x i - cubeCenter Q i)
      (⊤ : ENNReal) (MeasureTheory.volume.restrict (cubeSet Q)) := by
  let φ : Vec d → ℝ := fun x => x i - cubeCenter Q i
  have hφ_cont : Continuous φ := by
    dsimp [φ]
    fun_prop
  refine MeasureTheory.memLp_top_of_bound
    (μ := MeasureTheory.volume.restrict (cubeSet Q))
    hφ_cont.aestronglyMeasurable (cubeRadius Q) ?_
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)]
  exact Filter.Eventually.of_forall fun x hx => by
    have hxball : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
      cubeSet_subset_closedBall Q hx
    have hdist : ‖x - cubeCenter Q‖ ≤ cubeRadius Q := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
    have hcoord : ‖(x - cubeCenter Q) i‖ ≤ ‖x - cubeCenter Q‖ :=
      norm_le_pi_norm (x - cubeCenter Q) i
    calc
      ‖φ x‖ = ‖(x - cubeCenter Q) i‖ := by
        simp [φ, Pi.sub_apply]
      _ ≤ ‖x - cubeCenter Q‖ := hcoord
      _ ≤ cubeRadius Q := hdist

private theorem centeredCoord_fderiv_memLp_top_cubeSet
    {d : ℕ} (Q : TriadicCube d) (i j : Fin d) :
    MeasureTheory.MemLp
      (fun x : Vec d =>
        (fderiv ℝ (fun y : Vec d => y i - cubeCenter Q i) x) (basisVec j))
      (⊤ : ENNReal) (MeasureTheory.volume.restrict (cubeSet Q)) := by
  have hcont :
      Continuous
        (fun x : Vec d =>
          (fderiv ℝ (fun y : Vec d => y i - cubeCenter Q i) x) (basisVec j)) := by
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y i - cubeCenter Q i) := by
      fun_prop
    simpa using (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  refine MeasureTheory.memLp_top_of_bound
    (μ := MeasureTheory.volume.restrict (cubeSet Q))
    hcont.aestronglyMeasurable (1 : ℝ) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [fderiv_centeredCoord_apply_basisVec Q i j x]
    by_cases hji : j = i
    · have hb : basisVec j i = 1 := by
        simp [basisVec_apply, hji]
      rw [hb]
      norm_num
    · have hb : basisVec j i = 0 := by
        have hij : i ≠ j := fun hij => hji hij.symm
        simp [basisVec_apply, hij]
      rw [hb]
      norm_num

/-- On a half-open cube, the scalar average of an `H¹₀` function is a
coordinate-gradient pairing against the centered coordinate. -/
theorem cubeAverage_eq_neg_cubeAverage_grad_mul_centeredCoord_of_h10OnCube
    {d : ℕ} (Q : TriadicCube d) (u : H10Function (cubeSet Q)) (i : Fin d) :
    cubeAverage Q (fun x => u.toH1Function.toFun x) =
      - cubeAverage Q (fun x =>
          u.toH1Function.grad x i * (x i - cubeCenter Q i)) := by
  let : Fact (MeasureTheory.volume (cubeSet Q) < ⊤) :=
    ⟨volume_cubeSet_lt_top Q⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet Q))
    infer_instance
  let φ : Vec d → ℝ := fun x => x i - cubeCenter Q i
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    dsimp [φ]
    fun_prop
  have hφ_memTop :
      MeasureTheory.MemLp φ (⊤ : ENNReal)
        (MeasureTheory.volume.restrict (cubeSet Q)) := by
    simpa [φ] using centeredCoord_memLp_top_cubeSet Q i
  have hdφ_memTop :
      ∀ j : Fin d,
        MeasureTheory.MemLp (fun x => (fderiv ℝ φ x) (basisVec j))
          (⊤ : ENNReal) (MeasureTheory.volume.restrict (cubeSet Q)) := by
    intro j
    simpa [φ] using centeredCoord_fderiv_memLp_top_cubeSet Q i j
  let w : H10Function (cubeSet Q) := u.mulContDiffMemLpTop hφ hφ_memTop hdφ_memTop
  have hwavg : w.toH1Function.averageGradient = 0 := w.averageGradient_eq_zero
  have hvol : (MeasureTheory.volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hzero_vec :
      (fun k => ∫ x in cubeSet Q, w.toH1Function.grad x k ∂MeasureTheory.volume) = 0 :=
    H1Function.integral_eq_zero_of_averageGradient_eq_zero
      w.toH1Function hvol hwavg
  have hzero :
      ∫ x in cubeSet Q,
          (φ x * u.toH1Function.grad x i +
            u.toH1Function.toFun x *
              (fderiv ℝ φ x) (basisVec i)) ∂MeasureTheory.volume = 0 := by
    have hzeroi :=
      congrFun hzero_vec i
    simpa [w, H10Function.mulContDiffMemLpTop_grad] using hzeroi
  have hzero' :
      ∫ x in cubeSet Q,
          (φ x * u.toH1Function.grad x i +
            u.toH1Function.toFun x) ∂MeasureTheory.volume = 0 := by
    simpa [φ, fderiv_centeredCoord_apply_basisVec_self Q i] using hzero
  have hu_int :
      MeasureTheory.IntegrableOn (fun x => u.toH1Function.toFun x)
        (cubeSet Q) MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (u.toH1Function.memL2.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hgrad_mul_int :
      MeasureTheory.IntegrableOn
        (fun x => φ x * u.toH1Function.grad x i)
        (cubeSet Q) MeasureTheory.volume := by
    have hmem :
        MeasureTheory.MemLp (fun x => φ x * u.toH1Function.grad x i)
          (2 : ENNReal) (MeasureTheory.volume.restrict (cubeSet Q)) := by
      simpa [mul_comm] using (u.toH1Function.gradMemL2 i).mul' hφ_memTop
    simpa [MeasureTheory.IntegrableOn] using
      (hmem.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hsplit :
      ∫ x in cubeSet Q,
          (φ x * u.toH1Function.grad x i + u.toH1Function.toFun x)
          ∂MeasureTheory.volume =
        ∫ x in cubeSet Q, φ x * u.toH1Function.grad x i ∂MeasureTheory.volume +
          ∫ x in cubeSet Q, u.toH1Function.toFun x ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_add hgrad_mul_int hu_int
  have hint_eq :
      ∫ x in cubeSet Q, u.toH1Function.toFun x ∂MeasureTheory.volume =
        -∫ x in cubeSet Q, φ x * u.toH1Function.grad x i ∂MeasureTheory.volume := by
    nlinarith [hzero', hsplit]
  have hmul_eq :
      ∫ x in cubeSet Q, φ x * u.toH1Function.grad x i ∂MeasureTheory.volume =
        ∫ x in cubeSet Q,
          u.toH1Function.grad x i * (x i - cubeCenter Q i) ∂MeasureTheory.volume := by
    apply MeasureTheory.setIntegral_congr_fun (measurableSet_cubeSet Q)
    intro x hx
    simp [φ]
    ring
  calc
    cubeAverage Q (fun x => u.toH1Function.toFun x)
        = (cubeVolume Q)⁻¹ *
            ∫ x in cubeSet Q, u.toH1Function.toFun x ∂MeasureTheory.volume := rfl
    _ = (cubeVolume Q)⁻¹ *
          (-(∫ x in cubeSet Q, φ x * u.toH1Function.grad x i ∂MeasureTheory.volume)) := by
        rw [hint_eq]
    _ = -((cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q, φ x * u.toH1Function.grad x i ∂MeasureTheory.volume) := by
        ring
    _ = -((cubeVolume Q)⁻¹ *
          ∫ x in cubeSet Q,
            u.toH1Function.grad x i * (x i - cubeCenter Q i) ∂MeasureTheory.volume) := by
        rw [hmul_eq]
    _ = - cubeAverage Q (fun x =>
          u.toH1Function.grad x i * (x i - cubeCenter Q i)) := rfl

theorem IsSolenoidalZeroNormalTraceOn.integral_eq_zero
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {g : Vec d → Vec d} (hg : IsSolenoidalZeroNormalTraceOn U g) :
    (fun i => ∫ x in U, g x i ∂MeasureTheory.volume) = 0 := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  ext i
  have htest :
      ∫ x in U, vecDot (g x) (basisVec i) ∂MeasureTheory.volume = 0 := by
    simpa using hg (H1Function.coordOnIsSobolevRegularDomain hU i)
  simpa [vecDot, basisVec_apply] using htest

theorem cubeAverageVec_grad_eq_zero_of_h10OnCube {d : ℕ}
    (Q : TriadicCube d) (u : H10Function (cubeSet Q)) :
    cubeAverageVec Q (fun x => u.toH1Function.grad x) = 0 := by
  let : Fact (MeasureTheory.volume (cubeSet Q) < ⊤) :=
    ⟨volume_cubeSet_lt_top Q⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet Q))
    infer_instance
  funext i
  have hzero :
      (fun i => ∫ x in cubeSet Q, u.toH1Function.grad x i ∂MeasureTheory.volume) = 0 :=
    IsPotentialZeroTraceOn.integral_eq_zero u.isPotentialZeroTraceOn
  have hzeroi : ∫ x in cubeSet Q, u.toH1Function.grad x i ∂MeasureTheory.volume = 0 := by
    simpa using congrFun hzero i
  unfold cubeAverageVec cubeAverage
  rw [hzeroi]
  simp

end Homogenization
