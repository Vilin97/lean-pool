/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelClassical

/-!
# Time differentiation of the Euclidean Duhamel potential

This module proves the generator identity for the Euclidean heat semigroup on
globally coordinatewise Hölder data and uses it to identify the time
derivative of the inhomogeneous Duhamel potential.  The endpoint singularity
is genuine: the heat-kernel Hessian is bounded by `u ^ (-1 + r / 2)`, which is
integrable precisely because `r > 0`.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-! ## The homogeneous heat generator -/

/-- Additivity of one bundled coordinate Hessian of the heat semigroup. -/
theorem heatHessianCoordNDbcf_add {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) (f g : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    heatHessianCoordNDbcf ht (f + g) k =
      heatHessianCoordNDbcf ht f k + heatHessianCoordNDbcf ht g k := by
  ext x
  simp only [heatHessianCoordNDbcf_apply, BoundedContinuousFunction.add_apply]
  rw [heatHessianCoordConvolutionND]
  have hf := integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x
    f.continuous.aestronglyMeasurable
    (fun y => le_trans (f.norm_coe_le_norm y) (le_max_left ‖f‖ ‖g‖))
  have hg := integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x
    g.continuous.aestronglyMeasurable
    (fun y => le_trans (g.norm_coe_le_norm y) (le_max_right ‖f‖ ‖g‖))
  change (∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * (f + g) y) =
    (∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) +
    ∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * g y
  rw [← integral_add hf hg]
  apply integral_congr_ae
  filter_upwards with y
  rw [BoundedContinuousFunction.add_apply]
  ring

/-- Real-scalar homogeneity of one bundled coordinate Hessian. -/
theorem heatHessianCoordNDbcf_smul {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) (c : ℝ)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    heatHessianCoordNDbcf ht (c • f) k =
      c • heatHessianCoordNDbcf ht f k := by
  ext x
  simp only [heatHessianCoordNDbcf_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, heatHessianCoordConvolutionND]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Sup-norm operator estimate for a bundled heat Hessian coordinate. -/
theorem norm_heatHessianCoordNDbcf_le {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n) :
    ‖heatHessianCoordNDbcf ht f k‖ ≤ ‖f‖ / t := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [heatHessianCoordNDbcf_apply, Real.norm_eq_abs]
  simpa only [heatHessianCoordConvolutionND] using
    heatSemigroupND_coord_second_deriv_integral_bound ht x k
      f.continuous.aestronglyMeasurable (fun y => f.norm_coe_le_norm y)

/-- One coordinate of the heat Hessian as a bounded linear operator on the
global sup-norm space. -/
noncomputable def heatHessianCoordNDclm {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ →L[ℝ]
      BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => heatHessianCoordNDbcf ht f k
      map_add' := heatHessianCoordNDbcf_add ht k
      map_smul' := fun (c : ℝ) f => by
        simpa using heatHessianCoordNDbcf_smul ht k c f }
    (1 / t)
    (fun f => by
      calc
        ‖heatHessianCoordNDbcf ht f k‖ ≤ ‖f‖ / t :=
          norm_heatHessianCoordNDbcf_le ht f k
        _ = (1 / t) * ‖f‖ := by ring)

@[simp] theorem heatHessianCoordNDclm_apply {n : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Fin n) (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    heatHessianCoordNDclm ht k f = heatHessianCoordNDbcf ht f k := rfl

/-- At fixed positive heat time, a coordinate Hessian applied to a continuous
BCF-valued source varies continuously with the source time. -/
theorem continuous_heatHessianCoordConvolutionND_comp_sub_time
    {n : ℕ} {u : ℝ} (hu : 0 < u) (k : Fin n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (x : Fin n → ℝ) :
    Continuous (fun t => heatHessianCoordConvolutionND u (q (t - u)) k x) := by
  have hs : Continuous (fun t : ℝ => q (t - u)) :=
    hq.comp (continuous_id.sub continuous_const)
  have hop : Continuous (fun t : ℝ => heatHessianCoordNDclm hu k (q (t - u))) :=
    (heatHessianCoordNDclm hu k).continuous.comp hs
  have heval := (continuous_eval_const x).comp hop
  convert heval using 1
  funext t
  rfl

/-- The spatial Laplacian of a homogeneous Euclidean heat evolution, written
as the finite trace of its heat-kernel Hessian. -/
def heatSemigroupLaplacianND {n : ℕ} (t : ℝ)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, heatHessianCoordConvolutionND t w k x

/-- The actual positive-time derivative of the homogeneous heat semigroup is
its heat-kernel Laplacian. -/
theorem hasDerivAt_heatSemigroupND_time_eq_laplacian
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) :
    HasDerivAt (fun s => heatSemigroupND s (⇑w) x)
      (heatSemigroupLaplacianND t w x) t := by
  have htime := hasDerivAt_heatSemigroupND_time ht x
    w.continuous.aestronglyMeasurable (fun y => w.norm_coe_le_norm y)
  convert htime using 1
  rw [heatSemigroupLaplacianND]
  change (∑ k : Fin n, ∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) *
        ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * w y) = _
  calc
    _ = ∫ y : Fin n → ℝ, ∑ k : Fin n,
        (heatKernelND t (x - y) *
          ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * w y := by
      rw [integral_finsetSum]
      intro k _
      exact integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x
        w.continuous.aestronglyMeasurable (fun y => w.norm_coe_le_norm y)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [Finset.mul_sum, Finset.sum_mul]

/-- A single coordinate heat Hessian is integrable from heat time zero for
globally coordinatewise Hölder data. -/
theorem intervalIntegrable_heatHessianCoordConvolutionND_zero
    {n : ℕ} {T r : ℝ} (hT : 0 ≤ T) (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    IntervalIntegrable (fun u => heatHessianCoordConvolutionND u w k x)
      volume 0 T := by
  have hi := intervalIntegrable_hessian_heatKernelND_convolution
    (n := n) (t₀ := 0) (t := T) (r := r) hT hr0
    (q := fun _ => w) continuous_const hH
    (fun _ y => w.norm_coe_le_norm y) (fun _ a b => by
      calc
        |w b - w a| ≤ H * ∑ j : Fin n, |(b - a) j| ^ r := hholder b a
        _ = H * ∑ j : Fin n, |(a - b) j| ^ r := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          simp only [Pi.sub_apply, abs_sub_comm]) x k
  have hc := hi.comp_sub_left T
  simpa only [sub_zero, sub_self, sub_sub_cancel,
    heatHessianCoordConvolutionND] using hc.symm

/-- For globally coordinatewise Hölder data, the positive-time heat
Laplacian is integrable all the way down to heat time zero. -/
theorem intervalIntegrable_heatSemigroupLaplacianND
    {n : ℕ} {T r : ℝ} (hT : 0 ≤ T) (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    IntervalIntegrable (fun u => heatSemigroupLaplacianND u w x)
      volume 0 T := by
  have hk : ∀ k : Fin n, IntervalIntegrable
      (fun u => heatHessianCoordConvolutionND u w k x) volume 0 T := by
    intro k
    exact intervalIntegrable_heatHessianCoordConvolutionND_zero
      hT hr0 w hH hholder k x
  have hsum : IntervalIntegrable
      (∑ k : Fin n, fun u => heatHessianCoordConvolutionND u w k x)
      volume 0 T := IntervalIntegrable.sum Finset.univ (fun k _ => hk k)
  convert hsum using 1
  ext u
  rw [heatSemigroupLaplacianND, Finset.sum_apply]

/-- The extended heat-flow path is continuous on a compact interval starting
at zero when the datum has a positive Hölder modulus. -/
theorem continuousOn_heatFlowPathBcf_apply_Icc_of_coordHolder
    {n : ℕ} {T r : ℝ} (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    ContinuousOn (fun u => heatFlowPathBcf w u x) (Set.Icc 0 T) := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with rfl | hu0
  · exact (continuous_eval_const x).continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_heatFlowPathBcf_zero_of_coordHolder
        hr0 w hH hholder).mono (Set.Icc_subset_Ici_self))
  · exact (continuous_eval_const x).continuousAt.comp_continuousWithinAt
      ((continuousAt_heatFlowPathBcf w hu0).continuousWithinAt)

/-- **Generator integral identity at heat time zero.**  For bounded globally
coordinatewise Hölder data, the increment of the heat semigroup is the time
integral of its actual spatial Laplacian.  The proof is an improper-endpoint
FTC: continuity at zero comes from the fractional approximate identity, while
the Hölder Hessian estimate supplies the integrable derivative. -/
theorem heatSemigroupND_sub_self_eq_integral_laplacian
    {n : ℕ} {T r : ℝ} (hT : 0 < T) (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    heatSemigroupND T (⇑w) x - w x =
      ∫ u in (0 : ℝ)..T, heatSemigroupLaplacianND u w x := by
  let F : ℝ → ℝ := fun u => heatFlowPathBcf w u x
  have hcont : ContinuousOn F (Set.Icc 0 T) := by
    simpa only [F] using
      continuousOn_heatFlowPathBcf_apply_Icc_of_coordHolder
        (T := T) hr0 w hH hholder x
  have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt F (heatSemigroupLaplacianND u w x) (Set.Ioi u) u := by
    intro u hu
    have hd := hasDerivAt_heatSemigroupND_time_eq_laplacian hu.1 w x
    apply (hd.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Ioi_mem_nhds hu.1] with v hv
    have hvpos : 0 < v := hv
    rw [show F v = heatFlowPathBcf w v x by rfl,
      heatFlowPathBcf_of_pos w hvpos, heatSemigroupNDbcf_apply]
  have hint := intervalIntegrable_heatSemigroupLaplacianND
    hT.le hr0 w hH hholder x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hT.le hcont hderiv hint
  simpa [F, heatFlowPathBcf, hT, heatSemigroupNDbcf_apply] using hFTC.symm

/-! ## Positive-time continuity of the Duhamel Laplacian -/

/-- Reflection of the Duhamel Hessian time integral to heat time
`u = t - s`. -/
theorem heatDuhamelHessianCoordND_eq_comp_sub
    {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (k : Fin n) (x : Fin n → ℝ) :
    heatDuhamelHessianCoordND t₀ t q k x =
      ∫ u in (0 : ℝ)..(t - t₀),
        heatHessianCoordConvolutionND u (q (t - u)) k x := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := t₀) (b := t)
    (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) t
  simpa only [heatDuhamelHessianCoordND, sub_sub_cancel, sub_self] using h

/-- Measurability in reflected heat time of a coordinate Hessian applied to a
continuous BCF-valued source. -/
theorem aestronglyMeasurable_heatHessianCoordConvolutionND_comp_sub
    {n : ℕ} (t : ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (k : Fin n) (x : Fin n → ℝ) :
    AEStronglyMeasurable
      (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) volume := by
  have hK : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      heatKernelND p.1 (x - p.2)) := by
    exact measurable_uncurry_heatKernelND.comp
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  have hc : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (x - p.2) k ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)) := by
    fun_prop
  have hQ : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (q (t - p.1)) p.2) := by
    exact (ContinuousEval.continuous_eval.comp
      ((hq.comp (continuous_const.sub continuous_fst)).prodMk continuous_snd)).measurable
  have hG : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (heatKernelND p.1 (x - p.2) *
        ((x - p.2) k ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1))) *
          (q (t - p.1)) p.2) := (hK.mul hc).mul hQ
  simpa only [heatHessianCoordConvolutionND] using
    (hG.aestronglyMeasurable
      (μ := (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))).integral_prod_right'

/-- A coordinate of the Duhamel Hessian is continuous in the final time at
every time strictly after the initial slice.  Reflection puts the singularity
at the fixed endpoint `u = 0`, where the integrable Hölder majorant
`u ^ (-1 + r / 2)` permits dominated convergence. -/
theorem continuousAt_heatDuhamelHessianCoordND_time
    {n : ℕ} {t₀ t₁ r : ℝ} (ht : t₀ < t₁) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    ContinuousAt (fun t => heatDuhamelHessianCoordND t₀ t q k x) t₁ := by
  let A : ℝ := H * heatHessianHolderMoment n r k
  let p : ℝ := -1 + r / 2
  have hA : 0 ≤ A := mul_nonneg hH (heatHessianHolderMoment_nonneg n r k)
  have hp : (-1 : ℝ) < p := by simp only [p]; linarith
  have hfun : (fun t => heatDuhamelHessianCoordND t₀ t q k x) =
      fun t => ∫ u in (0 : ℝ)..(t - t₀),
        heatHessianCoordConvolutionND u (q (t - u)) k x := by
    funext t
    exact heatDuhamelHessianCoordND_eq_comp_sub t₀ t q k x
  rw [hfun]
  have hEq : (fun t => ∫ u in (0 : ℝ)..(t - t₀),
      heatHessianCoordConvolutionND u (q (t - u)) k x) =ᶠ[nhds t₁]
      fun t => ∫ u, Set.indicator (Set.Ioc (0 : ℝ) (t - t₀))
        (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) u := by
    filter_upwards [Ioi_mem_nhds ht] with t htmem
    have hle : (0 : ℝ) ≤ t - t₀ := by linarith [Set.mem_Ioi.1 htmem]
    rw [intervalIntegral.integral_of_le hle,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine ContinuousAt.congr ?_ hEq.symm
  refine continuousAt_of_dominated
    (bound := fun u => Set.indicator
      (Set.Ioc (0 : ℝ) (t₁ - t₀ + 1)) (fun u => A * u ^ p) u) ?_ ?_ ?_ ?_
  · filter_upwards with t
    exact (aestronglyMeasurable_heatHessianCoordConvolutionND_comp_sub
      t hq k x).indicator measurableSet_Ioc
  · filter_upwards [Iio_mem_nhds (show t₁ < t₁ + 1 by linarith)] with t htmem
    filter_upwards with u
    by_cases hmem : u ∈ Set.Ioc (0 : ℝ) (t - t₀)
    · rw [Set.indicator_of_mem hmem]
      have hupos : (0 : ℝ) < u := hmem.1
      have htlt : t < t₁ + 1 := Set.mem_Iio.1 htmem
      rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hupos, by linarith [hmem.2]⟩),
        Real.norm_eq_abs]
      have hb := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
        hupos hr0.le hH x k (q (t - u)).continuous.aestronglyMeasurable
        (hqb (t - u)) (hqholder (t - u) x)
      calc
        |heatHessianCoordConvolutionND u (q (t - u)) k x| ≤
            H * u ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
          simpa only [heatHessianCoordConvolutionND] using hb
        _ = A * u ^ p := by simp only [A, p]; ring
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact Set.indicator_nonneg
        (fun u hu => mul_nonneg hA (Real.rpow_nonneg hu.1.le p)) u
  · have hB : (0 : ℝ) ≤ t₁ - t₀ + 1 := by linarith
    have hpow : IntervalIntegrable (fun u : ℝ => u ^ p) volume 0 (t₁ - t₀ + 1) :=
      intervalIntegral.intervalIntegrable_rpow' hp
    have hpowOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp hpow
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (hpowOn.const_mul A)
  · have h0 : ∀ᵐ (u : ℝ), u ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : ℝ | ¬ a ≠ 0} = {0} := by ext a; simp
      rw [hset]
      exact MeasureTheory.measure_singleton 0
    have hd : ∀ᵐ (u : ℝ), u ≠ t₁ - t₀ := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : ℝ | ¬ a ≠ t₁ - t₀} = {t₁ - t₀} := by ext a; simp
      rw [hset]
      exact MeasureTheory.measure_singleton _
    filter_upwards [h0, hd] with u hu0 hud
    rcases lt_or_gt_of_ne hu0 with hult | hupos
    · have hzero : (fun t => Set.indicator (Set.Ioc (0 : ℝ) (t - t₀))
          (fun u => heatHessianCoordConvolutionND u (q (t - u)) k x) u) =
          fun _ => (0 : ℝ) := by
        funext t
        rw [Set.indicator_of_notMem
          (fun hm => absurd hm.1 (not_lt.2 hult.le))]
      rw [hzero]
      exact continuousAt_const
    · rcases lt_or_gt_of_ne hud with hulim | hulim
      · refine (continuous_heatHessianCoordConvolutionND_comp_sub_time
          hupos k hq x).continuousAt.congr ?_
        filter_upwards [Ioi_mem_nhds (show u + t₀ < t₁ by linarith)] with t htmem
        rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hupos, by linarith [Set.mem_Ioi.1 htmem]⟩)]
      · have hz : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t₁ := continuousAt_const
        refine hz.congr ?_
        filter_upwards [Iio_mem_nhds (show t₁ < u + t₀ by linarith)] with t htmem
        rw [Set.indicator_of_notMem
          (fun hm => absurd hm.2 (not_le.2 (by linarith [Set.mem_Iio.1 htmem])))]

/-- The full Duhamel Laplacian is continuous in positive final time. -/
theorem continuousAt_heatDuhamelLaplacianND_time
    {n : ℕ} {t₀ t₁ r : ℝ} (ht : t₀ < t₁) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    ContinuousAt (fun t => heatDuhamelLaplacianND t₀ t q x) t₁ := by
  classical
  rw [show (fun t => heatDuhamelLaplacianND t₀ t q x) =
      fun t => ∑ k : Fin n, heatDuhamelHessianCoordND t₀ t q k x by rfl]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t₁)
  | @insert k s hks ih =>
      have hadd := (continuousAt_heatDuhamelHessianCoordND_time
        ht hr0 hq hH hqb hqholder k x).add ih
      simp only [Finset.sum_insert hks]
      change ContinuousAt
        ((fun t => heatDuhamelHessianCoordND t₀ t q k x) +
          fun t => ∑ i ∈ s, heatDuhamelHessianCoordND t₀ t q i x) t₁
      exact hadd

/-! ## Triangular Fubini for the generator kernel -/

/-- The open time triangle `a < s < v < b`, ordered as `(v,s)`.  Removing
its boundary is harmless for Lebesgue integration and makes the heat time
`v-s` strictly positive everywhere on the set. -/
def heatTimeTriangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {z | a < z.1 ∧ z.1 < b ∧ a < z.2 ∧ z.2 < z.1}

theorem measurableSet_heatTimeTriangle (a b : ℝ) :
    MeasurableSet (heatTimeTriangle a b) := by
  simp only [heatTimeTriangle]
  measurability

/-- A vertical section of the open time-triangle indicator is the interval
integral over the earlier source times. -/
theorem integral_indicator_heatTimeTriangle_left
    {a b v : ℝ} (hv : v ∈ Set.Ioo a b) (G : ℝ × ℝ → ℝ) :
    (∫ s, Set.indicator (heatTimeTriangle a b) G (v, s)) =
      ∫ s in a..v, G (v, s) := by
  have heq : (fun s => Set.indicator (heatTimeTriangle a b) G (v, s)) =
      Set.indicator (Set.Ioo a v) (fun s => G (v, s)) := by
    funext s
    by_cases hs : s ∈ Set.Ioo a v
    · have htri : (v, s) ∈ heatTimeTriangle a b :=
        ⟨hv.1, hv.2, hs.1, hs.2⟩
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem htri]
    · have hn : (v, s) ∉ heatTimeTriangle a b := by
        intro htri
        exact hs ⟨htri.2.2.1, htri.2.2.2⟩
      rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hn]
  rw [heq, MeasureTheory.integral_indicator measurableSet_Ioo,
    MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le hv.1.le]

/-- A horizontal section of the open time-triangle indicator is the interval
integral over the later final times. -/
theorem integral_indicator_heatTimeTriangle_right
    {a b s : ℝ} (hs : s ∈ Set.Ioo a b) (G : ℝ × ℝ → ℝ) :
    (∫ v, Set.indicator (heatTimeTriangle a b) G (v, s)) =
      ∫ v in s..b, G (v, s) := by
  have heq : (fun v => Set.indicator (heatTimeTriangle a b) G (v, s)) =
      Set.indicator (Set.Ioo s b) (fun v => G (v, s)) := by
    funext v
    by_cases hv : v ∈ Set.Ioo s b
    · have htri : (v, s) ∈ heatTimeTriangle a b :=
        ⟨hs.1.trans hv.1, hv.2, hs.1, hv.1⟩
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem htri]
    · have hn : (v, s) ∉ heatTimeTriangle a b := by
        intro htri
        exact hv ⟨htri.2.2.2, htri.2.1⟩
      rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hn]
  rw [heq, MeasureTheory.integral_indicator measurableSet_Ioo,
    MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le hs.2.le]

/-- Joint measurability in final time and source time of a coordinate heat
Hessian convolution. -/
theorem aestronglyMeasurable_heatHessianCoordConvolutionND_twoTime
    {n : ℕ}
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (k : Fin n) (x : Fin n → ℝ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ =>
      heatHessianCoordConvolutionND (z.1 - z.2) (q z.2) k x)
      ((volume : Measure ℝ).prod volume) := by
  have hK : Measurable (fun z : (ℝ × ℝ) × (Fin n → ℝ) =>
      heatKernelND (z.1.1 - z.1.2) (x - z.2)) := by
    have hmap : Measurable (fun z : (ℝ × ℝ) × (Fin n → ℝ) =>
        (z.1.1 - z.1.2, x - z.2)) :=
      ((measurable_fst.comp measurable_fst).sub
        (measurable_snd.comp measurable_fst)).prodMk (measurable_const.sub measurable_snd)
    have hkernel := (measurable_uncurry_heatKernelND (n := n)).comp hmap
    exact hkernel
  have hc : Measurable (fun z : (ℝ × ℝ) × (Fin n → ℝ) =>
      (x - z.2) k ^ 2 / (4 * (z.1.1 - z.1.2) ^ 2) -
        1 / (2 * (z.1.1 - z.1.2))) := by
    fun_prop
  have hQ : Measurable (fun z : (ℝ × ℝ) × (Fin n → ℝ) =>
      (q z.1.2) z.2) := by
    exact (ContinuousEval.continuous_eval.comp
      ((hq.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)).measurable
  have hG : Measurable (fun z : (ℝ × ℝ) × (Fin n → ℝ) =>
      (heatKernelND (z.1.1 - z.1.2) (x - z.2) *
        ((x - z.2) k ^ 2 / (4 * (z.1.1 - z.1.2) ^ 2) -
          1 / (2 * (z.1.1 - z.1.2)))) * (q z.1.2) z.2) :=
    (hK.mul hc).mul hQ
  simpa only [heatHessianCoordConvolutionND] using
    (hG.aestronglyMeasurable
      (μ := ((volume : Measure ℝ).prod volume).prod
        (volume : Measure (Fin n → ℝ)))).integral_prod_right'

/-- The coordinate Hessian kernel is integrable on a finite open time
triangle.  This is the two-time integrability needed for Fubini: the spatial
Hölder cancellation bounds the kernel by `(v-s)^(-1+r/2)`, and integrating
first in `s` gives the finite outer majorant `(v-a)^(r/2)`. -/
theorem integrable_heatHessianCoordConvolutionND_timeTriangle
    {n : ℕ} {a b r : ℝ} (hab : a ≤ b) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    Integrable (Set.indicator (heatTimeTriangle a b)
      (fun z : ℝ × ℝ =>
        heatHessianCoordConvolutionND (z.1 - z.2) (q z.2) k x))
      ((volume : Measure ℝ).prod volume) := by
  let G : ℝ × ℝ → ℝ := fun z =>
    heatHessianCoordConvolutionND (z.1 - z.2) (q z.2) k x
  let F : ℝ × ℝ → ℝ := Set.indicator (heatTimeTriangle a b) G
  let A : ℝ := H * heatHessianHolderMoment n r k
  let p : ℝ := -1 + r / 2
  let R : ℝ → ℝ := fun v =>
    Set.indicator (Set.Ioo a b)
      (fun v => A * (v - a) ^ (r / 2) / (r / 2)) v
  have hA : 0 ≤ A := mul_nonneg hH (heatHessianHolderMoment_nonneg n r k)
  have hp : (-1 : ℝ) < p := by simp only [p]; linarith
  have hFm : AEStronglyMeasurable F ((volume : Measure ℝ).prod volume) := by
    exact (aestronglyMeasurable_heatHessianCoordConvolutionND_twoTime
      hq k x).indicator (measurableSet_heatTimeTriangle a b)
  have hsection : ∀ v : ℝ, Integrable (fun s => F (v, s)) := by
    intro v
    by_cases hv : v ∈ Set.Ioo a b
    · have hi := intervalIntegrable_hessian_heatKernelND_convolution
        (n := n) (t₀ := a) (t := v) (r := r) hv.1.le hr0 hq hH hqb
        hqholder x k
      have hiOn : IntegrableOn
          (fun s => heatHessianCoordConvolutionND (v - s) (q s) k x)
          (Set.Ioo a v) := by
        have hiIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hv.1.le).mp hi
        exact hiIoc.congr_set_ae Ioo_ae_eq_Ioc
      have hind := hiOn.integrable_indicator measurableSet_Ioo
      have heq : (fun s => F (v, s)) = Set.indicator (Set.Ioo a v)
          (fun s => heatHessianCoordConvolutionND (v - s) (q s) k x) := by
        funext s
        by_cases hs : s ∈ Set.Ioo a v
        · have htri : (v, s) ∈ heatTimeTriangle a b :=
            ⟨hv.1, hv.2, hs.1, hs.2⟩
          rw [Set.indicator_of_mem hs]
          simpa only [F] using Set.indicator_of_mem htri G
        · have hn : (v, s) ∉ heatTimeTriangle a b := by
            intro htri
            exact hs ⟨htri.2.2.1, htri.2.2.2⟩
          rw [Set.indicator_of_notMem hs]
          simpa only [F] using Set.indicator_of_notMem hn G
      rw [heq]
      exact hind
    · have hzero : (fun s => F (v, s)) = fun _ => (0 : ℝ) := by
        funext s
        have hn : ¬(a < v ∧ v < b ∧ a < s ∧ s < v) := by
          intro h
          exact hv ⟨h.1, h.2.1⟩
        have hn' : (v, s) ∉ heatTimeTriangle a b := by
          simpa only [heatTimeTriangle, Set.mem_ofPred_eq] using hn
        simpa only [F] using Set.indicator_of_notMem hn' G
      rw [hzero]
      exact MeasureTheory.integrable_zero ℝ ℝ volume
  have hR : Integrable R := by
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (r / 2))
        volume 0 (b - a) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hshift := hbase.comp_sub_right a
    have hw : IntervalIntegrable (fun v : ℝ => (v - a) ^ (r / 2))
        volume a b := by simpa only [zero_add, sub_add_cancel] using hshift
    have hscaled : IntervalIntegrable
        (fun v : ℝ => A * (v - a) ^ (r / 2) / (r / 2)) volume a b :=
      (hw.const_mul A).div_const (r / 2)
    have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hscaled
    have hIoo : IntegrableOn
        (fun v : ℝ => A * (v - a) ^ (r / 2) / (r / 2)) (Set.Ioo a b) :=
      hIoc.congr_set_ae Ioo_ae_eq_Ioc
    exact hIoo.integrable_indicator measurableSet_Ioo
  have hJm : AEStronglyMeasurable (fun v => ∫ s, ‖F (v, s)‖) :=
    hFm.norm.integral_prod_right'
  have hJbound : ∀ v : ℝ, (∫ s, ‖F (v, s)‖) ≤ R v := by
    intro v
    by_cases hv : v ∈ Set.Ioo a b
    · have hwbase : IntervalIntegrable (fun z : ℝ => z ^ p)
          volume 0 (v - a) := intervalIntegral.intervalIntegrable_rpow' hp
      have hwcomp := hwbase.comp_sub_left v
      have hw : IntervalIntegrable (fun s : ℝ => (v - s) ^ p)
          volume a v := by
        simpa only [sub_zero, sub_sub_cancel] using hwcomp.symm
      have hmajorI : Integrable
          (Set.indicator (Set.Ioo a v) (fun s => A * (v - s) ^ p)) := by
        have hwIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le hv.1.le).mp
          (hw.const_mul A)
        have hwIoo := hwIoc.congr_set_ae Ioo_ae_eq_Ioc
        exact hwIoo.integrable_indicator measurableSet_Ioo
      have hpoint : ∀ s, ‖F (v, s)‖ ≤
          Set.indicator (Set.Ioo a v) (fun s => A * (v - s) ^ p) s := by
        intro s
        by_cases hs : s ∈ Set.Ioo a v
        · rw [Set.indicator_of_mem hs]
          have htri : (v, s) ∈ heatTimeTriangle a b :=
            ⟨hv.1, hv.2, hs.1, hs.2⟩
          rw [show F (v, s) = G (v, s) by
            simpa only [F] using Set.indicator_of_mem htri G]
          rw [Real.norm_eq_abs]
          have hbnd := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
            (sub_pos.mpr hs.2) hr0.le hH x k
            (q s).continuous.aestronglyMeasurable (hqb s) (hqholder s x)
          calc
            |G (v, s)| ≤ H * (v - s) ^ (-1 + r / 2) *
                heatHessianHolderMoment n r k := by
              simpa only [G, heatHessianCoordConvolutionND] using hbnd
            _ = A * (v - s) ^ p := by simp only [A, p]; ring
        · rw [Set.indicator_of_notMem hs]
          have hn : (v, s) ∉ heatTimeTriangle a b := by
            intro htri
            exact hs ⟨htri.2.2.1, htri.2.2.2⟩
          rw [show F (v, s) = 0 by
            simpa only [F] using Set.indicator_of_notMem hn G, norm_zero]
      calc
        (∫ s, ‖F (v, s)‖) ≤
            ∫ s, Set.indicator (Set.Ioo a v)
              (fun s => A * (v - s) ^ p) s := by
          exact integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
            hmajorI (Filter.Eventually.of_forall hpoint)
        _ = A * (v - a) ^ (r / 2) / (r / 2) := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioo,
            MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
            ← intervalIntegral.integral_of_le hv.1.le,
            intervalIntegral.integral_const_mul,
            integral_rpow_sub a v hp]
          rw [show p + 1 = r / 2 by simp only [p]; ring]
          ring
        _ = R v := by simp only [R, Set.indicator_of_mem hv]
    · have hz : (fun s => F (v, s)) = fun _ => (0 : ℝ) := by
        funext s
        have hn : (v, s) ∉ heatTimeTriangle a b := by
          intro htri
          exact hv ⟨htri.1, htri.2.1⟩
        simpa only [F] using Set.indicator_of_notMem hn G
      have hRv : R v = 0 := by
        simpa only [R] using Set.indicator_of_notMem hv
          (fun v => A * (v - a) ^ (r / 2) / (r / 2))
      rw [hRv]
      have hnormzero : (fun s => ‖F (v, s)‖) = fun _ => (0 : ℝ) := by
        funext s
        rw [show F (v, s) = 0 by exact congrFun hz s, norm_zero]
      rw [hnormzero]
      simp
  have hJ : Integrable (fun v => ∫ s, ‖F (v, s)‖) :=
    hR.mono' hJm (Filter.Eventually.of_forall (fun v => by
      have hJn : 0 ≤ ∫ s : ℝ, ‖F (v, s)‖ :=
        integral_nonneg (fun s : ℝ => norm_nonneg (F (v, s)))
      rw [Real.norm_eq_abs, abs_of_nonneg hJn]
      exact hJbound v))
  have hprod : Integrable F ((volume : Measure ℝ).prod volume) :=
    (integrable_prod_iff hFm).mpr
      ⟨Filter.Eventually.of_forall (fun v => hsection v),
        hJ⟩
  simpa only [F, G] using hprod

/-- The time path of a coordinate Duhamel Hessian is interval-integrable on
every finite interval beginning at the initial time. -/
theorem intervalIntegrable_heatDuhamelHessianCoordND_time
    {n : ℕ} {a b r : ℝ} (hab : a ≤ b) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    IntervalIntegrable
      (fun v => heatDuhamelHessianCoordND a v q k x) volume a b := by
  let G : ℝ × ℝ → ℝ := fun z =>
    heatHessianCoordConvolutionND (z.1 - z.2) (q z.2) k x
  let F : ℝ × ℝ → ℝ := Set.indicator (heatTimeTriangle a b) G
  have hF : Integrable F ((volume : Measure ℝ).prod volume) := by
    simpa only [F, G] using
      integrable_heatHessianCoordConvolutionND_timeTriangle
        hab hr0 hq hH hqb hqholder k x
  have hout : Integrable (fun v => ∫ s, F (v, s)) := hF.integral_prod_left
  have heq : (fun v => ∫ s, F (v, s)) =
      Set.indicator (Set.Ioo a b)
        (fun v => heatDuhamelHessianCoordND a v q k x) := by
    funext v
    by_cases hv : v ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hv]
      simpa only [F, G, heatDuhamelHessianCoordND] using
        integral_indicator_heatTimeTriangle_left hv G
    · rw [Set.indicator_of_notMem hv]
      apply integral_eq_zero_of_ae
      filter_upwards with s
      have hn : (v, s) ∉ heatTimeTriangle a b := by
        intro htri
        exact hv ⟨htri.1, htri.2.1⟩
      change F (v, s) = 0
      simpa only [F] using Set.indicator_of_notMem hn G
  rw [heq] at hout
  have hIoo : IntegrableOn (fun v => heatDuhamelHessianCoordND a v q k x)
      (Set.Ioo a b) := (integrable_indicator_iff measurableSet_Ioo).mp hout
  have hIoc : IntegrableOn (fun v => heatDuhamelHessianCoordND a v q k x)
      (Set.Ioc a b) := hIoo.congr_set_ae Ioo_ae_eq_Ioc.symm
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hIoc

/-- The horizontal time-triangle section—integrating a fixed source time
through all later final times—is itself interval-integrable in the source
time. -/
theorem intervalIntegrable_integral_heatHessianCoordConvolutionND_laterTime
    {n : ℕ} {a b r : ℝ} (hab : a ≤ b) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    IntervalIntegrable (fun s => ∫ v in s..b,
      heatHessianCoordConvolutionND (v - s) (q s) k x) volume a b := by
  let G : ℝ × ℝ → ℝ := fun z =>
    heatHessianCoordConvolutionND (z.1 - z.2) (q z.2) k x
  let F : ℝ × ℝ → ℝ := Set.indicator (heatTimeTriangle a b) G
  have hF : Integrable F ((volume : Measure ℝ).prod volume) := by
    simpa only [F, G] using
      integrable_heatHessianCoordConvolutionND_timeTriangle
        hab hr0 hq hH hqb hqholder k x
  have hout : Integrable (fun s => ∫ v, F (v, s)) := hF.integral_prod_right
  have heq : (fun s => ∫ v, F (v, s)) =
      Set.indicator (Set.Ioo a b) (fun s => ∫ v in s..b,
        heatHessianCoordConvolutionND (v - s) (q s) k x) := by
    funext s
    by_cases hs : s ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hs]
      simpa only [F, G] using integral_indicator_heatTimeTriangle_right hs G
    · rw [Set.indicator_of_notMem hs]
      apply integral_eq_zero_of_ae
      filter_upwards with v
      have hn : (v, s) ∉ heatTimeTriangle a b := by
        intro htri
        exact hs ⟨htri.2.2.1, htri.2.2.2.trans htri.2.1⟩
      change F (v, s) = 0
      simpa only [F] using Set.indicator_of_notMem hn G
  rw [heq] at hout
  have hIoo : IntegrableOn (fun s => ∫ v in s..b,
      heatHessianCoordConvolutionND (v - s) (q s) k x) (Set.Ioo a b) :=
    (integrable_indicator_iff measurableSet_Ioo).mp hout
  have hIoc : IntegrableOn (fun s => ∫ v in s..b,
      heatHessianCoordConvolutionND (v - s) (q s) k x) (Set.Ioc a b) :=
    hIoo.congr_set_ae Ioo_ae_eq_Ioc.symm
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hIoc

/-- Fubini on the heat-time triangle, specialized to one coordinate Hessian.
The open-boundary representation is converted back to interval integrals on
both sides. -/
theorem integral_heatHessianCoordConvolutionND_timeTriangle_swap
    {n : ℕ} {a b r : ℝ} (hab : a ≤ b) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    (∫ v in a..b, ∫ s in a..v,
      heatHessianCoordConvolutionND (v - s) (q s) k x) =
      ∫ s in a..b, ∫ v in s..b,
        heatHessianCoordConvolutionND (v - s) (q s) k x := by
  let G : ℝ × ℝ → ℝ := fun z =>
    heatHessianCoordConvolutionND (z.1 - z.2) (q z.2) k x
  let F : ℝ × ℝ → ℝ := Set.indicator (heatTimeTriangle a b) G
  have hF : Integrable F ((volume : Measure ℝ).prod volume) := by
    simpa only [F, G] using
      integrable_heatHessianCoordConvolutionND_timeTriangle
        hab hr0 hq hH hqb hqholder k x
  have hleftSection : (fun v => ∫ s, F (v, s)) =
      Set.indicator (Set.Ioo a b) (fun v => ∫ s in a..v, G (v, s)) := by
    funext v
    by_cases hv : v ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hv]
      have heq : (fun s => F (v, s)) =
          Set.indicator (Set.Ioo a v) (fun s => G (v, s)) := by
        funext s
        by_cases hs : s ∈ Set.Ioo a v
        · have htri : (v, s) ∈ heatTimeTriangle a b :=
            ⟨hv.1, hv.2, hs.1, hs.2⟩
          rw [Set.indicator_of_mem hs]
          simpa only [F] using Set.indicator_of_mem htri G
        · have hn : (v, s) ∉ heatTimeTriangle a b := by
            intro htri
            exact hs ⟨htri.2.2.1, htri.2.2.2⟩
          rw [Set.indicator_of_notMem hs]
          simpa only [F] using Set.indicator_of_notMem hn G
      rw [heq, MeasureTheory.integral_indicator measurableSet_Ioo,
        MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
        ← intervalIntegral.integral_of_le hv.1.le]
    · rw [Set.indicator_of_notMem hv]
      apply integral_eq_zero_of_ae
      filter_upwards with s
      have hn : (v, s) ∉ heatTimeTriangle a b := by
        intro htri
        exact hv ⟨htri.1, htri.2.1⟩
      change F (v, s) = 0
      simpa only [F] using Set.indicator_of_notMem hn G
  have hrightSection : (fun s => ∫ v, F (v, s)) =
      Set.indicator (Set.Ioo a b) (fun s => ∫ v in s..b, G (v, s)) := by
    funext s
    by_cases hs : s ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hs]
      have heq : (fun v => F (v, s)) =
          Set.indicator (Set.Ioo s b) (fun v => G (v, s)) := by
        funext v
        by_cases hv : v ∈ Set.Ioo s b
        · have htri : (v, s) ∈ heatTimeTriangle a b :=
            ⟨hs.1.trans hv.1, hv.2, hs.1, hv.1⟩
          rw [Set.indicator_of_mem hv]
          simpa only [F] using Set.indicator_of_mem htri G
        · have hn : (v, s) ∉ heatTimeTriangle a b := by
            intro htri
            exact hv ⟨htri.2.2.2, htri.2.1⟩
          rw [Set.indicator_of_notMem hv]
          simpa only [F] using Set.indicator_of_notMem hn G
      rw [heq, MeasureTheory.integral_indicator measurableSet_Ioo,
        MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
        ← intervalIntegral.integral_of_le hs.2.le]
    · rw [Set.indicator_of_notMem hs]
      apply integral_eq_zero_of_ae
      filter_upwards with v
      have hn : (v, s) ∉ heatTimeTriangle a b := by
        intro htri
        exact hs ⟨htri.2.2.1, htri.2.2.2.trans htri.2.1⟩
      change F (v, s) = 0
      simpa only [F] using Set.indicator_of_notMem hn G
  have hF' : Integrable (Function.uncurry (fun v s => F (v, s)))
      ((volume : Measure ℝ).prod volume) := by
    change Integrable F ((volume : Measure ℝ).prod volume)
    exact hF
  have hswap := integral_integral_swap hF'
  rw [hleftSection, hrightSection] at hswap
  rw [MeasureTheory.integral_indicator measurableSet_Ioo,
    MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le hab] at hswap
  rw [MeasureTheory.integral_indicator measurableSet_Ioo,
    MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le hab] at hswap
  simpa only [G] using hswap

/-! ## The Duhamel time derivative -/

/-- Integrating the heat Laplacian of one frozen source from its source time
to a later final time recovers the corresponding heat-flow increment. -/
theorem integral_heatSemigroupLaplacianND_sub_source
    {n : ℕ} {s t r : ℝ} (hst : s < t) (hr0 : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    (∫ v in s..t, heatSemigroupLaplacianND (v - s) w x) =
      heatSemigroupND (t - s) (⇑w) x - w x := by
  rw [intervalIntegral.integral_comp_sub_right
    (fun u => heatSemigroupLaplacianND u w x) s]
  simpa only [sub_self] using
    (heatSemigroupND_sub_self_eq_integral_laplacian
      (sub_pos.mpr hst) hr0 w hH hholder x).symm

/-- The time integral of the Duhamel Laplacian is the integral of the
heat-flow increment of each frozen source.  This is the Fubini step behind
the classical inhomogeneous heat equation. -/
theorem integral_heatDuhamelLaplacianND_eq_integral_heat_sub
    {n : ℕ} {a b r : ℝ} (hab : a ≤ b) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    (∫ v in a..b, heatDuhamelLaplacianND a v q x) =
      ∫ s in a..b, (heatSemigroupND (b - s) (⇑(q s)) x - q s x) := by
  have houter : ∀ k : Fin n, IntervalIntegrable
      (fun v => heatDuhamelHessianCoordND a v q k x) volume a b := by
    intro k
    exact intervalIntegrable_heatDuhamelHessianCoordND_time
      hab hr0 hq hH hqb hqholder k x
  calc
    (∫ v in a..b, heatDuhamelLaplacianND a v q x) =
        ∑ k : Fin n, ∫ v in a..b,
          heatDuhamelHessianCoordND a v q k x := by
      change (∫ v in a..b, ∑ k : Fin n,
        heatDuhamelHessianCoordND a v q k x) = _
      rw [intervalIntegral.integral_finsetSum (fun k _ => houter k)]
    _ = ∑ k : Fin n, ∫ s in a..b, ∫ v in s..b,
          heatHessianCoordConvolutionND (v - s) (q s) k x := by
      apply Finset.sum_congr rfl
      intro k _
      exact integral_heatHessianCoordConvolutionND_timeTriangle_swap
        hab hr0 hq hH hqb hqholder k x
    _ = ∫ s in a..b, ∑ k : Fin n, ∫ v in s..b,
          heatHessianCoordConvolutionND (v - s) (q s) k x := by
      rw [intervalIntegral.integral_finsetSum]
      intro k _
      exact intervalIntegrable_integral_heatHessianCoordConvolutionND_laterTime
        hab hr0 hq hH hqb hqholder k x
    _ = ∫ s in a..b,
          (heatSemigroupND (b - s) (⇑(q s)) x - q s x) := by
      apply intervalIntegral.integral_congr_uIoo
      intro s hs
      rw [uIoo_of_le hab] at hs
      have hholderS : ∀ y z, |q s y - q s z| ≤
          H * ∑ j : Fin n, |(y - z) j| ^ r := by
        intro y z
        simpa only [abs_sub_comm] using hqholder s y z
      have hcoord : ∀ k : Fin n, IntervalIntegrable
          (fun v => heatHessianCoordConvolutionND (v - s) (q s) k x)
          volume s b := by
        intro k
        have hzero := intervalIntegrable_heatHessianCoordConvolutionND_zero
          (sub_nonneg.mpr hs.2.le) hr0 (q s) hH hholderS k x
        simpa only [zero_add, sub_add_cancel] using hzero.comp_sub_right s
      change (∑ k : Fin n, ∫ v in s..b,
        heatHessianCoordConvolutionND (v - s) (q s) k x) = _
      rw [← intervalIntegral.integral_finsetSum (fun k _ => hcoord k)]
      change (∫ v in s..b,
        heatSemigroupLaplacianND (v - s) (q s) x) = _
      exact integral_heatSemigroupLaplacianND_sub_source
        hs.2 hr0 (q s) hH hholderS x

/-- The Duhamel Laplacian is interval-integrable in final time. -/
theorem intervalIntegrable_heatDuhamelLaplacianND_time
    {n : ℕ} {a b r : ℝ} (hab : a ≤ b) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    IntervalIntegrable (fun v => heatDuhamelLaplacianND a v q x)
      volume a b := by
  have hsum : IntervalIntegrable
      (∑ k : Fin n, fun v => heatDuhamelHessianCoordND a v q k x)
      volume a b :=
    IntervalIntegrable.sum Finset.univ (fun k _ =>
      intervalIntegrable_heatDuhamelHessianCoordND_time
        hab hr0 hq hH hqb hqholder k x)
  convert hsum using 1
  ext v
  rw [heatDuhamelLaplacianND, Finset.sum_apply]

/-- **Duhamel integral equation.**  The mild inhomogeneous heat potential
satisfies the time integral of its classical right-hand side: source plus
its actual spatial Laplacian. -/
theorem heatDuhamelND_eq_integral_source_add_laplacian
    {n : ℕ} {a b r : ℝ} (hab : a ≤ b) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    (∫ s in a..b, heatSemigroupND (b - s) (⇑(q s)) x) =
      ∫ v in a..b, (q v x + heatDuhamelLaplacianND a v q x) := by
  have hsource : IntervalIntegrable (fun v => q v x) volume a b :=
    ((continuous_eval_const x).comp hq).intervalIntegrable a b
  have hheat : IntervalIntegrable
      (fun s => heatSemigroupND (b - s) (⇑(q s)) x) volume a b :=
    intervalIntegrable_heatSemigroupND_duhamel hab hq hqb x
  have hlap := intervalIntegrable_heatDuhamelLaplacianND_time
    hab hr0 hq hH hqb hqholder x
  rw [intervalIntegral.integral_add hsource hlap,
    integral_heatDuhamelLaplacianND_eq_integral_heat_sub
      hab hr0 hq hH hqb hqholder x,
    intervalIntegral.integral_sub hheat hsource]
  ring

/-- **Classical time equation for the Duhamel potential.**  At every time
strictly after the initial time, the Duhamel integral has time derivative
equal to its source plus its actual spatial Laplacian. -/
theorem hasDerivAt_heatDuhamelND_time_eq_source_add_laplacian
    {n : ℕ} {a t r : ℝ} (hat : a < t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    HasDerivAt
      (fun u => ∫ s in a..u, heatSemigroupND (u - s) (⇑(q s)) x)
      (q t x + heatDuhamelLaplacianND a t q x) t := by
  let F : ℝ → ℝ := fun v => q v x + heatDuhamelLaplacianND a v q x
  have hFint : IntervalIntegrable F volume a t := by
    apply IntervalIntegrable.add
    · exact ((continuous_eval_const x).comp hq).intervalIntegrable a t
    · exact intervalIntegrable_heatDuhamelLaplacianND_time
        hat.le hr0 hq hH hqb hqholder x
  have hFcont : ∀ u ∈ Set.Ioi a, ContinuousAt F u := by
    intro u hu
    exact ((continuous_eval_const x).comp hq).continuousAt.add
      (continuousAt_heatDuhamelLaplacianND_time
        hu hr0 hq hH hqb hqholder x)
  have hFmeas : StronglyMeasurableAtFilter F (nhds t) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hFcont t hat
  have hFTC : HasDerivAt (fun u => ∫ v in a..u, F v) (F t) t :=
    intervalIntegral.integral_hasDerivAt_right hFint hFmeas (hFcont t hat)
  have heq : Filter.Eventually (fun u =>
      (∫ s in a..u, heatSemigroupND (u - s) (⇑(q s)) x) =
        ∫ v in a..u, F v) (nhds t) := by
    filter_upwards [Ioi_mem_nhds hat] with u hu
    exact heatDuhamelND_eq_integral_source_add_laplacian
      hu.le hr0 hq hH hqb hqholder x
  simpa only [F] using hFTC.congr_of_eventuallyEq heq

/-- The complete scalar Euclidean mild heat solution, recorded here so its
time equation is proved in the same calculus environment as both summands. -/
def heatMildClassicalND {n : ℕ} (t₀ t : ℝ)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  heatSemigroupND (t - t₀) u₀ x +
    ∫ s in t₀..t, heatSemigroupND (t - s) (q s) x

/-- **Classical scalar Euclidean heat equation.**  The full mild solution has
time derivative equal to the homogeneous and Duhamel spatial Laplacians plus
the source at every positive elapsed time. -/
theorem hasDerivAt_heatMildClassicalND_time
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    @HasDerivAt ℝ _ ℝ NormedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun u => heatMildClassicalND t₀ u u₀ q x)
      (heatSemigroupLaplacianND (t - t₀) u₀ x +
        heatDuhamelLaplacianND t₀ t q x + q t x) t := by
  have hshift : HasDerivAt (fun u : ℝ => u - t₀) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t₀
  have hhom := (hasDerivAt_heatSemigroupND_time_eq_laplacian
    (sub_pos.mpr ht) u₀ x).comp t hshift
  have hduh := hasDerivAt_heatDuhamelND_time_eq_source_add_laplacian
    ht hr0 hq hH hqb hqholder x
  have hsum := hhom.add hduh
  have hfun : Filter.Eventually (fun u =>
      heatMildClassicalND t₀ u u₀ q x =
        (((fun s => heatSemigroupND s (⇑u₀) x) ∘ fun v => v - t₀) +
          fun v => ∫ s in t₀..v,
            heatSemigroupND (v - s) (⇑(q s)) x) u) (nhds t) := by
    filter_upwards with u
    rfl
  have hout := hsum.congr_of_eventuallyEq hfun
  apply hout.congr_deriv
  simp only [mul_one]
  ring

end AnalyticPDE
end RicciFlow
