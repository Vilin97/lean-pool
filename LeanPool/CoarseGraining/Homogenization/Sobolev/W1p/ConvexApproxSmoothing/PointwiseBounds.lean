/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Continuity

/-! # Pointwise Bounds -/

@[expose] public section

namespace Homogenization

open scoped Pointwise Convolution

/-!
# Pointwise bounds for `convexApproxSmoothing u − u`

Constant and zero-smoothing identities, the weighted-difference integral
representation of `convexApproxSmoothing u − u`, pointwise oscillation /
modulus / continuous bounds on `|convexApproxSmoothing u − u|`, and the
eventual-in-`ε` versions (including the one for the unit sequence), capped off
by `tendsto_unitConvexApproxSequence_of_continuous`.
-/

theorem norm_le_one_of_mem_closedBall_zero_one {d : ℕ} {z : Vec d}
    (hz : z ∈ Metric.closedBall (0 : Vec d) 1) :
    ‖z‖ ≤ 1 := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using hz

theorem convexApproxSample_mem_of_tsupport_subset_closedBall {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {ρ : Vec d → ℝ} {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U) (hball : Metric.closedBall x0 r ⊆ U)
    (hρ_sub : tsupport ρ ⊆ Metric.closedBall (0 : Vec d) 1)
    (hz : z ∈ tsupport ρ) (hr : 0 ≤ r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    convexApproxSample x0 z r ε x ∈ U := by
  exact convexApproxSample_mem_of_isOpenBoundedConvexDomain hU hx hball hr
    (norm_le_one_of_mem_closedBall_zero_one (hρ_sub hz)) hε0 hε1

theorem convexApproxSmoothing_const {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (c : ℝ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSmoothing ρ (fun _ => c) x0 r ε x = c := by
  simp [convexApproxSmoothing, convexApproxIntegrand, MeasureTheory.integral_mul_const,
    hρ.setIntegral_one]

theorem convexApproxSmoothing_zero {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ)
    (x0 : Vec d) (r : ℝ) (x : Vec d) :
    convexApproxSmoothing ρ u x0 r 0 x = u x := by
  simp [convexApproxSmoothing, convexApproxIntegrand, convexApproxSample,
    MeasureTheory.integral_mul_const, hρ.setIntegral_one]

theorem convexApproxSmoothing_sub_eq_setIntegral_weightedDiff {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSmoothing ρ u x0 r ε x - u x =
      ∫ z in tsupport ρ, ρ z * (u (convexApproxSample x0 z r ε x) - u x) := by
  have hInt1 :
      MeasureTheory.IntegrableOn
        (fun z => convexApproxIntegrand ρ u x0 r ε x z)
        (tsupport ρ) :=
    (integrable_convexApproxIntegrand hρ.continuous hρ.compactSupport hu x0 r ε x).integrableOn
  have hInt2 :
      MeasureTheory.IntegrableOn (fun z => ρ z * u x)
        (tsupport ρ) :=
    (integrable_convexApproxKernelMulConst hρ.continuous hρ.compactSupport (u x)).integrableOn
  have hconst :
      ∫ z in tsupport ρ, ρ z * u x = u x := by
    rw [MeasureTheory.integral_mul_const, hρ.setIntegral_one, one_mul]
  calc
    convexApproxSmoothing ρ u x0 r ε x - u x
      = (∫ z in tsupport ρ, convexApproxIntegrand ρ u x0 r ε x z) -
          ∫ z in tsupport ρ, ρ z * u x := by
            rw [convexApproxSmoothing]
            conv_lhs => rw [← hconst]
    _ = ∫ z in tsupport ρ, convexApproxIntegrand ρ u x0 r ε x z - ρ z * u x := by
          rw [MeasureTheory.integral_sub hInt1 hInt2]
    _ = ∫ z in tsupport ρ, ρ z * (u (convexApproxSample x0 z r ε x) - u x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with z
          simp [convexApproxIntegrand]
          ring

theorem abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤
      ∫ z in tsupport ρ, ρ z * |u (convexApproxSample x0 z r ε x) - u x| := by
  rw [convexApproxSmoothing_sub_eq_setIntegral_weightedDiff hρ hu x0 r ε x]
  calc
    |∫ z in tsupport ρ, ρ z * (u (convexApproxSample x0 z r ε x) - u x)| ≤
        ∫ z in tsupport ρ, |ρ z * (u (convexApproxSample x0 z r ε x) - u x)| := by
          simpa using
            (MeasureTheory.abs_integral_le_integral_abs
              (μ := MeasureTheory.volume.restrict (tsupport ρ))
              (f := fun z => ρ z * (u (convexApproxSample x0 z r ε x) - u x)))
    _ = ∫ z in tsupport ρ, ρ z * |u (convexApproxSample x0 z r ε x) - u x| := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with z
          rw [abs_mul, abs_of_nonneg (hρ.nonneg z)]

theorem abs_convexApproxSmoothing_sub_le_of_pointwiseOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) {δ : ℝ}
    (hosc : ∀ z ∈ tsupport ρ, |u (convexApproxSample x0 z r ε x) - u x| ≤ δ) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := by
  have hIntLeft :
      MeasureTheory.IntegrableOn
        (fun z => ρ z * |u (convexApproxSample x0 z r ε x) - u x|)
        (tsupport ρ) := by
    exact
      MeasureTheory.Integrable.integrableOn
        (integrable_convexApproxWeightedOscillation hρ.continuous hρ.compactSupport hu x0 r ε x)
  have hIntRight :
      MeasureTheory.IntegrableOn (fun z => ρ z * δ) (tsupport ρ) := by
    exact
      MeasureTheory.Integrable.integrableOn
        (integrable_convexApproxKernelMulConst hρ.continuous hρ.compactSupport δ)
  calc
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤
        ∫ z in tsupport ρ, ρ z * |u (convexApproxSample x0 z r ε x) - u x| :=
      abs_convexApproxSmoothing_sub_le_setIntegral_weightedOscillation hρ hu x0 r ε x
    _ ≤ ∫ z in tsupport ρ, ρ z * δ := by
          refine MeasureTheory.setIntegral_mono_on hIntLeft hIntRight
            (isClosed_tsupport ρ).measurableSet ?_
          intro z hz
          exact mul_le_mul_of_nonneg_left (hosc z hz) (hρ.nonneg z)
    _ = δ := by
          rw [MeasureTheory.integral_mul_const, hρ.setIntegral_one, one_mul]

theorem abs_convexApproxSmoothing_sub_le_of_modulus
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x x0 : Vec d} {r ε : ℝ}
    (hx : x ∈ U) (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {δ : ℝ}
    (hmod :
      ∀ y ∈ U, ‖y - x‖ ≤ ε * (2 * Classical.choose hU.isBoundedDomain) →
        |u y - u x| ≤ δ) :
    |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := by
  apply abs_convexApproxSmoothing_sub_le_of_pointwiseOscillation hρ hu x0 r ε x
  intro z hz
  have hy : convexApproxSample x0 z r ε x ∈ U :=
    convexApproxSample_mem_of_tsupport_subset_closedBall hU hx hball
      hρ.support_subset_closedBall hz hr hε0 hε1
  have hdist :
      ‖convexApproxSample x0 z r ε x - x‖ ≤
        ε * (2 * Classical.choose hU.isBoundedDomain) :=
    norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
      hU hx hball hr
      (norm_le_one_of_mem_closedBall_zero_one (hρ.support_subset_closedBall hz)) hε0
  exact hmod _ hy hdist

theorem exists_pos_forall_abs_convexApproxSmoothing_sub_le_of_continuous
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ ⦃x : Vec d⦄, x ∈ U → ∀ ⦃ε : ℝ⦄,
      0 ≤ ε → ε ≤ 1 → ε * (2 * Classical.choose hU.isBoundedDomain) ≤ η →
      |convexApproxSmoothing ρ u x0 r ε x - u x| ≤ δ := by
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  have huc : UniformContinuousOn u (closure U) :=
    hcompact.uniformContinuousOn_of_continuous hu.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp huc) δ hδ with ⟨η, hηpos, hη⟩
  refine ⟨η, hηpos, ?_⟩
  intro x hx ε hε0 hε1 hεη
  apply abs_convexApproxSmoothing_sub_le_of_modulus hU hρ hu hx hball hr hε0 hε1
  intro y hy hyx
  have hxcl : x ∈ closure U := subset_closure hx
  have hycl : y ∈ closure U := subset_closure hy
  have hdist : dist (u y) (u x) ≤ δ := by
    apply hη y hycl x hxcl
    calc
      dist y x = ‖y - x‖ := by simpa using (dist_eq_norm y x)
      _ ≤ ε * (2 * Classical.choose hU.isBoundedDomain) := hyx
      _ ≤ η := hεη
  simpa [dist_eq_norm] using hdist

theorem two_mul_choose_isBoundedDomain_nonneg
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    0 ≤ 2 * Classical.choose hU := by
  have hchoose_nonneg : 0 ≤ Classical.choose hU :=
    le_of_lt (Classical.choose_spec hU).1
  positivity

theorem eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
    {d : ℕ} {U : Set (Vec d)} {ρ u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hρ : IsConvexApproxKernel ρ) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ ε n)
    (hε_le_one : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ⦃x : Vec d⦄, x ∈ U →
      |convexApproxSmoothing ρ u x0 r (ε n) x - u x| ≤ δ := by
  obtain ⟨η, hηpos, hη⟩ :=
    exists_pos_forall_abs_convexApproxSmoothing_sub_le_of_continuous
      hU hρ hu hball hr hδ
  let C : ℝ := 2 * Classical.choose hU.isBoundedDomain
  have hCnonneg : 0 ≤ C := by
    simpa [C] using two_mul_choose_isBoundedDomain_nonneg hU.isBoundedDomain
  have hscaled :
      Filter.Tendsto (fun n : ℕ => ε n * C) Filter.atTop (nhds 0) := by
    simpa using (hε.mul_const C)
  filter_upwards [Metric.tendsto_nhds.mp hscaled η hηpos, hε_nonneg, hε_le_one] with
      n hn hε0 hε1 x hx
  have hlt : ε n * C < η := by
    have hn' : |ε n| * |C| < η := by
      simpa [Real.dist_eq] using hn
    simpa [abs_of_nonneg hε0, abs_of_nonneg hCnonneg] using hn'
  exact hη hx hε0 hε1 (le_of_lt hlt)

theorem eventually_forall_abs_unitConvexApproxSequence_sub_le_of_continuous
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ⦃x : Vec d⦄, x ∈ U →
      |unitConvexApproxSequence u x0 r n x - u x| ≤ δ := by
  simpa [unitConvexApproxSequence] using
    (eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
      hU (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hu hball hr
      tendsto_unitConvexApproxScale_zero
      (Filter.Eventually.of_forall unitConvexApproxScale_nonneg)
      (Filter.Eventually.of_forall unitConvexApproxScale_le_one)
      hδ)

theorem tendsto_unitConvexApproxSequence_of_continuous
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hu : Continuous u)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r)
    {x : Vec d} (hx : x ∈ U) :
    Filter.Tendsto
      (fun n : ℕ => unitConvexApproxSequence u x0 r n x)
      Filter.atTop (nhds (u x)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδhalf : 0 < δ / 2 := by linarith
  filter_upwards
    [eventually_forall_abs_unitConvexApproxSequence_sub_le_of_continuous
      hU hu hball hr hδhalf] with n hn
  have hbound :
      |unitConvexApproxSequence u x0 r n x - u x| ≤ δ / 2 := by
    exact hn hx
  have hlt : |unitConvexApproxSequence u x0 r n x - u x| < δ := by
    exact lt_of_le_of_lt hbound (by linarith)
  simpa [Real.dist_eq, unitConvexApproxSequence] using hlt

end Homogenization
