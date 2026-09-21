/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.SmoothCase

/-! # Convex Approx Tendsto -/

namespace Homogenization

open scoped ENNReal

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
theorem unitConvexApproxScale_pos (n : ℕ) :
    0 < unitConvexApproxScale n := by
  dsimp [unitConvexApproxScale]
  positivity

noncomputable def convexApproxSmoothW1p
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) : W1pFunction U p :=
  W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
    ((contDiff_convexApproxSmoothRepresentative
      (U := U) (ρ := unitConvexApproxKernel (d := d)) (u := u.toFun)
      (p := p) (x0 := x0) (r := r) (ε := unitConvexApproxScale n)
      hU.isOpen.measurableSet (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      hp1 u.memLp hr (unitConvexApproxScale_pos n)).of_le (by simp))

private theorem convexApproxSmoothW1p_toFun
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n).toFun =
      convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u.toFun x0 r
        (unitConvexApproxScale n) := by
  funext x
  simp [convexApproxSmoothW1p, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem convexApproxSmoothW1p_grad
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n).grad =
      fun x i =>
        (fderiv ℝ
          (convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u.toFun x0 r
            (unitConvexApproxScale n)) x) (basisVec i) := by
  funext x i
  simp [convexApproxSmoothW1p, W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

/-- Canonical convex smooth approximants converge to a `W^{1,p}` function in
the value `L^p` norm on a bounded open convex domain. -/
theorem tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => (convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n).toFun x - u.toFun x)
          p (volumeMeasureOn U))
      Filter.atTop (nhds 0) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → W1pFunction U p := convexApproxSmoothW1p (U := U) hU hp1 u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in Filter.atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      (fun _ hn => hn))
  have hraw :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x => convexApproxSmoothing ρ u.toFun x0 r (unitConvexApproxScale n) x -
              u.toFun x)
            p (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ hp1 hp u.memLp hball hr tendsto_unitConvexApproxScale_zero
        (Filter.Eventually.of_forall unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x =>
              convexApproxSmoothRepresentative U ρ u.toFun x0 r (unitConvexApproxScale n) x -
                u.toFun x)
            p (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u.toFun) hU hρ hx hball hr (unitConvexApproxScale_pos n) hε_lt_one]
  refine hrep.congr' ?_
  filter_upwards with n
  apply MeasureTheory.eLpNorm_congr_ae
  filter_upwards with x
  rw [show (ψ n).toFun x =
      convexApproxSmoothRepresentative U ρ u.toFun x0 r (unitConvexApproxScale n) x by
        simpa [ψ, ρ] using congrFun
          (convexApproxSmoothW1p_toFun (U := U) hU hp1 u x0 hr n) x]

/-- Canonical convex smooth approximants converge coordinatewise to the weak
gradient in the `L^p` norm on a bounded open convex domain. -/
theorem tendsto_convexApproxSmoothW1p_grad_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (i : Fin d) :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => (convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n).grad x i -
            u.grad x i)
          p (volumeMeasureOn U))
      Filter.atTop (nhds 0) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  let ψ : ℕ → W1pFunction U p := convexApproxSmoothW1p (U := U) hU hp1 u x0 hr
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hevent_lt_one : ∀ᶠ n : ℕ in Filter.atTop, unitConvexApproxScale n < 1 :=
    (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      (fun _ hn => hn))
  have hraw :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x =>
              (1 - unitConvexApproxScale n) *
                  convexApproxSmoothing ρ (fun y => u.grad y i) x0 r
                    (unitConvexApproxScale n) x -
                u.grad x i)
            p (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    simpa [ρ, volumeMeasureOn] using
      (tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ hp1 hp (u.grad_memLp i) hball hr
        tendsto_unitConvexApproxScale_zero
        (Filter.Eventually.of_forall unitConvexApproxScale_pos) hevent_lt_one)
  have hrep :
      Filter.Tendsto
        (fun n : ℕ =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ
                (convexApproxSmoothRepresentative U ρ u.toFun x0 r (unitConvexApproxScale n)) x)
                  (basisVec i) -
                u.grad x i)
            p (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    refine hraw.congr' ?_
    filter_upwards [hevent_lt_one] with n hε_lt_one
    apply MeasureTheory.eLpNorm_congr_ae
    have hbridge :=
      ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
        (U := U) (ρ := ρ) (u := u.toFun) (gi := fun y => u.grad y i)
        (i := i) (p := p) hU hρ hp1 u.memLp (u.grad_memLp i)
        (u.hasWeakPartialDerivOn i) hball hr (unitConvexApproxScale_pos n) hε_lt_one
    filter_upwards [hbridge, MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with
      x hxbridge hxU
    rw [hxbridge]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := fun y => u.grad y i) hU hρ hxU hball hr (unitConvexApproxScale_pos n)
        hε_lt_one]
  refine hrep.congr' ?_
  filter_upwards with n
  apply MeasureTheory.eLpNorm_congr_ae
  filter_upwards with x
  rw [show (ψ n).grad x i =
      (fderiv ℝ
        (convexApproxSmoothRepresentative U ρ u.toFun x0 r (unitConvexApproxScale n)) x)
          (basisVec i) by
        simpa [ψ, ρ] using congrFun
          (congrFun (convexApproxSmoothW1p_grad (U := U) hU hp1 u x0 hr n) x) i]

private theorem tendsto_setIntegral_of_tendsto_eLpNorm_sub_of_one_lt
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {q : ℝ} (hq : 1 < q) {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hDiffMeas :
      ∀ n, MeasureTheory.AEStronglyMeasurable (fun x => F n x - f x) (volumeMeasureOn U))
    (hf_int : MeasureTheory.Integrable f (volumeMeasureOn U))
    (hF_int : ∀ᶠ n : ℕ in Filter.atTop,
      MeasureTheory.Integrable (F n) (volumeMeasureOn U))
    (hLp :
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) (ENNReal.ofReal q)
          (volumeMeasureOn U))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, F n x ∂MeasureTheory.volume)
      Filter.atTop (nhds (∫ x in U, f x ∂MeasureTheory.volume)) := by
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let pE : ENNReal := ENNReal.ofReal q
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hpE_one : (1 : ENNReal) ≤ pE := by
    dsimp [pE]
    rw [ENNReal.one_le_ofReal]
    exact hq.le
  have hexp_nonneg : 0 ≤ (1 - 1 / q : ℝ) := by
    have hinv_le : 1 / q ≤ 1 := (div_le_one hq_pos).2 hq.le
    linarith
  have hL1_bound :
      ∀ n,
        MeasureTheory.eLpNorm (fun x => F n x - f x) 1 μ ≤
          MeasureTheory.eLpNorm (fun x => F n x - f x) pE μ *
            μ Set.univ ^ (1 - 1 / q : ℝ) := by
    intro n
    simpa [μ, pE, ENNReal.toReal_ofReal hq_pos.le] using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ)
        (f := fun x => F n x - f x)
        (p := (1 : ENNReal))
        (q := pE)
        hpE_one
        (by simpa [μ] using hDiffMeas n))
  have hConst_ne_top : μ Set.univ ^ (1 - 1 / q : ℝ) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg hexp_nonneg ?_).ne
    exact (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hL1 :
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) 1 μ)
        Filter.atTop (nhds 0) := by
    have hscaled :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm (fun x => F n x - f x) pE μ *
              μ Set.univ ^ (1 - 1 / q : ℝ))
          Filter.atTop
          (nhds (0 * (μ Set.univ ^ (1 - 1 / q : ℝ)))) := by
      exact ENNReal.Tendsto.mul_const (by simpa [μ, pE] using hLp) (Or.inr hConst_ne_top)
    have hscaled0 :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm (fun x => F n x - f x) pE μ *
              μ Set.univ ^ (1 - 1 / q : ℝ))
          Filter.atTop (nhds 0) := by
      simpa [zero_mul] using hscaled
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hscaled0
      (fun _ => zero_le)
      hL1_bound
  simpa [μ, volumeMeasureOn, Pi.sub_apply] using
    (MeasureTheory.tendsto_integral_of_L1'
      (μ := μ)
      (f := f)
      hf_int.aestronglyMeasurable
      (by
        filter_upwards [hF_int] with n hn
        exact hn)
      hL1)

private theorem tendsto_integralAverage_of_tendsto_eLpNorm_sub_of_one_lt
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {q : ℝ} (hq : 1 < q) {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hDiffMeas :
      ∀ n, MeasureTheory.AEStronglyMeasurable (fun x => F n x - f x) (volumeMeasureOn U))
    (hf_int : MeasureTheory.Integrable f (volumeMeasureOn U))
    (hF_int : ∀ᶠ n : ℕ in Filter.atTop,
      MeasureTheory.Integrable (F n) (volumeMeasureOn U))
    (hLp :
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) (ENNReal.ofReal q)
          (volumeMeasureOn U))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => integralAverage U (F n)) Filter.atTop
      (nhds (integralAverage U f)) := by
  have hInt :=
    tendsto_setIntegral_of_tendsto_eLpNorm_sub_of_one_lt
      (U := U) hq hDiffMeas hf_int hF_int hLp
  simpa [integralAverage, mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_const_nhds.mul hInt :
      Filter.Tendsto
        (fun n => (MeasureTheory.volume U).toReal⁻¹ *
          ∫ x in U, F n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds ((MeasureTheory.volume U).toReal⁻¹ *
          ∫ x in U, f x ∂MeasureTheory.volume)))

private theorem tendsto_toReal_eLpNorm_of_tendsto_eLpNorm_sub
    {μ : MeasureTheory.Measure (Vec d)} (hp1 : 1 ≤ p)
    {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hF_mem : ∀ n, MeasureTheory.MemLp (F n) p μ)
    (hf_mem : MeasureTheory.MemLp f p μ)
    (hLp :
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun x => F n x - f x) p μ)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ENNReal.toReal (MeasureTheory.eLpNorm (F n) p μ))
      Filter.atTop (nhds (ENNReal.toReal (MeasureTheory.eLpNorm f p μ))) := by
  let : Fact (1 ≤ p) := ⟨hp1⟩
  have hLpSpace :
      Filter.Tendsto (fun n => (hF_mem n).toLp (F n))
        Filter.atTop (nhds (hf_mem.toLp f)) := by
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (μ := μ) (p := p) F hF_mem f hf_mem).2
        (by simpa [Pi.sub_apply] using! hLp)
  have hnorm :
      Filter.Tendsto (fun n => ‖(hF_mem n).toLp (F n)‖)
        Filter.atTop (nhds ‖hf_mem.toLp f‖) :=
    hLpSpace.norm
  simpa [MeasureTheory.Lp.norm_toLp] using hnorm

private theorem tendsto_convexApproxSmoothW1p_gradCoordLpSeminorm
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (i : Fin d) :
    Filter.Tendsto
      (fun n => (convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n).gradCoordLpSeminorm i)
      Filter.atTop (nhds (u.gradCoordLpSeminorm i)) := by
  let ψ : ℕ → W1pFunction U p := convexApproxSmoothW1p (U := U) hU hp1 u x0 hr
  have hLp :=
    tendsto_convexApproxSmoothW1p_grad_eLpNorm_sub
      (U := U) hU hp1 hp u hball hr i
  have hnorm :=
    tendsto_toReal_eLpNorm_of_tendsto_eLpNorm_sub
      (μ := volumeMeasureOn U) (p := p) hp1
      (F := fun n => fun x => (ψ n).grad x i) (f := fun x => u.grad x i)
      (fun n => (ψ n).grad_memLp i) (u.grad_memLp i)
      (by simpa [ψ] using hLp)
  simpa [W1pFunction.gradCoordLpSeminorm, ψ] using hnorm

theorem tendsto_convexApproxSmoothW1p_gradientCoordLpSeminormSum
    (hU : IsOpenBoundedConvexDomain U) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Filter.Tendsto
      (fun n => (convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n).gradientCoordLpSeminormSum)
      Filter.atTop (nhds u.gradientCoordLpSeminormSum) := by
  have hgrad :
      ∀ i : Fin d,
        Filter.Tendsto
          (fun n => (convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n).gradCoordLpSeminorm i)
          Filter.atTop (nhds (u.gradCoordLpSeminorm i)) := by
    intro i
    exact tendsto_convexApproxSmoothW1p_gradCoordLpSeminorm
      (U := U) hU hp1 hp u hball hr i
  simpa [W1pFunction.gradientCoordLpSeminormSum] using
    tendsto_finsetSum Finset.univ (fun i _ => hgrad i)

private theorem tendsto_convexApproxSmoothW1p_integralAverage_ofReal
    (hU : IsOpenBoundedConvexDomain U) {q : ℝ} (hq : 1 < q)
    (u : W1pFunction U (ENNReal.ofReal q))
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Filter.Tendsto
      (fun n => integralAverage U
        (convexApproxSmoothW1p (U := U) hU
          (by rw [ENNReal.one_le_ofReal]; exact hq.le) u x0 hr n).toFun)
      Filter.atTop (nhds (integralAverage U u.toFun)) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  let pE : ENNReal := ENNReal.ofReal q
  let hp1 : 1 ≤ pE := by
    dsimp [pE]
    rw [ENNReal.one_le_ofReal]
    exact hq.le
  let ψ : ℕ → W1pFunction U pE := convexApproxSmoothW1p (U := U) hU hp1 u x0 hr
  have hp_top : pE ≠ ⊤ := by
    dsimp [pE]
    exact ENNReal.ofReal_ne_top
  have hLp :=
    tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
      (U := U) hU hp1 hp_top u hball hr
  have hDiffMeas :
      ∀ n, MeasureTheory.AEStronglyMeasurable
        (fun x => (ψ n).toFun x - u.toFun x) (volumeMeasureOn U) := by
    intro n
    exact ((ψ n).memLp.sub u.memLp).aestronglyMeasurable
  have hf_int : MeasureTheory.Integrable u.toFun (volumeMeasureOn U) :=
    u.memLp.integrable hp1
  have hψ_int : ∀ᶠ n : ℕ in Filter.atTop,
      MeasureTheory.Integrable (ψ n).toFun (volumeMeasureOn U) :=
    Filter.Eventually.of_forall fun n => (ψ n).memLp.integrable hp1
  have havg :=
    tendsto_integralAverage_of_tendsto_eLpNorm_sub_of_one_lt
      (U := U) hq hDiffMeas hf_int hψ_int
      (by simpa [ψ, pE] using hLp)
  simpa [ψ, pE, hp1] using havg

theorem tendsto_convexApproxSmoothW1p_subAverageLpSeminorm_ofReal
    (hU : IsOpenBoundedConvexDomain U) {q : ℝ} (hq : 1 < q)
    (u : W1pFunction U (ENNReal.ofReal q))
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    Filter.Tendsto
      (fun n =>
        (convexApproxSmoothW1p (U := U) hU
          (by rw [ENNReal.one_le_ofReal]; exact hq.le) u x0 hr n).subAverageLpSeminorm)
      Filter.atTop (nhds u.subAverageLpSeminorm) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn U
  let pE : ENNReal := ENNReal.ofReal q
  let hp1 : 1 ≤ pE := by
    dsimp [pE]
    rw [ENNReal.one_le_ofReal]
    exact hq.le
  let ψ : ℕ → W1pFunction U pE := convexApproxSmoothW1p (U := U) hU hp1 u x0 hr
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hp0 : pE ≠ 0 := by
    dsimp [pE]
    intro hzero
    exact (not_le_of_gt hq_pos) (ENNReal.ofReal_eq_zero.mp hzero)
  have hp_top : pE ≠ ⊤ := by
    dsimp [pE]
    exact ENNReal.ofReal_ne_top
  have hLp_value :=
    tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
      (U := U) hU hp1 hp_top u hball hr
  have havg :=
    tendsto_convexApproxSmoothW1p_integralAverage_ofReal
      (U := U) hU hq u hball hr
  have havgdiff :
      Filter.Tendsto
        (fun n => integralAverage U u.toFun - integralAverage U (ψ n).toFun)
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _ : ℕ => integralAverage U u.toFun)
          Filter.atTop (nhds (integralAverage U u.toFun)) :=
      tendsto_const_nhds
    have hψavg :
        Filter.Tendsto (fun n => integralAverage U (ψ n).toFun)
          Filter.atTop (nhds (integralAverage U u.toFun)) := by
      simpa [ψ, pE, hp1] using havg
    have htmp := hconst.sub hψavg
    simpa using htmp
  have hconstFactor_ne_top : μ Set.univ ^ (1 / q : ℝ) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_).ne
    exact (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hconst_tendsto :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun _ : Vec d => integralAverage U u.toFun - integralAverage U (ψ n).toFun)
            pE μ)
        Filter.atTop (nhds 0) := by
    have henorm :
        Filter.Tendsto
          (fun n => ‖integralAverage U u.toFun - integralAverage U (ψ n).toFun‖ₑ)
          Filter.atTop (nhds 0) := by
      have hnorm := havgdiff.norm
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using ENNReal.tendsto_ofReal hnorm
    have hscaled :
        Filter.Tendsto
          (fun n =>
            ‖integralAverage U u.toFun - integralAverage U (ψ n).toFun‖ₑ *
              μ Set.univ ^ (1 / q : ℝ))
          Filter.atTop (nhds 0) := by
      have htmp :=
        ENNReal.Tendsto.mul_const henorm (Or.inr hconstFactor_ne_top)
      simpa [zero_mul] using htmp
    have hformula :
        (fun n =>
          MeasureTheory.eLpNorm
            (fun _ : Vec d => integralAverage U u.toFun - integralAverage U (ψ n).toFun)
            pE μ) =
        fun n =>
          ‖integralAverage U u.toFun - integralAverage U (ψ n).toFun‖ₑ *
            μ Set.univ ^ (1 / q : ℝ) := by
      funext n
      simpa [pE, ENNReal.toReal_ofReal hq_pos.le] using
        (MeasureTheory.eLpNorm_const'
          (μ := μ) (p := pE)
          (c := integralAverage U u.toFun - integralAverage U (ψ n).toFun)
          hp0 hp_top)
    simpa [hformula] using hscaled
  have hsubavg_bound :
      ∀ n,
        MeasureTheory.eLpNorm
          (fun x =>
            ((ψ n).toFun x - integralAverage U (ψ n).toFun) -
              (u.toFun x - integralAverage U u.toFun))
          pE μ ≤
          MeasureTheory.eLpNorm (fun x => (ψ n).toFun x - u.toFun x) pE μ +
            MeasureTheory.eLpNorm
              (fun _ : Vec d => integralAverage U u.toFun - integralAverage U (ψ n).toFun)
              pE μ := by
    intro n
    let A : Vec d → ℝ := fun x => (ψ n).toFun x - u.toFun x
    let B : Vec d → ℝ := fun _ => integralAverage U u.toFun - integralAverage U (ψ n).toFun
    have hmeasA : MeasureTheory.AEStronglyMeasurable A μ :=
      ((ψ n).memLp.sub u.memLp).aestronglyMeasurable
    have hmeasB : MeasureTheory.AEStronglyMeasurable B μ :=
      (MeasureTheory.memLp_const (integralAverage U u.toFun - integralAverage U (ψ n).toFun)
        (μ := μ) (p := pE)).aestronglyMeasurable
    calc
      MeasureTheory.eLpNorm
          (fun x =>
            ((ψ n).toFun x - integralAverage U (ψ n).toFun) -
              (u.toFun x - integralAverage U u.toFun))
          pE μ
          = MeasureTheory.eLpNorm (A + B) pE μ := by
              apply MeasureTheory.eLpNorm_congr_ae
              filter_upwards with x
              dsimp [A, B]
              ring
      _ ≤ MeasureTheory.eLpNorm A pE μ + MeasureTheory.eLpNorm B pE μ :=
            MeasureTheory.eLpNorm_add_le hmeasA hmeasB hp1
      _ = MeasureTheory.eLpNorm (fun x => (ψ n).toFun x - u.toFun x) pE μ +
            MeasureTheory.eLpNorm
              (fun _ : Vec d => integralAverage U u.toFun - integralAverage U (ψ n).toFun)
              pE μ := by
            rfl
  have hsubavg_eLp :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              ((ψ n).toFun x - integralAverage U (ψ n).toFun) -
                (u.toFun x - integralAverage U u.toFun))
            pE μ)
        Filter.atTop (nhds 0) := by
    have hsum :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm (fun x => (ψ n).toFun x - u.toFun x) pE μ +
              MeasureTheory.eLpNorm
                (fun _ : Vec d => integralAverage U u.toFun - integralAverage U (ψ n).toFun)
                pE μ)
          Filter.atTop (nhds 0) := by
      have hvalue :
          Filter.Tendsto
            (fun n => MeasureTheory.eLpNorm (fun x => (ψ n).toFun x - u.toFun x) pE μ)
            Filter.atTop (nhds 0) := by
        simpa [ψ, pE, μ] using hLp_value
      simpa [zero_add] using hvalue.add hconst_tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hsum
      (fun _ => zero_le)
      hsubavg_bound
  have hF_mem :
      ∀ n, MeasureTheory.MemLp
        (fun x => (ψ n).toFun x - integralAverage U (ψ n).toFun) pE μ := by
    intro n
    exact (ψ n).memLp.sub (MeasureTheory.memLp_const (integralAverage U (ψ n).toFun))
  have hf_mem :
      MeasureTheory.MemLp (fun x => u.toFun x - integralAverage U u.toFun) pE μ :=
    u.memLp.sub (MeasureTheory.memLp_const (integralAverage U u.toFun))
  have hnorm :=
    tendsto_toReal_eLpNorm_of_tendsto_eLpNorm_sub
      (μ := μ) (p := pE) hp1
      (F := fun n => fun x => (ψ n).toFun x - integralAverage U (ψ n).toFun)
      (f := fun x => u.toFun x - integralAverage U u.toFun)
      hF_mem hf_mem
      (by simpa [Pi.sub_apply] using hsubavg_eLp)
  simpa [W1pFunction.subAverageLpSeminorm, ψ, pE, μ] using hnorm


end W1pFunction

end Homogenization
