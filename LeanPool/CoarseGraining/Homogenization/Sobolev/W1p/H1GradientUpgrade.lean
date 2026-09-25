/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.WeakGradientClosure
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent

/-!
# Upgrading `H¹` witnesses from higher-integrable gradients

On a bounded open convex domain, an `H1Function` whose weak-gradient
coordinates belong to a finite `L^p` space is also a `W^{1,p}` witness.  The
value membership is obtained from mixed-exponent convex smoothing and the
finite-`p` Poincare estimate; it is not an additional hypothesis.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace H1Function

private theorem ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec_mixed
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ} {p : FiniteLpExponent}
    (hρ : IsConvexApproxKernel ρ)
    (huMem : MemL2On U u) (hgiMem : MemLpOn U p.exponent gi)
    (huWeak : HasWeakPartialDerivOn U i u gi)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (fun x => (fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
        (basisVec i)) =ᵐ[volume.restrict U]
      fun x => (1 - ε) * convexApproxSmoothRepresentative U ρ gi x0 r ε x := by
  have huLoc : LocallyIntegrableOn u U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (huMem.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hgiLoc : LocallyIntegrableOn gi U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (hgiMem.locallyIntegrable p.one_lt.le)
  have hsmooth :
      ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative U ρ u x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hρ
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) huMem hr hε0
  have hgiSmooth :
      ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative U ρ gi x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hρ p.one_lt.le
      hgiMem hr hε0
  have hclassWeak :
      HasWeakPartialDerivOn U i
        (convexApproxSmoothRepresentative U ρ u x0 r ε)
        (fun x => (fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
          (basisVec i)) :=
    HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
      (hsmooth.of_le (by simp))
  have hroughWeak :
      HasWeakPartialDerivOn U i
        (convexApproxSmoothRepresentative U ρ u x0 r ε)
        (fun x => (1 - ε) * convexApproxSmoothRepresentative U ρ gi x0 r ε x) :=
    HasWeakPartialDerivOn.convexApproxSmoothRepresentative (i := i) hU huLoc hgiLoc huWeak
      hρ hball hr hε0 hε1
  have hclassLoc : LocallyIntegrableOn
      (fun x => (fderiv ℝ (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
        (basisVec i)) U volume :=
    ((hsmooth.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
      |>.locallyIntegrableOn hU.isOpen.measurableSet
  have hroughLoc : LocallyIntegrableOn
      (fun x => (1 - ε) * convexApproxSmoothRepresentative U ρ gi x0 r ε x) U volume :=
    (continuous_const.mul hgiSmooth.continuous).continuousOn
      |>.locallyIntegrableOn hU.isOpen.measurableSet
  exact HasWeakPartialDerivOn.ae_eq hU.isOpen hclassLoc hroughLoc hclassWeak hroughWeak

private theorem tendsto_eLpNorm_convexApproxSmoothH1_grad_sub
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.grad)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r)
    (i : Fin d) :
    Tendsto
      (fun n => eLpNorm
        (fun x => (convexApproxSmoothH1 (U := U) hU u x0 hr n).grad x i - u.grad x i)
        p.exponent (volume.restrict U))
      atTop (nhds 0) := by
  let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hε_lt_one : ∀ᶠ n : ℕ in atTop, unitConvexApproxScale n < 1 :=
    ((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
      (fun _ h => h)
  have hraw : Tendsto
      (fun n : ℕ => eLpNorm
        (fun x => (1 - unitConvexApproxScale n) *
          convexApproxSmoothing ρ (fun y => u.grad y i) x0 r (unitConvexApproxScale n) x -
            u.grad x i)
        p.exponent (volume.restrict U))
      atTop (nhds 0) := by
    simpa [ρ] using
      (tendsto_eLpNorm_sub_zero_one_sub_mul_convexApproxSmoothing_of_memLpOn
        (U := U) hU hρ p.one_lt.le p.lt_top.ne (hgrad i) hball hr
        tendsto_unitConvexApproxScale_zero
        (Eventually.of_forall W1pFunction.unitConvexApproxScale_pos) hε_lt_one)
  refine hraw.congr' ?_
  filter_upwards [hε_lt_one] with n hεn
  apply eLpNorm_congr_ae
  have hbridge :=
    ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec_mixed
      (hU := hU) (ρ := ρ) (u := u.toFun) (gi := fun x => u.grad x i) (p := p) hρ
      u.memL2 (hgrad i) (u.hasWeakPartialDerivOn i) hball hr
      (W1pFunction.unitConvexApproxScale_pos n) hεn
  have hψ := convexApproxSmoothH1_grad (U := U) hU u x0 hr n
  filter_upwards [hbridge, ae_restrict_mem hU.isOpen.measurableSet] with x hx hxU
  rw [show (convexApproxSmoothH1 (U := U) hU u x0 hr n).grad x i =
      (fderiv ℝ (convexApproxSmoothRepresentative U ρ u.toFun x0 r
        (unitConvexApproxScale n)) x) (basisVec i) by
        simpa [ρ] using congrFun (congrFun hψ x) i]
  rw [hx]
  rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    (u := fun x => u.grad x i) hU hρ hxU hball hr
    (W1pFunction.unitConvexApproxScale_pos n) hεn]

private theorem finiteLpExponent_exponent_eq_ofReal_toReal (p : FiniteLpExponent) :
    p.exponent = ENNReal.ofReal p.exponent.toReal := by
  symm
  exact ENNReal.ofReal_toReal p.lt_top.ne

private theorem finiteLpExponent_one_lt_toReal (p : FiniteLpExponent) :
    1 < p.exponent.toReal := by
  have h := (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) p.lt_top.ne).mpr
    p.one_lt
  simpa using h

private theorem subAverageLpSeminorm_cast_exponent
    {d : ℕ} {U : Set (Vec d)} {p q : ENNReal} (hpq : p = q)
    (v : W1pFunction U p) :
    (cast (congrArg (W1pFunction U) hpq) v).subAverageLpSeminorm =
      v.subAverageLpSeminorm := by
  subst q
  rfl

private theorem gradientCoordLpSeminormSum_cast_exponent
    {d : ℕ} {U : Set (Vec d)} {p q : ENNReal} (hpq : p = q)
    (v : W1pFunction U p) :
    (cast (congrArg (W1pFunction U) hpq) v).gradientCoordLpSeminormSum =
      v.gradientCoordLpSeminormSum := by
  subst q
  rfl

private theorem unitConvexApproxScale_pos' (n : ℕ) :
    0 < unitConvexApproxScale n :=
  W1pFunction.unitConvexApproxScale_pos n

private noncomputable def convexApproxSmoothH1W1p
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    W1pFunction U p.exponent := by
  exact W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := p.exponent) hU
    ((contDiff_convexApproxSmoothRepresentative
      (U := U) (ρ := unitConvexApproxKernel (d := d)) (u := u.toFun)
      (p := (2 : ℝ≥0∞)) (x0 := x0) (r := r) (ε := unitConvexApproxScale n)
      hU.isOpen.measurableSet (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) u.memL2 hr (unitConvexApproxScale_pos' n)).of_le
      (by simp))

private theorem convexApproxSmoothH1W1p_toFun
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (convexApproxSmoothH1W1p hU u p x0 hr n).toFun =
      (convexApproxSmoothH1 hU u x0 hr n).toFun := by
  funext x
  simp [convexApproxSmoothH1W1p, convexApproxSmoothH1,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain,
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem convexApproxSmoothH1W1p_grad
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (convexApproxSmoothH1W1p hU u p x0 hr n).grad =
      (convexApproxSmoothH1 hU u x0 hr n).grad := by
  funext x i
  simp [convexApproxSmoothH1W1p, convexApproxSmoothH1,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain,
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem eventually_gradientCoordLpSeminormSum_convexApproxSmoothH1W1p_le
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.grad)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      (convexApproxSmoothH1W1p hU u p x0 hr n).gradientCoordLpSeminormSum ≤ B := by
  let B : ℝ := ∑ i : Fin d, ((eLpNorm (fun x => u.grad x i) p.exponent
    (volume.restrict U)).toReal + 1)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB_nonneg, ?_⟩
  have hcoord : ∀ i : Fin d, ∀ᶠ n : ℕ in atTop,
      (convexApproxSmoothH1W1p hU u p x0 hr n).gradCoordLpSeminorm i ≤
        (eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict U)).toReal + 1 := by
    intro i
    have htend := tendsto_eLpNorm_convexApproxSmoothH1_grad_sub hU u p hgrad hball hr i
    have hsmall : ∀ᶠ n : ℕ in atTop,
        eLpNorm
          (fun x => (convexApproxSmoothH1 hU u x0 hr n).grad x i - u.grad x i)
          p.exponent (volume.restrict U) ≤ 1 :=
      ENNReal.tendsto_nhds_zero.1 htend 1 zero_lt_one
    filter_upwards [hsmall] with n hn
    let v := convexApproxSmoothH1W1p hU u p x0 hr n
    have hvgrad : v.grad = (convexApproxSmoothH1 hU u x0 hr n).grad :=
      convexApproxSmoothH1W1p_grad hU u p x0 hr n
    have htri : eLpNorm (fun x => v.grad x i) p.exponent (volume.restrict U) ≤
        eLpNorm (fun x => v.grad x i - u.grad x i) p.exponent (volume.restrict U) +
          eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict U) := by
      have hsub : MemLp (fun x => v.grad x i - u.grad x i) p.exponent
          (volume.restrict U) := (v.gradMemLp i).sub (hgrad i)
      calc
        eLpNorm (fun x => v.grad x i) p.exponent (volume.restrict U) =
            eLpNorm ((fun x => v.grad x i - u.grad x i) + fun x => u.grad x i)
              p.exponent (volume.restrict U) := by
                apply eLpNorm_congr_ae
                filter_upwards with x
                simp only [Pi.add_apply]
                ring
        _ ≤ _ := eLpNorm_add_le p.one_lt.le
    have hn' : eLpNorm (fun x => v.grad x i - u.grad x i) p.exponent
        (volume.restrict U) ≤ 1 := by
      simpa [v, hvgrad] using hn
    have hsum_top :
        eLpNorm (fun x => v.grad x i - u.grad x i) p.exponent (volume.restrict U) +
          eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict U) ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨((v.gradMemLp i).sub (hgrad i)).eLpNorm_ne_top,
        (hgrad i).eLpNorm_ne_top⟩
    change (eLpNorm (fun x => v.grad x i) p.exponent (volume.restrict U)).toReal ≤ _
    calc
      (eLpNorm (fun x => v.grad x i) p.exponent (volume.restrict U)).toReal ≤
          (eLpNorm (fun x => v.grad x i - u.grad x i) p.exponent (volume.restrict U) +
            eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict U)).toReal :=
        ENNReal.toReal_mono hsum_top htri
      _ = (eLpNorm (fun x => v.grad x i - u.grad x i) p.exponent
            (volume.restrict U)).toReal +
          (eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict U)).toReal := by
            exact ENNReal.toReal_add ((v.gradMemLp i).sub (hgrad i)).eLpNorm_ne_top
              (hgrad i).eLpNorm_ne_top
      _ ≤ 1 + (eLpNorm (fun x => u.grad x i) p.exponent
            (volume.restrict U)).toReal := by
            gcongr
            exact ENNReal.toReal_mono ENNReal.one_ne_top hn'
      _ = _ := by ring
  filter_upwards [(Filter.eventually_all_finset Finset.univ).2
    (fun i _ => hcoord i)] with n hn
  change ∑ i : Fin d,
      (convexApproxSmoothH1W1p hU u p x0 hr n).gradCoordLpSeminorm i ≤ B
  dsimp [B]
  exact Finset.sum_le_sum (s := Finset.univ) fun i _ => hn i (by simp)

private theorem eventually_abs_integralAverage_convexApproxSmoothH1_le
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      |integralAverage U (convexApproxSmoothH1 hU u x0 hr n)| ≤ A := by
  let A : ℝ := |integralAverage U u| + 1
  let : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  have hval : Tendsto
      (fun n => (convexApproxSmoothH1 hU u x0 hr n).toScalarL2)
      atTop (nhds u.toScalarL2) :=
    tendsto_convexApproxSmoothH1_toScalarL2 hU u hball hr
  have havg : Tendsto
      (fun n => integralAverage U (convexApproxSmoothH1 hU u x0 hr n))
      atTop (nhds (integralAverage U u)) :=
    H1Function.tendsto_integralAverage_of_tendsto_toScalarL2 hval
  have hnorm := havg.norm
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖integralAverage U (convexApproxSmoothH1 hU u x0 hr n)‖ ≤
        ‖integralAverage U u‖ + 1 :=
    ((tendsto_order.1 hnorm).2 (‖integralAverage U u‖ + 1) (by linarith)).mono
      (fun _ h => h.le)
  simpa [A, Real.norm_eq_abs] using hbound

private theorem eventually_valueLpSeminorm_convexApproxSmoothH1W1p_le
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.grad)
    {x0 : Vec d} {r : ℝ} (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      (convexApproxSmoothH1W1p hU u p x0 hr n).valueLpSeminorm ≤ B := by
  let : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  obtain ⟨C, hC, hPoincare⟩ :=
    W1pFunction.exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain
      (U := U) hU (finiteLpExponent_one_lt_toReal p)
  obtain ⟨G, hG, hgradBound⟩ :=
    eventually_gradientCoordLpSeminormSum_convexApproxSmoothH1W1p_le
      hU u p hgrad hball hr
  obtain ⟨A, hA, havgBound⟩ :=
    eventually_abs_integralAverage_convexApproxSmoothH1_le hU u hball hr
  let μ : Measure (Vec d) := volume.restrict U
  let M : ℝ := (μ Set.univ ^ (1 / p.exponent.toReal)).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  let B : ℝ := C * G + A * M
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [hgradBound, havgBound] with n hnGrad hnAvg
  let v := convexApproxSmoothH1W1p hU u p x0 hr n
  have hsub : v.subAverageLpSeminorm ≤ C * v.gradientCoordLpSeminormSum := by
    let hpq : p.exponent = ENNReal.ofReal p.exponent.toReal :=
      finiteLpExponent_exponent_eq_ofReal_toReal p
    let vq : W1pFunction U (ENNReal.ofReal p.exponent.toReal) :=
      cast (congrArg (W1pFunction U) hpq) v
    have hpc := hPoincare vq
    rw [subAverageLpSeminorm_cast_exponent hpq v,
      gradientCoordLpSeminormSum_cast_exponent hpq v] at hpc
    exact hpc
  have hconst : MemLp (fun _ : Vec d => integralAverage U v.toFun) p.exponent μ :=
    memLp_const (integralAverage U v.toFun)
  have hsubmem : MemLp (fun x => v.toFun x - integralAverage U v.toFun) p.exponent μ :=
    v.memLp.sub hconst
  have htri : eLpNorm v.toFun p.exponent μ ≤
      eLpNorm (fun x => v.toFun x - integralAverage U v.toFun) p.exponent μ +
        eLpNorm (fun _ : Vec d => integralAverage U v.toFun) p.exponent μ := by
    calc
      eLpNorm v.toFun p.exponent μ =
          eLpNorm ((fun x => v.toFun x - integralAverage U v.toFun) +
            fun _ : Vec d => integralAverage U v.toFun) p.exponent μ := by
              apply eLpNorm_congr_ae
              filter_upwards with x
              simp only [Pi.add_apply]
              ring
      _ ≤ _ := eLpNorm_add_le p.one_lt.le
  have hsum_top :
      eLpNorm (fun x => v.toFun x - integralAverage U v.toFun) p.exponent μ +
        eLpNorm (fun _ : Vec d => integralAverage U v.toFun) p.exponent μ ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hsubmem.eLpNorm_ne_top, hconst.eLpNorm_ne_top⟩
  have hfactor_top : μ Set.univ ^ (1 / p.exponent.toReal) ≠ ∞ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_).ne
    exact (measure_lt_top μ Set.univ).ne
  have hvalue : v.valueLpSeminorm ≤
      v.subAverageLpSeminorm + |integralAverage U v.toFun| * M := by
    change (eLpNorm v.toFun p.exponent μ).toReal ≤ _
    calc
      (eLpNorm v.toFun p.exponent μ).toReal ≤
          (eLpNorm (fun x => v.toFun x - integralAverage U v.toFun) p.exponent μ +
            eLpNorm (fun _ : Vec d => integralAverage U v.toFun) p.exponent μ).toReal :=
        ENNReal.toReal_mono hsum_top htri
      _ = (eLpNorm (fun x => v.toFun x - integralAverage U v.toFun) p.exponent μ).toReal +
          (eLpNorm (fun _ : Vec d => integralAverage U v.toFun) p.exponent μ).toReal :=
        ENNReal.toReal_add hsubmem.eLpNorm_ne_top hconst.eLpNorm_ne_top
      _ = v.subAverageLpSeminorm + |integralAverage U v.toFun| * M := by
        congr 1
        rw [eLpNorm_const' (integralAverage U v.toFun)
          (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne, ENNReal.toReal_mul]
        simp [Real.enorm_eq_ofReal_abs, M]
  have hsubbound : v.subAverageLpSeminorm ≤ C * G :=
    hsub.trans (mul_le_mul_of_nonneg_left (by simpa [v] using hnGrad) hC)
  have havgbound : |integralAverage U v.toFun| ≤ A := by
    simpa [v, convexApproxSmoothH1W1p_toFun] using hnAvg
  calc
    v.valueLpSeminorm ≤ v.subAverageLpSeminorm + |integralAverage U v.toFun| * M := hvalue
    _ ≤ C * G + A * M :=
      add_le_add hsubbound (mul_le_mul_of_nonneg_right havgbound hM)
    _ = B := rfl

private theorem memLp_of_gradMemLp_on_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.grad) :
    MemLpOn U p.exponent u.toFun := by
  let : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  by_cases hnonempty : U.Nonempty
  · rcases hnonempty with ⟨x0, hx0⟩
    rcases Metric.mem_nhds_iff.1 (hU.isOpen.mem_nhds hx0) with ⟨δ, hδpos, hδsub⟩
    let r : ℝ := δ / 2
    have hr : 0 < r := by positivity
    have hball : Metric.closedBall x0 r ⊆ U := by
      intro y hy
      apply hδsub
      have hy' : dist y x0 ≤ r := by simpa [Metric.mem_closedBall] using hy
      have hlt : dist y x0 < δ := by
        have : r < δ := by dsimp [r]; linarith
        exact lt_of_le_of_lt hy' this
      simpa [Metric.mem_ball] using hlt
    obtain ⟨B, hB, hbound⟩ :=
      eventually_valueLpSeminorm_convexApproxSmoothH1W1p_le hU u p hgrad hball hr
    let ψ : ℕ → W1pFunction U p.exponent :=
      fun n => convexApproxSmoothH1W1p hU u p x0 hr n
    have hbound' : ∀ᶠ n : ℕ in atTop,
        eLpNorm (ψ n).toFun p.exponent (volume.restrict U) ≤ ENNReal.ofReal B := by
      filter_upwards [hbound] with n hn
      apply (ENNReal.toReal_le_toReal (ψ n).memLp.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
      simpa [ψ, W1pFunction.valueLpSeminorm, volumeMeasureOn, ENNReal.toReal_ofReal hB] using hn
    have hLp2 : Tendsto (fun n => (convexApproxSmoothH1 hU u x0 hr n).toScalarL2)
        atTop (nhds u.toScalarL2) :=
      tendsto_convexApproxSmoothH1_toScalarL2 hU u hball hr
    let : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
    have hmeasureLp : TendstoInMeasure (volume.restrict U)
        (fun n => ((convexApproxSmoothH1 hU u x0 hr n).toScalarL2 : Vec d → ℝ)) atTop
        (u.toScalarL2 : Vec d → ℝ) :=
      tendstoInMeasure_of_tendsto_Lp hLp2
    have hmeasure : TendstoInMeasure (volume.restrict U)
        (fun n => (convexApproxSmoothH1 hU u x0 hr n).toFun) atTop u.toFun := by
      exact TendstoInMeasure.congr
        (fun n => (convexApproxSmoothH1 hU u x0 hr n).coeFn_toScalarL2)
        u.coeFn_toScalarL2 hmeasureLp
    have hmeasureψ : TendstoInMeasure (volume.restrict U)
        (fun n => (ψ n).toFun) atTop u.toFun := by
      apply TendstoInMeasure.congr_left (g := u.toFun)
        (fun n => ?_) hmeasure
      filter_upwards with x
      simp [ψ, convexApproxSmoothH1W1p_toFun]
    have hnorm := eLpNorm_le_of_tendstoInMeasure (p := p.exponent) hbound' hmeasureψ
      (fun n => (ψ n).memLp.aestronglyMeasurable)
    exact lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top
  · have hempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    subst U
    simp [MemLpOn]

/-- Upgrade an `H¹` witness on a bounded open convex domain to `W^{1,p}` when
its weak-gradient coordinates have finite `L^p` control.  The value `L^p`
membership is derived from convex smoothing and Poincaré, and the function and
weak-gradient representatives are preserved exactly. -/
noncomputable def toW1pOfGradMemLp
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.grad) : W1pFunction U p.exponent :=
  { toFun := u.toFun
    grad := u.grad
    memLp := memLp_of_gradMemLp_on_isOpenBoundedConvexDomain hU u p hgrad
    gradMemLp := hgrad
    hasWeakGradient := u.hasWeakGradient }

@[simp] theorem toW1pOfGradMemLp_toFun
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.grad) :
    (u.toW1pOfGradMemLp hU p hgrad).toFun = u.toFun :=
  rfl

@[simp] theorem toW1pOfGradMemLp_grad
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.grad) :
    (u.toW1pOfGradMemLp hU p hgrad).grad = u.grad :=
  rfl

end H1Function

end

end Homogenization
