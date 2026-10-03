/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HessianJointAll
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.ThirdVariationContinuity

/-! The third spatial derivative on forward target-time strips. -/

@[expose] public section

open Homogenization
open Filter
open Asymptotics
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- The third spatial derivative, viewed as the derivative of the Hessian. -/
def flowThirdSpatialDerivative
    (X : ℝ → Vec 2 → ℝ → Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ) :
    Vec 2 →L[ℝ] (Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2)) :=
  fderiv ℝ (fun y => flowSecondSpatialDerivative X t y s) x

/-- On forward times, the nested spatial Hessian agrees with the selected
second variational flow. -/
theorem flowSecondSpatialDerivative_eq_flowSecondVariation_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) (hst : s ≤ t) (h k : Vec 2) :
    flowSecondSpatialDerivative X t x s h k =
      flowSecondVariation hb hX x s
        (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
        h k t 0 s := by
  obtain ⟨V, hV, B, hB, hD⟩ :=
    exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX x s t hst
  have hEq : flowSecondSpatialDerivative X t x s = B := by
    simpa [flowSecondSpatialDerivative] using hD.fderiv
  rw [hEq]
  exact hB h k

/-- On a forward strip, the derivative of the Hessian is the selected third
variation. -/
theorem flowThirdSpatialDerivative_eval_eq_flowThirdVariation_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x u h k : Vec 2) (s t : ℝ) (hst : s ≤ t) :
    flowThirdSpatialDerivative X t x s u h k =
      flowThirdVariation hb hX x s
        (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s) |>.1)
        u h k t 0 s := by
  let V : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  obtain ⟨L, hL⟩ :=
    exists_flowThirdVariationContinuousLinear_left_of_le hb hX x s t hst hV h k
  obtain ⟨C, hC₀, hTaylor⟩ :=
    exists_flow_secondVariation_quadratic_remainder_all_times_of_le
      hb hX x s t hst
  have hrem (w : Vec 2) :
      ‖flowSecondSpatialDerivative X t (x + w) s h k -
          flowSecondSpatialDerivative X t x s h k - L w‖ ≤
        (C * ‖h‖ * ‖k‖) * ‖w‖ * ‖w‖ := by
    have hTaylorBound := hTaylor w h k t ⟨hst, le_rfl⟩
    rw [flowSecondSpatialDerivative_eq_flowSecondVariation_of_le
      hb hX (x + w) s t hst h k,
      flowSecondSpatialDerivative_eq_flowSecondVariation_of_le
      hb hX x s t hst h k,
      hL w]
    calc
      _ ≤ C * ‖w‖ * ‖w‖ * ‖h‖ * ‖k‖ := hTaylorBound
      _ = (C * ‖h‖ * ‖k‖) * ‖w‖ * ‖w‖ := by ring
  have hC' : 0 ≤ C * ‖h‖ * ‖k‖ :=
    mul_nonneg (mul_nonneg hC₀ (norm_nonneg h)) (norm_nonneg k)
  have hnormLittle :
      (fun w : Vec 2 => ‖flowSecondSpatialDerivative X t (x + w) s h k -
        flowSecondSpatialDerivative X t x s h k - L w‖) =o[𝓝 0] fun w => ‖w‖ := by
    rw [isLittleO_iff]
    intro c hc
    have hball : Metric.ball (0 : Vec 2) (c / (C * ‖h‖ * ‖k‖ + 1)) ∈ 𝓝 0 :=
      Metric.ball_mem_nhds _ (div_pos hc (by linarith [hC']))
    filter_upwards [hball] with w hw
    have hw' : ‖w‖ < c / (C * ‖h‖ * ‖k‖ + 1) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hscaled' : ‖w‖ * (C * ‖h‖ * ‖k‖ + 1) < c :=
      (lt_div_iff₀ (by linarith [hC'])).mp hw'
    have hscaled : (C * ‖h‖ * ‖k‖ + 1) * ‖w‖ ≤ c := by
      rw [mul_comm]
      exact le_of_lt hscaled'
    have hbound :
        ‖flowSecondSpatialDerivative X t (x + w) s h k -
          flowSecondSpatialDerivative X t x s h k - L w‖ ≤ c * ‖w‖ := by
      calc
        _ ≤ (C * ‖h‖ * ‖k‖) * ‖w‖ * ‖w‖ := hrem w
        _ ≤ ((C * ‖h‖ * ‖k‖ + 1) * ‖w‖) * ‖w‖ := by
          gcongr
          linarith [hC']
        _ ≤ c * ‖w‖ := mul_le_mul_of_nonneg_right hscaled (norm_nonneg w)
    change |‖flowSecondSpatialDerivative X t (x + w) s h k -
      flowSecondSpatialDerivative X t x s h k - L w‖| ≤ c * |‖w‖|
    simpa only [abs_of_nonneg (norm_nonneg _)] using hbound
  have hLittle := isLittleO_norm_norm.mp hnormLittle
  have hderiv : HasFDerivAt
      (fun y => flowSecondSpatialDerivative X t y s h k) L x := by
    apply (hasFDerivAt_iff_isLittleO_nhds_zero).2
    exact hLittle
  have hf : ContDiff ℝ 3 (fun y => X t y s) := flow_spatial_contDiff_three hb hX s t
  have hJ : ContDiff ℝ 2 (fun y => fderiv ℝ (fun z => X t z s) y) :=
    hf.fderiv_right (by norm_num)
  have hH : DifferentiableAt ℝ
      (fun y => flowSecondSpatialDerivative X t y s) x := by
    have hHcont : ContDiff ℝ 1
        (fun y => flowSecondSpatialDerivative X t y s) :=
      hJ.fderiv_right (m := 1) (by norm_num)
    exact hHcont.differentiable (by norm_num) x
  have hEval₁ : HasFDerivAt
      (fun y => flowSecondSpatialDerivative X t y s h)
      ((fderiv ℝ (fun y => flowSecondSpatialDerivative X t y s) x).flip h) x := by
    simpa using hH.hasFDerivAt.clm_apply (hasFDerivAt_const h x)
  have hEval₂ : HasFDerivAt
      (fun y => flowSecondSpatialDerivative X t y s h k)
      (((fderiv ℝ (fun y => flowSecondSpatialDerivative X t y s) x).flip h).flip k) x := by
    simpa using hEval₁.clm_apply (hasFDerivAt_const k x)
  have heq := hEval₂.unique hderiv
  have heqU := congrArg (fun A : Vec 2 →L[ℝ] Vec 2 => A u) heq
  rw [hL u] at heqU
  simpa [flowThirdSpatialDerivative, V] using heqU

/-- The third spatial derivative is jointly continuous in target time and
initial position on every forward compact strip, with start time fixed. -/
theorem flowThirdSpatialDerivative_continuousOn_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k l : Vec 2) (s T : ℝ) (hst : s ≤ T) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      flowThirdSpatialDerivative X p.1 p.2 s h k l) (Icc s T ×ˢ univ) := by
  have hvar := flow_thirdVariation_jointContinuous_of_le hb hX h k l s T hst
  apply hvar.congr
  intro p hp
  have hpst : s ≤ p.1 := hp.1.1
  exact flowThirdSpatialDerivative_eval_eq_flowThirdVariation_of_le
    hb hX p.2 h k l s p.1 hpst

/-- The third spatial derivative is continuous on the entire forward half
space, with start time fixed. -/
theorem flowThirdSpatialDerivative_continuousOn_forwardHalf
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k l : Vec 2) (s : ℝ) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      flowThirdSpatialDerivative X p.1 p.2 s h k l) (Ici s ×ˢ (univ : Set (Vec 2))) := by
  intro p hp
  let T : ℝ := p.1 + 1
  have hps : s ≤ p.1 := hp.1
  have hpstrip : p ∈ Icc s T ×ˢ (univ : Set (Vec 2)) := by
    refine ⟨⟨hps, ?_⟩, trivial⟩
    dsimp [T]
    linarith
  have hstrip := flowThirdSpatialDerivative_continuousOn_of_le
    hb hX h k l s T (by dsimp [T]; linarith [hps])
  have hupperOpen : IsOpen (Iio T ×ˢ (univ : Set (Vec 2))) :=
    isOpen_Iio.prod isOpen_univ
  have hpupper : p.1 < T := by
    dsimp [T]
    linarith
  have hpupper' : p ∈ Iio T ×ˢ (univ : Set (Vec 2)) := ⟨hpupper, trivial⟩
  have hupperMem : (Iio T ×ˢ (univ : Set (Vec 2))) ∈ 𝓝 p :=
    hupperOpen.mem_nhds hpupper'
  let forward : Set (ℝ × Vec 2) := Ici s ×ˢ (univ : Set (Vec 2))
  have hint :
      forward ∩ (Iio T ×ˢ (univ : Set (Vec 2))) ∈ 𝓝[forward] p :=
    inter_mem_nhdsWithin forward hupperMem
  have hsubset :
      forward ∩ (Iio T ×ˢ (univ : Set (Vec 2))) ⊆ Icc s T ×ˢ (univ : Set (Vec 2)) := by
    rintro q ⟨hq, hqT⟩
    rcases hq with ⟨hqs, _⟩
    rcases hqT with ⟨hqT, _⟩
    exact ⟨⟨hqs, le_of_lt hqT⟩, trivial⟩
  have hstripMem : Icc s T ×ˢ (univ : Set (Vec 2)) ∈ 𝓝[forward] p :=
    Filter.mem_of_superset hint hsubset
  exact (hstrip.continuousWithinAt hpstrip).mono_of_mem_nhdsWithin hstripMem

theorem ThirdSpatialDerivativeJoint.flowSecondSpatialDerivative_reverseTime_eq
    (X : ℝ → Vec 2 → ℝ → Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ) :
    flowSecondSpatialDerivative (regularityReverseTimeFlow X) (-t) x (-s) =
      flowSecondSpatialDerivative X t x s := by
  have hflow : (fun z => regularityReverseTimeFlow X (-t) z (-s)) =
      (fun z => X t z s) := by
    funext z
    change X (-(-t)) z (-(-s)) = X t z s
    simp
  have hJ : (fun y => fderiv ℝ (fun z => regularityReverseTimeFlow X (-t) z (-s)) y) =
      (fun y => fderiv ℝ (fun z => X t z s) y) :=
    congrArg (fun f : Vec 2 → Vec 2 => fun y => fderiv ℝ f y) hflow
  change fderiv ℝ (fun y => fderiv ℝ
      (fun z => regularityReverseTimeFlow X (-t) z (-s)) y) x =
    fderiv ℝ (fun y => fderiv ℝ (fun z => X t z s) y) x
  exact congrArg (fun J => fderiv ℝ J x) hJ

theorem ThirdSpatialDerivativeJoint.flowThirdSpatialDerivative_reverseTime_eq
    (X : ℝ → Vec 2 → ℝ → Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ)
    (h k l : Vec 2) :
    flowThirdSpatialDerivative (regularityReverseTimeFlow X) (-t) x (-s) h k l =
      flowThirdSpatialDerivative X t x s h k l := by
  have hH : (fun y => flowSecondSpatialDerivative
        (regularityReverseTimeFlow X) (-t) y (-s)) =
      (fun y => flowSecondSpatialDerivative X t y s) := by
    funext y
    exact ThirdSpatialDerivativeJoint.flowSecondSpatialDerivative_reverseTime_eq X t y s
  change (fderiv ℝ (fun y => flowSecondSpatialDerivative
      (regularityReverseTimeFlow X) (-t) y (-s)) x) h k l =
    (fderiv ℝ (fun y => flowSecondSpatialDerivative X t y s) x) h k l
  exact congrArg
    (fun H : Vec 2 → Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) =>
      (((fderiv ℝ H x) h) k) l) hH

theorem ThirdSpatialDerivativeJoint.continuousOn_reverseTimeMap
    {s : ℝ} {f : ℝ × Vec 2 → Vec 2}
    (hf : ContinuousOn f (Ici (-s) ×ˢ (univ : Set (Vec 2)))) :
    ContinuousOn (fun p : ℝ × Vec 2 => f (-p.1, p.2))
      (Iic s ×ˢ (univ : Set (Vec 2))) := by
  let reverseMap : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (-p.1, p.2)
  have hreverseMap : Continuous reverseMap := by fun_prop
  have hmaps : MapsTo reverseMap (Iic s ×ˢ (univ : Set (Vec 2)))
      (Ici (-s) ×ˢ (univ : Set (Vec 2))) := by
    rintro p ⟨hp, _⟩
    change p.1 ≤ s at hp
    exact ⟨by change -s ≤ -p.1; linarith, trivial⟩
  simpa only [Function.comp_def, reverseMap] using
    hf.comp hreverseMap.continuousOn hmaps

theorem ThirdSpatialDerivativeJoint.flowThirdSpatialDerivative_reverseMap_continuousOn
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k l : Vec 2) (s : ℝ) :
    ContinuousOn
      (fun p : ℝ × Vec 2 =>
        flowThirdSpatialDerivative (regularityReverseTimeFlow X)
          (-p.1) p.2 (-s) h k l)
      (Iic s ×ˢ (univ : Set (Vec 2))) := by
  let br := regularityReverseTimeField b
  let Xr := regularityReverseTimeFlow X
  have hbr : SmoothPeriodicField br := smoothPeriodicField_regularityReverseTime hb
  have hXr : AVenhance.IsFlow br Xr := isFlow_regularityReverseTime hX
  let reverseDerivative : ℝ × Vec 2 → Vec 2 := fun p =>
    flowThirdSpatialDerivative Xr p.1 p.2 (-s) h k l
  have hreverse : ContinuousOn reverseDerivative
      (Ici (-s) ×ˢ (univ : Set (Vec 2))) :=
    flowThirdSpatialDerivative_continuousOn_forwardHalf hbr hXr h k l (-s)
  have hcomp := ThirdSpatialDerivativeJoint.continuousOn_reverseTimeMap hreverse
  simpa [reverseDerivative, Xr] using hcomp

/-- The third spatial derivative is continuous on the entire backward half
space, with start time fixed. -/
theorem flowThirdSpatialDerivative_continuousOn_backwardHalf
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k l : Vec 2) (s : ℝ) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      flowThirdSpatialDerivative X p.1 p.2 s h k l) (Iic s ×ˢ (univ : Set (Vec 2))) := by
  have hbackward' := ThirdSpatialDerivativeJoint.flowThirdSpatialDerivative_reverseMap_continuousOn
    hb hX h k l s
  apply hbackward'.congr
  intro p hp
  exact (ThirdSpatialDerivativeJoint.flowThirdSpatialDerivative_reverseTime_eq X p.1 p.2 s h k
      l).symm

/-- The third spatial derivative is jointly continuous in target time and
initial position for every target time, with start time fixed. -/
theorem flowThirdSpatialDerivative_continuous_fixed_start
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k l : Vec 2) (s : ℝ) :
    Continuous (fun p : ℝ × Vec 2 =>
      flowThirdSpatialDerivative X p.1 p.2 s h k l) := by
  let forward : Set (ℝ × Vec 2) := Ici s ×ˢ (univ : Set (Vec 2))
  let backward : Set (ℝ × Vec 2) := Iic s ×ˢ (univ : Set (Vec 2))
  have hforward := flowThirdSpatialDerivative_continuousOn_forwardHalf
    hb hX h k l s
  have hbackward : ContinuousOn
      (fun p : ℝ × Vec 2 => flowThirdSpatialDerivative X p.1 p.2 s h k l)
      backward := flowThirdSpatialDerivative_continuousOn_backwardHalf
        hb hX h k l s
  have hclosedForward : IsClosed forward := isClosed_Ici.prod isClosed_univ
  have hclosedBackward : IsClosed backward := isClosed_Iic.prod isClosed_univ
  have hunion : forward ∪ backward = univ := by
    ext p
    simp only [forward, backward, mem_union, mem_prod, mem_Ici, mem_Iic,
      mem_univ, and_true]
    constructor
    · intro _
      trivial
    · intro _
      exact le_total s p.1
  have hunionCont : ContinuousOn
      (fun p : ℝ × Vec 2 => flowThirdSpatialDerivative X p.1 p.2 s h k l)
      (forward ∪ backward) :=
    hforward.union_of_isClosed hbackward hclosedForward hclosedBackward
  have hall : ContinuousOn
      (fun p : ℝ × Vec 2 => flowThirdSpatialDerivative X p.1 p.2 s h k l) univ := by
    rw [← hunion]
    exact hunionCont
  exact continuousOn_univ.mp hall

end

end AVenhance.Infra.Flow
