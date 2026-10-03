/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HessianJointAll
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Initial-time differentiability for augmented jet flows. -/

@[expose] public section

open Filter
open Asymptotics
open Homogenization
open MeasureTheory
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

theorem JetStartDerivative.hasDerivAt_diagonalIntervalIntegralOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ × ℝ → E} (hg : Continuous g) (a : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ u in r..a, g (u, r)) (-g (a, a)) a := by
  let F : ℝ → E := fun r => ∫ u in r..a, g (u, r)
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hnear : ∀ᶠ p in 𝓝 (a, a), ‖g p - g (a, a)‖ < c := by
    have hball := hg.continuousAt.eventually (Metric.ball_mem_nhds (g (a, a)) hc)
    simpa only [Metric.mem_ball, dist_eq_norm] using hball
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
  filter_upwards [Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun r hr => hr⟩] with r hr
  have hFa : F a = 0 := by simp [F]
  have hGint : IntervalIntegrable (fun u : ℝ => g (u, r)) volume r a := by
    exact (hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable r a
  have hCint : IntervalIntegrable (fun _ : ℝ => g (a, a)) volume r a :=
    intervalIntegrable_const
  have hrem :
      (F r - F a - (r - a) • (-g (a, a))) =
        ∫ u in r..a, (g (u, r) - g (a, a)) := by
    rw [hFa, sub_zero]
    change (∫ u in r..a, g (u, r)) - (r - a) • (-g (a, a)) = _
    rw [intervalIntegral.integral_sub hGint hCint, intervalIntegral.integral_const]
    rw [show r - a = -(a - r) by ring, neg_smul, smul_neg, neg_neg]
  have hbound : ∀ u ∈ Set.uIoc r a, ‖g (u, r) - g (a, a)‖ ≤ c := by
    intro u hu
    have huIcc : u ∈ uIcc r a := uIoc_subset_uIcc hu
    have huDist : dist u a ≤ dist r a := Real.dist_right_le_of_mem_uIcc huIcc
    have hprod : dist (u, r) (a, a) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (huDist.trans_lt hr) hr
    exact le_of_lt (hδbound hprod)
  have hIntBound := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    ‖F r - F a - (r - a) • (-g (a, a))‖ =
        ‖∫ u in r..a, (g (u, r) - g (a, a))‖ := congrArg norm hrem
    _ ≤ c * |a - r| := hIntBound
    _ = c * ‖r - a‖ := by rw [Real.norm_eq_abs, abs_sub_comm]

/-- A continuous characterized flow has the usual derivative with respect to
its initial-time parameter. -/
theorem isFlowOn_initialTime_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E → E} {Y : ℝ → E → ℝ → E}
    (hY : IsFlowOn F Y)
    (hYcont : Continuous (fun p : ℝ × E × ℝ => Y p.1 p.2.1 p.2.2))
    (hFcont : Continuous (Function.uncurry F))
    (z : E) (a : ℝ) :
    HasDerivAt (fun r => Y a z r) (-F a z) a := by
  let g : ℝ × ℝ → E := fun p => F p.1 (Y p.1 z p.2)
  have hYslice : Continuous (fun p : ℝ × ℝ => Y p.1 z p.2) := by
    have hmap : Continuous (fun p : ℝ × ℝ => (p.1, z, p.2)) := by fun_prop
    exact hYcont.comp hmap
  have hg : Continuous g := by
    have hmap : Continuous (fun p : ℝ × ℝ => (p.1, Y p.1 z p.2)) :=
      continuous_fst.prodMk hYslice
    exact hFcont.comp hmap
  let I : ℝ → E := fun r => ∫ u in r..a, g (u, r)
  have hderivIntegral : HasDerivAt I (-g (a, a)) a :=
    JetStartDerivative.hasDerivAt_diagonalIntervalIntegralOn hg a
  have hformula (r : ℝ) : Y a z r = z + I r := by
    let γ : ℝ → E := fun u => Y u z r
    have hγ : Continuous γ := by
      exact continuous_iff_continuousAt.mpr fun u => (hY.2 z r u).continuousAt
    have hf' : Continuous (fun u : ℝ => F u (Y u z r)) := by
      exact hFcont.comp (continuous_id.prodMk hγ)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := r) (b := a) (fun u _ => hY.2 z r u) (hf'.intervalIntegrable r a)
    have hsub : (∫ u in r..a, F u (Y u z r)) = Y a z r - z := by
      simpa [hY.1] using hFTC
    dsimp [I, g]
    have hrewrite : (fun u : ℝ => F u (Y u z r)) =
        (fun u => F u (Y u z r)) := rfl
    rw [← hrewrite, hsub]
    abel
  have hfunc : (fun r => Y a z r) = fun r => z + I r := funext hformula
  rw [hfunc]
  simpa [g, hY.1] using hderivIntegral.const_add z

/-- Start-time differentiability of a characterized flow with a C¹ spatial
state map and the flow composition law. -/
theorem isFlowOn_startTime_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E → E} {Y : ℝ → E → ℝ → E}
    (hY : IsFlowOn F Y)
    (hYcont : Continuous (fun p : ℝ × E × ℝ => Y p.1 p.2.1 p.2.2))
    (hFcont : Continuous (Function.uncurry F))
    (hYstate : ∀ s t, ContDiff ℝ 1 (fun z => Y t z s))
    (hgroup : ∀ z s r t, Y t (Y r z s) r = Y t z s)
    (z : E) (s t : ℝ) :
    HasDerivAt (fun r => Y t z r)
      (-(fderiv ℝ (fun w => Y t w s) z) (F s z)) s := by
  let inner : ℝ → E := fun r => Y s z r
  let outer : E → E := fun w => Y t w s
  have hinner : HasDerivAt inner (-F s z) s := by
    simpa [inner, hY.1] using isFlowOn_initialTime_hasDerivAt hY hYcont hFcont z s
  have houter : HasFDerivAt outer (fderiv ℝ outer z) z := by
    exact (hYstate s t).differentiable (by norm_num) z |>.hasFDerivAt
  have hinnerVal : inner s = z := by simp [inner, hY.1]
  have hcomp := houter.comp_hasDerivAt_of_eq s hinner hinnerVal.symm
  have hmap (r : ℝ) : outer (inner r) = Y t z r := hgroup z r s t
  have hderiv := hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hmap r).symm)
  simpa [inner, outer, ContinuousLinearMap.map_neg] using hderiv

theorem JetStartDerivative.firstJetFlow_continuous_joint
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (fun p : ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ =>
      firstJetFlow X p.1 p.2.1 p.2.2) := by
  let J : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1
  have hbase : Continuous (fun p : ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ =>
      X p.1 p.2.1.1 p.2.2) := by
    have hflow := flow_continuous_joint_of_smoothPeriodic hb hX
    have hmap : Continuous (fun p :
        ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ => (p.1, p.2.1.1, p.2.2)) := by
      fun_prop
    exact hflow.comp hmap
  have hJ : Continuous J := by
    change Continuous (fun p : ℝ × Vec 2 × ℝ =>
      fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1)
    exact flow_spatialFDeriv_jointContinuous hb hX
  have hJmap : Continuous (fun p :
      ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ => J (p.1, p.2.1.1, p.2.2)) := by
    exact hJ.comp (by fun_prop)
  have hcol (i : Fin 2) : Continuous (fun p :
      ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ =>
        J (p.1, p.2.1.1, p.2.2) (p.2.1.2 i)) :=
    hJmap.clm_apply (by fun_prop)
  have hcols : Continuous (fun p :
      ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ =>
        fun i => J (p.1, p.2.1.1, p.2.2) (p.2.1.2 i)) :=
    continuous_pi hcol
  have hpair := hbase.prodMk hcols
  simpa [firstJetFlow, J] using hpair

/-- The augmented first-jet flow has the standard initial-time derivative,
with its smooth augmented vector field. -/
theorem firstJetFlow_initialTime_hasDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (z : Vec 2 × (Fin 2 → Vec 2)) (s t : ℝ) :
    HasDerivAt (fun r => firstJetFlow X t z r)
      (-(fderiv ℝ (fun w => firstJetFlow X t w s) z)
        (firstJetField b s z)) s := by
  exact isFlowOn_startTime_hasDerivAt
    (firstJetFlow_isFlow hb hX)
    (JetStartDerivative.firstJetFlow_continuous_joint hb hX)
    (firstJetField_contDiff hb).continuous
    (fun u v => firstJetFlow_spatial_contDiff_one hb hX v u)
    (fun z s r t => firstJetFlow_group_law hb hX z s r t)
    z s t

/-- The state derivative of the first-jet flow, written in terms of the
spatial Jacobian and Hessian of the base flow. -/
noncomputable def firstJetFlowStateDerivativeAt
    (X : ℝ → Vec 2 → ℝ → Vec 2) (p : ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ) :
    (Vec 2 × (Fin 2 → Vec 2)) →L[ℝ] (Vec 2 × (Fin 2 → Vec 2)) :=
  let J : Vec 2 →L[ℝ] Vec 2 := fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1.1
  let H : Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 :=
    flowSecondSpatialDerivative X p.1 p.2.1.1 p.2.2
  let fstMap := ContinuousLinearMap.fst ℝ (Vec 2) (Fin 2 → Vec 2)
  let sndMap := ContinuousLinearMap.snd ℝ (Vec 2) (Fin 2 → Vec 2)
  (J.comp fstMap).prod (ContinuousLinearMap.pi fun i =>
    J.comp ((ContinuousLinearMap.proj i).comp sndMap) +
      ((H.comp fstMap).flip (p.2.1.2 i)))

/-- The first-jet state derivative is the actual spatial Fréchet derivative
of the augmented flow. -/
theorem firstJetFlow_state_fderiv_eq
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (p : ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ) :
    fderiv ℝ (fun w => firstJetFlow X p.1 w p.2.2) p.2.1 =
      firstJetFlowStateDerivativeAt X p := by
  let x := p.2.1.1
  let M := p.2.1.2
  let t := p.1
  let s := p.2.2
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y =>
    fderiv ℝ (fun z => X t z s) y
  let H : Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun y =>
    flowSecondSpatialDerivative X t y s
  let fstMap := ContinuousLinearMap.fst ℝ (Vec 2) (Fin 2 → Vec 2)
  let sndMap := ContinuousLinearMap.snd ℝ (Vec 2) (Fin 2 → Vec 2)
  let Dcols : Vec 2 × (Fin 2 → Vec 2) →L[ℝ] (Fin 2 → Vec 2) :=
    ContinuousLinearMap.pi fun i =>
      (J x).comp ((ContinuousLinearMap.proj i).comp sndMap) +
        ((H x).comp fstMap).flip (M i)
  let D : (Vec 2 × (Fin 2 → Vec 2)) →L[ℝ] (Vec 2 × (Fin 2 → Vec 2)) :=
    ((J x).comp fstMap).prod Dcols
  have hbaseX : HasFDerivAt (fun y : Vec 2 => X t y s) (J x) x := by
    exact ((flow_spatial_contDiff_one hb hX s t).differentiable (by norm_num) x).hasFDerivAt
  have hJderiv : HasFDerivAt J (H x) x := by
    have hC2 : ContDiff ℝ 2 (fun y : Vec 2 => X t y s) :=
      flow_spatial_contDiff_two hb hX s t
    have hJdiff : ContDiff ℝ 1 J := by
      exact hC2.fderiv_right (by norm_num)
    have hderiv := (hJdiff.differentiable (by norm_num) x).hasFDerivAt
    simpa [J, H, flowSecondSpatialDerivative] using hderiv
  have hfst : HasFDerivAt (fun w : Vec 2 × (Fin 2 → Vec 2) => w.1) fstMap
      (x, M) := by
    exact fstMap.hasFDerivAt
  have hsnd (i : Fin 2) :
      HasFDerivAt (fun w : Vec 2 × (Fin 2 → Vec 2) => w.2 i)
        ((ContinuousLinearMap.proj i).comp sndMap) (x, M) := by
    exact (((ContinuousLinearMap.proj i).comp sndMap).hasFDerivAt)
  have hJstate : HasFDerivAt (fun w : Vec 2 × (Fin 2 → Vec 2) => J w.1)
      ((H x).comp fstMap) (x, M) := by
    exact HasFDerivAt.comp (f := fun w : Vec 2 × (Fin 2 → Vec 2) => w.1)
      (x := (x, M)) hJderiv hfst
  have hbase : HasFDerivAt
      (fun w : Vec 2 × (Fin 2 → Vec 2) => X t w.1 s)
      ((J x).comp fstMap) (x, M) := by
    exact HasFDerivAt.comp (f := fun w : Vec 2 × (Fin 2 → Vec 2) => w.1)
      (x := (x, M)) hbaseX hfst
  have hcol (i : Fin 2) :
      HasFDerivAt
        (fun w : Vec 2 × (Fin 2 → Vec 2) => J w.1 (w.2 i))
        ((J x).comp ((ContinuousLinearMap.proj i).comp sndMap) +
          ((H x).comp fstMap).flip (M i)) (x, M) :=
    hJstate.clm_apply (hsnd i)
  have hcols : HasFDerivAt
      (fun w : Vec 2 × (Fin 2 → Vec 2) => fun i => J w.1 (w.2 i))
      Dcols (x, M) := hasFDerivAt_pi.mpr hcol
  have hpair := hbase.prodMk hcols
  have hpair' : HasFDerivAt
      (fun w : Vec 2 × (Fin 2 → Vec 2) => firstJetFlow X t w s)
      D (x, M) := by
    simpa [firstJetFlow, D, Dcols, J, H, x, M, t, s, fstMap, sndMap] using hpair
  have hEq := hpair'.fderiv
  simpa [firstJetFlowStateDerivativeAt, x, M, t, s, D, Dcols, J, H,
    fstMap, sndMap] using hEq

/-- The start-time derivative of the augmented flow, using its state
derivative and the augmented vector field. -/
noncomputable def firstJetFlowStateStartDerivativeAt
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × (Vec 2 × (Fin 2 → Vec 2)) × ℝ) :
    Vec 2 × (Fin 2 → Vec 2) :=
  -(firstJetFlowStateDerivativeAt X p) (firstJetField b p.2.2 p.2.1)

/-- The initial-time derivative of the spatial Jacobian applied to a fixed
direction. -/
noncomputable def flowSpatialFDerivApplyStartDerivativeAt
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (v : Vec 2) (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  -(flowSecondSpatialDerivative X p.1 p.2.1 p.2.2
        (b p.2.2 p.2.1) v +
      (fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1)
        (jointSpatialFDeriv b p.2.2 p.2.1 v))

/-- The parameter derivative of the spatial Jacobian applied to a direction,
when varying the initial point. -/
noncomputable def flowSpatialFDerivApplySpaceDerivativeAt
    (X : ℝ → Vec 2 → ℝ → Vec 2) (v : Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 →L[ℝ] Vec 2 :=
  (flowSecondSpatialDerivative X p.1 p.2.1 p.2.2).flip v

theorem JetStartDerivative.flowSpatialFDerivApplySpaceDerivativeAt_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (v : Vec 2) :
    Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSpatialFDerivApplySpaceDerivativeAt X v p) := by
  have hH : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSecondSpatialDerivative X p.1 p.2.1 p.2.2) :=
    flowSecondSpatialDerivative_jointContinuous_all hb hX
  apply continuous_clm_apply.mpr
  intro h
  have hrow : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSecondSpatialDerivative X p.1 p.2.1 p.2.2 h) :=
    hH.clm_apply continuous_const
  have hvalue : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSecondSpatialDerivative X p.1 p.2.1 p.2.2 h v) :=
    hrow.clm_apply continuous_const
  exact hvalue.congr fun p => rfl

theorem JetStartDerivative.flowSpatialFDerivApplyStartDerivativeAt_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (v : Vec 2) :
    Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSpatialFDerivApplyStartDerivativeAt b X v p) := by
  let J : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1
  let H : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun p =>
    flowSecondSpatialDerivative X p.1 p.2.1 p.2.2
  have hJ : Continuous J := by
    change Continuous (fun p : ℝ × Vec 2 × ℝ =>
      fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1)
    exact flow_spatialFDeriv_jointContinuous hb hX
  have hH : Continuous H := by
    change Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSecondSpatialDerivative X p.1 p.2.1 p.2.2)
    exact flowSecondSpatialDerivative_jointContinuous_all hb hX
  have hbvalue : Continuous (fun p : ℝ × Vec 2 × ℝ => b p.2.2 p.2.1) := by
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1)) := by
      fun_prop
    exact hb.smooth.continuous.comp hmap
  have hHrow : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      H p (b p.2.2 p.2.1)) := hH.clm_apply hbvalue
  have hHterm : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      H p (b p.2.2 p.2.1) v) := hHrow.clm_apply continuous_const
  have hDb : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      jointSpatialFDeriv b p.2.2 p.2.1) := by
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1)) := by
      fun_prop
    exact (jointSpatialFDeriv_continuous hb).comp hmap
  have hDbv : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      jointSpatialFDeriv b p.2.2 p.2.1 v) := hDb.clm_apply continuous_const
  have hJterm : Continuous (fun p : ℝ × Vec 2 × ℝ =>
      J p (jointSpatialFDeriv b p.2.2 p.2.1 v)) := hJ.clm_apply hDbv
  change Continuous (fun p : ℝ × Vec 2 × ℝ =>
    -(H p (b p.2.2 p.2.1) v + J p (jointSpatialFDeriv b p.2.2 p.2.1 v)))
  exact (hHterm.add hJterm).neg

/-- Initial-time differentiation of the Jacobian follows by applying the
augmented-flow derivative to a direction column. -/
theorem flow_spatialFDeriv_apply_initialTime_hasDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (v x : Vec 2) (s t : ℝ) :
    HasDerivAt (fun r => (fderiv ℝ (fun y => X t y r) x) v)
      (flowSpatialFDerivApplyStartDerivativeAt b X v (t, x, s)) s := by
  let M : Fin 2 → Vec 2 := fun _ => v
  let z : Vec 2 × (Fin 2 → Vec 2) := (x, M)
  let eval : (Vec 2 × (Fin 2 → Vec 2)) →L[ℝ] Vec 2 :=
    (ContinuousLinearMap.proj (0 : Fin 2)).comp
      (ContinuousLinearMap.snd ℝ (Vec 2) (Fin 2 → Vec 2))
  have hstart := firstJetFlow_initialTime_hasDerivAt hb hX z s t
  rw [firstJetFlow_state_fderiv_eq hb hX (t, z, s)] at hstart
  have houter : HasFDerivAt eval eval (firstJetFlow X t z s) := eval.hasFDerivAt
  have hcomp := houter.comp_hasDerivAt_of_eq s hstart rfl
  have hfunction :
      (fun r => eval (firstJetFlow X t z r)) =
        (fun r => (fderiv ℝ (fun y => X t y r) x) v) := by
    funext r
    simp [eval, firstJetFlow, z, M]
  have heval :
      eval (firstJetFlowStateStartDerivativeAt b X (t, z, s)) =
        flowSpatialFDerivApplyStartDerivativeAt b X v (t, x, s) := by
    simp [firstJetFlowStateStartDerivativeAt, firstJetFlowStateDerivativeAt,
      firstJetField, flowSpatialFDerivApplyStartDerivativeAt,
      ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.flip_apply, z, M, eval, add_comm]
  have hcomp' : HasDerivAt (fun r =>
      (fderiv ℝ (fun y => X t y r) x) v)
      (flowSpatialFDerivApplyStartDerivativeAt b X v (t, x, s)) s := by
    have hcompFun := hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (congrFun hfunction r).symm)
    have hderivval :
        -eval (firstJetFlowStateDerivativeAt X (t, z, s) (firstJetField b s z)) =
          flowSpatialFDerivApplyStartDerivativeAt b X v (t, x, s) := by
      rw [← map_neg eval]
      simpa [firstJetFlowStateStartDerivativeAt] using heval
    simpa [hderivval] using hcompFun
  exact hcomp'

theorem JetStartDerivative.flowSpatialFDerivApply_space_hasFDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (v : Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ) :
    HasFDerivAt (fun y : Vec 2 =>
      (fderiv ℝ (fun z => X t z s) y) v)
      (flowSpatialFDerivApplySpaceDerivativeAt X v (t, x, s)) x := by
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y =>
    fderiv ℝ (fun z => X t z s) y
  have hC2 : ContDiff ℝ 2 (fun y : Vec 2 => X t y s) :=
    flow_spatial_contDiff_two hb hX s t
  have hJ : ContDiff ℝ 1 J := hC2.fderiv_right (by norm_num)
  have hJderiv := (hJ.differentiable (by norm_num) x).hasFDerivAt
  have hconst : HasFDerivAt (fun _ : Vec 2 => v)
      (0 : Vec 2 →L[ℝ] Vec 2) x := by
    simpa using hasFDerivAt_const (𝕜 := ℝ) (E := Vec 2) (F := Vec 2) v x
  have happly := hJderiv.clm_apply hconst
  simpa [J, flowSpatialFDerivApplySpaceDerivativeAt,
    flowSecondSpatialDerivative, zero_apply] using happly

theorem JetStartDerivative.flowSpatialFDerivApply_space_hasStrictFDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (v : Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ) :
    HasStrictFDerivAt (fun y : Vec 2 =>
      (fderiv ℝ (fun z => X t z s) y) v)
      (flowSpatialFDerivApplySpaceDerivativeAt X v (t, x, s)) x := by
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y =>
    fderiv ℝ (fun z => X t z s) y
  have hC2 : ContDiff ℝ 2 (fun y : Vec 2 => X t y s) :=
    flow_spatial_contDiff_two hb hX s t
  have hJ : ContDiff ℝ 1 J := hC2.fderiv_right (by norm_num)
  have happly : ContDiff ℝ 1 (fun y : Vec 2 => J y v) :=
    hJ.clm_apply contDiff_const
  have hAt : ContDiffAt ℝ 1 (fun y : Vec 2 => J y v) x := happly.contDiffAt
  have hstrict := hAt.hasStrictFDerivAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hEq := (JetStartDerivative.flowSpatialFDerivApply_space_hasFDerivAt hb hX v t x s).fderiv
  rw [hEq] at hstrict
  simpa [J] using hstrict

/-- For a fixed target time, each variational direction is jointly C¹ in
start time and initial point. -/
theorem JetStartDerivative.flowSpatialFDerivApply_contDiff_start_space
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (v : Vec 2) (t : ℝ) :
    ContDiff ℝ 1 (fun q : ℝ × Vec 2 =>
      (fderiv ℝ (fun y => X t y q.1) q.2) v) := by
  let f : ℝ × Vec 2 → Vec 2 := fun q =>
    (fderiv ℝ (fun y => X t y q.1) q.2) v
  let dtime : ℝ × Vec 2 → Vec 2 := fun q =>
    flowSpatialFDerivApplyStartDerivativeAt b X v (t, q.2, q.1)
  let dparam : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun q =>
    flowSpatialFDerivApplySpaceDerivativeAt X v (t, q.2, q.1)
  have hTime : ∀ s x, HasDerivAt (fun r => f (r, x)) (dtime (s, x)) s := by
    intro s x
    exact flow_spatialFDeriv_apply_initialTime_hasDerivAt hb hX v x s t
  have hParam : ∀ s x,
      HasStrictFDerivAt (fun y => f (s, y)) (dparam (s, x)) x := by
    intro s x
    exact JetStartDerivative.flowSpatialFDerivApply_space_hasStrictFDerivAt hb hX v t x s
  have hmap : Continuous (fun q : ℝ × Vec 2 => (t, q.2, q.1)) := by fun_prop
  have hTimeCont : Continuous dtime :=
    (JetStartDerivative.flowSpatialFDerivApplyStartDerivativeAt_continuous hb hX v).comp hmap
  have hParamCont : Continuous dparam :=
    (JetStartDerivative.flowSpatialFDerivApplySpaceDerivativeAt_continuous hb hX v).comp hmap
  exact contDiff_one_of_time_and_parameter_derivatives
    f dtime dparam hTime hParam hTimeCont hParamCont

/-- Every fixed-direction value of the spatial Jacobian is jointly C¹ in
target time, initial point, and start time. -/
theorem flow_spatialFDeriv_apply_contDiff_one_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (v : Vec 2) :
    ContDiff ℝ 1 (fun p : ℝ × (ℝ × Vec 2) =>
      (fderiv ℝ (fun y => X p.1 y p.2.1) p.2.2) v) := by
  let J : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X p.1 y p.2.2) p.2.1
  let f : ℝ × (ℝ × Vec 2) → Vec 2 := fun p =>
    J (p.1, p.2.2, p.2.1) v
  let dtime : ℝ × (ℝ × Vec 2) → Vec 2 := fun p =>
    jointSpatialFDeriv b p.1 (X p.1 p.2.2 p.2.1)
      (J (p.1, p.2.2, p.2.1) v)
  let dparam : ℝ × (ℝ × Vec 2) → (ℝ × Vec 2) →L[ℝ] Vec 2 := fun p =>
    (ContinuousLinearMap.toSpanSingleton ℝ
      (flowSpatialFDerivApplyStartDerivativeAt b X v
        (p.1, p.2.2, p.2.1))).coprod
      (flowSpatialFDerivApplySpaceDerivativeAt X v
        (p.1, p.2.2, p.2.1))
  have hTime : ∀ t q, HasDerivAt (fun r => f (r, q)) (dtime (t, q)) t := by
    intro t q
    exact flow_spatialFDeriv_apply_hasDerivAt hb hX q.2 q.1 t v
  have hParam : ∀ t q,
      HasStrictFDerivAt (fun w => f (t, w)) (dparam (t, q)) q := by
    intro t q
    let fInner : ℝ × Vec 2 → Vec 2 := fun u =>
      (fderiv ℝ (fun y => X t y u.1) u.2) v
    let dtimeInner : ℝ × Vec 2 → Vec 2 := fun u =>
      flowSpatialFDerivApplyStartDerivativeAt b X v (t, u.2, u.1)
    let dparamInner : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun u =>
      flowSpatialFDerivApplySpaceDerivativeAt X v (t, u.2, u.1)
    have hTimeInner : ∀ s x,
        HasDerivAt (fun r => fInner (r, x)) (dtimeInner (s, x)) s := by
      intro s x
      exact flow_spatialFDeriv_apply_initialTime_hasDerivAt hb hX v x s t
    have hParamInner : ∀ s x,
        HasStrictFDerivAt (fun y => fInner (s, y)) (dparamInner (s, x)) x := by
      intro s x
      exact JetStartDerivative.flowSpatialFDerivApply_space_hasStrictFDerivAt hb hX v t x s
    have hmap : Continuous (fun u : ℝ × Vec 2 => (t, u.2, u.1)) := by fun_prop
    have htimeCont : Continuous dtimeInner :=
      (JetStartDerivative.flowSpatialFDerivApplyStartDerivativeAt_continuous hb hX v).comp hmap
    have hparamCont : Continuous dparamInner :=
      (JetStartDerivative.flowSpatialFDerivApplySpaceDerivativeAt_continuous hb hX v).comp hmap
    have hinner := hasFDerivAt_of_time_and_parameter_derivatives
      fInner dtimeInner dparamInner hTimeInner hParamInner htimeCont hparamCont q
    have hinnerContDiff := JetStartDerivative.flowSpatialFDerivApply_contDiff_start_space hb hX v t
    have hAt : ContDiffAt ℝ 1 (fun w : ℝ × Vec 2 =>
        (fderiv ℝ (fun y => X t y w.1) w.2) v) q := hinnerContDiff.contDiffAt
    have hstrict := hAt.hasStrictFDerivAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hEq := hinner.fderiv
    rw [hEq] at hstrict
    simpa [f, dparam, fInner, dtimeInner, dparamInner] using hstrict
  have hJall : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      J (p.1, p.2.2, p.2.1)) := by
    have hmap : Continuous (fun p : ℝ × (ℝ × Vec 2) => (p.1, p.2.2, p.2.1)) := by
      fun_prop
    exact (flow_spatialFDeriv_jointContinuous hb hX).comp hmap
  have hflow : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      X p.1 p.2.2 p.2.1) := by
    have hmap : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
        (p.1, p.2.2, p.2.1)) := by fun_prop
    exact (flow_continuous_joint_of_smoothPeriodic hb hX).comp hmap
  have hfield : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      jointSpatialFDeriv b p.1 (X p.1 p.2.2 p.2.1)) := by
    have hmap : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
        (p.1, X p.1 p.2.2 p.2.1)) := continuous_fst.prodMk hflow
    exact jointSpatialFDeriv_continuous hb |>.comp hmap
  have hJv : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      J (p.1, p.2.2, p.2.1) v) := hJall.clm_apply continuous_const
  have hTimeCont : Continuous dtime := hfield.clm_apply hJv
  have hStart : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      flowSpatialFDerivApplyStartDerivativeAt b X v
        (p.1, p.2.2, p.2.1)) :=
    (JetStartDerivative.flowSpatialFDerivApplyStartDerivativeAt_continuous hb hX v).comp (by
        fun_prop)
  have hSpace : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      flowSpatialFDerivApplySpaceDerivativeAt X v
        (p.1, p.2.2, p.2.1)) :=
    (JetStartDerivative.flowSpatialFDerivApplySpaceDerivativeAt_continuous hb hX v).comp (by
        fun_prop)
  have hStartCLM : Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      ContinuousLinearMap.toSpanSingleton ℝ
        (flowSpatialFDerivApplyStartDerivativeAt b X v
          (p.1, p.2.2, p.2.1))) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Vec 2)).continuous.comp hStart
  have hParamPair := hStartCLM.prodMk hSpace
  have hParamCont : Continuous dparam := by
    change Continuous (fun p : ℝ × (ℝ × Vec 2) =>
      (ContinuousLinearMap.toSpanSingleton ℝ
        (flowSpatialFDerivApplyStartDerivativeAt b X v
          (p.1, p.2.2, p.2.1))).coprod
        (flowSpatialFDerivApplySpaceDerivativeAt X v
          (p.1, p.2.2, p.2.1)))
    exact (ContinuousLinearMap.coprodEquivL (S := ℝ)
      (E := ℝ) (F := Vec 2) (G := Vec 2)).continuous.comp hParamPair
  have hordered := contDiff_one_of_time_and_parameter_derivatives
    f dtime dparam hTime hParam hTimeCont hParamCont
  simpa [f, J] using hordered

/-- The spatial Jacobian is jointly C¹ in all flow variables. -/
theorem flow_spatialFDeriv_contDiff_one_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (fun p : ℝ × (ℝ × Vec 2) =>
      fderiv ℝ (fun y => X p.1 y p.2.1) p.2.2) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  exact flow_spatialFDeriv_apply_contDiff_one_all hb hX v

end

end AVenhance.Infra.Flow
