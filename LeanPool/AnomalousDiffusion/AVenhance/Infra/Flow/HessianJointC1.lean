/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.ThirdSpatialDerivativeJoint
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalJointC1

/-! The spatial Hessian is C¹ in target time and position on forward strips. -/

@[expose] public section

open Homogenization
open Filter
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Continuous linear identification of nested Hessians with their coordinate values. -/
noncomputable def HessianJointC1.flowHessianCoordinates :
    (Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2)) ≃L[ℝ]
      (Fin 2 → (Fin 2 → Vec 2)) :=
  ((ContinuousLinearEquiv.refl ℝ (Vec 2)).arrowCongr
      (ContinuousLinearEquiv.piRing (Fin 2))).trans
    (ContinuousLinearEquiv.piRing (Fin 2))

theorem HessianJointC1.flowHessianCoordinates_apply
    (H : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2)) (i j : Fin 2) :
    HessianJointC1.flowHessianCoordinates H i j =
      H (Pi.basisFun ℝ (Fin 2) i) (Pi.basisFun ℝ (Fin 2) j) := by
  simp [HessianJointC1.flowHessianCoordinates, ContinuousLinearEquiv.piRing,
    LinearEquiv.piRing_apply, Pi.basisFun_apply]

theorem HessianJointC1.spatialSecondDerivativeEval_jointContinuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    Continuous (fun p : ℝ × (Vec 2 × (Vec 2 × Vec 2)) =>
      spatialSecondDerivativeEval b p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let f : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let D : ℝ × (Vec 2 × (Vec 2 × Vec 2)) →
      _root_.ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) :=
    fun p => iteratedFDeriv ℝ 2 f (p.1, p.2.1)
  let dirs : ℝ × (Vec 2 × (Vec 2 × Vec 2)) → Fin 2 → ℝ × Vec 2 :=
    fun p => fun i => if i = 0 then (0, p.2.2.1) else (0, p.2.2.2)
  have hD : Continuous D := by
    have hbase : Continuous (fun q : ℝ × Vec 2 => iteratedFDeriv ℝ 2 f q) :=
      hb.smooth.continuous_iteratedFDeriv (m := 2) (by simp)
    have hmap : Continuous (fun p : ℝ × (Vec 2 × (Vec 2 × Vec 2)) =>
        (p.1, p.2.1)) := by fun_prop
    exact hbase.comp hmap
  have hdirs : Continuous dirs := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun p : ℝ × (Vec 2 × (Vec 2 × Vec 2)) =>
        (0, p.2.2.1))
      fun_prop
    · change Continuous (fun p : ℝ × (Vec 2 × (Vec 2 × Vec 2)) =>
        (0, p.2.2.2))
      fun_prop
  have hEval : Continuous
      (fun q : _root_.ContinuousMultilinearMap ℝ
        (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) × (Fin 2 → ℝ × Vec 2) =>
          q.1 q.2) := by fun_prop
  have hcomp := hEval.comp (hD.prodMk hdirs)
  apply hcomp.congr
  intro p
  simp [D, dirs, f, spatialSecondDerivativeEval_eq_joint,
    iteratedFDeriv_two_apply]

theorem HessianJointC1.flowSecondSpatialDerivative_apply_hasDerivAt_of_lt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x h k : Vec 2) (s t : ℝ) (hst : s < t) :
    HasDerivAt (fun r => flowSecondSpatialDerivative X r x s h k)
      (jointSpatialFDeriv b t (X t x s)
          (flowSecondSpatialDerivative X t x s h k) +
        spatialSecondDerivativeEval b t (X t x s)
          (fderiv ℝ (fun y => X t y s) x h)
          (fderiv ℝ (fun y => X t y s) x k)) t := by
  let V : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  let W := flowSecondVariation hb hX x s hV h k
  have hW : AVenhance.IsFlow
      (fun r w => jointSpatialFDeriv b r (X r x s) w +
        spatialSecondDerivativeEval b r (X r x s)
          (V r h s) (V r k s)) W :=
    flowSecondVariation_isFlow hb hX x s hV h k
  have hEq : flowSecondSpatialDerivative X t x s h k = W t 0 s := by
    rw [flowSecondSpatialDerivative_eq_flowSecondVariation_of_le
      hb hX x s t (le_of_lt hst) h k]
  have hcol (w : Vec 2) :
      fderiv ℝ (fun y => X t y s) x w = V t w s := by
    obtain ⟨V', J, hV', hJ, hD⟩ :=
      exists_flow_hasFDerivAt_spatial hb hX x s t
    have hVeq : V' = V :=
      (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2
        V' hV'
    calc
      fderiv ℝ (fun y => X t y s) x w = J w := by rw [hD.fderiv]
      _ = V' t w s := hJ w
      _ = V t w s := by rw [hVeq]
  have hEqEvent : (fun r => flowSecondSpatialDerivative X r x s h k) =ᶠ[𝓝 t]
      fun r => W r 0 s := by
    have hnear : Ioi s ∈ 𝓝 t := isOpen_Ioi.mem_nhds hst
    filter_upwards [hnear] with r hrs
    have hrs' : s ≤ r := le_of_lt hrs
    exact flowSecondSpatialDerivative_eq_flowSecondVariation_of_le
      hb hX x s r hrs' h k
  have hderiv := (hW.2 0 s t).congr_of_eventuallyEq hEqEvent
  have hderivValue :
      (jointSpatialFDeriv b t (X t x s)) (W t 0 s) +
        spatialSecondDerivativeEval b t (X t x s) (V t h s) (V t k s) =
      jointSpatialFDeriv b t (X t x s) (flowSecondSpatialDerivative X t x s h k) +
        spatialSecondDerivativeEval b t (X t x s)
          (fderiv ℝ (fun y => X t y s) x h)
          (fderiv ℝ (fun y => X t y s) x k) := by
    rw [← hEq, ← hcol h, ← hcol k]
  have hderiv' : HasDerivAt (fun r => flowSecondSpatialDerivative X r x s h k)
      (jointSpatialFDeriv b t (X t x s) (W t 0 s) +
        spatialSecondDerivativeEval b t (X t x s) (V t h s) (V t k s)) t := by
    simpa using hderiv
  rw [← hderivValue]
  exact hderiv'

theorem HessianJointC1.flowHessianCoordinate_contDiffOn_one_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s T : ℝ) (h k : Vec 2) :
    ContDiffOn ℝ 1
      (fun p : ℝ × Vec 2 => flowSecondSpatialDerivative X p.1 p.2 s h k)
      (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
  let f : ℝ × Vec 2 → Vec 2 := fun p =>
    flowSecondSpatialDerivative X p.1 p.2 s h k
  let J : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X p.1 y s) p.2
  let A : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    jointSpatialFDeriv b p.1 (X p.1 p.2 s)
  let dtime : ℝ × Vec 2 → Vec 2 := fun p =>
    A p (f p) + spatialSecondDerivativeEval b p.1 (X p.1 p.2 s)
      (J p h) (J p k)
  let dparam : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    ((flowThirdSpatialDerivative X p.1 p.2 s).flip h).flip k
  let region := Ioo s T ×ˢ (univ : Set (Vec 2))
  have hopen : IsOpen region := isOpen_Ioo.prod isOpen_univ
  have hTime : ∀ t x, (t, x) ∈ region →
      HasDerivAt (fun r => f (r, x)) (dtime (t, x)) t := by
    intro t x hx
    exact HessianJointC1.flowSecondSpatialDerivative_apply_hasDerivAt_of_lt
      hb hX x h k s t hx.1.1
  have hParam : ∀ t x, (t, x) ∈ region →
      HasStrictFDerivAt (fun y => f (t, y)) (dparam (t, x)) x := by
    intro t x hx
    let H : Vec 2 → Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) := fun y =>
      flowSecondSpatialDerivative X t y s
    have hflow : ContDiff ℝ 3 (fun y : Vec 2 => X t y s) :=
      flow_spatial_contDiff_three hb hX s t
    have hJ : ContDiff ℝ 2 (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) :=
      hflow.fderiv_right (m := 2) (by norm_num)
    have hH : ContDiff ℝ 1 H := by
      change ContDiff ℝ 1 (fun y => fderiv ℝ
        (fun z => fderiv ℝ (fun w => X t w s) z) y)
      exact hJ.fderiv_right (m := 1) (by norm_num)
    have hHstrict : HasStrictFDerivAt H
        (flowThirdSpatialDerivative X t x s) x := by
      have hHAt : ContDiffAt ℝ 1 H x := hH.contDiffAt
      have hstrict := hHAt.hasStrictFDerivAt (by norm_num)
      simpa [flowThirdSpatialDerivative] using hstrict
    have hstrict₁ := hHstrict.clm_apply (hasStrictFDerivAt_const h x)
    have hstrict₂ := hstrict₁.clm_apply (hasStrictFDerivAt_const k x)
    have hfinal : HasStrictFDerivAt (fun y => f (t, y))
        (((flowThirdSpatialDerivative X t x s).flip h).flip k) x := by
      simpa [f, H, dparam] using hstrict₂.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => rfl)
    exact hfinal
  have hbase : Continuous (fun p : ℝ × Vec 2 => X p.1 p.2 s) := by
    have hmap : Continuous (fun p : ℝ × Vec 2 => (p.1, p.2, s)) := by fun_prop
    exact (flow_continuous_joint_of_smoothPeriodic hb hX).comp hmap
  have hJcont : Continuous J := by
    change Continuous (fun p : ℝ × Vec 2 =>
      fderiv ℝ (fun y => X p.1 y s) p.2)
    have hmap : Continuous (fun p : ℝ × Vec 2 => (p.1, p.2, s)) := by fun_prop
    exact (flow_spatialFDeriv_jointContinuous hb hX).comp hmap
  have hAcont : Continuous A := by
    change Continuous (fun p : ℝ × Vec 2 =>
      jointSpatialFDeriv b p.1 (X p.1 p.2 s))
    exact jointSpatialFDeriv_continuous hb |>.comp
      (continuous_fst.prodMk hbase)
  have hHcont : Continuous (fun p : ℝ × Vec 2 =>
      flowSecondSpatialDerivative X p.1 p.2 s) :=
    flowSecondSpatialDerivative_jointContinuous hb hX s
  have hJfixed (v : Vec 2) : Continuous (fun p : ℝ × Vec 2 => J p v) :=
    (continuous_clm_apply.mp hJcont) v
  have hDtime : ContinuousOn dtime region := by
    have hHh : Continuous (fun p : ℝ × Vec 2 =>
        flowSecondSpatialDerivative X p.1 p.2 s h) :=
      (continuous_clm_apply.mp hHcont) h
    have hHhk : Continuous (fun p : ℝ × Vec 2 =>
        flowSecondSpatialDerivative X p.1 p.2 s h k) :=
      (continuous_clm_apply.mp hHh) k
    have hAeval : Continuous (fun p : ℝ × Vec 2 => A p (f p)) :=
      hAcont.clm_apply hHhk
    have hforceMap : Continuous (fun p : ℝ × Vec 2 =>
        (p.1, (X p.1 p.2 s, (J p h, J p k)))) := by
      have hdirs : Continuous (fun p : ℝ × Vec 2 => (J p h, J p k)) :=
        (hJfixed h).prodMk (hJfixed k)
      exact continuous_fst.prodMk (hbase.prodMk hdirs)
    have hforce : Continuous (fun p : ℝ × Vec 2 =>
        spatialSecondDerivativeEval b p.1 (X p.1 p.2 s) (J p h) (J p k)) := by
      exact HessianJointC1.spatialSecondDerivativeEval_jointContinuous hb |>.comp hforceMap
    exact (hAeval.add hforce).continuousOn
  have hDparam : ContinuousOn dparam region := by
    apply continuousOn_clm_apply.mpr
    intro v
    change ContinuousOn (fun p : ℝ × Vec 2 =>
      (((flowThirdSpatialDerivative X p.1 p.2 s).flip h).flip k) v) region
    have hthirdEval : Continuous (fun p : ℝ × Vec 2 =>
        flowThirdSpatialDerivative X p.1 p.2 s v h k) :=
      flowThirdSpatialDerivative_continuous_fixed_start hb hX v h k s
    simpa using hthirdEval.continuousOn
  exact contDiffOn_one_of_time_and_parameter_derivatives
    f region hopen dtime dparam hTime hParam hDtime hDparam

/-- The spatial Hessian is jointly C¹ in target time and initial position on
forward open strips for fixed start time. -/
theorem flowSecondSpatialDerivative_contDiffOn_one_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s T : ℝ) :
    ContDiffOn ℝ 1
      (fun p : ℝ × Vec 2 => flowSecondSpatialDerivative X p.1 p.2 s)
      (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
  let H : ℝ × Vec 2 → Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) := fun p =>
    flowSecondSpatialDerivative X p.1 p.2 s
  have hcoords : ContDiffOn ℝ 1
      (fun p => HessianJointC1.flowHessianCoordinates (H p))
      (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
    apply contDiffOn_pi.2
    intro i
    apply contDiffOn_pi.2
    intro j
    have hcomponent := HessianJointC1.flowHessianCoordinate_contDiffOn_one_of_le
      hb hX s T (Pi.basisFun ℝ (Fin 2) i) (Pi.basisFun ℝ (Fin 2) j)
    apply hcomponent.congr
    intro p hp
    exact HessianJointC1.flowHessianCoordinates_apply (H p) i j
  have hH : ContDiffOn ℝ 1 H (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
    have hcoords' : ContDiffOn ℝ 1 (HessianJointC1.flowHessianCoordinates ∘ H)
        (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
      simpa only [Function.comp_def] using hcoords
    exact (HessianJointC1.flowHessianCoordinates.comp_contDiffOn_iff).mp hcoords'
  simpa [H] using hH

end

end AVenhance.Infra.Flow
