/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HessianJointC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalJointC1

/-! C² regularity of the Jacobian and C³ regularity of the flow on forward strips. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

theorem JointC3Forward.jointSpatialFDeriv_contDiff_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => jointSpatialFDeriv b p.1 p.2) := by
  let D : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    fun p => jointSpatialFDeriv b p.1 p.2
  have hDbase : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry b) p) :=
    hb.smooth.fderiv_right (by norm_num)
  have hD : ContDiff ℝ ∞ D := by
    have hcomp : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => (fderiv ℝ (Function.uncurry b) p).comp
          (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) :=
      hDbase.clm_comp contDiff_const
    simpa [D, jointSpatialFDeriv] using hcomp
  exact hD

/-- Spatial Jacobian of the flow with the starting time fixed. -/
def JointC3Forward.flowSpatialJacobianFixedStart
    (X : ℝ → Vec 2 → ℝ → Vec 2) (s : ℝ) (p : ℝ × Vec 2) :
    Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => X p.1 y s) p.2

/-- Observation-time derivative of the spatial Jacobian, given by the variational equation. -/
def JointC3Forward.flowSpatialJacobianTimeDerivative
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) (s : ℝ)
    (p : ℝ × Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  (jointSpatialFDeriv b p.1 (X p.1 p.2 s)).comp
    (JointC3Forward.flowSpatialJacobianFixedStart X s p)

/-- Full time-space differential of the spatial Jacobian with starting time fixed. -/
noncomputable def JointC3Forward.flowSpatialJacobianFullDerivative
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) (s : ℝ)
    (p : ℝ × Vec 2) :
    (ℝ × Vec 2) →L[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (JointC3Forward.flowSpatialJacobianTimeDerivative b X s p)).coprod
      (flowSecondSpatialDerivative X p.1 p.2 s)

/-- The spatial Jacobian is C² in target time and initial position on forward
open strips, with the start time fixed. -/
theorem flow_spatialFDeriv_contDiffOn_two_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s T : ℝ) (hst : s < T) :
    ContDiffOn ℝ 2
      (fun p : ℝ × Vec 2 => fderiv ℝ (fun y => X p.1 y s) p.2)
      (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
  let f : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    JointC3Forward.flowSpatialJacobianFixedStart X s
  let dtime : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    JointC3Forward.flowSpatialJacobianTimeDerivative b X s
  let dparam : ℝ × Vec 2 → Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
    fun p => flowSecondSpatialDerivative X p.1 p.2 s
  let D : ℝ × Vec 2 → (ℝ × Vec 2) →L[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
    JointC3Forward.flowSpatialJacobianFullDerivative b X s
  let region := Ioo s T ×ˢ (univ : Set (Vec 2))
  have hopen : IsOpen region := isOpen_Ioo.prod isOpen_univ
  have hTime : ∀ t x, (t, x) ∈ region →
      HasDerivAt (fun r => f (r, x)) (dtime (t, x)) t := by
    intro t x hx
    exact flow_spatialFDeriv_target_hasDerivAt hb hX x s t
  have hParam : ∀ t x, (t, x) ∈ region →
      HasStrictFDerivAt (fun y => f (t, y)) (dparam (t, x)) x := by
    intro t x hx
    have hslice : ContDiff ℝ 1
        (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) :=
      (flow_spatial_contDiff_two hb hX s t).fderiv_right (by norm_num)
    have hAt : ContDiffAt ℝ 1
        (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) x := hslice.contDiffAt
    have hstrict := hAt.hasStrictFDerivAt (by norm_num)
    simpa [f, dparam, JointC3Forward.flowSpatialJacobianFixedStart,
      flowSecondSpatialDerivative] using hstrict
  have hflowC1 : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => X p.1 p.2 s) := by
    have hmap : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => (p.1, p.2, s)) := by fun_prop
    exact (flow_joint_contDiff_one hb hX).comp hmap
  have hflowMap : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => (p.1, X p.1 p.2 s)) :=
    contDiff_fst.prodMk hflowC1
  have hA : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => jointSpatialFDeriv b p.1 (X p.1 p.2 s)) := by
    exact ((JointC3Forward.jointSpatialFDeriv_contDiff_all hb).of_le
      (by norm_num : (1 : ℕ∞ω) ≤ ∞)).comp hflowMap
  have hJcont : Continuous f := by
    change Continuous (fun p : ℝ × Vec 2 =>
      fderiv ℝ (fun y => X p.1 y s) p.2)
    have hmap : Continuous (fun p : ℝ × Vec 2 => (p.1, p.2, s)) := by fun_prop
    exact (flow_spatialFDeriv_jointContinuous hb hX).comp hmap
  have hDtimeCont : Continuous dtime := by
    change Continuous (fun p : ℝ × Vec 2 =>
      (jointSpatialFDeriv b p.1 (X p.1 p.2 s)).comp (f p))
    exact hA.continuous.clm_comp hJcont
  have hHcont : Continuous dparam := by
    change Continuous (fun p : ℝ × Vec 2 =>
      flowSecondSpatialDerivative X p.1 p.2 s)
    exact flowSecondSpatialDerivative_jointContinuous hb hX s
  have hF : ∀ p : ℝ × Vec 2, HasFDerivAt f (D p) p := by
    intro p
    rcases p with ⟨t, x⟩
    have h := hasFDerivAt_of_time_and_parameter_derivatives
      f dtime dparam
      (fun t x => flow_spatialFDeriv_target_hasDerivAt hb hX x s t)
      (fun t x => by
        have hslice : ContDiff ℝ 1
            (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) :=
          (flow_spatial_contDiff_two hb hX s t).fderiv_right (by norm_num)
        have hAt : ContDiffAt ℝ 1
            (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) x := hslice.contDiffAt
        have hstrict := hAt.hasStrictFDerivAt (by norm_num)
        simpa [f, dparam, JointC3Forward.flowSpatialJacobianFixedStart,
          flowSecondSpatialDerivative] using hstrict)
      hDtimeCont hHcont (t, x)
    simpa [D, JointC3Forward.flowSpatialJacobianFullDerivative,
      JointC3Forward.flowSpatialJacobianTimeDerivative,
          JointC3Forward.flowSpatialJacobianFixedStart,
      f, dtime, dparam] using h
  have hDtime : ContDiffOn ℝ 1 dtime region := by
    change ContDiffOn ℝ 1
      (fun p => (jointSpatialFDeriv b p.1 (X p.1 p.2 s)).comp (f p)) region
    have hJ : ContDiffOn ℝ 1 f region :=
      flow_spatialFDeriv_contDiffOn_one_of_le hb hX s T hst
    exact hA.contDiffOn.clm_comp hJ
  have hDparam : ContDiffOn ℝ 1 dparam region := by
    change ContDiffOn ℝ 1
      (fun p : ℝ × Vec 2 => flowSecondSpatialDerivative X p.1 p.2 s) region
    exact flowSecondSpatialDerivative_contDiffOn_one_of_le hb hX s T
  have hDcont : ContDiffOn ℝ 1 D region := by
    apply (contDiffOn_clm_apply (𝕜 := ℝ) (n := (1 : ℕ∞ω))).2
    intro q
    rcases q with ⟨r, y⟩
    have hconst : ContDiffOn ℝ 1
        (fun _ : ℝ × Vec 2 => r) region := contDiffOn_const
    have htimeEval : ContDiffOn ℝ 1
        (fun p : ℝ × Vec 2 => r • dtime p) region := hconst.smul hDtime
    have hparamEval : ContDiffOn ℝ 1
        (fun p : ℝ × Vec 2 => dparam p y) region :=
      hDparam.clm_apply contDiffOn_const
    simpa [D, JointC3Forward.flowSpatialJacobianFullDerivative] using htimeEval.add hparamEval
  rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen hopen]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact (hF p).differentiableAt.differentiableWithinAt
  · intro h
    norm_num at h
  · change ContDiffOn ℝ 1
      (fun p => fderiv ℝ
        (fun q : ℝ × Vec 2 => JointC3Forward.flowSpatialJacobianFixedStart X s q) p) region
    change ContDiffOn ℝ 1 (fderiv ℝ f) region
    apply hDcont.congr
    intro p hp
    exact (hF p).fderiv

end

end AVenhance.Infra.Flow
