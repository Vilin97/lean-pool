/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothBootstrap
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Joint smoothness from fixed-start smoothness and the global flow law. -/

@[expose] public section

open Homogenization
open Filter
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Graph map advancing each spatial point from time zero to its time coordinate. -/
def JointSmoothFromFixedStart.flowGraphForward (X : ℝ → Vec 2 → ℝ → Vec 2) :
    (ℝ × Vec 2) → ℝ × Vec 2 := fun p => (p.1, X p.1 p.2 0)

/-- Graph map returning each spatial point from its time coordinate to time zero. -/
def JointSmoothFromFixedStart.flowGraphBackward (X : ℝ → Vec 2 → ℝ → Vec 2) :
    (ℝ × Vec 2) → ℝ × Vec 2 := fun p => (p.1, X 0 p.2 p.1)

theorem JointSmoothFromFixedStart.flow_graph_maps_are_inverse
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Function.LeftInverse (JointSmoothFromFixedStart.flowGraphBackward X)
        (JointSmoothFromFixedStart.flowGraphForward X) ∧
      Function.RightInverse (JointSmoothFromFixedStart.flowGraphBackward X)
          (JointSmoothFromFixedStart.flowGraphForward X) := by
  obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
  constructor
  · intro p
    rcases p with ⟨s, x⟩
    apply Prod.ext
    · rfl
    · change X 0 (X s x 0) s = x
      calc
        X 0 (X s x 0) s = X 0 x 0 := flow_group_law b ⟨L, hL⟩ hX x 0 s 0
        _ = x := hX.1 x 0
  · intro p
    rcases p with ⟨s, x⟩
    apply Prod.ext
    · rfl
    · change X s (X 0 x s) 0 = x
      calc
        X s (X 0 x s) 0 = X s x s := flow_group_law b ⟨L, hL⟩ hX x s 0 s
        _ = x := hX.1 x s

theorem JointSmoothFromFixedStart.flowGraphForward_contDiff
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ ∞ (JointSmoothFromFixedStart.flowGraphForward X) := by
  have hposition : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => X p.1 p.2 0) :=
    flow_target_initial_contDiff_infty_fixed_start hb hX 0
  change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, X p.1 p.2 0))
  exact contDiff_fst.prodMk hposition

theorem JointSmoothFromFixedStart.flowGraphBackward_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ 1 (JointSmoothFromFixedStart.flowGraphBackward X) := by
  have hperm : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => ((0 : ℝ), p.2, p.1)) := by fun_prop
  have hposition : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => X 0 p.2 p.1) := by
    have h := (flow_joint_contDiff_one hb hX).comp hperm
    simpa only [Function.comp_def] using h
  change ContDiff ℝ 1 (fun p : ℝ × Vec 2 => (p.1, X 0 p.2 p.1))
  exact contDiff_fst.prodMk hposition

theorem JointSmoothFromFixedStart.flowGraphBackward_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ ∞ (JointSmoothFromFixedStart.flowGraphBackward X) := by
  have hforward := JointSmoothFromFixedStart.flowGraphForward_contDiff hb hX
  have hbackwardC1 := JointSmoothFromFixedStart.flowGraphBackward_contDiff_one hb hX
  have hinverses := JointSmoothFromFixedStart.flow_graph_maps_are_inverse hb hX
  have hderivForward (p : ℝ × Vec 2) :
      HasFDerivAt (JointSmoothFromFixedStart.flowGraphForward X) (fderiv ℝ
          (JointSmoothFromFixedStart.flowGraphForward X) p) p :=
    (hforward.differentiable (by norm_num) p).hasFDerivAt
  have hderivBackward (p : ℝ × Vec 2) :
      HasFDerivAt (JointSmoothFromFixedStart.flowGraphBackward X) (fderiv ℝ
          (JointSmoothFromFixedStart.flowGraphBackward X) p) p :=
    (hbackwardC1.differentiable (by norm_num) p).hasFDerivAt
  have hbackwardAt (p : ℝ × Vec 2) :
      ContDiffAt ℝ ∞ (JointSmoothFromFixedStart.flowGraphBackward X)
          (JointSmoothFromFixedStart.flowGraphForward X p) := by
    let dF := fderiv ℝ (JointSmoothFromFixedStart.flowGraphForward X) p
    let dB := fderiv ℝ (JointSmoothFromFixedStart.flowGraphBackward X)
        (JointSmoothFromFixedStart.flowGraphForward X p)
    have hchain := (hderivBackward (JointSmoothFromFixedStart.flowGraphForward X p)).comp p
        (hderivForward p)
    have hleft : dB.comp dF = ContinuousLinearMap.id ℝ (ℝ × Vec 2) := by
      have hid : JointSmoothFromFixedStart.flowGraphBackward X ∘
          JointSmoothFromFixedStart.flowGraphForward X = id := by
        funext q
        exact hinverses.1 q
      have hchain' : HasFDerivAt id (dB.comp dF) p := by
        rw [← hid]
        exact hchain
      exact hchain'.unique (hasFDerivAt_id p)
    have hderivForwardBack : HasFDerivAt (JointSmoothFromFixedStart.flowGraphForward X) dF
        (JointSmoothFromFixedStart.flowGraphBackward X (JointSmoothFromFixedStart.flowGraphForward
            X p)) := by
      convert hderivForward p using 1
      exact hinverses.1 p
    have hchainR := HasFDerivAt.comp (JointSmoothFromFixedStart.flowGraphForward X p)
        hderivForwardBack
      (hderivBackward (JointSmoothFromFixedStart.flowGraphForward X p))
    have hright : dF.comp dB = ContinuousLinearMap.id ℝ (ℝ × Vec 2) := by
      have hid : JointSmoothFromFixedStart.flowGraphForward X ∘
          JointSmoothFromFixedStart.flowGraphBackward X = id := by
        funext q
        exact hinverses.2 q
      have hchainR' : HasFDerivAt id (dF.comp dB) (JointSmoothFromFixedStart.flowGraphForward X p)
          := by
        rw [← hid]
        exact hchainR
      exact hchainR'.unique (hasFDerivAt_id (JointSmoothFromFixedStart.flowGraphForward X p))
    have hinj : Function.Injective dF := by
      intro v w hvw
      have hv : dB (dF v) = v := by
        have h := congrArg (fun T : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2) => T v) hleft
        simpa using h
      have hw : dB (dF w) = w := by
        have h := congrArg (fun T : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2) => T w) hleft
        simpa using h
      calc
        v = dB (dF v) := hv.symm
        _ = dB (dF w) := congrArg dB hvw
        _ = w := hw
    have hsurj : Function.Surjective dF := by
      intro v
      refine ⟨dB v, ?_⟩
      have h := congrArg (fun T : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2) => T v) hright
      simpa using h
    let eL : (ℝ × Vec 2) ≃ₗ[ℝ] (ℝ × Vec 2) :=
      LinearEquiv.ofBijective dF.toLinearMap ⟨hinj, hsurj⟩
    let e : (ℝ × Vec 2) ≃L[ℝ] (ℝ × Vec 2) := eL.toContinuousLinearEquiv
    have he : (e : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2)) = dF := by
      apply ContinuousLinearMap.ext
      intro v
      change eL v = dF v
      exact LinearEquiv.ofBijective_apply dF.toLinearMap v
    have hF' : HasFDerivAt (JointSmoothFromFixedStart.flowGraphForward X) (e : _ →L[ℝ] _) p := by
      rw [he]
      exact hderivForward p
    have hlocal := (hforward.contDiffAt (x := p)).to_localInverse hF' (by simp)
    have hevent : JointSmoothFromFixedStart.flowGraphBackward X =ᶠ[𝓝
        (JointSmoothFromFixedStart.flowGraphForward X p)]
        (hforward.contDiffAt (x := p)).localInverse hF' (by simp) := by
      have hFstrict := (hforward.contDiffAt (x := p)).hasStrictFDerivAt' hF' (by simp)
      have hu := hFstrict.localInverse_unique
        (g := JointSmoothFromFixedStart.flowGraphBackward X) (Filter.Eventually.of_forall
            hinverses.1)
      change ∀ᶠ y in 𝓝 (JointSmoothFromFixedStart.flowGraphForward X p),
        JointSmoothFromFixedStart.flowGraphBackward X y =
          (hforward.contDiffAt (x := p)).localInverse hF' (by simp) y
      exact hu
    exact hlocal.congr_of_eventuallyEq hevent
  rw [contDiff_iff_contDiffAt]
  intro q
  let p := JointSmoothFromFixedStart.flowGraphBackward X q
  have hp : JointSmoothFromFixedStart.flowGraphForward X p = q := hinverses.2 q
  rw [← hp]
  exact hbackwardAt p

theorem JointSmoothFromFixedStart.flowZeroStartPosition_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => X 0 p.2 p.1) := by
  have hgraph := JointSmoothFromFixedStart.flowGraphBackward_contDiff_infty hb hX
  have hproj : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (JointSmoothFromFixedStart.flowGraphBackward X
      p).2) :=
    (ContinuousLinearMap.snd ℝ ℝ (Vec 2)).contDiff.comp hgraph
  change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => X 0 p.2 p.1) at hproj
  exact hproj

/-- The nonautonomous flow is smooth jointly in target time, initial position,
and start time. The proof first bootstraps all fixed-start augmented flows,
then applies the inverse function theorem to the global graph map
`(s,x) ↦ (s, X(s,x,0))`. -/
theorem flow_joint_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) := by
  obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
  have hfixed : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => X p.1 p.2 0) :=
    flow_target_initial_contDiff_infty_fixed_start hb hX 0
  have hzero : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => X 0 p.2 p.1) :=
    JointSmoothFromFixedStart.flowZeroStartPosition_contDiff_infty hb hX
  have hinput : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ => (p.1, X 0 p.2.1 p.2.2)) := by
    have hperm : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1)) := by fun_prop
    exact contDiff_fst.prodMk (hzero.comp hperm)
  have hcomp : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ => X p.1 (X 0 p.2.1 p.2.2) 0) := by
    have h := hfixed.comp hinput
    simpa only [Function.comp_def] using h
  have heq : (fun p : ℝ × Vec 2 × ℝ => X p.1 (X 0 p.2.1 p.2.2) 0) =
      fun p => X p.1 p.2.1 p.2.2 := by
    funext p
    exact flow_group_law b ⟨L, hL⟩ hX p.2.1 p.2.2 0 p.1
  rw [← heq]
  exact hcomp

/-- The reversed-time-variable flow map is jointly smooth as well. -/
theorem flow_inverse_joint_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) := by
  have hperm : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 × ℝ => (p.2.2, p.2.1, p.1)) := by fun_prop
  simpa only [Function.comp_def] using (flow_joint_contDiff_infty hb hX).comp hperm

end

end AVenhance.Infra.Flow
