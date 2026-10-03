/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalJointC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC2

/-! Start-time continuity of the second spatial derivative via inverse flow. -/

@[expose] public section

open Homogenization
open Filter
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- The second derivative of a composition, represented as a nested
continuous linear map. -/
theorem HessianJointAll.flowSecondSpatialDerivative_comp
    {F G : Vec 2 → Vec 2} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (x h k : Vec 2) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => F (G z)) y) x h k =
      fderiv ℝ (fun y => fderiv ℝ F y) (G x)
          (fderiv ℝ G x h) (fderiv ℝ G x k) +
        fderiv ℝ F (G x)
          (fderiv ℝ (fun y => fderiv ℝ G y) x h k) := by
  let A : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ F y
  let B : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ G y
  let CF : Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ A y
  let CG : Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ B y
  let H : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y => (A (G y)).comp (B y)
  let FG : Vec 2 → Vec 2 := fun y => F (G y)
  have hAderiv (y : Vec 2) : HasFDerivAt A (CF y) y := by
    have hdiff := (hF.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) y
    simpa [A, CF] using hdiff.hasFDerivAt
  have hBderiv (y : Vec 2) : HasFDerivAt B (CG y) y := by
    have hdiff := (hG.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) y
    simpa [B, CG] using hdiff.hasFDerivAt
  have hFderiv (y : Vec 2) : HasFDerivAt F (A y) y := by
    exact (hF.differentiable (by norm_num) y).hasFDerivAt
  have hGderiv (y : Vec 2) : HasFDerivAt G (B y) y := by
    exact (hG.differentiable (by norm_num) y).hasFDerivAt
  have hchain (y : Vec 2) : HasFDerivAt FG (H y) y := by
    simpa [FG, H, A, B] using
      (HasFDerivAt.comp (f := G) (x := y) (g := F)
        (hFderiv (G y)) (hGderiv y))
  have hAcomp : HasFDerivAt (fun y => A (G y)) ((CF (G x)).comp (B x)) x :=
    HasFDerivAt.comp (f := G) (x := x) (g := A)
      (hAderiv (G x)) (hGderiv x)
  have hHderiv := hAcomp.clm_comp (hBderiv x)
  have hHderiv' : HasFDerivAt (fun y => fderiv ℝ FG y)
      ((ContinuousLinearMap.compL ℝ (Vec 2) (Vec 2) (Vec 2)) (A (G x)) ∘L CG x +
        ((ContinuousLinearMap.compL ℝ (Vec 2) (Vec 2) (Vec 2)).flip (B x)).comp
          ((CF (G x)).comp (B x))) x := by
    exact hHderiv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (hchain y).fderiv)
  have hEval := congrArg
    (fun Q : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) => Q h k) hHderiv'.fderiv
  have hEval' : fderiv ℝ (fun y => fderiv ℝ (fun z => F (G z)) y) x h k =
      fderiv ℝ F (G x) (fderiv ℝ (fun y => fderiv ℝ G y) x h k) +
        fderiv ℝ (fun y => fderiv ℝ F y) (G x) (fderiv ℝ G x h) (fderiv ℝ G x k) := by
    simpa [A, B, CF, CG, H, FG, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply] using hEval
  calc
    _ = fderiv ℝ F (G x) (fderiv ℝ (fun y => fderiv ℝ G y) x h k) +
          fderiv ℝ (fun y => fderiv ℝ F y) (G x) (fderiv ℝ G x h)
            (fderiv ℝ G x k) := hEval'
    _ = _ := add_comm _ _

/-- The Hessian of the inverse fixed-time flow is determined by the Hessian
of the forward map and the inverse first derivative. -/
theorem flowSecondSpatialDerivative_inverse_formula
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (r s : ℝ) (x h k : Vec 2) :
    flowSecondSpatialDerivative X r x s h k =
      - (fderiv ℝ (fun y => X r y s) x)
        (flowSecondSpatialDerivative X s (X r x s) r
          ((fderiv ℝ (fun y => X r y s) x) h)
          ((fderiv ℝ (fun y => X r y s) x) k)) := by
  let F : Vec 2 → Vec 2 := fun y => X s y r
  let G : Vec 2 → Vec 2 := fun y => X r y s
  let A : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ F y
  let B : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ G y
  let CF : Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ A y
  let CG : Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun y => fderiv ℝ B y
  let z : Vec 2 := G x
  obtain ⟨L, hL₀, hL⟩ := exists_global_spatial_lipschitz hb
  have hLip : ∃ L : ℝ, ∀ t y w, ‖b t y - b t w‖ ≤ L * ‖y - w‖ := ⟨L, hL⟩
  have hFG (y : Vec 2) : F (G y) = y := by
    dsimp [F, G]
    calc
      X s (X r y s) r = X s y s := flow_group_law b hLip hX y s r s
      _ = y := hX.1 y s
  have hGF (y : Vec 2) : G (F y) = y := by
    dsimp [F, G]
    calc
      X r (X s y r) s = X r y r := flow_group_law b hLip hX y r s r
      _ = y := hX.1 y r
  have hFcont : ContDiff ℝ 2 F := flow_spatial_contDiff_two hb hX r s
  have hGcont : ContDiff ℝ 2 G := flow_spatial_contDiff_two hb hX s r
  have hAderiv (y : Vec 2) : HasFDerivAt A (CF y) y := by
    have hdiff := (hFcont.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) y
    simpa [A, CF] using hdiff.hasFDerivAt
  have hBderiv (y : Vec 2) : HasFDerivAt B (CG y) y := by
    have hdiff := (hGcont.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) y
    simpa [B, CG] using hdiff.hasFDerivAt
  have hFderiv (y : Vec 2) : HasFDerivAt F (A y) y := by
    exact (hFcont.differentiable (by norm_num) y).hasFDerivAt
  have hGderiv (y : Vec 2) : HasFDerivAt G (B y) y := by
    exact (hGcont.differentiable (by norm_num) y).hasFDerivAt
  have hAB (y : Vec 2) : (A (G y)).comp (B y) = ContinuousLinearMap.id ℝ (Vec 2) := by
    have hchain := HasFDerivAt.comp y (hFderiv (G y)) (hGderiv y)
    have hchain' := hchain.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => (hFG w).symm)
    exact hchain'.unique (hasFDerivAt_id y)
  have hFz : F z = x := by simpa [z] using hFG x
  have hBA : (B x).comp (A z) = ContinuousLinearMap.id ℝ (Vec 2) := by
    have hG' : HasFDerivAt G (B x) (F z) := by simpa [hFz] using hGderiv x
    have hchain := HasFDerivAt.comp z hG' (hFderiv z)
    have hchain' := hchain.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (hGF y).symm)
    exact hchain'.unique (hasFDerivAt_id z)
  have hAcomp : HasFDerivAt (fun y => A (G y)) ((CF z).comp (B x)) x :=
    HasFDerivAt.comp (f := G) (x := x) (g := A) (hAderiv z) (hGderiv x)
  have hHderiv := hAcomp.clm_comp (hBderiv x)
  have hHconst := hHderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => (hAB y).symm)
  have hsum := hHconst.unique (hasFDerivAt_const
    (ContinuousLinearMap.id ℝ (Vec 2)) x)
  have hEq : A z (CG x h k) + CF z (B x h) (B x k) = 0 := by
    have hEval := congrArg
      (fun Q : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) => Q h k) hsum
    simpa [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply] using hEval
  have hAeq : A z (CG x h k) = -CF z (B x h) (B x k) :=
    (add_eq_zero_iff_eq_neg.mp hEq)
  have hBA' : B x (A z (CG x h k)) = CG x h k := by
    have := congrArg (fun Q : Vec 2 →L[ℝ] Vec 2 => Q (CG x h k)) hBA
    simpa [ContinuousLinearMap.comp_apply] using this
  have hfinal : CG x h k = -B x (CF z (B x h) (B x k)) := by
    calc
      CG x h k = B x (A z (CG x h k)) := hBA'.symm
      _ = B x (-CF z (B x h) (B x k)) := by rw [hAeq]
      _ = -B x (CF z (B x h) (B x k)) := by rw [map_neg]
  simpa [F, G, A, B, CF, CG, z, flowSecondSpatialDerivative] using hfinal

/-- The Hessian of the flow is jointly continuous in target time, initial
point, and start time. The proof factors through one reference time and uses
the inverse Hessian identity for the backward leg. -/
theorem flowSecondSpatialDerivative_jointContinuous_all
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X) :
    Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSecondSpatialDerivative X p.1 p.2.1 p.2.2) := by
  let r : ℝ := 0
  let Z : ℝ × Vec 2 × ℝ → Vec 2 := fun p => X r p.2.1 p.2.2
  let B : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X r y p.2.2) p.2.1
  let A : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X p.1 y r) (Z p)
  let Ht : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun p =>
    flowSecondSpatialDerivative X p.1 (Z p) r
  let Hs : ℝ × Vec 2 × ℝ → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun p =>
    flowSecondSpatialDerivative X p.2.2 (Z p) r
  have hflow : Continuous (fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) :=
    flow_continuous_joint_of_smoothPeriodic hb hX
  have hZ : Continuous Z := by
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (r, p.2.1, p.2.2)) := by fun_prop
    exact hflow.comp hmap
  have hB : Continuous B := by
    change Continuous (fun p : ℝ × Vec 2 × ℝ =>
      fderiv ℝ (fun y => X r y p.2.2) p.2.1)
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (r, p.2.1, p.2.2)) := by fun_prop
    exact (flow_spatialFDeriv_jointContinuous hb hX).comp hmap
  have hA : Continuous A := by
    change Continuous (fun p : ℝ × Vec 2 × ℝ =>
      fderiv ℝ (fun y => X p.1 y r) (X r p.2.1 p.2.2))
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.1, X r p.2.1 p.2.2)) := by
      exact continuous_fst.prodMk hZ
    exact (flow_spatialFDeriv_contDiff_one hb hX r).continuous.comp hmap
  have hHtCont : Continuous Ht := by
    change Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSecondSpatialDerivative X p.1 (X r p.2.1 p.2.2) r)
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.1, X r p.2.1 p.2.2)) :=
      continuous_fst.prodMk hZ
    exact (flowSecondSpatialDerivative_jointContinuous hb hX r).comp hmap
  have hHsCont : Continuous Hs := by
    change Continuous (fun p : ℝ × Vec 2 × ℝ =>
      flowSecondSpatialDerivative X p.2.2 (X r p.2.1 p.2.2) r)
    have hmap : Continuous (fun p : ℝ × Vec 2 × ℝ => (p.2.2, X r p.2.1 p.2.2)) := by
      fun_prop
    exact (flowSecondSpatialDerivative_jointContinuous hb hX r).comp hmap
  apply continuous_clm_apply.mpr
  intro h
  apply continuous_clm_apply.mpr
  intro k
  have hBh : Continuous (fun p => B p h) := (continuous_clm_apply.mp hB) h
  have hBk : Continuous (fun p => B p k) := (continuous_clm_apply.mp hB) k
  have hHtH : Continuous (fun p => Ht p (B p h)) :=
    hHtCont.clm_apply hBh
  have htermForward : Continuous (fun p => Ht p (B p h) (B p k)) :=
    hHtH.clm_apply hBk
  have hHsH : Continuous (fun p => Hs p (B p h)) :=
    hHsCont.clm_apply hBh
  have htermHs : Continuous (fun p => Hs p (B p h) (B p k)) :=
    hHsH.clm_apply hBk
  have hBcurv : Continuous (fun p => B p (Hs p (B p h) (B p k))) :=
    hB.clm_apply htermHs
  have hminusBcurv : Continuous (fun p => -B p (Hs p (B p h) (B p k))) :=
    continuous_neg.comp hBcurv
  have htermInverse : Continuous (fun p => A p (-B p (Hs p (B p h) (B p k)))) :=
    hA.clm_apply hminusBcurv
  have hsum : Continuous (fun p =>
      Ht p (B p h) (B p k) + A p (-B p (Hs p (B p h) (B p k)))) :=
    htermForward.add htermInverse
  exact hsum.congr fun p => by
    dsimp [Ht, Hs, A, B, Z, r]
    let t := p.1
    let x := p.2.1
    let s := p.2.2
    let z := X r x s
    let F : Vec 2 → Vec 2 := fun y => X t y r
    let G : Vec 2 → Vec 2 := fun y => X r y s
    have hLip : ∃ L : ℝ, ∀ u y w, ‖b u y - b u w‖ ≤ L * ‖y - w‖ := by
      obtain ⟨L, _, hL⟩ := exists_global_spatial_lipschitz hb
      exact ⟨L, hL⟩
    have hmap : (fun y => F (G y)) = (fun y => X t y s) := by
      funext y
      dsimp [F, G]
      exact flow_group_law b hLip hX y s r t
    have hcomp := HessianJointAll.flowSecondSpatialDerivative_comp
      (flow_spatial_contDiff_two hb hX r t)
      (flow_spatial_contDiff_two hb hX s r) x h k
    have hcomp' :
        flowSecondSpatialDerivative X t x s h k =
          flowSecondSpatialDerivative X t z r
              ((fderiv ℝ (fun y => X r y s) x) h)
              ((fderiv ℝ (fun y => X r y s) x) k) +
            (fderiv ℝ (fun y => X t y r) z)
              (flowSecondSpatialDerivative X r x s h k) := by
      simpa [F, G, z, flowSecondSpatialDerivative, hmap,
        ContinuousLinearMap.comp_apply] using hcomp
    have hinv := flowSecondSpatialDerivative_inverse_formula hb hX r s x h k
    have heq := hcomp'.trans (congrArg (fun v : Vec 2 =>
        flowSecondSpatialDerivative X t z r
            ((fderiv ℝ (fun y => X r y s) x) h)
            ((fderiv ℝ (fun y => X r y s) x) k) +
          (fderiv ℝ (fun y => X t y r) z) v) hinv)
    simpa [F, G, z, flowSecondSpatialDerivative, add_comm] using heq.symm

end

end AVenhance.Infra.Flow
