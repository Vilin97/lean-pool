/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialTransition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart

/-! Pulling material derivatives back along a flow turns them into ordinary
time derivatives. This is the all-order chain-rule interface for material
estimates. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Construction

/-- View a curried scalar field as a function on joint time-space. -/
def constructionJointScalar (F : ℝ → Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => F p.1 p.2

/-- View a curried vector field as a function on joint time-space. -/
def constructionJointVector (b : ℝ → Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  fun p => b p.1 p.2

/-- Embed a spatial direction into the time-space-start-time domain, fixing both times. -/
def MaterialPullback.constructionSpatialInputCLM :
    Vec 2 →L[ℝ] (ℝ × Vec 2 × ℝ) :=
  (0 : Vec 2 →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.id ℝ (Vec 2)).prod (0 : Vec 2 →L[ℝ] ℝ))

/-- The material derivative is the joint derivative in the space-time
direction `(1,b)`. -/
theorem constructionMaterialDerivative_eq_joint_fderiv
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) (t : ℝ) (x : Vec 2) :
    constructionMaterialDerivative b F t x =
      fderiv ℝ (constructionJointScalar F) (t, x) (1, b t x) := by
  let H := constructionJointScalar F
  have hH := (hF.differentiable (by norm_num) (t, x)).hasFDerivAt
  have htimePath : HasDerivAt (fun r : ℝ => (r, x)) (1, (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const (c := x) (x := t))
  have htime := hH.comp_hasDerivAt t htimePath
  have htime' : deriv (fun r : ℝ => F r x) t =
      fderiv ℝ H (t, x) (1, (0 : Vec 2)) := by
    simpa [H, constructionJointScalar, Function.comp_def] using htime.deriv
  have hspacePath := hasFDerivAt_prodMk_right
    (𝕜 := ℝ) (E := ℝ) (F := Vec 2) t x
  have hspace := hH.comp x hspacePath
  have hspace' : fderiv ℝ (F t) x =
      (fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) := by
    simpa [H, constructionJointScalar, Function.comp_def] using hspace.fderiv
  change deriv (fun r : ℝ => F r x) t + fderiv ℝ (F t) x (b t x) = _
  rw [htime', hspace']
  change fderiv ℝ H (t, x) (1, (0 : Vec 2)) +
      fderiv ℝ H (t, x) (0, b t x) = _
  have hsplit : ((1 : ℝ), b t x) =
      (1, (0 : Vec 2)) + (0, b t x) := by
    ext <;> simp
  rw [← map_add]
  exact congrArg (fderiv ℝ H (t, x)) hsplit.symm

/-- Smooth space-time data give a smooth material derivative. -/
theorem constructionMaterialDerivative_joint_contDiff
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar (constructionMaterialDerivative b F)) := by
  let H := constructionJointScalar F
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ H p) :=
    hF.fderiv_right (by simp)
  have hb' : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) := hb
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => ((1 : ℝ), constructionJointVector b p)) :=
    contDiff_const.prodMk hb'
  have hresult := hdf.clm_apply hv
  have heq : constructionJointScalar (constructionMaterialDerivative b F) =
      fun p => fderiv ℝ H p ((1 : ℝ), constructionJointVector b p) := by
    funext p
    exact constructionMaterialDerivative_eq_joint_fderiv hF p.1 p.2
  rw [heq]
  exact hresult

/-- Every material iterate stays smooth when the velocity and the original
space-time profile are smooth. -/
theorem constructionMaterialIterate_joint_contDiff
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) :
    ∀ ell : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar (constructionMaterialIterate b ell F)) := by
  intro ell
  induction ell with
  | zero => exact hF
  | succ ell ih =>
      simpa [constructionMaterialIterate] using
        constructionMaterialDerivative_joint_contDiff hb ih

/-- The composed forward Jacobian is jointly smooth in the target time and
spatial point. This is obtained by differentiating the joint smooth flow in
its spatial variable and composing with the jointly smooth inverse flow. -/
theorem constructionComposedFlowJacobian_joint_contDiff
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionComposedFlowJacobian hseq m s p.1 p.2) := by
  let v : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let hφ := streamSeq_isAdmissible hseq m
  have hv : Infra.Flow.SmoothPeriodicField v := smoothPeriodic_streamVel hφ
  have hIsFlow : IsFlow v (constructionFlow hseq m) := by
    dsimp [v, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hforward : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) := by
    simpa [constructionFlow] using
      Infra.Flow.flow_joint_contDiff_infty hv hIsFlow
  have hdf : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ => fderiv ℝ
        (fun q : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m q.1 q.2.1 q.2.2) p) :=
    hforward.fderiv_right (by simp)
  have hpartial : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ =>
        (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m q.1 q.2.1 q.2.2) p).comp
          MaterialPullback.constructionSpatialInputCLM) :=
    hdf.clm_comp contDiff_const
  have hparam : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => (s + p.1, p.2, s)) := by
    fun_prop
  have hpartialShift : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
          constructionFlow hseq m q.1 q.2.1 q.2.2) (s + p.1, p.2, s)).comp
          MaterialPullback.constructionSpatialInputCLM) := by
    exact hpartial.comp hparam
  have hJacobian : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionFlowJacobian hseq m p.1 s p.2) := by
    have heq : (fun p : ℝ × Vec 2 =>
        constructionFlowJacobian hseq m p.1 s p.2) =
        fun p =>
          (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
            constructionFlow hseq m q.1 q.2.1 q.2.2) (s + p.1, p.2, s)).comp
            MaterialPullback.constructionSpatialInputCLM := by
      funext p
      let q : ℝ × Vec 2 × ℝ := (s + p.1, p.2, s)
      have hfirst : HasFDerivAt (fun _ : Vec 2 => q.1)
          (0 : Vec 2 →L[ℝ] ℝ) p.2 :=
        hasFDerivAt_const (c := q.1) (x := p.2)
      have hsecond : HasFDerivAt (fun y : Vec 2 => (y, q.2.2))
          ((ContinuousLinearMap.id ℝ (Vec 2)).prod
            (0 : Vec 2 →L[ℝ] ℝ)) p.2 :=
        (hasFDerivAt_id p.2).prodMk
          (hasFDerivAt_const (c := q.2.2) (x := p.2))
      have hinput : HasFDerivAt (fun y : Vec 2 => (q.1, (y, q.2.2)))
          MaterialPullback.constructionSpatialInputCLM p.2 := by
        simpa [MaterialPullback.constructionSpatialInputCLM] using hfirst.prodMk hsecond
      have hjointDeriv := (hforward.differentiable (by norm_num) q).hasFDerivAt
      have hcomp := hjointDeriv.comp p.2 hinput
      calc
        fderiv ℝ (fun y : Vec 2 => constructionFlow hseq m (s + p.1) y s)
            p.2 = fderiv ℝ (fun y : Vec 2 =>
              (fun q : ℝ × Vec 2 × ℝ =>
                constructionFlow hseq m q.1 q.2.1 q.2.2) (s + p.1, y, s)) p.2 := by
                congr 1
        _ = (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
              constructionFlow hseq m q.1 q.2.1 q.2.2)
              (s + p.1, p.2, s)).comp MaterialPullback.constructionSpatialInputCLM := by
                simpa [Function.comp_def, q, MaterialPullback.constructionSpatialInputCLM] using
                  hcomp.fderiv
    rw [heq]
    exact hpartialShift
  have hinverseJoint : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ =>
        constructionFlowInv hseq m p.1 p.2.1 p.2.2) := by
    simpa [constructionFlowInv, constructionFlow, AVenhance.flowInv] using
      Infra.Flow.flow_inverse_joint_contDiff_infty hv hIsFlow
  have hinverseMap : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionFlowInv hseq m (s + p.1) p.2 s) := by
    have h := hinverseJoint.comp hparam
    simpa [Function.comp_def] using h
  have hpair : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        (p.1, constructionFlowInv hseq m (s + p.1) p.2 s)) :=
    contDiff_fst.prodMk hinverseMap
  have hmatrix : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionFlowJacobian hseq m p.1 s
          (constructionFlowInv hseq m (s + p.1) p.2 s)) := by
    simpa [Function.comp_def] using hJacobian.comp hpair
  have heq : (fun p : ℝ × Vec 2 =>
      constructionComposedFlowJacobian hseq m s p.1 p.2) =
      fun p => constructionFlowJacobian hseq m p.1 s
        (constructionFlowInv hseq m (s + p.1) p.2 s) := by
    funext p
    rfl
  rw [heq]
  exact hmatrix

/-- Along any differentiable characteristic of `b`, one material derivative
is the ordinary derivative of the pulled-back profile. -/
theorem constructionMaterialDerivative_eq_deriv_pullback
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ} {X : ℝ → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) (t : ℝ)
    (hX : HasDerivAt X (b t (X t)) t) :
    constructionMaterialDerivative b F t (X t) =
      deriv (fun r : ℝ => F r (X r)) t := by
  let H := constructionJointScalar F
  have hH := (hF.differentiable (by norm_num) (t, X t)).hasFDerivAt
  have hpath : HasDerivAt (fun r : ℝ => (r, X r)) (1, b t (X t)) t :=
    (hasDerivAt_id t).prodMk hX
  have hcomp := hH.comp_hasDerivAt t hpath
  have hjoint : deriv (fun r : ℝ => F r (X r)) t =
      fderiv ℝ H (t, X t) (1, b t (X t)) := by
    simpa [H, constructionJointScalar, Function.comp_def] using hcomp.deriv
  rw [constructionMaterialDerivative_eq_joint_fderiv hF t (X t), hjoint]

/-- All iterated material derivatives pull back to ordinary time derivatives
along the characteristic. -/
theorem constructionMaterialIterate_eq_iteratedTimeDerivative_pullback
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ} {X : ℝ → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F))
    (hX : ∀ t : ℝ, HasDerivAt X (b t (X t)) t)
    (ell : ℕ) (t : ℝ) :
    constructionMaterialIterate b ell F t (X t) =
      iteratedTimeDerivative ell (fun r : ℝ => F r (X r)) t := by
  induction ell generalizing t with
  | zero => rfl
  | succ ell ih =>
      have hprev : iteratedTimeDerivative ell (fun r : ℝ => F r (X r)) =
          fun r : ℝ => constructionMaterialIterate b ell F r (X r) := by
        funext r
        exact (ih r).symm
      rw [iteratedTimeDerivative, hprev]
      have hstep := constructionMaterialDerivative_eq_deriv_pullback
        (F := constructionMaterialIterate b ell F)
        (constructionMaterialIterate_joint_contDiff hb hF ell) t (hX t)
      simpa [constructionMaterialIterate] using hstep

/-- For the Section 2 flow, material iteration of the composed forward
Jacobian becomes ordinary differentiation of the forward Jacobian along its
starting point. The smoothness premise is qualitative joint smoothness of the
composed Jacobian entry. -/
theorem constructionComposedFlowJacobian_materialIterate_eq_timeDerivative
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s : ℝ) (x : Vec 2)
    (i j : Fin 2) (ell : ℕ) (t : ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionComposedFlowJacobian hseq m s p.1 p.2
          (basisVec j) i)) :
    constructionMaterialIterate
      (fun r y => streamVel (Φ m) (s + r) y) ell
      (fun r y => constructionComposedFlowJacobian hseq m s r y
        (basisVec j) i) t
      (constructionFlow hseq m (s + t) x s) =
    iteratedTimeDerivative ell
      (fun r => constructionFlowJacobian hseq m r s x (basisVec j) i) t := by
  let b : ℝ → Vec 2 → Vec 2 := fun r y => streamVel (Φ m) (s + r) y
  let F : ℝ → Vec 2 → ℝ := fun r y =>
    constructionComposedFlowJacobian hseq m s r y (basisVec j) i
  let X : ℝ → Vec 2 := fun r => constructionFlow hseq m (s + r) x s
  let v := streamVel (Φ m)
  let hφ := streamSeq_isAdmissible hseq m
  have hv : Infra.Flow.SmoothPeriodicField v := smoothPeriodic_streamVel hφ
  have hIsFlow : IsFlow v (constructionFlow hseq m) := by
    dsimp [v, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) := by
    have hbase : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => v p.1 p.2) := hv.smooth
    have hshift : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => streamVel (Φ m) (s + p.1) p.2)
    exact hbase.comp hshift
  have hX (r : ℝ) : HasDerivAt X (b r (X r)) r := by
    have hode := hIsFlow.2 x s (r + s)
    simpa [X, b, v, constructionFlow, add_comm] using hode.comp_add_const r s
  have hF' : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionComposedFlowJacobian hseq m s p.1 p.2
          (basisVec j) i)
    exact hF
  have hpull := constructionMaterialIterate_eq_iteratedTimeDerivative_pullback
    (b := b) (F := F) (X := X) hb hF' hX ell t
  have hL : ∃ L : ℝ, ∀ q y z,
      ‖v q y - v q z‖ ≤ L * ‖y - z‖ := by
    obtain ⟨L, _, hL⟩ := Infra.Flow.exists_global_spatial_lipschitz hv
    exact ⟨L, hL⟩
  have hinv (r : ℝ) :
      constructionFlowInv hseq m (s + r)
        (constructionFlow hseq m (s + r) x s) s = x := by
    calc
      constructionFlowInv hseq m (s + r)
          (constructionFlow hseq m (s + r) x s) s =
        constructionFlow hseq m s
          (constructionFlow hseq m (s + r) x s) (s + r) := by
            rfl
      _ = constructionFlow hseq m s x s := by
        exact Infra.Flow.flow_group_law v hL hIsFlow x s (s + r) s
      _ = x := hIsFlow.1 x s
  have htrace : (fun r : ℝ => F r (X r)) =
      fun r => constructionFlowJacobian hseq m r s x (basisVec j) i := by
    funext r
    simp [F, X, constructionComposedFlowJacobian, hinv r]
  calc
    _ = iteratedTimeDerivative ell (fun r : ℝ => F r (X r)) t := by
      simpa [b, F, X] using hpull
    _ = iteratedTimeDerivative ell
        (fun r => constructionFlowJacobian hseq m r s x (basisVec j) i) t := by
      rw [htrace]

/-- The composed-flow Jacobian pullback identity with its qualitative
smoothness premise supplied by joint smoothness of the construction flow. -/
theorem constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s : ℝ) (x : Vec 2)
    (i j : Fin 2) (ell : ℕ) (t : ℝ) :
    constructionMaterialIterate
      (fun r y => streamVel (Φ m) (s + r) y) ell
      (fun r y => constructionComposedFlowJacobian hseq m s r y
        (basisVec j) i) t
      (constructionFlow hseq m (s + t) x s) =
    iteratedTimeDerivative ell
      (fun r => constructionFlowJacobian hseq m r s x (basisVec j) i) t := by
  have hmatrix := constructionComposedFlowJacobian_joint_contDiff
    (hseq := hseq) m s
  have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionComposedFlowJacobian hseq m s p.1 p.2 (basisVec j)) :=
    hmatrix.clm_apply contDiff_const
  have hentry : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        constructionComposedFlowJacobian hseq m s p.1 p.2 (basisVec j) i) :=
    (contDiff_pi.1 hcolumn) i
  exact constructionComposedFlowJacobian_materialIterate_eq_timeDerivative
    (hseq := hseq) m s x i j ell t hentry

end AVenhance.Infra.Construction

end
