/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.FlowBounds

/-! Structural identities for the Section 2 construction flow. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Construction

theorem Section2FlowIdentities.linearMap_apply_two
    (A : Vec 2 →L[ℝ] Vec 2) (v : Vec 2) (i : Fin 2) :
    A v i = A (Homogenization.basisVec 0) i * v 0 +
      A (Homogenization.basisVec 1) i * v 1 := by
  have hv : v = v 0 • Homogenization.basisVec 0 + v 1 • Homogenization.basisVec 1 := by
    ext j
    fin_cases j <;> simp [Homogenization.basisVec]
  rw [hv, map_add, map_smul, map_smul]
  simp [Homogenization.basisVec]
  ring

theorem Section2FlowIdentities.continuousLinearMap_det_two (J : Vec 2 →L[ℝ] Vec 2) :
    J.det = J (Homogenization.basisVec 0) 0 * J (Homogenization.basisVec 1) 1 -
      J (Homogenization.basisVec 1) 0 * J (Homogenization.basisVec 0) 1 := by
  change LinearMap.det J.toLinearMap = _
  rw [← LinearMap.det_toMatrix' J.toLinearMap, Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, Homogenization.basisVec]

/-- In two dimensions, a left inverse of a determinant-one map is its
cofactor transpose. The four coordinate equalities are the form used in
`c.material.DX.Xinv`. -/
theorem left_inverse_entries_of_det_one
    {A B : Vec 2 →L[ℝ] Vec 2}
    (hcomp : A.comp B = ContinuousLinearMap.id ℝ (Vec 2))
    (hdet : B.det = 1) :
    A (Homogenization.basisVec 0) 0 = B (Homogenization.basisVec 1) 1 ∧
    A (Homogenization.basisVec 1) 0 = -B (Homogenization.basisVec 1) 0 ∧
    A (Homogenization.basisVec 0) 1 = -B (Homogenization.basisVec 0) 1 ∧
    A (Homogenization.basisVec 1) 1 = B (Homogenization.basisVec 0) 0 := by
  let a := B (Homogenization.basisVec 0) 0
  let b := B (Homogenization.basisVec 1) 0
  let c := B (Homogenization.basisVec 0) 1
  let d := B (Homogenization.basisVec 1) 1
  have hdet' : a * d - b * c = 1 := by
    have h := Section2FlowIdentities.continuousLinearMap_det_two B
    rw [h] at hdet
    dsimp [a, b, c, d]
    nlinarith
  have h0 : A (B (Homogenization.basisVec 0)) = Homogenization.basisVec 0 := by
    have h := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (Homogenization.basisVec 0)) hcomp
    simpa using h
  have h1 : A (B (Homogenization.basisVec 1)) = Homogenization.basisVec 1 := by
    have h := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (Homogenization.basisVec 1)) hcomp
    simpa using h
  have h00 : A (Homogenization.basisVec 0) 0 * a +
      A (Homogenization.basisVec 1) 0 * c = 1 := by
    have h := congrArg (fun v : Vec 2 => v 0) h0
    rw [Section2FlowIdentities.linearMap_apply_two] at h
    simpa [a, b, c, d, Homogenization.basisVec] using h
  have h01 : A (Homogenization.basisVec 0) 0 * b +
      A (Homogenization.basisVec 1) 0 * d = 0 := by
    have h := congrArg (fun v : Vec 2 => v 0) h1
    rw [Section2FlowIdentities.linearMap_apply_two] at h
    simpa [a, b, c, d, Homogenization.basisVec] using h
  have h10 : A (Homogenization.basisVec 0) 1 * a +
      A (Homogenization.basisVec 1) 1 * c = 0 := by
    have h := congrArg (fun v : Vec 2 => v 1) h0
    rw [Section2FlowIdentities.linearMap_apply_two] at h
    simpa [a, b, c, d, Homogenization.basisVec] using h
  have h11 : A (Homogenization.basisVec 0) 1 * b +
      A (Homogenization.basisVec 1) 1 * d = 1 := by
    have h := congrArg (fun v : Vec 2 => v 1) h1
    rw [Section2FlowIdentities.linearMap_apply_two] at h
    simpa [a, b, c, d, Homogenization.basisVec] using h
  constructor
  · linear_combination d * h00 - c * h01 -
      (A (Homogenization.basisVec 0) 0) * hdet'
  constructor
  · linear_combination -b * h00 + a * h01 -
      (A (Homogenization.basisVec 1) 0) * hdet'
  constructor
  · linear_combination d * h10 - c * h11 -
      (A (Homogenization.basisVec 0) 1) * hdet'
  · linear_combination -b * h10 + a * h11 -
      (A (Homogenization.basisVec 1) 1) * hdet'

/-- The spatial derivative trace used in Liouville's formula is the classical divergence of a
    smooth spatial slice. -/
theorem spatialDivergence_eq_vecDiv
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (t : ℝ) (x : Vec 2) :
    Infra.Flow.spatialDivergence b t x =
      AVenhance.vecDiv (b t) x := by
  rw [Infra.Flow.spatialDivergence,
    Infra.Flow.jointSpatialFDeriv_eq_slice hb]
  unfold AVenhance.vecDiv
  rw [Fin.sum_univ_two]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (b t) :=
    hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hd : DifferentiableAt ℝ (b t) x := hsmooth.differentiable (by simp) x
  have h0 := fderiv_apply hd 0
  have h1 := fderiv_apply hd 1
  have h0' : fderiv ℝ (fun y => b t y 0) x (Homogenization.basisVec 0) =
      fderiv ℝ (b t) x (Homogenization.basisVec 0) 0 := by
    rw [h0]
    rfl
  have h1' : fderiv ℝ (fun y => b t y 1) x (Homogenization.basisVec 1) =
      fderiv ℝ (b t) x (Homogenization.basisVec 1) 1 := by
    rw [h1]
    rfl
  change
    fderiv ℝ (b t) x (Homogenization.basisVec 0) 0 +
      fderiv ℝ (b t) x (Homogenization.basisVec 1) 1 =
    fderiv ℝ (fun y => b t y 0) x (Homogenization.basisVec 0) +
      fderiv ℝ (fun y => b t y 1) x (Homogenization.basisVec 1)
  rw [h0', h1']

/-- The velocity from any admissible stream function is classically
divergence-free. -/
theorem streamVel_spatialDivergence_eq_zero
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t : ℝ) (x : Vec 2) :
    Infra.Flow.spatialDivergence (streamVel φ) t x = 0 := by
  rw [spatialDivergence_eq_vecDiv (smoothPeriodic_streamVel hφ)]
  exact Infra.Classical.streamVel_vecDiv_eq_zero φ hφ t x

/-- The inverse-flow spatial derivative also has determinant one. -/
theorem constructionFlowInvJacobian_det_eq_one
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) (x : Vec 2) :
    (constructionFlowInvJacobian hseq m r s x).det = 1 := by
  let hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField (streamVel (Φ m)) :=
    smoothPeriodic_streamVel hφ
  have hX : IsFlow (streamVel (Φ m)) (constructionFlow hseq m) := by
    dsimp [constructionFlow]
    exact AVenhance.flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hdiv : ∀ t y, Infra.Flow.spatialDivergence (streamVel (Φ m)) t y = 0 :=
    fun t y => streamVel_spatialDivergence_eq_zero hφ t y
  simpa [constructionFlowInvJacobian, constructionFlowInv, constructionFlow,
    AVenhance.flowInv] using
    Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free hb hX hdiv x (s + r) s

/-- The forward and inverse variational maps at a fixed pair of times are
compositional inverses. -/
theorem constructionComposedJacobian_comp_inverse_eq_id
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) (x : Vec 2) :
    (constructionComposedFlowJacobian hseq m s r x).comp
      (constructionFlowInvJacobian hseq m r s x) =
        ContinuousLinearMap.id ℝ (Vec 2) := by
  let F : Vec 2 → Vec 2 := fun y => constructionFlow hseq m (s + r) y s
  let H : Vec 2 → Vec 2 := fun y => constructionFlowInv hseq m (s + r) y s
  let hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField (streamVel (Φ m)) :=
    smoothPeriodic_streamVel hφ
  have hX : IsFlow (streamVel (Φ m)) (constructionFlow hseq m) := by
    dsimp [constructionFlow]
    exact AVenhance.flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  obtain ⟨_, _, _, hinv⟩ :=
    Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX s (s + r)
  have hmap (y : Vec 2) : F (H y) = y := by
    simpa [F, H, constructionFlow, constructionFlowInv, flowInv] using hinv y
  have hF : HasFDerivAt F
      (constructionFlowJacobian hseq m r s (H x)) (H x) := by
    have hdiff := Infra.Flow.flow_spatial_contDiff_one hb hX s (s + r)
    simpa [F, constructionFlowJacobian, constructionFlow] using
      (hdiff.differentiable (by norm_num) (H x)).hasFDerivAt
  have hH : HasFDerivAt H (constructionFlowInvJacobian hseq m r s x) x := by
    have hdiff := Infra.Flow.flow_spatial_contDiff_one hb hX (s + r) s
    simpa [H, constructionFlowInvJacobian, constructionFlowInv, constructionFlow,
      flowInv] using (hdiff.differentiable (by norm_num) x).hasFDerivAt
  have hchain := HasFDerivAt.comp x hF hH
  have hid := hchain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => (hmap y).symm)
  have hderiv := hid.unique (hasFDerivAt_id x)
  simpa [F, H, constructionComposedFlowJacobian, constructionFlowJacobian,
    constructionFlowInvJacobian] using hderiv

/-- The `c.material.DX.Xinv` cofactor identity: in two dimensions the
composed forward Jacobian is the cofactor transpose of the inverse Jacobian.
This identity is pointwise; quantitative derivative bounds are separate. -/
theorem constructionComposedJacobian_cofactor_entries
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s r : ℝ) (x : Vec 2) :
    constructionComposedFlowJacobian hseq m s r x (Homogenization.basisVec 0) 0 =
        constructionFlowInvJacobian hseq m r s x (Homogenization.basisVec 1) 1 ∧
    constructionComposedFlowJacobian hseq m s r x (Homogenization.basisVec 1) 0 =
        -constructionFlowInvJacobian hseq m r s x (Homogenization.basisVec 1) 0 ∧
    constructionComposedFlowJacobian hseq m s r x (Homogenization.basisVec 0) 1 =
        -constructionFlowInvJacobian hseq m r s x (Homogenization.basisVec 0) 1 ∧
    constructionComposedFlowJacobian hseq m s r x (Homogenization.basisVec 1) 1 =
        constructionFlowInvJacobian hseq m r s x (Homogenization.basisVec 0) 0 := by
  exact left_inverse_entries_of_det_one
    (constructionComposedJacobian_comp_inverse_eq_id m s r x)
    (constructionFlowInvJacobian_det_eq_one m s r x)

end AVenhance.Infra.Construction
