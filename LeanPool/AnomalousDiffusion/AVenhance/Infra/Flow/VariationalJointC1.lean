/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC1Core
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSpatialDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSpatialDerivativeAll
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SecondJetContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FirstJet
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Matrix.Normed

/-! Joint C¹ regularity of the variational flow on forward regions. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Equip the spatial matrix space with its coordinate supremum norm. -/
local instance avInfraFlowVariationalJointC1NormedAddCommGroup1 : NormedAddCommGroup (Matrix (Fin
    2) (Fin 2) ℝ) :=
  Matrix.normedAddCommGroup
/-- Real normed-space structure for spatial matrices with the coordinate supremum norm. -/
local instance avInfraFlowVariationalJointC1NormedSpace2 : NormedSpace ℝ (Matrix (Fin 2) (Fin 2)
    ℝ) :=
  Matrix.normedSpace

/-- Coordinate basis used to represent the variational Jacobian by a matrix. -/
noncomputable def VariationalJointC1.jacobianMatrixBasis : Module.Basis (Fin 2) ℝ (Vec 2) :=
  Pi.basisFun ℝ (Fin 2)

/-- Continuous linear equivalence from Jacobian matrices to spatial endomorphisms. -/
noncomputable def VariationalJointC1.jacobianMatrixToCLM :
    Matrix (Fin 2) (Fin 2) ℝ ≃L[ℝ] (Vec 2 →L[ℝ] Vec 2) := by
  let e₀ : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Vec 2 →ₗ[ℝ] Vec 2) :=
    Matrix.toLin VariationalJointC1.jacobianMatrixBasis VariationalJointC1.jacobianMatrixBasis
  let e₁ : (Vec 2 →ₗ[ℝ] Vec 2) ≃ₗ[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
    LinearMap.toContinuousLinearMap
  let e : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Vec 2 →L[ℝ] Vec 2) := e₀.trans e₁
  refine ⟨e, ?_, ?_⟩
  · exact e.toLinearMap.continuous_of_finiteDimensional
  · exact e.symm.toLinearMap.continuous_of_finiteDimensional

theorem flow_spatialFDeriv_apply_hasDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) (v : Vec 2) :
    HasDerivAt (fun r => fderiv ℝ (fun z => X r z s) x v)
      (jointSpatialFDeriv b t (X t x s)
        (fderiv ℝ (fun z => X t z s) x v)) t := by
  let V : ℝ → Vec 2 → ℝ → Vec 2 :=
    Classical.choose (existsUnique_flow_variationalEquation hb hX x s)
  have hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).1
  have hVuniq : ∀ W, AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) W → W = V :=
    (Classical.choose_spec (existsUnique_flow_variationalEquation hb hX x s)).2
  have hcolumn (r : ℝ) (w : Vec 2) :
      fderiv ℝ (fun z => X r z s) x w = V r w s := by
    obtain ⟨W, J, hW, hJ, hD⟩ :=
      exists_flow_hasFDerivAt_spatial hb hX x s r
    have hW_eq : W = V := hVuniq W hW
    calc
      fderiv ℝ (fun z => X r z s) x w = J w := by rw [hD.fderiv]
      _ = W r w s := hJ w
      _ = V r w s := by rw [hW_eq]
  have hEq : (fun r => fderiv ℝ (fun z => X r z s) x v) =
      fun r => V r v s := by
    funext r
    exact hcolumn r v
  rw [hEq]
  simpa [linearizedFieldAlongFlow, hcolumn t v] using hV.2 v s t

/-- On a compact forward target-time interval, the Fréchet derivative of the
spatial Jacobian in target time is the variational equation in operator form. -/
theorem flow_spatialFDeriv_target_hasDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    HasDerivAt (fun r => fderiv ℝ (fun z => X r z s) x)
      ((jointSpatialFDeriv b t (X t x s)).comp
        (fderiv ℝ (fun z => X t z s) x)) t := by
  let J : ℝ → Vec 2 →L[ℝ] Vec 2 := fun r =>
    fderiv ℝ (fun z => X r z s) x
  let M : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun r =>
    VariationalJointC1.jacobianMatrixBasis.toMatrix (fun j => J r
        (VariationalJointC1.jacobianMatrixBasis j))
  let A : Vec 2 →L[ℝ] Vec 2 :=
    (jointSpatialFDeriv b t (X t x s)).comp (J t)
  let M' : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    A (VariationalJointC1.jacobianMatrixBasis j) i
  have hmatrix (r : ℝ) : M r = LinearMap.toMatrix VariationalJointC1.jacobianMatrixBasis
      VariationalJointC1.jacobianMatrixBasis (J r).toLinearMap := by
    ext i j
    simp [M, Module.Basis.toMatrix_apply, VariationalJointC1.jacobianMatrixBasis]
  have hrecover (r : ℝ) : VariationalJointC1.jacobianMatrixToCLM (M r) = J r := by
    ext w i
    dsimp [VariationalJointC1.jacobianMatrixToCLM]
    change (Matrix.toLin VariationalJointC1.jacobianMatrixBasis
        VariationalJointC1.jacobianMatrixBasis (M r) w) i =
      (J r w) i
    rw [hmatrix r, Matrix.toLin_toMatrix]
    rfl
  have hM : HasDerivAt M M' t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have hcol := flow_spatialFDeriv_apply_hasDerivAt hb hX x s t
      (VariationalJointC1.jacobianMatrixBasis j)
    have hcoord : HasDerivAt (fun r => J r (VariationalJointC1.jacobianMatrixBasis j) i)
        (jointSpatialFDeriv b t (X t x s)
          (J t (VariationalJointC1.jacobianMatrixBasis j)) i) t :=
      (hasDerivAt_pi.mp hcol) i
    simpa [M, M', A, J, Module.Basis.toMatrix_apply, VariationalJointC1.jacobianMatrixBasis] using
        hcoord
  have hE : HasFDerivAt (fun m : Matrix (Fin 2) (Fin 2) ℝ =>
      VariationalJointC1.jacobianMatrixToCLM m)
      VariationalJointC1.jacobianMatrixToCLM.toContinuousLinearMap (M t) :=
    VariationalJointC1.jacobianMatrixToCLM.toContinuousLinearMap.hasFDerivAt
  have hEcurve := HasFDerivAt.comp_hasDerivAt t hE hM
  have hM' : M' = VariationalJointC1.jacobianMatrixBasis.toMatrix (fun j => A
      (VariationalJointC1.jacobianMatrixBasis j)) := by
    ext i j
    simp [M', Module.Basis.toMatrix_apply, VariationalJointC1.jacobianMatrixBasis]
  have hEderiv : VariationalJointC1.jacobianMatrixToCLM.toContinuousLinearMap M' = A := by
    rw [hM']
    have hmatrixA : VariationalJointC1.jacobianMatrixBasis.toMatrix (fun j => A
        (VariationalJointC1.jacobianMatrixBasis j)) =
        LinearMap.toMatrix VariationalJointC1.jacobianMatrixBasis
            VariationalJointC1.jacobianMatrixBasis A.toLinearMap := by
      ext i j
      simp [Module.Basis.toMatrix_apply, VariationalJointC1.jacobianMatrixBasis]
    rw [hmatrixA]
    ext w i
    dsimp [VariationalJointC1.jacobianMatrixToCLM]
    change (Matrix.toLin VariationalJointC1.jacobianMatrixBasis
        VariationalJointC1.jacobianMatrixBasis
      (LinearMap.toMatrix VariationalJointC1.jacobianMatrixBasis
          VariationalJointC1.jacobianMatrixBasis A.toLinearMap) w) i =
        (A w) i
    rw [Matrix.toLin_toMatrix]
    rfl
  have hJ : HasDerivAt (fun r => J r) (A) t := by
    have hJ' := hEcurve.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (hrecover r).symm)
    change HasDerivAt (fun r => J r)
      (VariationalJointC1.jacobianMatrixToCLM.toContinuousLinearMap M') t at hJ'
    rw [hEderiv] at hJ'
    exact hJ'
  simpa [J, A] using hJ

/-- The spatial Jacobian is jointly C¹ in target time and initial point on a
forward open strip with fixed initial time. -/
theorem flow_spatialFDeriv_contDiffOn_one_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s T : ℝ) (hst : s < T) :
    ContDiffOn ℝ 1
      (fun p : ℝ × Vec 2 => fderiv ℝ (fun y => X p.1 y s) p.2)
      (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
  let f : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X p.1 y s) p.2
  let J : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p => f p
  let Dtime : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    (jointSpatialFDeriv b p.1 (X p.1 p.2 s)).comp (J p)
  let Dparam : ℝ × Vec 2 → Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) := fun p =>
    flowSecondSpatialDerivative X p.1 p.2 s
  have hopen : IsOpen (Ioo s T ×ˢ (univ : Set (Vec 2))) :=
    isOpen_Ioo.prod isOpen_univ
  have hTime : ∀ t x, (t, x) ∈ Ioo s T ×ˢ (univ : Set (Vec 2)) →
      HasDerivAt (fun r => f (r, x)) (Dtime (t, x)) t := by
    intro t x hx
    exact flow_spatialFDeriv_target_hasDerivAt hb hX x s t
  have hParam : ∀ t x, (t, x) ∈ Ioo s T ×ˢ (univ : Set (Vec 2)) →
      HasStrictFDerivAt (fun y => f (t, y)) (Dparam (t, x)) x := by
    intro t x hx
    have hslice : ContDiff ℝ 1 (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) :=
      (flow_spatial_contDiff_two hb hX s t).fderiv_right (by norm_num)
    have hAt : ContDiffAt ℝ 1
        (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) x := by
      exact hslice.contDiffAt
    have hstrict := hAt.hasStrictFDerivAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
    simpa [f, Dparam, flowSecondSpatialDerivative] using hstrict
  have hA : Continuous (fun q : ℝ × Vec 2 =>
      jointSpatialFDeriv b q.1 (X q.1 q.2 s)) := by
    have hbase := flow_continuous_joint_of_smoothPeriodic hb hX
    have hmap : Continuous (fun q : ℝ × Vec 2 => (q.1, q.2, s)) := by fun_prop
    have hX' : Continuous (fun q : ℝ × Vec 2 => X q.1 q.2 s) :=
      hbase.comp hmap
    have hpair : Continuous (fun q : ℝ × Vec 2 =>
        (q.1, X q.1 q.2 s)) := continuous_fst.prodMk hX'
    exact jointSpatialFDeriv_continuous hb |>.comp hpair
  have hJ : ContinuousOn J (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
    have hstrip := flow_spatialFDeriv_jointContinuousOn_of_le hb hX s T
      (le_of_lt hst)
    have hrestrict : ContinuousOn J (Icc s T ×ˢ (univ : Set (Vec 2))) := hstrip
    exact hrestrict.mono fun p hp =>
      ⟨Ioo_subset_Icc_self hp.1, hp.2⟩
  have hDtime : ContinuousOn Dtime (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
    have hA' : ContinuousOn
        (fun p : ℝ × Vec 2 => jointSpatialFDeriv b p.1 (X p.1 p.2 s))
        (Ioo s T ×ˢ (univ : Set (Vec 2))) := hA.continuousOn
    exact hA'.clm_comp hJ
  have hDparam : ContinuousOn Dparam (Ioo s T ×ˢ (univ : Set (Vec 2))) := by
    have hstrip := flowSecondSpatialDerivative_jointContinuousOn_of_le hb hX s T
      (le_of_lt hst)
    have hrestrict : ContinuousOn Dparam (Icc s T ×ˢ (univ : Set (Vec 2))) := hstrip
    exact hrestrict.mono fun p hp =>
      ⟨Ioo_subset_Icc_self hp.1, hp.2⟩
  have hresult := contDiffOn_one_of_time_and_parameter_derivatives
    f (Ioo s T ×ˢ (univ : Set (Vec 2))) hopen Dtime Dparam hTime hParam hDtime hDparam
  simpa [f] using hresult

/-- Joint time-space differential of the flow with its starting time fixed. -/
noncomputable def VariationalJointC1.flowFixedStartDerivativeAt
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) (s : ℝ)
    (q : ℝ × Vec 2) : (ℝ × Vec 2) →L[ℝ] Vec 2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ (b q.1 (X q.1 q.2 s))).coprod
    (fderiv ℝ (fun y => X q.1 y s) q.2)

/-- For a fixed start time, the spatial Jacobian is jointly C¹ across both
target-time orientations. -/
theorem flow_spatialFDeriv_contDiff_one
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s : ℝ) :
    ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => fderiv ℝ (fun y => X p.1 y s) p.2) := by
  let f : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    fderiv ℝ (fun y => X p.1 y s) p.2
  let J : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := f
  let Dtime : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    (jointSpatialFDeriv b p.1 (X p.1 p.2 s)).comp (J p)
  let Dparam : ℝ × Vec 2 → Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) := fun p =>
    flowSecondSpatialDerivative X p.1 p.2 s
  have hTime : ∀ t x, HasDerivAt (fun r => f (r, x)) (Dtime (t, x)) t := by
    intro t x
    exact flow_spatialFDeriv_target_hasDerivAt hb hX x s t
  have hParam : ∀ t x,
      HasStrictFDerivAt (fun y => f (t, y)) (Dparam (t, x)) x := by
    intro t x
    have hslice : ContDiff ℝ 1
        (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) :=
      (flow_spatial_contDiff_two hb hX s t).fderiv_right (by norm_num)
    have hAt : ContDiffAt ℝ 1
        (fun y : Vec 2 => fderiv ℝ (fun z => X t z s) y) x := hslice.contDiffAt
    have hstrict := hAt.hasStrictFDerivAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    simpa [f, Dparam, flowSecondSpatialDerivative] using hstrict
  have hflow : Continuous (fun p : ℝ × Vec 2 => X p.1 p.2 s) := by
    have hbase := flow_continuous_joint_of_smoothPeriodic hb hX
    have hmap : Continuous (fun p : ℝ × Vec 2 => (p.1, p.2, s)) := by fun_prop
    exact hbase.comp hmap
  have hfield : Continuous (fun p : ℝ × Vec 2 =>
      jointSpatialFDeriv b p.1 (X p.1 p.2 s)) := by
    have hpair : Continuous (fun p : ℝ × Vec 2 => (p.1, X p.1 p.2 s)) :=
      continuous_fst.prodMk hflow
    exact jointSpatialFDeriv_continuous hb |>.comp hpair
  have hJcont : Continuous (fun p : ℝ × Vec 2 => J p) := by
    have hmap : Continuous (fun p : ℝ × Vec 2 => (p.1, p.2, s)) := by fun_prop
    exact (flow_spatialFDeriv_jointContinuous hb hX).comp hmap
  have hDtimeCont : Continuous (fun p : ℝ × Vec 2 => Dtime p) := by
    change Continuous (fun p =>
      (jointSpatialFDeriv b p.1 (X p.1 p.2 s)).comp (J p))
    exact hfield.clm_comp hJcont
  have hDparamCont : Continuous (fun p : ℝ × Vec 2 => Dparam p) := by
    change Continuous (fun p : ℝ × Vec 2 =>
      flowSecondSpatialDerivative X p.1 p.2 s)
    exact flowSecondSpatialDerivative_jointContinuous hb hX s
  exact contDiff_one_of_time_and_parameter_derivatives f Dtime Dparam
    hTime hParam hDtimeCont hDparamCont

end

end AVenhance.Infra.Flow
