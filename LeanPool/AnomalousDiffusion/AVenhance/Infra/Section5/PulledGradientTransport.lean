/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv

/-! Target-time differentiation of the pulled gradient along its
characteristic. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance
open Infra.Flow

/-- An entry of the row-Jacobian convention is the corresponding Fréchet
derivative evaluated on the coordinate vector. -/
theorem gradMatrix_entry_eq_fderiv
    {X : Vec 2 → Vec 2} {x : Vec 2} (hX : DifferentiableAt ℝ X x)
    (i j : Fin 2) :
    gradMatrix X x i j = fderiv ℝ X x (basisVec i) j := by
  rw [gradMatrix, Matrix.of_apply]
  change fderiv ℝ (fun y => X y j) x (basisVec i) = _
  rw [fderiv_apply hX j]
  simp

theorem PulledGradientTransport.flow_jacobian_target_deriv_component
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (s t : ℝ) (y : Vec 2) (i j : Fin 2) :
    HasDerivAt (fun r => gradMatrix (fun z => X r z s) y i j)
      (jointSpatialFDeriv b t (X t y s)
        (fderiv ℝ (fun z => X t z s) y (basisVec i)) j) t := by
  let P := existsUnique_flow_variationalEquation hb hX y s
  let V : ℝ → Vec 2 → ℝ → Vec 2 := Classical.choose P
  have hV : IsFlow (linearizedFieldAlongFlow b X y s) V :=
    (Classical.choose_spec P).1
  have hV_unique : ∀ W, IsFlow (linearizedFieldAlongFlow b X y s) W → W = V :=
    (Classical.choose_spec P).2
  have hspatial (r : ℝ) (v : Vec 2) :
      fderiv ℝ (fun z => X r z s) y v = V r v s := by
    obtain ⟨W, J, hW, hJ, hF⟩ := exists_flow_hasFDerivAt_spatial hb hX y s r
    have hWV : W = V := hV_unique W hW
    calc
      fderiv ℝ (fun z => X r z s) y v = J v := by rw [hF.fderiv]
      _ = W r v s := hJ v
      _ = V r v s := by rw [hWV]
  have hvar := hV.2 (basisVec i) s t
  have hcoord : HasDerivAt (fun r => V r (basisVec i) s j)
      (jointSpatialFDeriv b t (X t y s) (V t (basisVec i) s) j) t := by
    let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj j
    have hproj : HasFDerivAt (fun v : Vec 2 => v j)
        P (V t (basisVec i) s) := by
      change HasFDerivAt (fun v => P v) P (V t (basisVec i) s)
      exact P.hasFDerivAt
    have hcomp := hproj.comp t hvar.hasFDerivAt
    simpa [P, Function.comp_def, ContinuousLinearMap.comp_apply,
      linearizedFieldAlongFlow] using hcomp.hasDerivAt
  have hvalue : V t (basisVec i) s =
      fderiv ℝ (fun z => X t z s) y (basisVec i) := by
    exact (hspatial t (basisVec i)).symm
  have hcoord' : HasDerivAt (fun r =>
      fderiv ℝ (fun z => X r z s) y (basisVec i) j)
      (jointSpatialFDeriv b t (X t y s)
        (fderiv ℝ (fun z => X t z s) y (basisVec i)) j) t := by
    have heq : (fun r => fderiv ℝ (fun z => X r z s) y (basisVec i) j) =
        fun r => V r (basisVec i) s j := by
      funext r
      exact congrArg (fun v : Vec 2 => v j) (hspatial r (basisVec i))
    rw [heq]
    simpa [hvalue] using hcoord
  have hentry (r : ℝ) :
      gradMatrix (fun z => X r z s) y i j =
        fderiv ℝ (fun z => X r z s) y (basisVec i) j := by
    exact gradMatrix_entry_eq_fderiv
      ((Infra.Flow.flow_spatial_contDiff_one hb hX s r).differentiable
        (by norm_num) y) i j
  have hfun : (fun r => gradMatrix (fun z => X r z s) y i j) =
      fun r => fderiv ℝ (fun z => X r z s) y (basisVec i) j := by
    funext r
    exact hentry r
  simpa only [hfun] using hcoord'

/-- The pulled spatial Jacobian follows the linearized flow equation along
the characteristic. -/
theorem flowGrad_material_deriv_component
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (y : Vec 2) (i j : Fin 2) :
    HasDerivAt
      (fun r => I.flowGrad hΦ m l r (I.xFlow hΦ m l r y) i j)
      (jointSpatialFDeriv (streamVel (Φ (m - 1))) t
        (I.xFlow hΦ m l t y)
        (fderiv ℝ (I.xFlow hΦ m l t) y (basisVec i)) j) t := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  have hb : Infra.Flow.SmoothPeriodicField b :=
    Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  have hX' : IsFlow b X := flow_isFlow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  have hderiv := PulledGradientTransport.flow_jacobian_target_deriv_component hb hX' s t y i j
  have hinv (r : ℝ) : I.xFlowInv hΦ m l r (I.xFlow hΦ m l r y) = y := by
    change X s (X r y s) r = y
    calc
      X s (X r y s) r = X s y s :=
        Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hX' y s r s
      _ = y := hX'.1 y s
  have hfun : (fun r => I.flowGrad hΦ m l r (I.xFlow hΦ m l r y) i j) =
      fun r => gradMatrix (I.xFlow hΦ m l r) y i j := by
    funext r
    simp [Ingredients.flowGrad, hinv r]
  have hslice (r : ℝ) : (fun z => X r z s) = I.xFlow hΦ m l r := by
    funext z
    rfl
  have hderiv' : HasDerivAt (fun r => gradMatrix (I.xFlow hΦ m l r) y i j)
      (jointSpatialFDeriv b t (I.xFlow hΦ m l t y)
        (fderiv ℝ (I.xFlow hΦ m l t) y (basisVec i)) j) t := by
    have htrans := hderiv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r =>
        congrArg (fun Y : Vec 2 → Vec 2 => gradMatrix Y y i j) (hslice r).symm)
    simpa only [← hslice t] using htrans
  simpa only [hfun] using hderiv'

end AVenhance.Infra.Section5
