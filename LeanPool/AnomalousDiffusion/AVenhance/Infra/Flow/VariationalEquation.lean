/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FlowIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! The linear variational equation along a characterized flow trajectory. -/

@[expose] public section

open Homogenization
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

/-- The spatial derivative of `b` written as the restriction of the joint
time-space derivative to the spatial factor. -/
noncomputable def jointSpatialFDeriv
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) :
    Vec 2 →L[ℝ] Vec 2 :=
  (fderiv ℝ (Function.uncurry b) (t, x)).comp
    (ContinuousLinearMap.inr ℝ ℝ (Vec 2))

/-- The joint derivative restricted to the spatial factor is the derivative of
the fixed-time spatial slice. -/
theorem jointSpatialFDeriv_eq_slice
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x : Vec 2) :
    jointSpatialFDeriv b t x = fderiv ℝ (fun y => b t y) x := by
  have hF : Differentiable ℝ (Function.uncurry b) :=
    hb.smooth.differentiable (by norm_num)
  have hcomp := (hF (t, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right t x)
  have hslice : HasFDerivAt (fun y : Vec 2 => b t y)
      (jointSpatialFDeriv b t x) x := by
    simpa [jointSpatialFDeriv, Function.uncurry] using hcomp
  exact hslice.fderiv.symm

/-- The joint spatial derivative varies continuously in its time and space
arguments. -/
theorem jointSpatialFDeriv_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    Continuous (fun p : ℝ × Vec 2 => jointSpatialFDeriv b p.1 p.2) := by
  have hD : Continuous (fun p : ℝ × Vec 2 =>
      fderiv ℝ (Function.uncurry b) p) :=
    hb.smooth.continuous_fderiv (by norm_num)
  have hcomp : Continuous
      (fun D : (ℝ × Vec 2) →L[ℝ] Vec 2 =>
        D.comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) := by
    fun_prop
  exact hcomp.comp hD

/-- The joint spatial derivative is globally bounded for a smooth periodic
field. -/
theorem exists_global_jointSpatialFDeriv_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_global_iteratedFDeriv_bound hb 1
  refine ⟨C, hC0, ?_⟩
  intro t x
  rw [jointSpatialFDeriv]
  calc
    ‖(fderiv ℝ (Function.uncurry b) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2))‖ ≤
        ‖fderiv ℝ (Function.uncurry b) (t, x)‖ *
          ‖ContinuousLinearMap.inr ℝ ℝ (Vec 2)‖ :=
      (fderiv ℝ (Function.uncurry b) (t, x)).opNorm_comp_le
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2))
    _ = ‖fderiv ℝ (Function.uncurry b) (t, x)‖ := by
      rw [ContinuousLinearMap.norm_inr, mul_one]
    _ ≤ C := by
      simpa only [norm_iteratedFDeriv_one] using hC (t, x)

/-- The coefficient field of the variational equation along a fixed
characterized trajectory. -/
noncomputable def linearizedFieldAlongFlow
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (x : Vec 2) (s : ℝ) : ℝ → Vec 2 → Vec 2 :=
  fun t v => jointSpatialFDeriv b t (X t x s) v

/-- The variational coefficient along a fixed flow trajectory is continuous. -/
theorem linearizedFieldAlongFlow_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s : ℝ) :
    Continuous (fun t => jointSpatialFDeriv b t (X t x s)) := by
  exact (jointSpatialFDeriv_continuous hb).comp
    (continuous_id.prodMk (flow_continuous_time b hX x s))

/-- A bounded continuous family of linear vector fields has a globally
characterized flow. -/
theorem existsUnique_linearSystemFlow
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (hA : Continuous A)
    (M : ℝ) (hM : ∀ t, ‖A t‖ ≤ M) :
    ∃! V : ℝ → Vec 2 → ℝ → Vec 2,
      AVenhance.IsFlow (fun t v => A t v) V := by
  have hfield : Continuous (fun p : ℝ × Vec 2 => A p.1 p.2) := by
    fun_prop
  have hLip : ∀ t u v, ‖A t u - A t v‖ ≤ M * ‖u - v‖ := by
    intro t u v
    calc
      ‖A t u - A t v‖ = ‖A t (u - v)‖ := by rw [map_sub]
      _ ≤ ‖A t‖ * ‖u - v‖ := (A t).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)
  exact existsUnique_flow (fun t v => A t v) hfield ⟨M, hLip⟩

/-- A vector solution of a homogeneous linear system vanishing initially is
identically zero. -/
theorem linearSystemFlow_zero
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (M : ℝ)
    (hLip : ∀ t u v, ‖A t u - A t v‖ ≤ M * ‖u - v‖)
    {V : ℝ → Vec 2 → ℝ → Vec 2}
    (hV : AVenhance.IsFlow (fun t v => A t v) V) (s : ℝ) :
    ∀ t, V t 0 s = 0 := by
  have hzero : ∀ t, HasDerivAt (fun _ : ℝ => (0 : Vec 2)) (A t 0) t := by
    intro t
    simpa using (hasDerivAt_const t (0 : Vec 2))
  have hcurves := integralCurve_unique (fun t v => A t v) hLip
    (fun t => hV.2 0 s t) hzero (s := s) (hV.1 0 s)
  intro t
  have h := congrFun hcurves t
  simpa using h

/-- Solutions of the linear variational equation depend linearly on their
initial direction. -/
theorem VariationalEquation.linearSystemFlow_add_smul
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (M : ℝ)
    (hLip : ∀ t u v, ‖A t u - A t v‖ ≤ M * ‖u - v‖)
    {V : ℝ → Vec 2 → ℝ → Vec 2}
    (hV : AVenhance.IsFlow (fun t v => A t v) V) (s : ℝ) :
    (∀ t v w, V t (v + w) s = V t v s + V t w s) ∧
    (∀ t (c : ℝ) v, V t (c • v) s = c • V t v s) := by
  have hadd (v w : Vec 2) (t : ℝ) :
      V t (v + w) s = V t v s + V t w s := by
    have hsum : ∀ r, HasDerivAt (fun q => V q v s + V q w s)
        (A r (V r v s + V r w s)) r := by
      intro r
      convert (hV.2 v s r).add (hV.2 w s r) using 1
      ext q
      simp [map_add]
    have hstart : V s (v + w) s = V s v s + V s w s := by
      rw [hV.1, hV.1, hV.1]
    have hcurves := integralCurve_unique (fun r z => A r z) hLip
      (fun r => hV.2 (v + w) s r)
      (fun r => hsum r) (s := s) hstart
    exact congrFun hcurves t
  have hsmul (c : ℝ) (v : Vec 2) (t : ℝ) :
      V t (c • v) s = c • V t v s := by
    have hscale : ∀ r, HasDerivAt (fun q => c • V q v s)
        (A r (c • V r v s)) r := by
      intro r
      convert (hV.2 v s r).const_smul c using 1
      ext q
      simp [map_smul]
    have hstart : V s (c • v) s = c • V s v s := by
      rw [hV.1, hV.1]
    have hcurves := integralCurve_unique (fun r z => A r z) hLip
      (fun r => hV.2 (c • v) s r)
      (fun r => hscale r) (s := s) hstart
    exact congrFun hcurves t
  exact ⟨fun t v w => hadd v w t, fun t c v => hsmul c v t⟩

/-- At each time, the variational solution in its initial vector is a
continuous linear map. -/
theorem exists_flow_variationalContinuousLinearMap
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (M : ℝ)
    (hM : ∀ t, ‖A t‖ ≤ M)
    {V : ℝ → Vec 2 → ℝ → Vec 2}
    (hV : AVenhance.IsFlow (fun t v => A t v) V)
    (t s : ℝ) :
    ∃ J : Vec 2 →L[ℝ] Vec 2, ∀ v, J v = V t v s := by
  have hLip : ∀ r u v, ‖A r u - A r v‖ ≤ M * ‖u - v‖ := by
    intro r u v
    calc
      ‖A r u - A r v‖ = ‖A r (u - v)‖ := by rw [map_sub]
      _ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right (hM r) (norm_nonneg _)
  obtain ⟨hadd, hsmul⟩ := VariationalEquation.linearSystemFlow_add_smul A M hLip hV s
  let L : Vec 2 →ₗ[ℝ] Vec 2 :=
    { toFun := fun v => V t v s
      map_add' := hadd t
      map_smul' := hsmul t }
  have hbound : ∀ v, ‖L v‖ ≤ Real.exp (M * |t - s|) * ‖v‖ := by
    intro v
    have hgron := flow_spatial_gronwall (fun r z => A r z) hLip hV v 0 s t
    have hzero := linearSystemFlow_zero A M hLip hV s t
    simpa [L, hzero] using hgron
  refine ⟨L.mkContinuous (Real.exp (M * |t - s|)) hbound, ?_⟩
  intro v
  rfl

/-- Existence and uniqueness of the vector-valued variational solution along
any characterized flow of a smooth periodic field. -/
theorem existsUnique_flow_variationalEquation
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s : ℝ) :
    ∃! V : ℝ → Vec 2 → ℝ → Vec 2,
      AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V := by
  obtain ⟨M, hM0, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  exact existsUnique_linearSystemFlow
    (fun t => jointSpatialFDeriv b t (X t x s))
    (linearizedFieldAlongFlow_continuous hb hX x s) M
    (fun t => hM t (X t x s))

end AVenhance.Infra.Flow
