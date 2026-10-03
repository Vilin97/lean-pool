/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Preparatory ODE systems for higher spatial variations of a smooth flow. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem HigherVariation.gronwallBound_zero_scale_higher (L a c d : ℝ) :
    gronwallBound 0 L (c * a) d = c * gronwallBound 0 L a d := by
  by_cases hL : L = 0
  · simp [gronwallBound, hL]
    ring
  · simp [gronwallBound, hL]
    ring

/-- The pair of spatial directions, embedded into the joint time-space domain. -/
def HigherVariation.spatialDirections (h k : Vec 2) : Fin 2 → ℝ × Vec 2 :=
  fun i => if i = 0 then (0, h) else (0, k)

/-- The second spatial derivative of a joint field, evaluated on spatial
directions. -/
noncomputable def spatialSecondDerivativeEval
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x h k : Vec 2) : Vec 2 :=
  iteratedFDeriv ℝ 2 (Function.uncurry b) (t, x) (HigherVariation.spatialDirections h k)

/-- The second spatial derivative evaluation is the iterated derivative of
the full time-space field restricted to spatial directions. -/
theorem spatialSecondDerivativeEval_eq_joint
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x h k : Vec 2) :
    spatialSecondDerivativeEval b t x h k =
      fderiv ℝ (fderiv ℝ (Function.uncurry b)) (t, x) (0, h) (0, k) := by
  rw [spatialSecondDerivativeEval, iteratedFDeriv_two_apply]
  simp [HigherVariation.spatialDirections]

/-- The second spatial derivative of the field is the base-point derivative of
its spatial Jacobian, evaluated on the second direction. -/
theorem spatialSecondDerivativeEval_eq_spatialJacobianFDeriv_apply
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x h k : Vec 2) :
    spatialSecondDerivativeEval b t x h k =
      fderiv ℝ (fun z => jointSpatialFDeriv b t z k) x h := by
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let g : Vec 2 → ℝ × Vec 2 := fun z => (t, z)
  let incl : Vec 2 →L[ℝ] (ℝ × Vec 2) := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  let R : (ℝ × Vec 2 →L[ℝ] Vec 2) →L[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
    (ContinuousLinearMap.apply ℝ (Vec 2 →L[ℝ] Vec 2) incl) ∘L
      (ContinuousLinearMap.compL ℝ (Vec 2) (ℝ × Vec 2) (Vec 2))
  let H : Vec 2 → (ℝ × Vec 2 →L[ℝ] Vec 2) := fun z => fderiv ℝ F (g z)
  have hg : Differentiable ℝ g := by fun_prop
  have hF : Differentiable ℝ F := hb.smooth.differentiable (by norm_num)
  have hFderiv : Differentiable ℝ (fderiv ℝ F) :=
    (hb.smooth.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hslice : (fun z => b t z) = F ∘ g := by
    funext z
    rfl
  have hfirst : ∀ z, fderiv ℝ (fun y => b t y) z =
      (fderiv ℝ F (g z)).comp incl := by
    intro z
    rw [hslice, fderiv_comp z (hF (g z)) (hg z)]
    have hginr : fderiv ℝ g z = incl := by
      exact (hasFDerivAt_prodMk_right t z).fderiv
    rw [hginr]
  have hmap : (fun z => fderiv ℝ (fun y => b t y) z) = R ∘ H := by
    funext z
    rw [hfirst]
    simp [R, H, ContinuousLinearMap.compL_apply, incl]
  have hH : HasFDerivAt H
      ((fderiv ℝ (fderiv ℝ F) (g x)).comp incl) x := by
    have hcomp := HasFDerivAt.comp x
      (hFderiv (g x)).hasFDerivAt (hg x).hasFDerivAt
    have hginr : fderiv ℝ g x = incl := by
      exact (hasFDerivAt_prodMk_right t x).fderiv
    rw [hginr] at hcomp
    change HasFDerivAt (fun z => fderiv ℝ F (g z)) _ x
    exact hcomp
  have hsecondMap : fderiv ℝ (fun z => fderiv ℝ (fun y => b t y) z) x =
      R.comp ((fderiv ℝ (fderiv ℝ F) (g x)).comp incl) := by
    rw [hmap]
    exact (HasFDerivAt.comp x R.hasFDerivAt hH).fderiv
  have hEval : fderiv ℝ (fun z => jointSpatialFDeriv b t z k) x h =
      (fderiv ℝ (fun z => fderiv ℝ (fun y => b t y) z) x h) k := by
    let Ev : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] Vec 2 :=
      (ContinuousLinearMap.apply ℝ (Vec 2)) k
    have hA : Differentiable ℝ (fun z => fderiv ℝ (fun y => b t y) z) := by
      have hgSlice : ContDiff ℝ ∞ (fun y => b t y) := by
        exact hb.smooth.comp (contDiff_const.prodMk contDiff_id)
      exact (hgSlice.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hcomp := HasFDerivAt.comp x Ev.hasFDerivAt (hA x).hasFDerivAt
    have hsliceA : (fun z => jointSpatialFDeriv b t z k) =
        Ev ∘ (fun z => fderiv ℝ (fun y => b t y) z) := by
      funext z
      rw [jointSpatialFDeriv_eq_slice hb t z]
      rfl
    rw [hsliceA]
    have hderiv := hcomp.fderiv
    simpa [Ev, ContinuousLinearMap.comp_apply] using congrArg (fun L => L h) hderiv
  rw [spatialSecondDerivativeEval_eq_joint, hEval, hsecondMap]
  simp [F, R, g, ContinuousLinearMap.compL_apply, incl, ContinuousLinearMap.comp_apply]

/-- The second spatial derivative evaluation is symmetric in its directions. -/
theorem spatialSecondDerivativeEval_comm
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x h k : Vec 2) :
    spatialSecondDerivativeEval b t x h k = spatialSecondDerivativeEval b t x k h := by
  rw [spatialSecondDerivativeEval_eq_joint, spatialSecondDerivativeEval_eq_joint]
  let f : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  have hf : Differentiable ℝ f := hb.smooth.differentiable (by norm_num)
  have hD : ∀ y, HasFDerivAt f (fderiv ℝ f y) y := fun y => (hf y).hasFDerivAt
  have hD2 : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hb.smooth.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD2x : HasFDerivAt (fun y => fderiv ℝ f y)
      (fderiv ℝ (fun y => fderiv ℝ f y) (t, x)) (t, x) :=
    (hD2 (t, x)).hasFDerivAt
  exact second_derivative_symmetric hD hD2x (0, h) (0, k)

/-- The second spatial derivative evaluation is bilinear in its directions. -/
theorem spatialSecondDerivativeEval_add_left
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x h₁ h₂ k : Vec 2) :
    spatialSecondDerivativeEval b t x (h₁ + h₂) k =
      spatialSecondDerivativeEval b t x h₁ k +
        spatialSecondDerivativeEval b t x h₂ k := by
  rw [spatialSecondDerivativeEval_eq_joint, spatialSecondDerivativeEval_eq_joint,
    spatialSecondDerivativeEval_eq_joint]
  let D := fderiv ℝ (fderiv ℝ (Function.uncurry b)) (t, x)
  have hpair : ((0 : ℝ), h₁ + h₂) = (0, h₁) + (0, h₂) := by ext <;> simp
  calc
    D (0, h₁ + h₂) (0, k) = D ((0, h₁) + (0, h₂)) (0, k) :=
      congrArg (fun q => D q (0, k)) hpair
    _ = D (0, h₁) (0, k) + D (0, h₂) (0, k) := by
      rw [map_add]
      rfl

/-- The second spatial derivative evaluation is linear in its second direction. -/
theorem spatialSecondDerivativeEval_add_right
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x h k₁ k₂ : Vec 2) :
    spatialSecondDerivativeEval b t x h (k₁ + k₂) =
      spatialSecondDerivativeEval b t x h k₁ +
        spatialSecondDerivativeEval b t x h k₂ := by
  rw [spatialSecondDerivativeEval_eq_joint, spatialSecondDerivativeEval_eq_joint,
    spatialSecondDerivativeEval_eq_joint]
  let D := fderiv ℝ (fderiv ℝ (Function.uncurry b)) (t, x)
  have hpair : ((0 : ℝ), k₁ + k₂) = (0, k₁) + (0, k₂) := by ext <;> simp
  calc
    D (0, h) (0, k₁ + k₂) = D (0, h) ((0, k₁) + (0, k₂)) :=
      congrArg (D (0, h)) hpair
    _ = D (0, h) (0, k₁) + D (0, h) (0, k₂) := by
      rw [map_add]

/-- The second spatial derivative evaluation is homogeneous in its first
direction. -/
theorem spatialSecondDerivativeEval_smul_left
    (b : ℝ → Vec 2 → Vec 2) (t c : ℝ) (x h k : Vec 2) :
    spatialSecondDerivativeEval b t x (c • h) k =
      c • spatialSecondDerivativeEval b t x h k := by
  rw [spatialSecondDerivativeEval_eq_joint, spatialSecondDerivativeEval_eq_joint]
  let D := fderiv ℝ (fderiv ℝ (Function.uncurry b)) (t, x)
  have hpair : ((0 : ℝ), c • h) = c • (0, h) := by ext <;> simp
  calc
    D (0, c • h) (0, k) = D (c • (0, h)) (0, k) :=
      congrArg (fun q => D q (0, k)) hpair
    _ = c • (D (0, h) (0, k)) := by rw [map_smul]; simp [D]

/-- The second spatial derivative evaluation is homogeneous in its second
direction. -/
theorem spatialSecondDerivativeEval_smul_right
    (b : ℝ → Vec 2 → Vec 2) (t c : ℝ) (x h k : Vec 2) :
    spatialSecondDerivativeEval b t x h (c • k) =
      c • spatialSecondDerivativeEval b t x h k := by
  rw [spatialSecondDerivativeEval_eq_joint, spatialSecondDerivativeEval_eq_joint]
  let D := fderiv ℝ (fderiv ℝ (Function.uncurry b)) (t, x)
  have hpair : ((0 : ℝ), c • k) = c • (0, k) := by ext <;> simp
  calc
    D (0, h) (0, c • k) = D (0, h) (c • (0, k)) :=
      congrArg (D (0, h)) hpair
    _ = c • (D (0, h) (0, k)) := by rw [map_smul]

/-- Periodicity gives a uniform bilinear operator bound for the second spatial
derivative of the field. -/
theorem exists_global_spatialSecondDerivativeEval_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x h k,
      ‖spatialSecondDerivativeEval b t x h k‖ ≤ C * ‖h‖ * ‖k‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_global_iteratedFDeriv_bound hb 2
  refine ⟨C, hC₀, ?_⟩
  intro t x h k
  have hprod : (∏ i : Fin 2, ‖HigherVariation.spatialDirections h k i‖) = ‖h‖ * ‖k‖ := by
    simp [HigherVariation.spatialDirections, Fin.prod_univ_succ]
  calc
    ‖spatialSecondDerivativeEval b t x h k‖ ≤
        ‖iteratedFDeriv ℝ 2 (Function.uncurry b) (t, x)‖ *
          ∏ i : Fin 2, ‖HigherVariation.spatialDirections h k i‖ := by
      exact (iteratedFDeriv ℝ 2 (Function.uncurry b) (t, x)).le_opNorm _
    _ ≤ C * (‖h‖ * ‖k‖) := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right (hC (t, x)) (by positivity)
    _ = C * ‖h‖ * ‖k‖ := by ring

/-- A continuous affine linear system with uniformly bounded linear part has
a unique global flow. -/
theorem existsUnique_forcedLinearSystemFlow
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (F : ℝ → Vec 2)
    (hA : Continuous A) (hF : Continuous F)
    (M : ℝ) (hM : ∀ t, ‖A t‖ ≤ M) :
    ∃! W : ℝ → Vec 2 → ℝ → Vec 2,
      AVenhance.IsFlow (fun t w => A t w + F t) W := by
  have hfield : Continuous (fun p : ℝ × Vec 2 => A p.1 p.2 + F p.1) := by
    fun_prop
  have hLip : ∃ L : ℝ, ∀ t u v,
      ‖(A t u + F t) - (A t v + F t)‖ ≤ L * ‖u - v‖ := by
    refine ⟨M, ?_⟩
    intro t u v
    have hsub : (A t u + F t) - (A t v + F t) = A t (u - v) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    calc
      ‖(A t u + F t) - (A t v + F t)‖ = ‖A t (u - v)‖ := by rw [hsub]
      _ ≤ ‖A t‖ * ‖u - v‖ := (A t).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)
  exact existsUnique_flow (fun t w => A t w + F t) hfield hLip

/-- The second variational equation along a smooth flow has a global solution.
Its forcing is the second spatial derivative of the field applied to the two
first variational solutions. This constructs the candidate second variation;
the identification with the derivative of the first variation is a separate
regularity step. -/
theorem existsUnique_flow_secondVariationCandidate
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k : Vec 2) :
    ∃! W : ℝ → Vec 2 → ℝ → Vec 2,
      AVenhance.IsFlow
        (fun t w => jointSpatialFDeriv b t (X t x s) w +
          spatialSecondDerivativeEval b t (X t x s) (V t h s) (V t k s)) W := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun t => jointSpatialFDeriv b t (X t x s)
  let F : ℝ → Vec 2 := fun t =>
    spatialSecondDerivativeEval b t (X t x s) (V t h s) (V t k s)
  have hA : Continuous A := by
    exact (jointSpatialFDeriv_continuous hb).comp
      (continuous_id.prodMk (flow_continuous_time b hX x s))
  have hVh : Continuous (fun t => V t h s) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hV.2 h s t).continuousAt
  have hVk : Continuous (fun t => V t k s) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hV.2 k s t).continuousAt
  have hF : Continuous F := by
    have hcurve : Continuous (fun t : ℝ => (t, X t x s)) :=
      continuous_id.prodMk (flow_continuous_time b hX x s)
    have hD : Continuous (fun t : ℝ =>
        iteratedFDeriv ℝ 2 (Function.uncurry b) (t, X t x s)) := by
      exact (hb.smooth.continuous_iteratedFDeriv (m := 2) (by simp)).comp hcurve
    have hdirs : Continuous (fun t : ℝ =>
        HigherVariation.spatialDirections (V t h s) (V t k s)) := by
      apply continuous_pi
      intro i
      fin_cases i
      · simpa [HigherVariation.spatialDirections] using (continuous_const.prodMk hVh)
      · simpa [HigherVariation.spatialDirections] using (continuous_const.prodMk hVk)
    have hEval : Continuous
        (fun z : _root_.ContinuousMultilinearMap ℝ
          (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) × (Fin 2 → ℝ × Vec 2) =>
            z.1 z.2) := by
      fun_prop
    change Continuous (fun t =>
      iteratedFDeriv ℝ 2 (Function.uncurry b) (t, X t x s)
        (HigherVariation.spatialDirections (V t h s) (V t k s)))
    have hcomp := hEval.comp (hD.prodMk hdirs)
    convert hcomp using 1
    funext t
    rfl
  have hbound : ∀ t, ‖A t‖ ≤ M := by
    intro t
    exact hM t (X t x s)
  simpa [A, F] using
    existsUnique_forcedLinearSystemFlow A F hA hF M hbound

/-- The selected global flow solving the second variational equation. -/
noncomputable def flowSecondVariation
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k : Vec 2) : ℝ → Vec 2 → ℝ → Vec 2 :=
  Classical.choose
    (existsUnique_flow_secondVariationCandidate hb hX x s hV h k)

/-- The selected second variation solves its defining affine system. -/
theorem flowSecondVariation_isFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k : Vec 2) :
    AVenhance.IsFlow
      (fun t w => jointSpatialFDeriv b t (X t x s) w +
        spatialSecondDerivativeEval b t (X t x s) (V t h s) (V t k s))
      (flowSecondVariation hb hX x s hV h k) := by
  exact (Classical.choose_spec
    (existsUnique_flow_secondVariationCandidate hb hX x s hV h k)).1

theorem HigherVariation.variationalFlow_addDirection
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h₁ h₂ : Vec 2) :
    V t (h₁ + h₂) s = V t h₁ s + V t h₂ s := by
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨J, hJ⟩ := exists_flow_variationalContinuousLinearMap
    (fun r => jointSpatialFDeriv b r (X r x s)) M
    (fun r => hM r (X r x s)) hV t s
  calc
    V t (h₁ + h₂) s = J (h₁ + h₂) := (hJ (h₁ + h₂)).symm
    _ = J h₁ + J h₂ := map_add J h₁ h₂
    _ = V t h₁ s + V t h₂ s := by rw [hJ h₁, hJ h₂]

theorem HigherVariation.variationalFlow_smulDirection
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t c : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h : Vec 2) :
    V t (c • h) s = c • V t h s := by
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨J, hJ⟩ := exists_flow_variationalContinuousLinearMap
    (fun r => jointSpatialFDeriv b r (X r x s)) M
    (fun r => hM r (X r x s)) hV t s
  calc
    V t (c • h) s = J (c • h) := (hJ (c • h)).symm
    _ = c • J h := map_smul J c h
    _ = c • V t h s := by rw [hJ h]

/-- The zero-initial-data second variational solution is additive in its first
direction. -/
theorem flowSecondVariation_add_left
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h₁ h₂ k : Vec 2) (t : ℝ) :
    flowSecondVariation hb hX x s hV (h₁ + h₂) k t 0 s =
      flowSecondVariation hb hX x s hV h₁ k t 0 s +
        flowSecondVariation hb hX x s hV h₂ k t 0 s := by
  let W12 := flowSecondVariation hb hX x s hV (h₁ + h₂) k
  let W1 := flowSecondVariation hb hX x s hV h₁ k
  let W2 := flowSecondVariation hb hX x s hV h₂ k
  have hW12 := flowSecondVariation_isFlow hb hX x s hV (h₁ + h₂) k
  have hW1 := flowSecondVariation_isFlow hb hX x s hV h₁ k
  have hW2 := flowSecondVariation_isFlow hb hX x s hV h₂ k
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let F12 : ℝ → Vec 2 := fun r =>
    spatialSecondDerivativeEval b r (X r x s) (V r (h₁ + h₂) s) (V r k s)
  let F1 : ℝ → Vec 2 := fun r =>
    spatialSecondDerivativeEval b r (X r x s) (V r h₁ s) (V r k s)
  let F2 : ℝ → Vec 2 := fun r =>
    spatialSecondDerivativeEval b r (X r x s) (V r h₂ s) (V r k s)
  have hF : ∀ r, F12 r = F1 r + F2 r := by
    intro r
    dsimp [F12, F1, F2]
    rw [HigherVariation.variationalFlow_addDirection hb x s r hV h₁ h₂]
    exact spatialSecondDerivativeEval_add_left b r (X r x s)
      (V r h₁ s) (V r h₂ s) (V r k s)
  have hLip : ∀ r u v,
      ‖(A r u + F12 r) - (A r v + F12 r)‖ ≤ M * ‖u - v‖ := by
    intro r u v
    have hsub : (A r u + F12 r) - (A r v + F12 r) = A r (u - v) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - v)‖ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM r (X r x s)) (norm_nonneg _)
  have hsumDer (r : ℝ) :
      HasDerivAt ((fun q => W1 q 0 s) + (fun q => W2 q 0 s))
        (A r (W1 r 0 s + W2 r 0 s) + F12 r) r := by
    have h := (hW1.2 0 s r).add (hW2.2 0 s r)
    simpa [W1, W2, A, F1, F2, F12, map_add, hF r,
      add_assoc, add_comm, add_left_comm] using h
  have hstart :
      ((fun q => W1 q 0 s) + (fun q => W2 q 0 s)) s = W12 s 0 s := by
    simp [W1, W2, W12, hW1.1, hW2.1, hW12.1]
  have hcurves := integralCurve_unique
    (fun r w => A r w + F12 r) hLip hsumDer (fun r => hW12.2 0 s r) hstart
  exact (congrFun hcurves t).symm

/-- The zero-initial-data second variational solution is symmetric in its
directions. -/
theorem flowSecondVariation_comm
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k : Vec 2) (t : ℝ) :
    flowSecondVariation hb hX x s hV h k t 0 s =
      flowSecondVariation hb hX x s hV k h t 0 s := by
  let W₁ := flowSecondVariation hb hX x s hV h k
  let W₂ := flowSecondVariation hb hX x s hV k h
  have hW₁ := flowSecondVariation_isFlow hb hX x s hV h k
  have hW₂ := flowSecondVariation_isFlow hb hX x s hV k h
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let F : ℝ → Vec 2 := fun r =>
    spatialSecondDerivativeEval b r (X r x s) (V r h s) (V r k s)
  have hLip : ∀ r u v,
      ‖(A r u + F r) - (A r v + F r)‖ ≤ M * ‖u - v‖ := by
    intro r u v
    have hsub : (A r u + F r) - (A r v + F r) = A r (u - v) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - v)‖ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM r (X r x s)) (norm_nonneg _)
  have hderiv₂ (r : ℝ) :
      HasDerivAt (fun q => W₂ q 0 s) (A r (W₂ r 0 s) + F r) r := by
    simpa [W₂, A, F, spatialSecondDerivativeEval_comm hb r (X r x s)] using
      hW₂.2 0 s r
  have hstart : W₁ s 0 s = W₂ s 0 s := by
    simp [W₁, W₂, hW₁.1, hW₂.1]
  have hcurves := integralCurve_unique
    (fun r w => A r w + F r) hLip (fun r => hW₁.2 0 s r) hderiv₂ hstart
  exact congrFun hcurves t

/-- The zero-initial-data second variational solution is additive in its
second direction. -/
theorem flowSecondVariation_add_right
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k₁ k₂ : Vec 2) (t : ℝ) :
    flowSecondVariation hb hX x s hV h (k₁ + k₂) t 0 s =
      flowSecondVariation hb hX x s hV h k₁ t 0 s +
        flowSecondVariation hb hX x s hV h k₂ t 0 s := by
  calc
    flowSecondVariation hb hX x s hV h (k₁ + k₂) t 0 s =
        flowSecondVariation hb hX x s hV (k₁ + k₂) h t 0 s :=
      flowSecondVariation_comm hb hX x s hV h (k₁ + k₂) t
    _ = flowSecondVariation hb hX x s hV k₁ h t 0 s +
          flowSecondVariation hb hX x s hV k₂ h t 0 s :=
      flowSecondVariation_add_left hb hX x s hV k₁ k₂ h t
    _ = flowSecondVariation hb hX x s hV h k₁ t 0 s +
          flowSecondVariation hb hX x s hV h k₂ t 0 s := by
      rw [(flowSecondVariation_comm hb hX x s hV h k₁ t).symm,
        (flowSecondVariation_comm hb hX x s hV h k₂ t).symm]

/-- The zero-initial-data second variational solution is homogeneous in its
first direction. -/
theorem flowSecondVariation_smul_left
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s c : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k : Vec 2) (t : ℝ) :
    flowSecondVariation hb hX x s hV (c • h) k t 0 s =
      c • flowSecondVariation hb hX x s hV h k t 0 s := by
  let Wc := flowSecondVariation hb hX x s hV (c • h) k
  let W := flowSecondVariation hb hX x s hV h k
  have hWc := flowSecondVariation_isFlow hb hX x s hV (c • h) k
  have hW := flowSecondVariation_isFlow hb hX x s hV h k
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let Fc : ℝ → Vec 2 := fun r =>
    spatialSecondDerivativeEval b r (X r x s) (V r (c • h) s) (V r k s)
  let F : ℝ → Vec 2 := fun r =>
    spatialSecondDerivativeEval b r (X r x s) (V r h s) (V r k s)
  have hF (r : ℝ) : Fc r = c • F r := by
    dsimp [Fc, F]
    rw [HigherVariation.variationalFlow_smulDirection hb x s r c hV h]
    exact spatialSecondDerivativeEval_smul_left b r c (X r x s)
      (V r h s) (V r k s)
  have hLip : ∀ r u v,
      ‖(A r u + Fc r) - (A r v + Fc r)‖ ≤ M * ‖u - v‖ := by
    intro r u v
    have hsub : (A r u + Fc r) - (A r v + Fc r) = A r (u - v) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - v)‖ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM r (X r x s)) (norm_nonneg _)
  have hscaled (r : ℝ) :
      HasDerivAt (c • (fun q => W q 0 s))
        (A r (c • W r 0 s) + Fc r) r := by
    have h := (hW.2 0 s r).const_smul c
    simpa [W, A, F, Fc, hF r, map_smul, smul_add, add_comm, add_left_comm,
      add_assoc] using h
  have hstart : (c • (fun q => W q 0 s)) s = Wc s 0 s := by
    simp [W, Wc, hW.1, hWc.1]
  have hcurves := integralCurve_unique
    (fun r w => A r w + Fc r) hLip hscaled (fun r => hWc.2 0 s r) hstart
  simpa using (congrFun hcurves t).symm

/-- The zero-initial-data second variational solution is homogeneous in its
second direction. -/
theorem flowSecondVariation_smul_right
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s c : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k : Vec 2) (t : ℝ) :
    flowSecondVariation hb hX x s hV h (c • k) t 0 s =
      c • flowSecondVariation hb hX x s hV h k t 0 s := by
  calc
    flowSecondVariation hb hX x s hV h (c • k) t 0 s =
        flowSecondVariation hb hX x s hV (c • k) h t 0 s :=
      flowSecondVariation_comm hb hX x s hV h (c • k) t
    _ = c • flowSecondVariation hb hX x s hV k h t 0 s :=
      flowSecondVariation_smul_left hb hX x s c hV k h t
    _ = c • flowSecondVariation hb hX x s hV h k t 0 s := by
      rw [(flowSecondVariation_comm hb hX x s hV h k t).symm]

/-- The second variational solution has a uniform bilinear bound on forward
time intervals. -/
theorem flowSecondVariation_bound_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h k,
      ‖flowSecondVariation hb hX x s hV h k t 0 s‖ ≤ K * ‖h‖ * ‖k‖ := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  obtain ⟨C, hC₀, hC⟩ := exists_global_spatialSecondDerivativeEval_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  have hAL : ∀ r u v, ‖A r u - A r v‖ ≤ M * ‖u - v‖ := by
    intro r u v
    calc
      ‖A r u - A r v‖ = ‖A r (u - v)‖ := by rw [map_sub]
      _ ≤ ‖A r‖ * ‖u - v‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM r (X r x s)) (norm_nonneg _)
  let d : ℝ := t - s
  let E : ℝ := Real.exp (M * d)
  let D : ℝ := C * E * E
  let K : ℝ := gronwallBound 0 M D d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hD₀ : 0 ≤ D := mul_nonneg (mul_nonneg hC₀ hE₀) hE₀
  have hK₀ : 0 ≤ K := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hD₀ hM₀
    have h := hmono hd₀
    simpa [K, gronwallBound_x0] using h
  refine ⟨K, hK₀, ?_⟩
  intro h k
  let W := flowSecondVariation hb hX x s hV h k
  have hW := flowSecondVariation_isFlow hb hX x s hV h k
  have hVzero (r : ℝ) : V r 0 s = 0 :=
    linearSystemFlow_zero A M hAL hV s r
  have hVbound (v : Vec 2) (r : ℝ) (hr : r ∈ Ico s t) :
      ‖V r v s‖ ≤ E * ‖v‖ := by
    have hgr := flow_spatial_gronwall (fun q z => A q z) hAL hV v 0 s r
    have hexp : Real.exp (M * |r - s|) ≤ E := by
      apply Real.exp_le_exp.mpr
      calc
        M * |r - s| = M * (r - s) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
        _ ≤ M * d := by
          exact mul_le_mul_of_nonneg_left (by dsimp [d]; linarith [hr.2]) hM₀
    calc
      ‖V r v s‖ = ‖V r v s - V r 0 s‖ := by rw [hVzero r, sub_zero]
      _ ≤ Real.exp (M * |r - s|) * ‖v - 0‖ := hgr
      _ = Real.exp (M * |r - s|) * ‖v‖ := by simp
      _ ≤ E * ‖v‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  let F : ℝ → Vec 2 := fun r =>
    spatialSecondDerivativeEval b r (X r x s) (V r h s) (V r k s)
  let ε : ℝ := D * ‖h‖ * ‖k‖
  have hFbound (r : ℝ) (hr : r ∈ Ico s t) : ‖F r‖ ≤ ε := by
    have hh := hVbound h r hr
    have hk := hVbound k r hr
    calc
      ‖F r‖ ≤ C * ‖V r h s‖ * ‖V r k s‖ := hC r (X r x s) (V r h s) (V r k s)
      _ ≤ C * (E * ‖h‖) * (E * ‖k‖) := by gcongr
      _ = ε := by dsimp [ε, D]; ring
  let f : ℝ → Vec 2 := fun _ => 0
  let g : ℝ → Vec 2 := fun r => W r 0 s
  have hfderiv (r : ℝ) : HasDerivAt f (A r (f r)) r := by
    simpa [f] using (hasDerivAt_const r (0 : Vec 2))
  have hgderiv (r : ℝ) : HasDerivAt g (A r (g r) + F r) r := by
    simpa [g, W, F, A] using hW.2 0 s r
  have hfcont : ContinuousOn f (Icc s t) := continuousOn_const
  have hgcont : ContinuousOn g (Icc s t) :=
    HasDerivAt.continuousOn (fun r _ => hgderiv r)
  have hfwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt f (A r (f r)) (Ici r) r :=
    fun r _ => (hfderiv r).hasDerivWithinAt
  have hgwithin : ∀ r ∈ Ico s t,
      HasDerivWithinAt g (A r (g r) + F r) (Ici r) r :=
    fun r _ => (hgderiv r).hasDerivWithinAt
  have hfbound : ∀ r ∈ Ico s t, dist (A r (f r)) (A r (f r)) ≤ (0 : ℝ) := by
    intro r hr
    simp
  have hgapprox : ∀ r ∈ Ico s t,
      dist (A r (g r) + F r) (A r (g r)) ≤ ε := by
    intro r hr
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hFbound r hr
  let KN : ℝ≥0 := ⟨M, hM₀⟩
  have hAlip : ∀ r, LipschitzWith KN (fun v => A r v) := by
    intro r
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    exact hAL r u v
  have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
    simp [f, g, W, hW.1]
  have hcomp := dist_le_of_approx_trajectories_ODE
    (K := KN) (v := fun r z => A r z) (a := s) (b := t)
    (εf := 0) (εg := ε) (δ := 0)
    hAlip hfcont hfwithin hfbound hgcont hgwithin hgapprox hstart
  have hKcast : (KN : ℝ) = M := rfl
  have hnorm : ‖W t 0 s‖ ≤ gronwallBound 0 M ε d := by
    have h := hcomp t ⟨hst, le_rfl⟩
    simpa only [f, g, dist_eq_norm, hKcast, zero_add, zero_sub, norm_neg, d] using h
  have hscale : gronwallBound 0 M ε d = (‖h‖ * ‖k‖) * K := by
    rw [show ε = (‖h‖ * ‖k‖) * D by dsimp [ε]; ring]
    rw [HigherVariation.gronwallBound_zero_scale_higher M D (‖h‖ * ‖k‖) d]
  calc
    ‖W t 0 s‖ ≤ gronwallBound 0 M ε d := hnorm
    _ = (‖h‖ * ‖k‖) * K := hscale
    _ = K * ‖h‖ * ‖k‖ := by ring

/-- The second variation obeys its bilinear growth bound uniformly over every
target time in a forward interval. -/
theorem flowSecondVariation_bound_all_times_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (M C : ℝ) (hM₀ : 0 ≤ M)
    (hM : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (hC₀ : 0 ≤ C)
    (hC : ∀ t x h k, ‖spatialSecondDerivativeEval b t x h k‖ ≤ C * ‖h‖ * ‖k‖)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V) :
    ∃ K : ℝ, 0 ≤ K ∧
      K = gronwallBound 0 M
        (C * Real.exp (M * (t - s)) * Real.exp (M * (t - s))) (t - s) ∧
      ∀ r, r ∈ Icc s t → ∀ h k,
      ‖flowSecondVariation hb hX x s hV h k r 0 s‖ ≤ K * ‖h‖ * ‖k‖ := by
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun q => jointSpatialFDeriv b q (X q x s)
  have hAL : ∀ q u v, ‖A q u - A q v‖ ≤ M * ‖u - v‖ := by
    intro q u v
    calc
      ‖A q u - A q v‖ = ‖A q (u - v)‖ := by rw [map_sub]
      _ ≤ ‖A q‖ * ‖u - v‖ := (A q).le_opNorm _
      _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
        (hM q (X q x s)) (norm_nonneg _)
  let d : ℝ := t - s
  let E : ℝ := Real.exp (M * d)
  let D : ℝ := C * E * E
  let K : ℝ := gronwallBound 0 M D d
  have hd₀ : 0 ≤ d := by dsimp [d]; linarith
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hD₀ : 0 ≤ D := mul_nonneg (mul_nonneg hC₀ hE₀) hE₀
  have hK₀ : 0 ≤ K := by
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hD₀ hM₀
    have h := hmono hd₀
    simpa [K, gronwallBound_x0] using h
  refine ⟨K, hK₀, ?_, ?_⟩
  · rfl
  · intro r hr h k
    let W := flowSecondVariation hb hX x s hV h k
    have hW := flowSecondVariation_isFlow hb hX x s hV h k
    have hVzero (q : ℝ) : V q 0 s = 0 := linearSystemFlow_zero A M hAL hV s q
    have hVbound (v : Vec 2) (q : ℝ) (hq : q ∈ Ico s t) :
        ‖V q v s‖ ≤ E * ‖v‖ := by
      have hgr := flow_spatial_gronwall (fun q z => A q z) hAL hV v 0 s q
      have hexp : Real.exp (M * |q - s|) ≤ E := by
        apply Real.exp_le_exp.mpr
        calc
          M * |q - s| = M * (q - s) := by
            rw [abs_of_nonneg (sub_nonneg.mpr hq.1)]
          _ ≤ M * d := by
            exact mul_le_mul_of_nonneg_left (by dsimp [d]; linarith [hq.2]) hM₀
      calc
        ‖V q v s‖ = ‖V q v s - V q 0 s‖ := by rw [hVzero q, sub_zero]
        _ ≤ Real.exp (M * |q - s|) * ‖v - 0‖ := hgr
        _ = Real.exp (M * |q - s|) * ‖v‖ := by simp
        _ ≤ E * ‖v‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    let F : ℝ → Vec 2 := fun q =>
      spatialSecondDerivativeEval b q (X q x s) (V q h s) (V q k s)
    let ε : ℝ := D * ‖h‖ * ‖k‖
    have hFbound (q : ℝ) (hq : q ∈ Ico s t) : ‖F q‖ ≤ ε := by
      have hh := hVbound h q hq
      have hk := hVbound k q hq
      calc
        ‖F q‖ ≤ C * ‖V q h s‖ * ‖V q k s‖ := hC q (X q x s) _ _
        _ ≤ C * (E * ‖h‖) * (E * ‖k‖) := by gcongr
        _ = ε := by dsimp [ε, D]; ring
    let f : ℝ → Vec 2 := fun _ => 0
    let g : ℝ → Vec 2 := fun q => W q 0 s
    have hfderiv (q : ℝ) : HasDerivAt f (A q (f q)) q := by
      simpa [f] using (hasDerivAt_const q (0 : Vec 2))
    have hgderiv (q : ℝ) : HasDerivAt g (A q (g q) + F q) q := by
      simpa [g, W, F, A] using hW.2 0 s q
    have hfcont : ContinuousOn f (Icc s t) := continuousOn_const
    have hgcont : ContinuousOn g (Icc s t) :=
      HasDerivAt.continuousOn (fun q _ => hgderiv q)
    have hfwithin : ∀ q ∈ Ico s t,
        HasDerivWithinAt f (A q (f q)) (Ici q) q :=
      fun q _ => (hfderiv q).hasDerivWithinAt
    have hgwithin : ∀ q ∈ Ico s t,
        HasDerivWithinAt g (A q (g q) + F q) (Ici q) q :=
      fun q _ => (hgderiv q).hasDerivWithinAt
    have hfapprox : ∀ q ∈ Ico s t,
        dist (A q (f q)) (A q (f q)) ≤ (0 : ℝ) := by
      intro q hq
      simp
    have hgapprox : ∀ q ∈ Ico s t,
        dist (A q (g q) + F q) (A q (g q)) ≤ ε := by
      intro q hq
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hFbound q hq
    let KN : ℝ≥0 := ⟨M, hM₀⟩
    have hAlip : ∀ q, LipschitzWith KN (fun v => A q v) := by
      intro q
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [dist_eq_norm, dist_eq_norm]
      exact hAL q u v
    have hstart : dist (f s) (g s) ≤ (0 : ℝ) := by
      simp [f, g, W, hW.1]
    have hcomp := dist_le_of_approx_trajectories_ODE
      (K := KN) (v := fun q z => A q z) (a := s) (b := t)
      (εf := 0) (εg := ε) (δ := 0)
      hAlip hfcont hfwithin hfapprox hgcont hgwithin hgapprox hstart
    have hKcast : (KN : ℝ) = M := rfl
    have hdist : ‖W r 0 s‖ ≤ gronwallBound 0 M ε (r - s) := by
      have h := hcomp r hr
      simpa only [f, g, dist_eq_norm, hKcast, zero_add, zero_sub, norm_neg, d] using h
    have htime : r - s ≤ d := by dsimp [d]; linarith [hr.2]
    have hmono := gronwallBound_mono
      (show 0 ≤ (0 : ℝ) by norm_num) hD₀ hM₀
    have hscale : gronwallBound 0 M ε (r - s) =
        (‖h‖ * ‖k‖) * gronwallBound 0 M D (r - s) := by
      rw [show ε = (‖h‖ * ‖k‖) * D by dsimp [ε, D]; ring]
      rw [HigherVariation.gronwallBound_zero_scale_higher M D (‖h‖ * ‖k‖) (r - s)]
    calc
      ‖W r 0 s‖ ≤ gronwallBound 0 M ε (r - s) := hdist
      _ = (‖h‖ * ‖k‖) * gronwallBound 0 M D (r - s) := hscale
      _ ≤ (‖h‖ * ‖k‖) * K := by
        dsimp [K]
        exact mul_le_mul_of_nonneg_left (hmono htime)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = K * ‖h‖ * ‖k‖ := by ring

/-- On a forward interval, the second variational solution is represented by a
continuous bilinear map in its two directions. -/
theorem exists_flowSecondVariationContinuousBilinear_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ) (hst : s ≤ t)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V) :
    ∃ B : Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2, ∀ h k,
      B h k = flowSecondVariation hb hX x s hV h k t 0 s := by
  obtain ⟨K, hK₀, hK⟩ := flowSecondVariation_bound_of_le hb hX x s t hst hV
  let innerLinear (h : Vec 2) : Vec 2 →ₗ[ℝ] Vec 2 :=
    { toFun := fun k => flowSecondVariation hb hX x s hV h k t 0 s
      map_add' := by
        intro k₁ k₂
        exact flowSecondVariation_add_right hb hX x s hV h k₁ k₂ t
      map_smul' := by
        intro c k
        exact flowSecondVariation_smul_right hb hX x s c hV h k t }
  let innerContinuous (h : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
    (innerLinear h).mkContinuous (K * ‖h‖) (fun k => hK h k)
  let outerLinear : Vec 2 →ₗ[ℝ] Vec 2 →L[ℝ] Vec 2 :=
    { toFun := innerContinuous
      map_add' := by
        intro h₁ h₂
        ext k i
        exact congrArg (fun z : Vec 2 => z i)
          (flowSecondVariation_add_left hb hX x s hV h₁ h₂ k t)
      map_smul' := by
        intro c h
        ext k i
        exact congrArg (fun z : Vec 2 => z i)
          (flowSecondVariation_smul_left hb hX x s c hV h k t) }
  have houterBound (h : Vec 2) : ‖outerLinear h‖ ≤ K * ‖h‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK₀ (norm_nonneg h))
    intro k
    change ‖innerContinuous h k‖ ≤ K * ‖h‖ * ‖k‖
    exact hK h k
  refine ⟨outerLinear.mkContinuous K houterBound, ?_⟩
  intro h k
  rfl

end AVenhance.Infra.Flow
