/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Existence

/-! # Multilinear

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem Multilinear.flowVariation_addDirection3
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t : ℝ)
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

theorem Multilinear.flowVariation_smulDirection3
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s t c : ℝ)
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

/-- The selected third variational solution is additive in the direction that
indexes the derivative of the second variation. -/
theorem flowThirdVariation_add_left
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h₁ h₂ k l : Vec 2) (t : ℝ) :
    flowThirdVariation hb hX x s hV (h₁ + h₂) k l t 0 s =
      flowThirdVariation hb hX x s hV h₁ k l t 0 s +
        flowThirdVariation hb hX x s hV h₂ k l t 0 s := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let W₁₂ := flowThirdVariation hb hX x s hV (h₁ + h₂) k l
  let W₁ := flowThirdVariation hb hX x s hV h₁ k l
  let W₂ := flowThirdVariation hb hX x s hV h₂ k l
  have hW₁₂ := flowThirdVariation_isFlow hb hX x s hV (h₁ + h₂) k l
  have hW₁ := flowThirdVariation_isFlow hb hX x s hV h₁ k l
  have hW₂ := flowThirdVariation_isFlow hb hX x s hV h₂ k l
  let F₁₂ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r (h₁ + h₂) s) (V r k s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV (h₁ + h₂) k r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV (h₁ + h₂) l r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l r 0 s) (V r (h₁ + h₂) s)
  let F₁ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h₁ s) (V r k s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h₁ k r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h₁ l r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l r 0 s) (V r h₁ s)
  let F₂ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h₂ s) (V r k s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h₂ k r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h₂ l r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l r 0 s) (V r h₂ s)
  have hF (r : ℝ) : F₁₂ r = F₁ r + F₂ r := by
    dsimp [F₁₂, F₁, F₂]
    rw [Multilinear.flowVariation_addDirection3 hb x s r hV h₁ h₂]
    rw [spatialThirdDerivativeEval_add_left hb r (X r x s)]
    rw [flowSecondVariation_add_left hb hX x s hV h₁ h₂ k r]
    rw [spatialSecondDerivativeEval_add_left]
    rw [flowSecondVariation_add_left hb hX x s hV h₁ h₂ l r]
    rw [spatialSecondDerivativeEval_add_left]
    rw [spatialSecondDerivativeEval_add_right]
    abel
  have hLip : ∀ r u w, ‖(A r u + F₁₂ r) - (A r w + F₁₂ r)‖ ≤ M * ‖u - w‖ := by
    intro r u w
    have hsub : (A r u + F₁₂ r) - (A r w + F₁₂ r) = A r (u - w) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - w)‖ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  have hsumDer (r : ℝ) :
      HasDerivAt (fun q => W₁ q 0 s + W₂ q 0 s)
        (A r (W₁ r 0 s + W₂ r 0 s) + F₁₂ r) r := by
    have h := (hW₁.2 0 s r).add (hW₂.2 0 s r)
    have hder :
        A r (W₁ r 0 s + W₂ r 0 s) + F₁₂ r =
          (A r (W₁ r 0 s) + F₁ r) + (A r (W₂ r 0 s) + F₂ r) := by
      rw [map_add, hF r]
      abel
    rw [hder]
    convert h using 1
    ext q
    dsimp [A, F₁, F₂]
    abel
  have hW₁₂der (r : ℝ) :
      HasDerivAt (fun q => W₁₂ q 0 s) (A r (W₁₂ r 0 s) + F₁₂ r) r := by
    have h := hW₁₂.2 0 s r
    convert h using 1
    funext q
    dsimp [A, F₁₂, W₁₂]
    abel
  have hstart : W₁ s 0 s + W₂ s 0 s = W₁₂ s 0 s := by
    simp [W₁, W₂, W₁₂, hW₁.1, hW₂.1, hW₁₂.1]
  have hcurves := integralCurve_unique
    (fun r w => A r w + F₁₂ r) hLip hsumDer
    hW₁₂der (s := s) hstart
  exact (congrFun hcurves t).symm

/-- The selected third variational solution is additive in its middle direction. -/
theorem flowThirdVariation_add_middle
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k₁ k₂ l : Vec 2) (t : ℝ) :
    flowThirdVariation hb hX x s hV h (k₁ + k₂) l t 0 s =
      flowThirdVariation hb hX x s hV h k₁ l t 0 s +
        flowThirdVariation hb hX x s hV h k₂ l t 0 s := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let W₁₂ := flowThirdVariation hb hX x s hV h (k₁ + k₂) l
  let W₁ := flowThirdVariation hb hX x s hV h k₁ l
  let W₂ := flowThirdVariation hb hX x s hV h k₂ l
  have hW₁₂ := flowThirdVariation_isFlow hb hX x s hV h (k₁ + k₂) l
  have hW₁ := flowThirdVariation_isFlow hb hX x s hV h k₁ l
  have hW₂ := flowThirdVariation_isFlow hb hX x s hV h k₂ l
  let F₁₂ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r (k₁ + k₂) s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h (k₁ + k₂) r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l r 0 s) (V r (k₁ + k₂) s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV (k₁ + k₂) l r 0 s) (V r h s)
  let F₁ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k₁ s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k₁ r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l r 0 s) (V r k₁ s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k₁ l r 0 s) (V r h s)
  let F₂ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k₂ s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k₂ r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l r 0 s) (V r k₂ s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k₂ l r 0 s) (V r h s)
  have hF (r : ℝ) : F₁₂ r = F₁ r + F₂ r := by
    dsimp [F₁₂, F₁, F₂]
    rw [Multilinear.flowVariation_addDirection3 hb x s r hV k₁ k₂]
    rw [spatialThirdDerivativeEval_add_middle hb r (X r x s)]
    rw [flowSecondVariation_add_right hb hX x s hV h k₁ k₂ r]
    rw [spatialSecondDerivativeEval_add_left]
    rw [spatialSecondDerivativeEval_add_right]
    rw [flowSecondVariation_add_left hb hX x s hV k₁ k₂ l r]
    rw [spatialSecondDerivativeEval_add_left]
    abel
  have hLip : ∀ r u w,
      ‖(A r u + F₁₂ r) - (A r w + F₁₂ r)‖ ≤ M * ‖u - w‖ := by
    intro r u w
    have hsub : (A r u + F₁₂ r) - (A r w + F₁₂ r) = A r (u - w) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - w)‖ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  have hsumDer (r : ℝ) :
      HasDerivAt (fun q => W₁ q 0 s + W₂ q 0 s)
        (A r (W₁ r 0 s + W₂ r 0 s) + F₁₂ r) r := by
    have h := (hW₁.2 0 s r).add (hW₂.2 0 s r)
    have hder :
        A r (W₁ r 0 s + W₂ r 0 s) + F₁₂ r =
          (A r (W₁ r 0 s) + F₁ r) + (A r (W₂ r 0 s) + F₂ r) := by
      rw [map_add, hF r]
      abel
    rw [hder]
    convert h using 1
    ext q
    dsimp [A, F₁, F₂]
    abel
  have hW₁₂der (r : ℝ) :
      HasDerivAt (fun q => W₁₂ q 0 s) (A r (W₁₂ r 0 s) + F₁₂ r) r := by
    have h := hW₁₂.2 0 s r
    convert h using 1
    funext q
    dsimp [A, F₁₂, W₁₂]
    abel
  have hstart : W₁ s 0 s + W₂ s 0 s = W₁₂ s 0 s := by
    simp [W₁, W₂, W₁₂, hW₁.1, hW₂.1, hW₁₂.1]
  have hcurves := integralCurve_unique
    (fun r w => A r w + F₁₂ r) hLip hsumDer hW₁₂der (s := s) hstart
  exact (congrFun hcurves t).symm

/-- The selected third variational solution is additive in its right direction. -/
theorem flowThirdVariation_add_right
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k l₁ l₂ : Vec 2) (t : ℝ) :
    flowThirdVariation hb hX x s hV h k (l₁ + l₂) t 0 s =
      flowThirdVariation hb hX x s hV h k l₁ t 0 s +
        flowThirdVariation hb hX x s hV h k l₂ t 0 s := by
  obtain ⟨M, hM₀, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let W₁₂ := flowThirdVariation hb hX x s hV h k (l₁ + l₂)
  let W₁ := flowThirdVariation hb hX x s hV h k l₁
  let W₂ := flowThirdVariation hb hX x s hV h k l₂
  have hW₁₂ := flowThirdVariation_isFlow hb hX x s hV h k (l₁ + l₂)
  have hW₁ := flowThirdVariation_isFlow hb hX x s hV h k l₁
  have hW₂ := flowThirdVariation_isFlow hb hX x s hV h k l₂
  let F₁₂ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k s) (V r (l₁ + l₂) s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k r 0 s) (V r (l₁ + l₂) s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h (l₁ + l₂) r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k (l₁ + l₂) r 0 s) (V r h s)
  let F₁ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k s) (V r l₁ s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k r 0 s) (V r l₁ s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l₁ r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l₁ r 0 s) (V r h s)
  let F₂ : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k s) (V r l₂ s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k r 0 s) (V r l₂ s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l₂ r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l₂ r 0 s) (V r h s)
  have hF (r : ℝ) : F₁₂ r = F₁ r + F₂ r := by
    dsimp [F₁₂, F₁, F₂]
    rw [Multilinear.flowVariation_addDirection3 hb x s r hV l₁ l₂]
    rw [spatialThirdDerivativeEval_add_right hb r (X r x s)]
    rw [spatialSecondDerivativeEval_add_right]
    rw [flowSecondVariation_add_right hb hX x s hV h l₁ l₂ r]
    rw [spatialSecondDerivativeEval_add_left]
    rw [flowSecondVariation_add_right hb hX x s hV k l₁ l₂ r]
    rw [spatialSecondDerivativeEval_add_left]
    abel
  have hLip : ∀ r u w,
      ‖(A r u + F₁₂ r) - (A r w + F₁₂ r)‖ ≤ M * ‖u - w‖ := by
    intro r u w
    have hsub : (A r u + F₁₂ r) - (A r w + F₁₂ r) = A r (u - w) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - w)‖ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  have hsumDer (r : ℝ) :
      HasDerivAt (fun q => W₁ q 0 s + W₂ q 0 s)
        (A r (W₁ r 0 s + W₂ r 0 s) + F₁₂ r) r := by
    have h := (hW₁.2 0 s r).add (hW₂.2 0 s r)
    have hder :
        A r (W₁ r 0 s + W₂ r 0 s) + F₁₂ r =
          (A r (W₁ r 0 s) + F₁ r) + (A r (W₂ r 0 s) + F₂ r) := by
      rw [map_add, hF r]
      abel
    rw [hder]
    convert h using 1
    ext q
    dsimp [A, F₁, F₂]
    abel
  have hW₁₂der (r : ℝ) :
      HasDerivAt (fun q => W₁₂ q 0 s) (A r (W₁₂ r 0 s) + F₁₂ r) r := by
    have h := hW₁₂.2 0 s r
    convert h using 1
    funext q
    dsimp [A, F₁₂, W₁₂]
    abel
  have hstart : W₁ s 0 s + W₂ s 0 s = W₁₂ s 0 s := by
    simp [W₁, W₂, W₁₂, hW₁.1, hW₂.1, hW₁₂.1]
  have hcurves := integralCurve_unique
    (fun r w => A r w + F₁₂ r) hLip hsumDer hW₁₂der (s := s) hstart
  exact (congrFun hcurves t).symm

/-- The selected third variational solution is homogeneous in the direction
that indexes differentiation of the second variation. -/
theorem flowThirdVariation_smul_left
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s c : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k l : Vec 2) (t : ℝ) :
    flowThirdVariation hb hX x s hV (c • h) k l t 0 s =
      c • flowThirdVariation hb hX x s hV h k l t 0 s := by
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let Wc := flowThirdVariation hb hX x s hV (c • h) k l
  let W := flowThirdVariation hb hX x s hV h k l
  have hWc := flowThirdVariation_isFlow hb hX x s hV (c • h) k l
  have hW := flowThirdVariation_isFlow hb hX x s hV h k l
  let Fc : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r (c • h) s) (V r k s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV (c • h) k r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV (c • h) l r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l r 0 s) (V r (c • h) s)
  let F : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l r 0 s) (V r h s)
  have hF (r : ℝ) : Fc r = c • F r := by
    dsimp [Fc, F]
    rw [Multilinear.flowVariation_smulDirection3 hb x s r c hV h]
    rw [spatialThirdDerivativeEval_smul_left hb r (X r x s) c]
    rw [flowSecondVariation_smul_left hb hX x s c hV h k r]
    rw [spatialSecondDerivativeEval_smul_left]
    rw [flowSecondVariation_smul_left hb hX x s c hV h l r]
    rw [spatialSecondDerivativeEval_smul_left]
    rw [spatialSecondDerivativeEval_smul_right]
    simp only [smul_add]
  have hLip : ∀ r u w, ‖(A r u + Fc r) - (A r w + Fc r)‖ ≤ M * ‖u - w‖ := by
    intro r u w
    have hsub : (A r u + Fc r) - (A r w + Fc r) = A r (u - w) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - w)‖ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  have hscaled (r : ℝ) :
      HasDerivAt (c • (fun q => W q 0 s))
        (A r (c • W r 0 s) + Fc r) r := by
    have h := (hW.2 0 s r).const_smul c
    have hder : A r (c • W r 0 s) + Fc r =
        c • (A r (W r 0 s) + F r) := by
      rw [map_smul, hF r]
      simp only [smul_add]
    rw [hder]
    convert h using 1
    ext q
    dsimp [W, A, F]
    abel_nf
  have hstart : (c • (fun q => W q 0 s)) s = Wc s 0 s := by
    simp [W, Wc, hW.1, hWc.1]
  have hWcder (r : ℝ) :
      HasDerivAt (fun q => Wc q 0 s) (A r (Wc r 0 s) + Fc r) r := by
    have h := hWc.2 0 s r
    convert h using 1
    funext q
    dsimp [A, Fc, Wc]
    abel
  have hcurves := integralCurve_unique
    (fun r w => A r w + Fc r) hLip hscaled hWcder hstart
  simpa using (congrFun hcurves t).symm

/-- The selected third variational solution is homogeneous in its middle direction. -/
theorem flowThirdVariation_smul_middle
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s c : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k l : Vec 2) (t : ℝ) :
    flowThirdVariation hb hX x s hV h (c • k) l t 0 s =
      c • flowThirdVariation hb hX x s hV h k l t 0 s := by
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let Wc := flowThirdVariation hb hX x s hV h (c • k) l
  let W := flowThirdVariation hb hX x s hV h k l
  have hWc := flowThirdVariation_isFlow hb hX x s hV h (c • k) l
  have hW := flowThirdVariation_isFlow hb hX x s hV h k l
  let Fc : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r (c • k) s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h (c • k) r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l r 0 s) (V r (c • k) s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV (c • k) l r 0 s) (V r h s)
  let F : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l r 0 s) (V r h s)
  have hF (r : ℝ) : Fc r = c • F r := by
    dsimp [Fc, F]
    rw [Multilinear.flowVariation_smulDirection3 hb x s r c hV k]
    rw [spatialThirdDerivativeEval_smul_middle hb r (X r x s) c]
    rw [flowSecondVariation_smul_right hb hX x s c hV h k r]
    rw [spatialSecondDerivativeEval_smul_left]
    rw [spatialSecondDerivativeEval_smul_right]
    rw [flowSecondVariation_smul_left hb hX x s c hV k l r]
    rw [spatialSecondDerivativeEval_smul_left]
    simp only [smul_add]
  have hLip : ∀ r u w,
      ‖(A r u + Fc r) - (A r w + Fc r)‖ ≤ M * ‖u - w‖ := by
    intro r u w
    have hsub : (A r u + Fc r) - (A r w + Fc r) = A r (u - w) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - w)‖ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  have hscaled (r : ℝ) :
      HasDerivAt (c • (fun q => W q 0 s))
        (A r (c • W r 0 s) + Fc r) r := by
    have h := (hW.2 0 s r).const_smul c
    have hder : A r (c • W r 0 s) + Fc r =
        c • (A r (W r 0 s) + F r) := by
      rw [map_smul, hF r]
      simp only [smul_add]
    rw [hder]
    convert h using 1
    ext q
    dsimp [W, A, F]
    abel_nf
  have hstart : (c • (fun q => W q 0 s)) s = Wc s 0 s := by
    simp [W, Wc, hW.1, hWc.1]
  have hWcder (r : ℝ) :
      HasDerivAt (fun q => Wc q 0 s) (A r (Wc r 0 s) + Fc r) r := by
    have h := hWc.2 0 s r
    convert h using 1
    funext q
    dsimp [A, Fc, Wc]
    abel
  have hcurves := integralCurve_unique
    (fun r w => A r w + Fc r) hLip hscaled hWcder hstart
  simpa using (congrFun hcurves t).symm

/-- The selected third variational solution is homogeneous in its right direction. -/
theorem flowThirdVariation_smul_right
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {V : ℝ → Vec 2 → ℝ → Vec 2} (x : Vec 2) (s c : ℝ)
    (hV : AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V)
    (h k l : Vec 2) (t : ℝ) :
    flowThirdVariation hb hX x s hV h k (c • l) t 0 s =
      c • flowThirdVariation hb hX x s hV h k l t 0 s := by
  obtain ⟨M, _, hM⟩ := exists_global_jointSpatialFDeriv_bound hb
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let Wc := flowThirdVariation hb hX x s hV h k (c • l)
  let W := flowThirdVariation hb hX x s hV h k l
  have hWc := flowThirdVariation_isFlow hb hX x s hV h k (c • l)
  have hW := flowThirdVariation_isFlow hb hX x s hV h k l
  let Fc : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k s) (V r (c • l) s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k r 0 s) (V r (c • l) s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h (c • l) r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k (c • l) r 0 s) (V r h s)
  let F : ℝ → Vec 2 := fun r =>
    spatialThirdDerivativeEval b r (X r x s)
        (V r h s) (V r k s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h k r 0 s) (V r l s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV h l r 0 s) (V r k s) +
      spatialSecondDerivativeEval b r (X r x s)
        (flowSecondVariation hb hX x s hV k l r 0 s) (V r h s)
  have hF (r : ℝ) : Fc r = c • F r := by
    dsimp [Fc, F]
    rw [Multilinear.flowVariation_smulDirection3 hb x s r c hV l]
    rw [spatialThirdDerivativeEval_smul_right hb r (X r x s) c]
    rw [spatialSecondDerivativeEval_smul_right]
    rw [flowSecondVariation_smul_right hb hX x s c hV h l r]
    rw [spatialSecondDerivativeEval_smul_left]
    rw [flowSecondVariation_smul_right hb hX x s c hV k l r]
    rw [spatialSecondDerivativeEval_smul_left]
    simp only [smul_add]
  have hLip : ∀ r u w,
      ‖(A r u + Fc r) - (A r w + Fc r)‖ ≤ M * ‖u - w‖ := by
    intro r u w
    have hsub : (A r u + Fc r) - (A r w + Fc r) = A r (u - w) := by
      rw [add_sub_add_right_eq_sub, map_sub]
    rw [hsub]
    calc
      ‖A r (u - w)‖ ≤ ‖A r‖ * ‖u - w‖ := (A r).le_opNorm _
      _ ≤ M * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hM r (X r x s)) (norm_nonneg _)
  have hscaled (r : ℝ) :
      HasDerivAt (c • (fun q => W q 0 s))
        (A r (c • W r 0 s) + Fc r) r := by
    have h := (hW.2 0 s r).const_smul c
    have hder : A r (c • W r 0 s) + Fc r =
        c • (A r (W r 0 s) + F r) := by
      rw [map_smul, hF r]
      simp only [smul_add]
    rw [hder]
    convert h using 1
    ext q
    dsimp [W, A, F]
    abel_nf
  have hstart : (c • (fun q => W q 0 s)) s = Wc s 0 s := by
    simp [W, Wc, hW.1, hWc.1]
  have hWcder (r : ℝ) :
      HasDerivAt (fun q => Wc q 0 s) (A r (Wc r 0 s) + Fc r) r := by
    have h := hWc.2 0 s r
    convert h using 1
    funext q
    dsimp [A, Fc, Wc]
    abel
  have hcurves := integralCurve_unique
    (fun r w => A r w + Fc r) hLip hscaled hWcder hstart
  simpa using (congrFun hcurves t).symm

end AVenhance.Infra.Flow
