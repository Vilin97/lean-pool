/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSupportedSubspace
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

/-!
# Actual coefficient multiplication on supported spatial L²

Bounded continuous coefficient fields act on the closed supported subspace of
ordinary spatial L². Crucially, the operator norm can be bounded using only
coefficient values on the support set. Thus the localized (H3) propagator
bound is retained without any estimate outside its stated region.
-/

noncomputable section


namespace EulerLpSupportedMultiplier

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerLiftedPressure
  EulerLpSupportedSubspace
open scoped BoundedContinuousFunction

variable {α V : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α)
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set α) (hS : MeasurableSet S)

abbrev Field := α →ᵇ (V →L[ℝ] V)

/-- The ordinary full-space L² coefficient multiplier. -/
def full (A : Field (α := α) (V := V)) : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  coefficientOperator A A.continuous.aestronglyMeasurable ‖A‖₊ A.norm_coe_le_norm

/-- Its representative is actual pointwise multiplication. -/
theorem full_ae (A : Field (α := α) (V := V)) (u : Lp V 2 μ) :
    full μ A u =ᵐ[μ] fun x => A x (u x) :=
  coefficientOperator_ae A A.continuous.aestronglyMeasurable ‖A‖₊ A.norm_coe_le_norm u

/-- Coefficient multiplication cannot enlarge support. -/
theorem full_mem (A : Field (α := α) (V := V)) (u : supportedSpace (V := V) μ S hS) :
    full μ A (u : Lp V 2 μ) ∈ supportedSpace μ S hS := by
  apply (mem_supportedSpace_ae μ S hS _).2
  filter_upwards [full_ae μ A (u : Lp V 2 μ),
    (mem_supportedSpace_ae μ S hS (u : Lp V 2 μ)).1 u.property] with x ha hu hs
  rw [ha, hu hs, map_zero]

/-- The genuine coefficient operator on the supported Hilbert space. -/
def operator (A : Field (α := α) (V := V)) :
    supportedSpace (V := V) μ S hS →L[ℝ] supportedSpace (V := V) μ S hS :=
  ((full μ A).comp (supportedSpace μ S hS).subtypeL).codRestrict
    (supportedSpace μ S hS) (full_mem μ S hS A)

/-- The supported operator retains the actual pointwise representative. -/
theorem operator_ae (A : Field (α := α) (V := V)) (u : supportedSpace (V := V) μ S hS) :
    ((operator μ S hS A u : supportedSpace μ S hS) : Lp V 2 μ) =ᵐ[μ]
      fun x => A x ((u : Lp V 2 μ) x) := full_ae μ A u

/-- The actual L² bound only requires control on the set supporting the input. -/
theorem operator_apply_norm_le (A : Field (α := α) (V := V)) (C : ℝ)
    (hbound : ∀ x ∈ S, ‖A x‖ ≤ C) (u : supportedSpace (V := V) μ S hS) :
    ‖operator μ S hS A u‖ ≤ C*‖u‖ := by
  change ‖full μ A (u : Lp V 2 μ)‖ ≤ C*‖(u : Lp V 2 μ)‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [full_ae μ A (u : Lp V 2 μ),
    (mem_supportedSpace_ae μ S hS (u : Lp V 2 μ)).1 u.property] with x ha hu
  rw [ha]
  by_cases hx : x ∈ S
  · exact ((A x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _))
  · rw [hu hx, map_zero, norm_zero, mul_zero]

/-- The localized coefficient bound is the genuine supported-space operator bound. -/
theorem operator_norm_le (A : Field (α := α) (V := V)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ S, ‖A x‖ ≤ C) : ‖operator μ S hS A‖ ≤ C :=
  opNorm_le_bound _ hC (operator_apply_norm_le μ S hS A C hbound)

/-- Equality on the supporting set suffices for equality of the actual operators. -/
theorem operator_congr_on (A B : Field (α := α) (V := V))
    (hAB : ∀ x ∈ S, A x = B x) : operator μ S hS A = operator μ S hS B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [full_ae μ A (u : Lp V 2 μ), full_ae μ B (u : Lp V 2 μ),
    (mem_supportedSpace_ae μ S hS (u : Lp V 2 μ)).1 u.property] with x ha hb hu
  change (full μ A (u : Lp V 2 μ)) x = (full μ B (u : Lp V 2 μ)) x
  rw [ha,hb]
  by_cases hx : x ∈ S
  · rw [hAB x hx]
  · rw [hu hx, map_zero, map_zero]

/-- Addition of coefficient fields is actual addition of supported multipliers. -/
theorem operator_add (A B : Field (α := α) (V := V)) :
    operator μ S hS (A+B) = operator μ S hS A + operator μ S hS B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change full μ (A+B) (u : Lp V 2 μ) = full μ A (u : Lp V 2 μ) + full μ B (u : Lp V 2 μ)
  apply Lp.ext
  filter_upwards [full_ae μ (A+B) (u : Lp V 2 μ), full_ae μ A (u : Lp V 2 μ),
    full_ae μ B (u : Lp V 2 μ), Lp.coeFn_add (full μ A (u : Lp V 2 μ)) (full μ B (u : Lp V 2 μ))]
    with x hab ha hb hs
  simp only [Pi.add_apply] at hs
  rw [hab,hs,ha,hb]
  rfl

/-- Scalar multiplication commutes with the actual supported multiplier. -/
theorem operator_smul (r : ℝ) (A : Field (α := α) (V := V)) :
    operator μ S hS (r • A) = r • operator μ S hS A := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change full μ (r • A) (u : Lp V 2 μ) = r • full μ A (u : Lp V 2 μ)
  apply Lp.ext
  filter_upwards [full_ae μ (r • A) (u : Lp V 2 μ), full_ae μ A (u : Lp V 2 μ),
    Lp.coeFn_smul r (full μ A (u : Lp V 2 μ))] with x hra ha hs
  simp only [Pi.smul_apply] at hs
  rw [hra,hs,ha]
  rfl

/-- Pointwise composition of fields is actual operator composition. -/
theorem operator_mul (A B : Field (α := α) (V := V)) :
    operator μ S hS (A*B) = (operator μ S hS A).comp (operator μ S hS B) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change full μ (A*B) (u : Lp V 2 μ) = full μ A (full μ B (u : Lp V 2 μ))
  apply Lp.ext
  filter_upwards [full_ae μ (A*B) (u : Lp V 2 μ), full_ae μ A (full μ B (u : Lp V 2 μ)),
    full_ae μ B (u : Lp V 2 μ)] with x hab ha hb
  rw [hab,ha,hb]
  rfl

/-- The identity field gives the identity on the supported space. -/
theorem operator_one : operator μ S hS (1 : Field (α := α) (V := V)) =
    ContinuousLinearMap.id ℝ (supportedSpace μ S hS) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [full_ae μ (1 : Field (α := α) (V := V)) (u : Lp V 2 μ)] with x hx
  exact hx

/-- Coefficient-to-operator lifting is a genuine bounded linear map. -/
def operatorMap : Field (α := α) (V := V) →L[ℝ]
    (supportedSpace (V := V) μ S hS →L[ℝ] supportedSpace (V := V) μ S hS) where
  toLinearMap :=
    { toFun := operator μ S hS
      map_add' := operator_add μ S hS
      map_smul' := operator_smul μ S hS }
  cont := AddMonoidHomClass.continuous_of_bound
    ({ toFun := operator μ S hS
       map_add' := operator_add μ S hS
       map_smul' := operator_smul μ S hS } : Field (α := α) (V := V) →ₗ[ℝ] _)
    1 (fun A => by
      change ‖operator μ S hS A‖ ≤ (1 : ℝ)*‖A‖
      rw [one_mul]
      exact operator_norm_le μ S hS A ‖A‖ (norm_nonneg A) (fun x _ => A.norm_coe_le_norm x))

end EulerLpSupportedMultiplier
