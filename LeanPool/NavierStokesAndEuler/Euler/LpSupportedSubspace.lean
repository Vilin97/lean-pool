/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD

/-!
# The actual supported subspace of ordinary spatial L²

Support is imposed on genuine Bochner L² functions by the closed kernel of
identity minus measurable-set projection. This gives a complete Hilbert space
for localized propagators and keeps the support restriction explicit.
-/

@[expose] public section


noncomputable section

namespace EulerLpSupportedSubspace

open Set MeasureTheory ContinuousLinearMap
open scoped ENNReal

variable {α V : Type*} [MeasurableSpace α] (μ : Measure α)
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set α) (hS : MeasurableSet S)

/-- The actual measurable-set cutoff on a Bochner L² function. -/
def cutoff (u : Lp V 2 μ) : Lp V 2 μ :=
  ((Lp.memLp u).indicator hS).toLp (S.indicator u)

omit [InnerProductSpace ℝ V] in
/-- Its representative is the literal indicator product. -/
theorem cutoff_ae (u : Lp V 2 μ) : cutoff μ S hS u =ᵐ[μ] S.indicator u :=
  ((Lp.memLp u).indicator hS).coeFn_toLp

omit [InnerProductSpace ℝ V] in
/-- Measurable-set projection is norm-decreasing. -/
theorem cutoff_norm (u : Lp V 2 μ) : ‖cutoff μ S hS u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutoff_ae μ S hS u] with x hx
  rw [hx]
  by_cases hs : x ∈ S
  · rw [indicator_of_mem hs]
  · rw [indicator_of_notMem hs, norm_zero]
    exact norm_nonneg _

/-- The actual cutoff is linear. -/
def cutoffLinear : Lp V 2 μ →ₗ[ℝ] Lp V 2 μ where
  toFun := cutoff μ S hS
  map_add' u v := by
    apply Lp.ext
    filter_upwards [cutoff_ae μ S hS (u+v), cutoff_ae μ S hS u, cutoff_ae μ S hS v,
      Lp.coeFn_add u v, Lp.coeFn_add (cutoff μ S hS u) (cutoff μ S hS v)] with x huv hu hv ha hc
    simp only [Pi.add_apply] at ha hc
    rw [huv, hc, hu, hv]
    by_cases hs : x ∈ S
    · simp only [indicator_of_mem hs, ha]
    · simp only [indicator_of_notMem hs, add_zero]
  map_smul' r u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [cutoff_ae μ S hS (r • u), cutoff_ae μ S hS u,
      Lp.coeFn_smul r u, Lp.coeFn_smul r (cutoff μ S hS u)] with x hru hu ha hc
    simp only [Pi.smul_apply] at ha hc
    rw [hru, hc, hu]
    by_cases hs : x ∈ S
    · simp only [indicator_of_mem hs, ha]
    · simp only [indicator_of_notMem hs, smul_zero]

/-- The supported-set projection as a genuine bounded linear map. -/
def cutoffOperator : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  (cutoffLinear μ S hS).mkContinuous 1 (fun u => by
    change ‖cutoff μ S hS u‖ ≤ (1 : ℝ)*‖u‖
    simpa only [one_mul] using cutoff_norm μ S hS u)

/-- The localized Hilbert subspace is a closed kernel. -/
def supportedSpace : Submodule ℝ (Lp V 2 μ) :=
  (ContinuousLinearMap.id ℝ (Lp V 2 μ) - cutoffOperator μ S hS).ker

/-- Membership is fixedness under actual measurable-set projection. -/
theorem mem_supportedSpace_iff (u : Lp V 2 μ) :
    u ∈ supportedSpace μ S hS ↔ u = cutoff μ S hS u := by
  change u - cutoff μ S hS u = 0 ↔ _
  exact sub_eq_zero

/-- Membership is exactly almost-everywhere vanishing outside the given set. -/
theorem mem_supportedSpace_ae (u : Lp V 2 μ) :
    u ∈ supportedSpace μ S hS ↔ ∀ᵐ x ∂μ, x ∉ S → u x = 0 := by
  rw [mem_supportedSpace_iff]
  constructor
  · intro hu
    have he : u =ᵐ[μ] S.indicator u := by
      conv_lhs => rw [hu]
      exact cutoff_ae μ S hS u
    filter_upwards [he] with x hx hs
    rw [hx, indicator_of_notMem hs]
  · intro hu
    apply Lp.ext
    filter_upwards [cutoff_ae μ S hS u, hu] with x hx ho
    rw [hx]
    by_cases hs : x ∈ S
    · exact (indicator_of_mem hs u).symm
    · rw [indicator_of_notMem hs]
      exact ho hs

/-- The support condition is closed in the actual L² norm. -/
theorem supportedSpace_closed : IsClosed (supportedSpace (V := V) μ S hS : Set (Lp V 2 μ)) :=
  (ContinuousLinearMap.id ℝ (Lp V 2 μ) - cutoffOperator μ S hS).isClosed_ker

instance [CompleteSpace V] : CompleteSpace (supportedSpace (V := V) μ S hS) :=
  (supportedSpace_closed μ S hS).completeSpace_coe

/-- Every cutoff output belongs to the supported subspace. -/
theorem cutoff_mem (u : Lp V 2 μ) : cutoff μ S hS u ∈ supportedSpace μ S hS := by
  apply (mem_supportedSpace_ae μ S hS _).2
  filter_upwards [cutoff_ae μ S hS u] with x hx hs
  rw [hx, indicator_of_notMem hs]

/-- Actual projection from full spatial L² to its supported Hilbert subspace. -/
def projection : Lp V 2 μ →L[ℝ] supportedSpace (V := V) μ S hS :=
  (cutoffOperator μ S hS).codRestrict (supportedSpace μ S hS) (cutoff_mem μ S hS)

/-- The projection has norm at most one. -/
theorem projection_norm : ‖projection (V := V) μ S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  change ‖cutoff μ S hS u‖ ≤ (1 : ℝ)*‖u‖
  simpa only [one_mul] using cutoff_norm μ S hS u

/-- Inclusion after projection fixes every already supported field. -/
theorem projection_supported (u : supportedSpace (V := V) μ S hS) :
    projection μ S hS (u : Lp V 2 μ) = u := by
  apply Subtype.ext
  exact ((mem_supportedSpace_iff μ S hS (u : Lp V 2 μ)).1 u.property).symm

end EulerLpSupportedSubspace
