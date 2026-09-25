/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleModular
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Hom.Set

/-!
# Young functions are bijections of the nonnegative half-line

This proves the assertion preceding the inverse notation in Section 2.5 of
the paper from the existing Young-function definition, including its identity
exception. No additional growth or regularity hypothesis is imposed.
-/

@[expose] public section

open Filter Set
open scoped NNReal

namespace QuadraticCarleson.YoungFunction


/-- Both the identity exception and superlinear alternative eventually
dominate the identity function. -/
theorem eventually_id_le (Φ : YoungFunction) :
    ∀ᶠ t : ℝ in atTop, t ≤ Φ t := by
  rcases Φ.identity_or_superlinear with hidentity | hsuperlinear
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact le_of_eq (hidentity t ht).symm
  · filter_upwards [hsuperlinear.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_ge_atTop (1 : ℝ)] with t hratio ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    simpa only [one_mul] using (le_div_iff₀ htpos).mp hratio

theorem tendsto_atTop (Φ : YoungFunction) : Tendsto Φ atTop atTop :=
  tendsto_atTop_mono' atTop Φ.eventually_id_le tendsto_id

/-- The source's bijection assertion on exactly `[0,∞)`. -/
theorem bijOn_nonneg (Φ : YoungFunction) : BijOn Φ (Ici 0) (Ici 0) := by
  refine ⟨fun _ ht ↦ Φ.nonneg ht, Φ.strictMonoOn_nonneg.injOn, ?_⟩
  simpa only [SurjOn, Φ.map_zero] using
    intermediate_value_Ici Φ.continuousOn_nonneg Φ.tendsto_atTop

/-- The Young function and its inverse, as an order-preserving bijection of
the nonnegative real numbers. -/
noncomputable def nonnegOrderIso (Φ : YoungFunction) : ℝ≥0 ≃o ℝ≥0 := by
  apply StrictMono.orderIsoOfSurjective
    (fun t : ℝ≥0 ↦ (⟨Φ t, Φ.nonneg t.property⟩ : ℝ≥0))
  · intro x y hxy
    exact Φ.strictMonoOn_nonneg x.property y.property hxy
  · intro y
    obtain ⟨x, hx, hxy⟩ := Φ.bijOn_nonneg.2.2 y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp] theorem nonnegOrderIso_apply (Φ : YoungFunction) (t : ℝ≥0) :
    (Φ.nonnegOrderIso t : ℝ) = Φ t := rfl

/-- The inverse provided by the paper's notation is a right inverse. -/
@[simp] theorem apply_nonnegOrderIso_symm (Φ : YoungFunction) (t : ℝ≥0) :
    Φ (Φ.nonnegOrderIso.symm t : ℝ) = t :=
  congrArg (fun y : ℝ≥0 ↦ (y : ℝ)) (Φ.nonnegOrderIso.apply_symm_apply t)

/-- The same inverse is a left inverse on the entire nonnegative half-line. -/
@[simp] theorem nonnegOrderIso_symm_apply (Φ : YoungFunction) (t : ℝ≥0) :
    Φ.nonnegOrderIso.symm ⟨Φ t, Φ.nonneg t.property⟩ = t :=
  Φ.nonnegOrderIso.symm_apply_apply t


end QuadraticCarleson.YoungFunction
