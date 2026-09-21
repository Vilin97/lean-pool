/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.EMP.AreaVectorTarget
import LeanPool.NandakumarRamanaRao.NRR.EMP.WeightSpace

/-!
# `NRR.EMP.NormalizedAreaDeviation` — the deviation map on zero-sum weights

The additive-constant freedom of power weights is removed by restricting to the linear
hyperplane of weight vectors whose coordinate sum is zero.  The area-deviation vector also
has coordinate sum zero, so it defines a continuous self-map of that finite-dimensional
hyperplane.

This is the finite-dimensional map to which the eventual degree / outward-pointing argument
for existence of equal-area power weights is applied.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody

namespace NRR

variable {n : ℕ}

namespace EMP

/-- The zero-sum weight hyperplane, represented as a subtype of `Fin n → ℝ`. -/
abbrev NormalizedWeightSpace (n : ℕ) :=
  {w : Fin n → ℝ // EMP.WeightNormalized w}

namespace NormalizedWeightSpace

@[ext] theorem ext {u v : EMP.NormalizedWeightSpace n}
    (h : (u : Fin n → ℝ) = (v : Fin n → ℝ)) :
    u = v :=
  Subtype.ext h

/-- The zero weight vector belongs to the normalized weight hyperplane. -/
noncomputable def zero (n : ℕ) : EMP.NormalizedWeightSpace n :=
  ⟨fun _ => 0, EMP.weightSum_zero⟩

@[simp] theorem coe_zero :
    ((zero n : EMP.NormalizedWeightSpace n) : Fin n → ℝ) = 0 :=
  rfl

end NormalizedWeightSpace

/-- The area-deviation vector, regarded as a self-map of the normalized weight hyperplane. -/
noncomputable def normalizedAreaDeviation
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : EMP.NormalizedWeightSpace n) : EMP.NormalizedWeightSpace n :=
  ⟨EMP.areaDeviation K s w.1,
    EMP.sum_areaDeviation_eq_zero K s w.1 hn hs⟩

@[simp] theorem normalizedAreaDeviation_coe
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : EMP.NormalizedWeightSpace n) :
    ((EMP.normalizedAreaDeviation K s hn hs w : EMP.NormalizedWeightSpace n) : Fin n → ℝ) =
      EMP.areaDeviation K s w.1 :=
  rfl

/-- The normalized deviation map is continuous. -/
theorem continuous_normalizedAreaDeviation
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s) :
    Continuous (EMP.normalizedAreaDeviation K s hn hs) := by
  exact Continuous.subtype_mk
    ((EMP.continuous_areaDeviation_weights K s hs).comp continuous_subtype_val) _

/-- A zero of the normalized deviation map is exactly a normalized equal-area weight. -/
theorem normalizedAreaDeviation_eq_zero_iff
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : EMP.NormalizedWeightSpace n) :
    ((EMP.normalizedAreaDeviation K s hn hs w : EMP.NormalizedWeightSpace n) : Fin n → ℝ) = 0 ↔
      EMP.IsEqualAreaWeight K s w.1 := by
  rw [EMP.normalizedAreaDeviation_coe]
  constructor
  · intro h i
    have hi := congrFun h i
    simp only [EMP.areaDeviation_apply, Pi.zero_apply, sub_eq_zero] at hi
    simpa [EMP.equalAreaTarget] using hi
  · intro h
    funext i
    simp only [EMP.areaDeviation_apply, Pi.zero_apply, sub_eq_zero]
    simpa [EMP.equalAreaTarget] using h i

/-- Any zero of the normalized deviation map supplies the unrestricted existence theorem. -/
theorem exists_equalArea_weights_of_normalizedDeviation_zero
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (hzero : ∃ w : EMP.NormalizedWeightSpace n,
      ((EMP.normalizedAreaDeviation K s hn hs w : EMP.NormalizedWeightSpace n) : Fin n → ℝ) = 0) :
    ∃ w : Fin n → ℝ, EMP.IsEqualAreaWeight K s w := by
  obtain ⟨w, hw⟩ := hzero
  exact ⟨w.1, (EMP.normalizedAreaDeviation_eq_zero_iff K s hn hs w).mp hw⟩

end EMP

end NRR
