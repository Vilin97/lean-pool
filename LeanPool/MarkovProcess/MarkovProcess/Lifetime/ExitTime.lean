/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Lifetime.Basic

/-!
# Exit times of lifetime paths

This file defines the first time at which a lifetime path is not a live point of a prescribed
set. Reaching the cemetery state counts as exit. The infimum of the empty set is infinity, so a
path which never exits has infinite exit time.

Only deterministic order properties are proved here. No measurability or stopping-time claim is
made.
-/

open Set
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The first time at which a lifetime path is not a live point of `U`. -/
def exitTime (U : Set alpha) (omega : LifetimePath alpha) : ENNReal :=
  sInf {s : ENNReal | ∃ t : NNReal, s = (t : ENNReal) ∧
    coordinate t omega ∉ Cemetery.alive '' U}

/-- A failed live-`U` coordinate bounds the first exit time from above. -/
theorem exitTime_le_of_coordinate_notMem (U : Set alpha) (omega : LifetimePath alpha)
    (t : NNReal) (ht : coordinate t omega ∉ Cemetery.alive '' U) :
    exitTime U omega ≤ (t : ENNReal) := by
  apply sInf_le
  exact ⟨t, rfl, ht⟩

/-- Strictly before the exit time, the coordinate is a live point of `U`. -/
theorem exists_coordinate_eq_alive_of_lt_exitTime (U : Set alpha)
    (omega : LifetimePath alpha) (t : NNReal) (ht : (t : ENNReal) < exitTime U omega) :
    ∃ x ∈ U, coordinate t omega = Cemetery.alive x := by
  by_contra hcoordinate
  have hnotmem : coordinate t omega ∉ Cemetery.alive '' U := by
    rintro ⟨x, hx, hxeq⟩
    exact hcoordinate ⟨x, hx, hxeq.symm⟩
  exact (not_le_of_gt ht) (exitTime_le_of_coordinate_notMem U omega t hnotmem)

/-- The exit time is no later than the lifetime, since killing counts as exit. -/
theorem exitTime_le_lifetime (U : Set alpha) (omega : LifetimePath alpha) :
    exitTime U omega ≤ omega.lifetime := by
  by_cases hlifetime : omega.lifetime = ∞
  · rw [hlifetime]
    exact le_top
  · let t : NNReal := omega.lifetime.toNNReal
    have ht : (t : ENNReal) = omega.lifetime := ENNReal.coe_toNNReal hlifetime
    rw [← ht]
    apply exitTime_le_of_coordinate_notMem
    rw [coordinate_of_le omega t ht.ge]
    rintro ⟨x, _, hdelta⟩
    exact Sum.inl_ne_inr hdelta

end LifetimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The first time at which an ordinary continuous path leaves `U`. -/
def exitTime (U : Set alpha) (omega : ContinuousPath alpha) : ENNReal :=
  sInf {s : ENNReal | ∃ t : NNReal, s = (t : ENNReal) ∧ omega t ∉ U}

end ContinuousPath

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The lifetime-path exit time of an ordinary continuous path is its ordinary exit time. -/
@[simp]
theorem exitTime_ofContinuousPath (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTime U (ofContinuousPath omega) = ContinuousPath.exitTime U omega := by
  apply congrArg sInf
  ext s
  constructor
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    intro homega
    apply ht
    exact ⟨omega t, homega, coordinate_ofContinuousPath omega t |>.symm⟩
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    rintro ⟨x, hx, hcoordinate⟩
    rw [coordinate_ofContinuousPath] at hcoordinate
    have heq : omega t = x := Sum.inl.inj hcoordinate.symm
    exact ht (heq.symm ▸ hx)

/-- An infinite-lifetime path has the exit time of its associated ordinary continuous path. -/
theorem exitTime_eq_exitTime_toContinuousPath (U : Set alpha) (omega : LifetimePath alpha)
    (homega : omega.lifetime = ∞) :
    exitTime U omega = ContinuousPath.exitTime U (toContinuousPath omega homega) := by
  rw [← exitTime_ofContinuousPath, ofContinuousPath_toContinuousPath omega homega]

end LifetimePath

end
end MarkovProcess
