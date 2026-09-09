/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference

/-! Restriction of an ordinary Euler evolution to a translated closed interval. -/

@[expose] public section


noncomputable section


namespace EulerOrdinarySobolev

open Set Filter EulerSmoothLimit
open scoped Topology

/-- Embed the shifted time interval into the original evolution interval. -/
def shiftTimeMap (S T a : ℝ) (ha : 0 ≤ a) (haT : a + T ≤ S) :
    C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨a + t, add_nonneg ha t.property.1,
    (add_le_add le_rfl t.property.2).trans haT⟩
  continuous_toFun := (continuous_subtype_val.const_add a).subtype_mk _

@[simp] theorem shiftTimeMap_val (S T a : ℝ) (ha : 0 ≤ a) (haT : a + T ≤ S)
    (t : Icc (0 : ℝ) T) : ((shiftTimeMap S T a ha haT t) : ℝ) = a + t := rfl

namespace Evolution

variable {S : ℝ} {hS : 0 ≤ S}

/-- Restart an evolution at time `a`, retaining its next `T` units of time. -/
def shiftTime (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) : Evolution T hT where
  velocity t := U.velocity (shiftTimeMap S T a ha haT t)
  pressureForce t := U.pressureForce (shiftTimeMap S T a ha haT t)
  velocity_continuous n :=
    (U.velocity_continuous n).comp (shiftTimeMap S T a ha haT).continuous
  pressure_continuous n :=
    (U.pressure_continuous n).comp (shiftTimeMap S T a ha haT).continuous
  solenoidal t := U.solenoidal (shiftTimeMap S T a ha haT t)
  gradient t := U.gradient (shiftTimeMap S T a ha haT t)
  time_law t ht x := by
    have hat : a + t ∈ Ioo (0 : ℝ) S :=
      ⟨add_pos_of_nonneg_of_pos ha ht.1,
        (add_lt_add_of_le_of_lt le_rfl ht.2).trans_le haT⟩
    have hd := (U.time_law (a + t) hat x).comp_const_add a t
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have har : a + r ∈ Icc (0 : ℝ) S :=
      ⟨add_nonneg ha hr.1.le, (add_le_add le_rfl hr.2.le).trans haT⟩
    rw [projIcc_of_mem hT hrT, projIcc_of_mem hS har]
    rfl

@[simp] theorem shiftTime_velocity (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) (t : Icc (0 : ℝ) T) :
    (U.shiftTime a ha T hT haT).velocity t =
      U.velocity (shiftTimeMap S T a ha haT t) := rfl

@[simp] theorem shiftTime_pressureForce (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) (t : Icc (0 : ℝ) T) :
    (U.shiftTime a ha T hT haT).pressureForce t =
      U.pressureForce (shiftTimeMap S T a ha haT t) := rfl

theorem shiftTime_initial (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) :
    (U.shiftTime a ha T hT haT).velocity ⟨0, le_rfl, hT⟩ =
      U.velocity ⟨a, ha, (le_add_of_nonneg_right hT).trans haT⟩ := by
  rw [shiftTime_velocity]
  congr 1
  apply Subtype.ext
  exact add_zero a

end Evolution
end EulerOrdinarySobolev
