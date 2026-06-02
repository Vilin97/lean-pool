/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import Mathlib.Topology.UnitInterval

/-!
# LeanPool.WhiteheadTheorem.Shapes.UnitInterval

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.UnitInterval`.
-/


namespace unitInterval

instance continuousMul : ContinuousMul I where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact Continuous.mul
      (continuous_induced_dom.comp continuous_fst)
      (continuous_induced_dom.comp continuous_snd)

/-- `zeroOne` -/
abbrev zeroOne : Set ℝ := {0, 1}
instance : OfNat zeroOne 0 where ofNat := ⟨0, by norm_num⟩  -- typecheck `0` as an element of {0, 1}
instance : OfNat zeroOne 1 where ofNat := ⟨1, by norm_num⟩

namespace zeroOne

lemma val_eq_zero_or_val_eq_one (t : zeroOne) : t.val = 0 ∨ t.val = 1 := by
  obtain ⟨val, property⟩ := t
  simp_all only
  simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma eq_zero_or_eq_one (t : zeroOne) : t = 0 ∨ t = 1 := by
  obtain ht | ht := val_eq_zero_or_val_eq_one t
  all_goals obtain ⟨val, property⟩ := t; subst ht
  · left; rfl
  · right; rfl

end zeroOne

/-- `zeroOneIncl` -/
abbrev zeroOneIncl : C(zeroOne, I) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨x, by
    simp only [Set.mem_Icc]
    obtain hx | hx := hx
    all_goals subst hx; norm_num ⟩
  continuous_toFun := by fun_prop

end unitInterval
