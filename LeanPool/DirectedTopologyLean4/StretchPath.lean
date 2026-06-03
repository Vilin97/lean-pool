/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.Dipath
import LeanPool.DirectedTopologyLean4.DTop
import LeanPool.DirectedTopologyLean4.UnitIntervalAux

/-!
# LeanPool.DirectedTopologyLean4.StretchPath
-/

/-
  This file contains definitions about stretching a (directed) path in `I` in two ways:
    If its image is contained in `[0, 1/2]`, it can be stretched upwards
    If its image is contained in `[1/2, 1]`, it can be stretched downwards

  These cases can be determined by the endpoints of the directed path.
-/

open unitIAux
open scoped unitInterval

namespace Dipath

/-### Stretching a path that only lives in the first half of the unit interval upwards -/

lemma double_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ))
    : 2 * (γ t : ℝ) ∈ I :=
  double_mem_I <| le_trans (monotone_path_bounded γ.dipath_toPath t).2 (ht₁)

/-- Stretch a path whose image lies in `[0, 1/2]` to a path on the full unit interval by doubling
all parameter values. -/
def stretchUpPath {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : Path
  (⟨2 * ↑t₀, by { rw [←γ.source']; exact double_mem_I_of_bounded 0 γ ht₁ }⟩ : I)
  ⟨2 * ↑t₁, double_mem_I ht₁⟩ where
    toFun := fun t => ⟨2 * (γ t), double_mem_I_of_bounded t γ ht₁⟩
    source' := by simp
    target' := by simp

lemma isDipath_stretch_up {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) :
  IsDipath (stretchUpPath γ ht₁) := by
  intros x y hxy
  unfold stretchUpPath
  simp only [Path.coe_mk', ContinuousMap.coe_mk, Subtype.mk_le_mk, Nat.ofNat_pos,
    mul_le_mul_iff_right₀, Subtype.coe_le_coe]
  exact γ.dipath_toPath hxy

/-- The dipath obtained by stretching a dipath whose image lies in `[0, 1/2]` to the full unit
interval. -/
def stretchUp {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₁ : ↑t₁ ≤ (2⁻¹ : ℝ)) : Dipath
  (⟨2 * ↑t₀, by { rw [←γ.source']; exact double_mem_I_of_bounded 0 γ ht₁ }⟩ : I)
  ⟨2 * ↑t₁, double_mem_I ht₁⟩ where
    toPath := stretchUpPath γ ht₁
    dipath_toPath := isDipath_stretch_up γ ht₁

/-### Stretching a path that only lives in the second half of the unit interval downwards -/

lemma double_sub_one_mem_I_of_bounded {t₀ t₁ : I} (t : I) (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀)
 : 2 * (γ t : ℝ) - 1 ∈ I :=
  double_sub_one_mem_I <| le_trans ht₀ (monotone_path_bounded γ.dipath_toPath t).1

/-- Stretch a path whose image lies in `[1/2, 1]` to a path on the full unit interval by mapping
each parameter `s` to `2s - 1`. -/
def stretchDownPath {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) : Path
  (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
  ⟨2 * ↑t₁ - 1, by { rw [←γ.target']; exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ where
    toFun := fun t => ⟨2 * (γ t) - 1, double_sub_one_mem_I_of_bounded t γ ht₀⟩
    source' := by simp
    target' := by simp

lemma isDipath_stretch_down {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) :
  IsDipath (stretchDownPath γ ht₀) := by
  intros x y hxy
  unfold stretchDownPath
  simp only [Path.coe_mk', ContinuousMap.coe_mk, Subtype.mk_le_mk, tsub_le_iff_right,
    sub_add_cancel, Nat.ofNat_pos, mul_le_mul_iff_right₀, Subtype.coe_le_coe]
  exact γ.dipath_toPath hxy

/-- The dipath obtained by stretching a dipath whose image lies in `[1/2, 1]` to the full unit
interval. -/
def stretchDown {t₀ t₁ : I} (γ : Dipath t₀ t₁) (ht₀ : (2⁻¹ : ℝ) ≤ ↑t₀) : Dipath
  (⟨2 * ↑t₀ - 1, double_sub_one_mem_I ht₀⟩ : I)
  ⟨2 * ↑t₁ - 1, by { rw [←γ.target']; exact double_sub_one_mem_I_of_bounded 1 γ ht₀ }⟩ where
    toPath := stretchDownPath γ ht₀
    dipath_toPath := isDipath_stretch_down γ ht₀

end Dipath
