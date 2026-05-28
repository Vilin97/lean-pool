/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import LeanPool.DirectedTopologyLean4.DirectedHomotopy

/-
  Auxiliary lemmas for the refl_trans and trans_refl definitions in directed_path_homotopy.lean.
  These two are definitions are dihomotopies related to a `p : Dipath x₀ x₁`:
    refl_trans : from `(refl x₀).trans p` to `p`
    trans_refl : from `p` to `p.trans (refl x₁)`

  Those for trans_refl can be based on the auxiliary lemmas found in
  algebraic_topology.fundamental_groupoid.basic.
  They use symmetry for refl_trans which is not possible in the directed case, so we have to define
  them manually.
-/

open DirectedSpace DirectedMap
open scoped unitInterval

universe u v

variable {X : Type u} {Y : Type v}
variable [DirectedSpace X] [DirectedSpace Y]
variable {x₀ x₁ : X}

noncomputable section

namespace Dipath

namespace Dihomotopy

open Path.Homotopy

lemma directed_transReflReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩
       continuous_toFun := Continuous.subtype_mk continuous_transReflReparamAux _ } :
      C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transReflReparamAux
  simp only [one_div, ContinuousMap.coe_mk, Subtype.mk_le_mk]
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₁ h₂
  · linarith
  · calc 2 * (x : ℝ)
      _ ≤ 2 * 2⁻¹ := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr h₁
      _ = 1       := by simp
  · linarith
  · linarith

/-- The auxiliary reparametrization map `I → I` used to show that `p.trans (refl _)` is
dihomotopic to `p`, packaged as a directed map. -/
def TransReflReparamAuxMap : D(I,I) where
  toFun := fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩
  continuous_toFun := Continuous.subtype_mk continuous_transReflReparamAux _
  directed_toFun := directed_transReflReparamAux

lemma trans_refl_reparam_dipath (p : Dipath x₀ x₁) : p.trans (Dipath.refl x₁) =
    p.reparam TransReflReparamAuxMap (Subtype.ext transReflReparamAux_zero)
      (Subtype.ext transReflReparamAux_one) := by
  ext t
  have : (p.trans (Dipath.refl x₁)) t = p.toPath.trans (Path.refl x₁) t := rfl
  rw [this, Path.Homotopy.trans_refl_reparam p.toPath]
  rfl

/-- Auxilliary function for `ReflTransReparam` -/
def ReflTransReparamAux (t : I) : ℝ :=
if (t : ℝ) ≤ 1/2 then
  0
else
  2 * t - 1

@[continuity]
lemma continuous_ReflTransReparamAux : Continuous ReflTransReparamAux := by
  refine continuous_if_le ?_ ?_ (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) ?_ <;>
  [continuity; continuity; continuity; continuity; skip]
  intros x hx
  norm_num [hx]

lemma reflTransReparamAux_mem_I (t : I) : ReflTransReparamAux t ∈ I := by
  unfold ReflTransReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

lemma reflTransReparamAux_zero : ReflTransReparamAux 0 = 0 :=
by norm_num [ReflTransReparamAux]

lemma reflTransReparamAux_one : ReflTransReparamAux 1 = 1 :=
by norm_num [ReflTransReparamAux]


lemma directed_ReflTransReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩
       continuous_toFun := Continuous.subtype_mk continuous_ReflTransReparamAux _ } :
      C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold ReflTransReparamAux
  simp only [one_div, ContinuousMap.coe_mk, Subtype.mk_le_mk]
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₁ h₂
  · linarith
  · calc (0 : ℝ)
      _ = (2 : ℝ) * (2⁻¹ : ℝ) - (1 : ℝ) := by norm_num
      _ ≤ 2 * (y : ℝ) - 1 := le_of_lt <|
        sub_lt_sub_right ((mul_lt_mul_iff_of_pos_left (by norm_num)).mpr
          (lt_of_not_ge h₂)) 1
  · linarith
  · linarith

/-- The auxiliary reparametrization map `I → I` used to show that `(refl _).trans p` is
dihomotopic to `p`, packaged as a directed map. -/
def ReflTransReparamAuxMap : D(I,I) where
  toFun := fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩
  continuous_toFun := Continuous.subtype_mk continuous_ReflTransReparamAux _
  directed_toFun := directed_ReflTransReparamAux

lemma refl_trans_reparam (p : Path x₀ x₁) :
    (Path.refl x₀).trans p =
      p.reparam (fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext
  unfold ReflTransReparamAux
  simp [Path.trans_apply, Function.comp_apply]
  split_ifs
  · simp
  · simp
  · rfl
  · rfl

lemma refl_trans_reparam_dipath (p : Dipath x₀ x₁) : (Dipath.refl x₀).trans p =
    p.reparam ReflTransReparamAuxMap
      (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext t
  have : ((Dipath.refl x₀).trans p) t =  (Path.refl x₀).trans p.toPath t := rfl
  rw [this, refl_trans_reparam p.toPath]
  rfl

end Dihomotopy

end Dipath
