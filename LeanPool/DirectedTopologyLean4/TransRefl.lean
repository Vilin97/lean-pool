/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import LeanPool.DirectedTopologyLean4.DirectedHomotopy

/-!
# LeanPool.DirectedTopologyLean4.TransRefl
-/

/-
  Auxiliary lemmas for the reflTrans and transRefl definitions in directed_path_homotopy.lean.
  These two are definitions are dihomotopies related to a `p : Dipath x₀ x₁`:
    reflTrans : from `(refl x₀).trans p` to `p`
    transRefl : from `p` to `p.trans (refl x₁)`

  Those for transRefl can be based on the auxiliary lemmas found in
  algebraic_topology.fundamental_groupoid.basic.
  They use symmetry for reflTrans which is not possible in the directed case, so we have to define
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
  split_ifs <;> linarith

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
  rw [show (p.trans (Dipath.refl x₁)) t = p.toPath.trans (Path.refl x₁) t from rfl,
    Path.Homotopy.trans_refl_reparam p.toPath]
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
  · have := lt_of_not_ge h₂
    linarith
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
  split_ifs <;> simp

lemma refl_trans_reparam_dipath (p : Dipath x₀ x₁) : (Dipath.refl x₀).trans p =
    p.reparam ReflTransReparamAuxMap
      (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext t
  rw [show ((Dipath.refl x₀).trans p) t = (Path.refl x₀).trans p.toPath t from rfl,
    refl_trans_reparam p.toPath]
  rfl

end Dihomotopy

end Dipath
