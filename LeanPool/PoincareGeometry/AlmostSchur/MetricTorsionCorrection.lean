/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

/-! # Algebraic metric and torsion correction

The correction is constructed by Riesz representation from the metric defect
and torsion, rather than postulated through its desired properties. The metric
defect uses slot order `Q(v,w,u)` and is symmetric in its first two slots.
-/

@[expose] public noncomputable section
namespace AlmostSchur
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The correction paired with a test vector, as an actual continuous linear
functional in that test vector. -/
def koszulCorrectionForm (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V) (u v : V) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w ↦ (Q v w u + Q u w v - Q u v w -
        inner ℝ (T u v) w - inner ℝ (T w u) v + inner ℝ (T v w) u) / 2
      map_add' := by
        intro w z
        simp only [map_add, add_apply, inner_add_left, inner_add_right]
        ring
      map_smul' := by
        intro a w
        simp only [map_smul, smul_apply, smul_eq_mul, inner_smul_left, inner_smul_right,
          conj_trivial, RingHom.id_apply]
        ring }

theorem koszulCorrectionForm_add_left (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V) (u z v : V) :
    koszulCorrectionForm Q T (u + z) v =
      koszulCorrectionForm Q T u v + koszulCorrectionForm Q T z v := by
  ext w
  simp only [koszulCorrectionForm, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, add_apply,
    map_add, inner_add_left, inner_add_right]
  dsimp only [AddHom.coe_mk]
  ring

theorem koszulCorrectionForm_smul_left (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V) (a : ℝ) (u v : V) :
    koszulCorrectionForm Q T (a • u) v = a • koszulCorrectionForm Q T u v := by
  ext w
  simp only [koszulCorrectionForm, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, smul_apply,
    map_smul, smul_eq_mul, inner_smul_left, inner_smul_right, conj_trivial]
  dsimp only [AddHom.coe_mk]
  ring

theorem koszulCorrectionForm_add_right (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V) (u v z : V) :
    koszulCorrectionForm Q T u (v + z) =
      koszulCorrectionForm Q T u v + koszulCorrectionForm Q T u z := by
  ext w
  simp only [koszulCorrectionForm, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, add_apply,
    map_add, inner_add_left, inner_add_right]
  dsimp only [AddHom.coe_mk]
  ring

theorem koszulCorrectionForm_smul_right (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V) (a : ℝ) (u v : V) :
    koszulCorrectionForm Q T u (a • v) = a • koszulCorrectionForm Q T u v := by
  ext w
  simp only [koszulCorrectionForm, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, smul_apply,
    map_smul, smul_eq_mul, inner_smul_left, inner_smul_right, conj_trivial]
  dsimp only [AddHom.coe_mk]
  ring

/-- The actual bilinear vector-valued correction obtained by Riesz representation. -/
def koszulCorrection (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V) : V →L[ℝ] V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ LinearMap.toContinuousLinearMap
        { toFun := fun v ↦ (InnerProductSpace.toDual ℝ V).symm (koszulCorrectionForm Q T u v)
          map_add' := by intros; simp only [koszulCorrectionForm_add_right, map_add]
          map_smul' := by intros; simp only [koszulCorrectionForm_smul_right, map_smul, RingHom.id_apply] }
      map_add' := by
        intro u z
        ext v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, add_apply,
          koszulCorrectionForm_add_left, map_add]
        rfl
      map_smul' := by
        intro a u
        ext v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, smul_apply,
          koszulCorrectionForm_smul_left, map_smul, RingHom.id_apply]
        rfl }

/-- Exact pairing formula for the constructed correction. -/
theorem koszulCorrection_inner (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V) (u v w : V) :
    inner ℝ (koszulCorrection Q T u v) w =
      (Q v w u + Q u w v - Q u v w - inner ℝ (T u v) w -
        inner ℝ (T w u) v + inner ℝ (T v w) u) / 2 := by
  exact InnerProductSpace.toDual_symm_apply

/-- The correction cancels the metric defect. -/
theorem koszulCorrection_metric (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V)
    (hQ : ∀ u v w, Q u v w = Q v u w) (hT : ∀ u v, T u v = -T v u)
    (u v w : V) :
    inner ℝ (koszulCorrection Q T u v) w +
      inner ℝ v (koszulCorrection Q T u w) = Q v w u := by
  rw [← real_inner_comm v (koszulCorrection Q T u w), koszulCorrection_inner, koszulCorrection_inner,
    hQ w v u, hT u w, hT v u, hT w v]
  simp only [inner_neg_left]
  ring

/-- The correction cancels the torsion. -/
theorem koszulCorrection_torsion (Q : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ)
    (T : V →L[ℝ] V →L[ℝ] V)
    (hQ : ∀ u v w, Q u v w = Q v u w) (hT : ∀ u v, T u v = -T v u)
    (u v : V) : koszulCorrection Q T u v - koszulCorrection Q T v u = -T u v := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_sub_left, koszulCorrection_inner, koszulCorrection_inner,
    hQ v u w, hT v u, hT w v, hT u w]
  simp only [inner_neg_left]
  ring

end AlmostSchur
