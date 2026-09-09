/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialNormalMap

@[expose] public section

/-! An inverse-free polynomial formula for the actual normal multiplier's time derivative. -/

noncomputable section

namespace EulerPacketCrossProduct

open ContinuousLinearMap InnerProductSpace EulerSmoothLimit

/-- Differentiate the normal functional using only itself and the normal's derivative column. -/
def normalTimeMap (N : Space →L[ℝ] ℝ) (Q₁ : ℝ →L[ℝ] Space) : Space →L[ℝ] ℝ :=
  (N.comp N.adjoint).comp Q₁.adjoint - (2 : ℝ) • (N.comp Q₁).comp N

theorem normalTimeMap_apply (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m,v⟫_ℝ / ‖m‖^2) (v : Space) :
    normalTimeMap N (toSpanSingleton ℝ mt) v =
      ⟪mt,v⟫_ℝ / ‖m‖^2 - (2*⟪m,mt⟫_ℝ/(‖m‖^2)^2)*⟪m,v⟫_ℝ := by
  have hd : ‖m‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hm)
  have hNm : N m = 1 := by rw [hN, real_inner_self_eq_norm_sq, div_self hd]
  have hAdj (s : ℝ) : N.adjoint s = s • (((‖m‖^2)⁻¹) • m) := by
    calc
      N.adjoint s = N.adjoint (s • (1 : ℝ)) := by simp
      _ = s • N.adjoint 1 := map_smul N.adjoint s 1
      _ = _ := by rw [normalVector_eq m N hN]
  simp only [normalTimeMap, sub_apply, smul_apply, comp_apply, adjoint_toSpanSingleton,
    innerSL_apply_apply, toSpanSingleton_apply]
  rw [hAdj, map_smul, map_smul, hNm, map_smul, hN mt, hN v]
  simp only [smul_eq_mul, mul_one]
  field_simp

theorem normalTimeMap_vector (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m,v⟫_ℝ / ‖m‖^2) :
    (normalTimeMap N (toSpanSingleton ℝ mt)).adjoint 1 =
      ((‖m‖^2)⁻¹) • mt - (2*⟪m,mt⟫_ℝ/(‖m‖^2)^2) • m := by
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left, Real.inner_apply, one_mul, normalTimeMap_apply m mt N hm hN]
  simp only [inner_sub_left, real_inner_smul_left, div_eq_mul_inv]
  ring

/-- This polynomial coefficient is exactly the derivative of −cross(m)/|m|². -/
theorem normalTimeMap_potential (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m,v⟫_ℝ / ‖m‖^2) :
    normalPotentialMap (normalTimeMap N (toSpanSingleton ℝ mt)) =
      potentialMultiplierDerivative m mt := by
  change -crossOperator ((normalTimeMap N (toSpanSingleton ℝ mt)).adjoint 1) = _
  rw [normalTimeMap_vector m mt N hm hN, map_sub, map_smul, map_smul, neg_sub]
  rfl

end EulerPacketCrossProduct
