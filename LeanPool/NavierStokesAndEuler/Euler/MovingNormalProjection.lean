/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
The actual orthogonal projection onto a moving ray's perpendicular plane.
The derivative bound depends on the ray equation through `‖m'‖/‖m‖`, and
therefore costs only the parent matrix norm, with no deformation-gradient loss.
-/

noncomputable section


namespace EulerMovingNormalProjection

open InnerProductSpace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
private local instance : AddCommGroup (E →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E)).toAddCommGroup
private local instance : Module ℝ (E →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E)).toModule
private local instance : TopologicalSpace (E →L[ℝ] E) :=
  (inferInstance : PseudoMetricSpace (E →L[ℝ] E)).toUniformSpace.toTopologicalSpace

def normalProjection (m : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (‖m‖ ^ 2)⁻¹ • rankOne ℝ m m

theorem normalProjection_apply (m x : E) :
    normalProjection m x = x - (⟪m, x⟫_ℝ / ‖m‖ ^ 2) • m := by
  simp only [normalProjection, sub_apply, id_apply, smul_apply, rankOne_apply,
    smul_smul, div_eq_mul_inv, mul_comm]

theorem normalProjection_tangent (m : E) (hm : m ≠ 0) (x : E) :
    ⟪m, normalProjection m x⟫_ℝ = 0 := by
  rw [normalProjection_apply, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem normalProjection_fixed (m x : E) (hx : ⟪m, x⟫_ℝ = 0) :
    normalProjection m x = x := by
  rw [normalProjection_apply, hx, zero_div, zero_smul, sub_zero]

theorem normalProjection_norm_sq (m : E) (hm : m ≠ 0) (x : E) :
    ‖normalProjection m x‖ ^ 2 = ‖x‖ ^ 2 - ⟪m, x⟫_ℝ ^ 2 / ‖m‖ ^ 2 := by
  rw [normalProjection_apply, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm m x]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem normalProjection_norm_le (m : E) (hm : m ≠ 0) : ‖normalProjection m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp only [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [normalProjection_norm_sq m hm]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

def normalProjectionDerivative (m m₁ : E) : E →L[ℝ] E :=
  -((- (2 * ⟪m, m₁⟫_ℝ) / (‖m‖ ^ 2) ^ 2) • rankOne ℝ m m +
    (‖m‖ ^ 2)⁻¹ • (rankOne ℝ m₁ m + rankOne ℝ m m₁))

/-- The projection derivative is derived from the actual ray derivative. -/
theorem normalProjection_hasDerivAt {m : ℝ → E} {m₁ : E} {t : ℝ}
    (hd : HasDerivAt m m₁ t) (hm : m t ≠ 0) :
    HasDerivAt (fun s => normalProjection (m s))
      (normalProjectionDerivative (m t) m₁) t := by
  have hr : HasDerivAt (fun s => rankOne ℝ (m s) (m s))
      (rankOne ℝ m₁ (m t) + rankOne ℝ (m t) m₁) t := by
    convert! ContinuousLinearMap.hasDerivAt_of_bilinear
      (B := (rankOne ℝ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) (fun _ => hd) (fun _ => hd) using 1
    ext v
    change ⟪m t, v⟫_ℝ • m₁ + ⟪m₁, v⟫_ℝ • m t =
      ⟪m₁, v⟫_ℝ • m t + ⟪m t, v⟫_ℝ • m₁
    exact add_comm _ _
  have hi := hd.norm_sq.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  change HasDerivAt (fun s => ContinuousLinearMap.id ℝ E - (‖m s‖ ^ 2)⁻¹ • rankOne ℝ (m s) (m s))
    (normalProjectionDerivative (m t) m₁) t
  convert! (hi.smul hr).const_sub (ContinuousLinearMap.id ℝ E) using 1
  simp only [normalProjectionDerivative, Pi.inv_apply, add_comm]

theorem normalProjection_hasDerivWithinAt {m : ℝ → E} {m₁ : E} {t : ℝ} {S : Set ℝ}
    (hd : HasDerivWithinAt m m₁ S t) (hm : m t ≠ 0) :
    HasDerivWithinAt (fun s => normalProjection (m s))
      (normalProjectionDerivative (m t) m₁) S t := by
  have hr : HasDerivWithinAt (fun s => rankOne ℝ (m s) (m s))
      (rankOne ℝ m₁ (m t) + rankOne ℝ (m t) m₁) S t := by
    convert! ContinuousLinearMap.hasDerivWithinAt_of_bilinear
      (B := (rankOne ℝ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) hd hd using 1
    ext v
    change ⟪m t, v⟫_ℝ • m₁ + ⟪m₁, v⟫_ℝ • m t =
      ⟪m₁, v⟫_ℝ • m t + ⟪m t, v⟫_ℝ • m₁
    exact add_comm _ _
  have hi := hd.norm_sq.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  change HasDerivWithinAt
    (fun s => ContinuousLinearMap.id ℝ E - (‖m s‖ ^ 2)⁻¹ • rankOne ℝ (m s) (m s))
    (normalProjectionDerivative (m t) m₁) S t
  convert! (hi.smul hr).const_sub (ContinuousLinearMap.id ℝ E) using 1
  simp only [normalProjectionDerivative, Pi.inv_apply, add_comm]

theorem normalProjection_continuous {α : Type*} [TopologicalSpace α]
    {f : α → E} (hf : Continuous f) (hne : ∀ a, f a ≠ 0) :
    Continuous (fun a => normalProjection (f a)) := by
  let R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E := rankOne ℝ
  have hr : Continuous (fun a => rankOne ℝ (f a) (f a)) := R.continuous₂.comp₂ hf hf
  exact continuous_const.sub
    (((hf.norm.pow 2).inv₀ (fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne a)))).smul hr)

theorem normalProjectionDerivative_continuous {α : Type*} [TopologicalSpace α]
    {f g : α → E} (hf : Continuous f) (hg : Continuous g) (hne : ∀ a, f a ≠ 0) :
    Continuous (fun a => normalProjectionDerivative (f a) (g a)) := by
  let R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E := rankOne ℝ
  have h0 : Continuous (fun a => rankOne ℝ (f a) (f a)) := R.continuous₂.comp₂ hf hf
  have h1 : Continuous (fun a => rankOne ℝ (g a) (f a)) := R.continuous₂.comp₂ hg hf
  have h2 : Continuous (fun a => rankOne ℝ (f a) (g a)) := R.continuous₂.comp₂ hf hg
  have hn := fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne a))
  have hi := (hf.norm.pow 2).inv₀ hn
  have hq := ((hf.inner hg).const_mul 2).neg.div ((hf.norm.pow 2).pow 2)
    (fun a => pow_ne_zero 2 (hn a))
  exact ((hq.smul h0).add (hi.smul (h1.add h2))).neg

/-- The bound is independent of the length of the ray. -/
theorem normalProjectionDerivative_norm_le (m m₁ : E) (hm : m ≠ 0) :
    ‖normalProjectionDerivative m m₁‖ ≤ 4 * ‖m₁‖ / ‖m‖ := by
  have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hnorm : 0 ≤ ‖m‖ ^ 2 := sq_nonneg _
  have hr := abs_real_inner_le_norm m m₁
  have hs := norm_add_le (rankOne ℝ m₁ m) (rankOne ℝ m m₁)
  simp only [norm_rankOne] at hs
  calc
    ‖normalProjectionDerivative m m₁‖ ≤
        |-(2 * ⟪m, m₁⟫_ℝ) / (‖m‖ ^ 2) ^ 2| * (‖m‖ * ‖m‖) +
          |(‖m‖ ^ 2)⁻¹| * (‖m₁‖ * ‖m‖ + ‖m‖ * ‖m₁‖) := by
      unfold normalProjectionDerivative
      rw [norm_neg]
      apply (norm_add_le _ _).trans
      rw [norm_smul, norm_smul, norm_rankOne, Real.norm_eq_abs, Real.norm_eq_abs]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
    _ = (2 * |⟪m, m₁⟫_ℝ| / (‖m‖ ^ 2) ^ 2) * (‖m‖ * ‖m‖) +
          (‖m‖ ^ 2)⁻¹ * (‖m₁‖ * ‖m‖ + ‖m‖ * ‖m₁‖) := by
      rw [abs_div, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg (‖m‖ ^ 2)), abs_of_nonneg (inv_nonneg.mpr hnorm)]
    _ ≤ (2 * (‖m‖ * ‖m₁‖) / (‖m‖ ^ 2) ^ 2) * (‖m‖ * ‖m‖) +
          (‖m‖ ^ 2)⁻¹ * (‖m₁‖ * ‖m‖ + ‖m‖ * ‖m₁‖) := by
      gcongr
    _ = 4 * ‖m₁‖ / ‖m‖ := by
      field_simp
      ring

variable [CompleteSpace E]

/-- For the actual ray equation `m'=-M* m`, only the parent gradient norm enters. -/
theorem normalProjectionDerivative_ray_bound (m : E) (hm : m ≠ 0) (M : E →L[ℝ] E) :
    ‖normalProjectionDerivative m (-(M.adjoint m))‖ ≤ 4 * ‖M‖ := by
  have hb : ‖-(M.adjoint m)‖ ≤ ‖M‖ * ‖m‖ := by
    simpa only [norm_neg, LinearIsometryEquiv.norm_map] using M.adjoint.le_opNorm m
  calc
    ‖normalProjectionDerivative m (-(M.adjoint m))‖ ≤
        4 * ‖-(M.adjoint m)‖ / ‖m‖ := normalProjectionDerivative_norm_le m _ hm
    _ ≤ 4 * (‖M‖ * ‖m‖) / ‖m‖ := by gcongr
    _ = 4 * ‖M‖ := by field_simp

end EulerMovingNormalProjection
