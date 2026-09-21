/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Contractivity of integration against a positive operator kernel (L4.2d support)

If `K t` is a positive operator for `t ∈ (a, b]` and `∫ t in a..b, K t = c • 1`, then integrating a
bounded scalar weight `f` against `K` is contractive up to the mass `c`:
`‖∫ t in a..b, f t • K t‖ ≤ c * sup ‖f‖`.  This is the bridge from the pointwise positivity of the
double-layer kernel (`DoubleLayer.lean`, `PositiveIntegral.lean`) to the sharp symmetrized bound of
Crouzeix–Palencia: the raw double-layer kernel has total mass `4π` (`DoubleLayerIntegral.lean`), so
after the `1 / (2π)` normalization of the contour integral the estimate carries the factor `2`.

Route: for a positive `K`, `⟪x, K y⟫ = ⟪√K x, √K y⟫`, hence
`‖⟪x, K y⟫‖ ≤ √(re ⟪x, K x⟫) * √(re ⟪y, K y⟫)` (Cauchy–Schwarz for the positive form); the weighted
AM–GM inequality `√A * √B ≤ (s * A + B / s) / 2` turns this into an integrable majorant with integral
`M * ((s * c * ‖x‖ ^ 2 + c * ‖y‖ ^ 2 / s) / 2)`; optimizing `s = ‖y‖ / ‖x‖` gives
`‖⟪x, T y⟫‖ ≤ c * M * ‖x‖ * ‖y‖`, and an operator with such matrix coefficients has norm at most
`c * M`.

## Main declarations

* `norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg` — Cauchy–Schwarz for a positive operator, via the
  continuous-functional-calculus square root (`inner_apply_eq_inner_cfcSqrt_of_nonneg`).
* `opNorm_le_of_forall_norm_inner_le` — an operator norm bound from a matrix-coefficient bound.
* `sqrt_mul_sqrt_le_of_pos`, `norm_inner_le_of_forall_pos_le` — the scalar AM–GM step and its
  optimization.
* `norm_intervalIntegral_smul_le_of_ae_nonneg` — the contractivity bound
  `‖∫ t in a..b, f t • K t‖ ≤ c * M` (hypotheses almost everywhere on `Ioc a b`), and its
  pointwise form `norm_intervalIntegral_smul_le_of_nonneg`.

Requires `[CompleteSpace E]` for the square root of a positive operator and for the operator-valued
Bochner integrals.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- For a positive operator `K`, `⟪x, K y⟫ = ⟪√K x, √K y⟫`. -/
theorem inner_apply_eq_inner_cfcSqrt_of_nonneg {K : E →L[ℂ] E} (hK : 0 ≤ K) (x y : E) :
    ⟪x, K y⟫_ℂ = ⟪CFC.sqrt K x, CFC.sqrt K y⟫_ℂ := by
  have hS : IsSelfAdjoint (CFC.sqrt K) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg K)
  calc ⟪x, K y⟫_ℂ = ⟪x, (CFC.sqrt K * CFC.sqrt K) y⟫_ℂ := by rw [CFC.sqrt_mul_sqrt_self K hK]
    _ = ⟪x, adjoint (CFC.sqrt K) (CFC.sqrt K y)⟫_ℂ := by rw [mul_apply_eq_comp, hS.adjoint_eq]
    _ = ⟪CFC.sqrt K x, CFC.sqrt K y⟫_ℂ := adjoint_inner_right _ _ _

/-- For a positive operator `K`, `re ⟪x, K x⟫ = ‖√K x‖ ^ 2`. -/
theorem re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg {K : E →L[ℂ] E} (hK : 0 ≤ K) (x : E) :
    RCLike.re ⟪x, K x⟫_ℂ = ‖CFC.sqrt K x‖ ^ 2 := by
  rw [inner_apply_eq_inner_cfcSqrt_of_nonneg hK, inner_self_eq_norm_sq]

/-- Cauchy–Schwarz for a positive operator:
`‖⟪x, K y⟫‖ ≤ √(re ⟪x, K x⟫) * √(re ⟪y, K y⟫)`. -/
theorem norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg {K : E →L[ℂ] E} (hK : 0 ≤ K) (x y : E) :
    ‖⟪x, K y⟫_ℂ‖ ≤
      Real.sqrt (RCLike.re ⟪x, K x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, K y⟫_ℂ) := by
  rw [inner_apply_eq_inner_cfcSqrt_of_nonneg hK x y,
    re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg hK x,
    re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg hK y,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _

omit [CompleteSpace E] in
/-- An operator whose matrix coefficients are bounded by `M * ‖x‖ * ‖y‖` has norm at most `M`. -/
theorem opNorm_le_of_forall_norm_inner_le {T : E →L[ℂ] E} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x y : E, ‖⟪x, T y⟫_ℂ‖ ≤ M * ‖x‖ * ‖y‖) : ‖T‖ ≤ M := by
  refine opNorm_le_bound T hM fun y => ?_
  by_cases hy : T y = 0
  · rw [hy, norm_zero]; positivity
  · have hpos : 0 < ‖T y‖ := norm_pos_iff.mpr hy
    have h1 : ‖T y‖ ^ 2 ≤ ‖⟪T y, T y⟫_ℂ‖ := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; exact RCLike.re_le_norm _
    have h2 : ‖T y‖ * ‖T y‖ ≤ ‖T y‖ * (M * ‖y‖) := by
      calc ‖T y‖ * ‖T y‖ = ‖T y‖ ^ 2 := (sq _).symm
        _ ≤ ‖⟪T y, T y⟫_ℂ‖ := h1
        _ ≤ M * ‖T y‖ * ‖y‖ := h (T y) y
        _ = ‖T y‖ * (M * ‖y‖) := by ring
    exact le_of_mul_le_mul_left h2 hpos

/-- Weighted AM–GM: `√A * √B ≤ (s * A + B / s) / 2` for `A, B ≥ 0` and `s > 0`. -/
theorem sqrt_mul_sqrt_le_of_pos {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < s) :
    Real.sqrt A * Real.sqrt B ≤ (s * A + B / s) / 2 := by
  have h1 : Real.sqrt A * Real.sqrt B = Real.sqrt (s * A) * Real.sqrt (B / s) := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [h1]
  have hu := Real.sq_sqrt (by positivity : 0 ≤ s * A)
  have hv := Real.sq_sqrt (by positivity : 0 ≤ B / s)
  nlinarith only [sq_nonneg (Real.sqrt (s * A) - Real.sqrt (B / s)), hu, hv]

omit [CompleteSpace E] in
/-- If `‖⟪x, T y⟫‖ ≤ M * ((s * (c ‖x‖²) + c ‖y‖² / s) / 2)` for every `s > 0`, then
`‖⟪x, T y⟫‖ ≤ c * M * ‖x‖ * ‖y‖`. -/
theorem norm_inner_le_of_forall_pos_le {T : E →L[ℂ] E} {c M : ℝ} (x y : E)
    (h : ∀ s : ℝ, 0 < s →
      ‖⟪x, T y⟫_ℂ‖ ≤ M * ((s * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / s) / 2)) :
    ‖⟪x, T y⟫_ℂ‖ ≤ c * M * ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · rw [hx, inner_zero_left, norm_zero, norm_zero, mul_zero, zero_mul]
  by_cases hy : y = 0
  · rw [hy, map_zero, inner_zero_right, norm_zero, norm_zero, mul_zero]
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hkey : (‖y‖ / ‖x‖ * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / (‖y‖ / ‖x‖)) / 2 = c * ‖x‖ * ‖y‖ := by
    field_simp
    ring
  calc ‖⟪x, T y⟫_ℂ‖ ≤ M * ((‖y‖ / ‖x‖ * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / (‖y‖ / ‖x‖)) / 2) :=
        h (‖y‖ / ‖x‖) (by positivity)
    _ = c * M * ‖x‖ * ‖y‖ := by rw [hkey]; ring

/-- **Contractivity of integration against a normalized positive operator kernel.**
If `K t ≥ 0` almost everywhere on `Ioc a b`, `∫ t in a..b, K t = c • 1`, and `‖f t‖ ≤ M` almost
everywhere on `Ioc a b`, then `‖∫ t in a..b, f t • K t‖ ≤ c * M`. -/
theorem norm_intervalIntegral_smul_le_of_ae_nonneg {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ}
    {a b c M : ℝ} (hab : a ≤ b) (hK : IntervalIntegrable K volume a b)
    (hfK : IntervalIntegrable (fun t => f t • K t) volume a b)
    (hpos : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), 0 ≤ K t)
    (hnorm : ∫ t in a..b, K t = c • (1 : E →L[ℂ] E))
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hf : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖f t‖ ≤ M) :
    ‖∫ t in a..b, f t • K t‖ ≤ c * M := by
  rw [intervalIntegral.integral_of_le hab] at hnorm ⊢
  have hK' : IntegrableOn K (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hK
  have hfK' : IntegrableOn (fun t => f t • K t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hfK
  -- the quadratic forms `t ↦ re ⟪x, K t x⟫` are integrable with integral `c * ‖x‖ ^ 2`
  have hKx : ∀ x : E, Integrable (fun t => K t x) (volume.restrict (Set.Ioc a b)) := fun x =>
    (ContinuousLinearMap.apply ℂ E x).integrable_comp hK'
  have hgint : ∀ x : E,
      Integrable (fun t => RCLike.re ⟪x, K t x⟫_ℂ) (volume.restrict (Set.Ioc a b)) := fun x =>
    ((hKx x).const_inner x).re
  have hgval : ∀ x : E, ∫ t in Set.Ioc a b, RCLike.re ⟪x, K t x⟫_ℂ = c * ‖x‖ ^ 2 := by
    intro x
    rw [integral_re ((hKx x).const_inner x), integral_inner (hKx x),
      ← ContinuousLinearMap.integral_apply hK', hnorm, smul_apply, one_apply_eq_self,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq]
  refine opNorm_le_of_forall_norm_inner_le (mul_nonneg hc hM) fun x y => ?_
  refine norm_inner_le_of_forall_pos_le x y fun s hs => ?_
  have hΦy : Integrable (fun t => (f t • K t) y) (volume.restrict (Set.Ioc a b)) :=
    (ContinuousLinearMap.apply ℂ E y).integrable_comp hfK'
  rw [ContinuousLinearMap.integral_apply hfK', ← integral_inner hΦy]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖⟪x, (f t • K t) y⟫_ℂ‖ ≤
        M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2) := by
    filter_upwards [hpos, hf] with t hKt hft
    have hKt' : IsPositive (K t) := (nonneg_iff_isPositive _).mp hKt
    rw [smul_apply, inner_smul_right, norm_mul]
    calc ‖f t‖ * ‖⟪x, K t y⟫_ℂ‖
        ≤ M * (Real.sqrt (RCLike.re ⟪x, K t x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, K t y⟫_ℂ)) :=
          mul_le_mul hft (norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg hKt x y)
            (norm_nonneg _) hM
      _ ≤ M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2) :=
          mul_le_mul_of_nonneg_left
            (sqrt_mul_sqrt_le_of_pos (hKt'.re_inner_nonneg_right x)
              (hKt'.re_inner_nonneg_right y) hs) hM
  have hrhs : Integrable
      (fun t => M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2))
      (volume.restrict (Set.Ioc a b)) :=
    ((((hgint x).const_mul s).add ((hgint y).div_const s)).div_const 2).const_mul M
  calc ∫ t in Set.Ioc a b, ‖⟪x, (f t • K t) y⟫_ℂ‖
      ≤ ∫ t in Set.Ioc a b,
          M * ((s * RCLike.re ⟪x, K t x⟫_ℂ + RCLike.re ⟪y, K t y⟫_ℂ / s) / 2) :=
        integral_mono_ae (hΦy.const_inner x).norm hrhs hpt
    _ = M * ((s * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / s) / 2) := by
        rw [integral_const_mul, integral_div,
          integral_add ((hgint x).const_mul s) ((hgint y).div_const s),
          integral_const_mul, integral_div, hgval x, hgval y]

/-- The contractivity bound with pointwise hypotheses on `Ioc a b`. -/
theorem norm_intervalIntegral_smul_le_of_nonneg {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {a b c M : ℝ}
    (hab : a ≤ b) (hK : IntervalIntegrable K volume a b)
    (hfK : IntervalIntegrable (fun t => f t • K t) volume a b)
    (hpos : ∀ t ∈ Set.Ioc a b, 0 ≤ K t)
    (hnorm : ∫ t in a..b, K t = c • (1 : E →L[ℂ] E))
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc a b, ‖f t‖ ≤ M) :
    ‖∫ t in a..b, f t • K t‖ ≤ c * M :=
  norm_intervalIntegral_smul_le_of_ae_nonneg hab hK hfK
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hpos t ht) hnorm hc hM
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hf t ht)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
