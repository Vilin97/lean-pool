/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatKernelBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothParameterIntegral
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section

/-!
# The transformed integral for a terminal flat primitive

The change of variables is `u = x / sqrt (1 + x² t)` for `x > 0`.
Natural powers of the square root encode the real power `(j - 3) / 2`
without truncating subtraction in the natural numbers.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ContDiff
open NavierStokes.FlatCutoff NavierStokes.FlatPrimitive

namespace NavierStokes.FlatPrimitiveFactor

def denominator (x t : ℝ) : ℝ := Real.sqrt (1 + x ^ 2 * t)

def coordinate (x t : ℝ) : ℝ := x / denominator x t

def kernel (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (-c * t) *
    (denominator x t ^ j / denominator x t ^ 3) * b (coordinate x t)

def factor (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), kernel c j b x t

theorem denominator_inner_pos (x : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 < 1 + x ^ 2 * t := by
  have := mul_nonneg (sq_nonneg x) ht
  linarith

theorem denominator_pos (x : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 < denominator x t :=
  Real.sqrt_pos.mpr (denominator_inner_pos x ht)

theorem denominator_sq (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    denominator x t ^ 2 = 1 + x ^ 2 * t :=
  Real.sq_sqrt (denominator_inner_pos x ht).le

/-- The square-root notation is exactly the real power appearing in the
substitution formula, including when `j < 3`. -/
theorem denominator_ratio_eq_rpow (j : ℕ) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    denominator x t ^ j / denominator x t ^ 3 =
      (1 + x ^ 2 * t) ^ (((j : ℝ) - 3) / 2) := by
  have ha := denominator_inner_pos x ht
  rw [denominator, Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast ((1 + x ^ 2 * t) ^ (1 / 2 : ℝ)) j,
    ← Real.rpow_natCast ((1 + x ^ 2 * t) ^ (1 / 2 : ℝ)) 3]
  rw [← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le, ← Real.rpow_sub ha]
  congr 1
  norm_num
  ring

theorem coordinate_pos {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) : 0 < coordinate x t :=
  div_pos hx (denominator_pos x ht)

theorem coordinate_hasDerivAt (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (coordinate x) (-(x ^ 3 / (2 * denominator x t ^ 3))) t := by
  have ha : HasDerivAt (fun s : ℝ => 1 + x ^ 2 * s) (x ^ 2) t := by
    simpa using ((hasDerivAt_id t).const_mul (x ^ 2)).const_add 1
  have hd : HasDerivAt (denominator x) (x ^ 2 / (2 * denominator x t)) t :=
    ha.sqrt (denominator_inner_pos x ht).ne'
  have hu := (hasDerivAt_const t x).div hd (denominator_pos x ht).ne'
  convert! hu using 1
  field_simp ; ring

theorem coordinate_mem_Ioo {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    coordinate x t ∈ Ioo 0 x := by
  have hinner : 1 < 1 + x ^ 2 * t := by
    have := mul_pos (sq_pos_of_pos hx) ht
    linarith
  have hd : 1 < denominator x t := by
    simpa only [denominator, Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      hinner
  constructor
  · exact coordinate_pos hx ht.le
  · apply (div_lt_iff₀ (denominator_pos x ht.le)).mpr
    nlinarith

theorem coordinate_injOn {x : ℝ} (hx : 0 < x) : InjOn (coordinate x) (Ioi 0) := by
  intro t ht s hs h
  have hcross := (div_eq_div_iff (denominator_pos x ht.le).ne'
    (denominator_pos x hs.le).ne').mp h
  have hd : denominator x t = denominator x s := (mul_left_cancel₀ hx.ne' hcross).symm
  have hsq := congrArg (fun a : ℝ => a ^ 2) hd
  rw [denominator_sq x ht.le, denominator_sq x hs.le] at hsq
  have hmul : x ^ 2 * t = x ^ 2 * s := by linarith
  exact mul_left_cancel₀ (pow_ne_zero 2 hx.ne') hmul

theorem coordinate_image {x : ℝ} (hx : 0 < x) : coordinate x '' Ioi 0 = Ioo 0 x := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact coordinate_mem_Ioo hx ht
  · intro hu
    let t : ℝ := (x ^ 2 - u ^ 2) / (x ^ 2 * u ^ 2)
    have ht : 0 < t := by
      apply div_pos
      · nlinarith [hu.1, hu.2]
      · exact mul_pos (sq_pos_of_pos hx) (sq_pos_of_pos hu.1)
    refine ⟨t, ht, ?_⟩
    have ha : 1 + x ^ 2 * t = (x / u) ^ 2 := by
      dsimp [t]
      field_simp [hx.ne', hu.1.ne'] ; ring
    have hd : denominator x t = x / u := by
      rw [denominator, ha, Real.sqrt_sq (div_nonneg hx.le hu.1.le)]
    rw [coordinate, hd]
    field_simp

theorem edge_coordinate (c : ℝ) {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    edge c (coordinate x t) = edge c x * Real.exp (-c * t) := by
  rw [edge_of_pos c (coordinate_pos hx ht), edge_of_pos c hx, ← Real.exp_add]
  congr 1
  calc
    -c / coordinate x t ^ 2 = (-c / x ^ 2) * denominator x t ^ 2 := by
      dsimp [coordinate]
      field_simp
    _ = (-c / x ^ 2) * (1 + x ^ 2 * t) := by rw [denominator_sq x ht]
    _ = -c / x ^ 2 + -c * t := by field_simp ; ring

theorem transformed_integrand (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    |-(x ^ 3 / (2 * denominator x t ^ 3))| *
        integrand c j b (coordinate x t) =
      scale c j x * kernel c j b x t := by
  have hd : 0 < denominator x t := denominator_pos x ht
  rw [abs_neg, abs_of_pos (div_pos (pow_pos hx 3) (mul_pos (by norm_num) (pow_pos hd 3)))]
  simp only [integrand, scale, kernel, edge_coordinate c hx ht]
  dsimp [coordinate]
  rw [div_pow]
  field_simp

/-- Exact change of variables for the actual primitive. The Jacobian theorem
supplies the equality even before separate integrability estimates are used. -/
theorem primitive_eq_scale_mul_factor (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x : ℝ} (hx : 0 < x) :
    primitive c j b x = scale c j x * factor c j b x := by
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (coordinate_hasDerivAt x ht.le).hasDerivWithinAt)
    (coordinate_injOn hx) (integrand c j b)
  rw [coordinate_image hx] at hchange
  rw [primitive, intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo,
    hchange]
  calc
    (∫ t in Ioi (0 : ℝ), |-(x ^ 3 / (2 * denominator x t ^ 3))| •
        integrand c j b (coordinate x t)) =
        ∫ t in Ioi (0 : ℝ), scale c j x * kernel c j b x t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact transformed_integrand c j b hx ht.le
    _ = scale c j x * factor c j b x := integral_const_mul _ _

/-- The transformed integral is the normalized primitive for positive `x`. -/
theorem factor_eq_normalized_primitive (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x : ℝ} (hx : 0 < x) :
    factor c j b x = primitive c j b x / scale c j x := by
  have hs : scale c j x ≠ 0 := (scale_pos c j hx).ne'
  rw [primitive_eq_scale_mul_factor c j b hx]
  field_simp [hs]

theorem kernel_at_zero (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (t : ℝ) :
    kernel c j b 0 t = (b 0 / 2) * Real.exp (-c * t) := by
  simp [kernel, denominator, coordinate]
  ring

/-- The transformed integral has the predicted endpoint value directly,
without passing to the normalized primitive's limit. -/
theorem factor_at_zero {c : ℝ} (hc : 0 < c) (j : ℕ) (b : ℝ → ℝ) :
    factor c j b 0 = b 0 / (2 * c) := by
  simp only [factor, kernel_at_zero]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hc) 0]
  simp
  ring

/-- Every fixed polynomial majorant is integrable against the decaying
exponential on the transformed half-line. -/
theorem polynomial_exp_integrable {c : ℝ} (hc : 0 < c) (N : ℕ) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ N * Real.exp (-c * t)) (Ioi 0) := by
  have hc2 : 0 < c / 2 := half_pos hc
  have hshift : Tendsto (fun t : ℝ => 1 + t) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [eventually_ge_atTop r] with t ht
    linarith
  have hbase : Tendsto (fun t : ℝ => (1 + t) ^ N * Real.exp (-(c / 2) * (1 + t)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) (c / 2) hc2).comp hshift
  have hratio : Tendsto
      (fun t : ℝ => ((1 + t) ^ N * Real.exp (-c * t)) / Real.exp (-(c / 2) * t))
      atTop (𝓝 0) := by
    have hh := hbase.mul_const (Real.exp (c / 2))
    simp only [zero_mul] at hh
    convert! hh using 1
    funext t
    rw [mul_div_assoc, ← Real.exp_sub, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have ho : (fun t : ℝ => (1 + t) ^ N * Real.exp (-c * t)) =o[atTop]
      (fun t : ℝ => Real.exp (-(c / 2) * t)) :=
    Asymptotics.isLittleO_of_tendsto (fun t ht => (Real.exp_ne_zero _ ht).elim) hratio
  apply integrable_of_isBigO_exp_neg hc2 _ ho.isBigO
  exact (((continuous_const.add continuous_id).pow N).mul
    ((continuous_const.mul continuous_id).rexp)).continuousOn

theorem const_polynomial_exp_integrable {c : ℝ} (hc : 0 < c) (C : ℝ) (N : ℕ) :
    IntegrableOn (fun t : ℝ => C * (1 + t) ^ N * Real.exp (-c * t)) (Ioi 0) := by
  simpa only [IntegrableOn, mul_assoc] using (polynomial_exp_integrable hc N).const_mul C

theorem kernel_ae_contDiff (c : ℝ) (j : ℕ) {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ContDiff ℝ ∞ (fun x => kernel c j b x t) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact NavierStokes.FlatKernelBounds.kernel_contDiff_x hb c j ht.le

theorem kernel_iteratedDeriv_measurable (c : ℝ) (j : ℕ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (n : ℕ) (x : ℝ) :
    AEStronglyMeasurable (fun t => iteratedDeriv n (fun y => kernel c j b y t) x)
      (volume.restrict (Ioi 0)) := by
  have hcont : ContinuousOn
      (fun t => iteratedDeriv n (fun y => kernel c j b y t) x) (Ioi 0) :=
    (NavierStokes.FlatKernelBounds.kernel_iteratedDeriv_continuousOn_t hb c j n x).mono
      Ioi_subset_Ici_self
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-- All hypotheses for dominated differentiation come from actual kernel
derivatives and polynomial-exponential bounds on bounded parameter sets. -/
theorem kernel_locallyDominated {c : ℝ} (hc : 0 < c) (j : ℕ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) :
    NavierStokes.SmoothParameterIntegral.LocallyDominatedDeriv
      (kernel c j b) (volume.restrict (Ioi 0)) := by
  intro n x
  have hR : 0 ≤ |x| + 1 := by positivity
  obtain ⟨C, N, _hC, hbound⟩ :=
    NavierStokes.FlatKernelBounds.kernel_iteratedDeriv_bound hb c j n hR
  refine ⟨1, by norm_num, (fun t => C * (1 + t) ^ N * Real.exp (-c * t)),
    const_polynomial_exp_integrable hc C N, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  intro y hy
  have hdist : |y - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
  have hyR : |y| ≤ |x| + 1 := by
    have htri : |y| ≤ |y - x| + |x| := by
      simpa only [sub_add_cancel] using abs_add_le (y - x) x
    linarith
  simpa only [Real.norm_eq_abs, kernel, FlatKernelBounds.kernel, coordinate, denominator,
    FlatKernelBounds.coordinate, FlatKernelBounds.denominator] using hbound y t hyR ht.le

/-- The concrete transformed integral is smooth on all of `ℝ`, including
across the endpoint of the original primitive. -/
theorem factor_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (factor c j b) :=
  NavierStokes.SmoothParameterIntegral.contDiff_integral_of_iteratedDeriv
    (kernel_ae_contDiff c j hb) (kernel_iteratedDeriv_measurable c j hb)
    (kernel_locallyDominated hc j hb)

theorem factor_iteratedDeriv {c : ℝ} (hc : 0 < c) (j : ℕ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (factor c j b) x =
      ∫ t in Ioi (0 : ℝ), iteratedDeriv n (fun y => kernel c j b y t) x :=
  NavierStokes.SmoothParameterIntegral.iteratedDeriv_integral
    (kernel_ae_contDiff c j hb) (kernel_iteratedDeriv_measurable c j hb)
    (kernel_locallyDominated hc j hb) n x

/-- Full smooth factorization of the actual terminal primitive, with its
endpoint value fixed by the coefficient. The smooth factor is constructed
as an improper integral rather than assumed. -/
theorem exists_smooth_factor {c : ℝ} (hc : 0 < c) (j : ℕ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ F 0 = b 0 / (2 * c) ∧
      ∀ x : ℝ, 0 ≤ x → primitive c j b x = scale c j x * F x := by
  refine ⟨factor c j b, factor_contDiff hc j hb, factor_at_zero hc j b, ?_⟩
  intro x hx
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    simp
  · exact primitive_eq_scale_mul_factor c j b hpos

theorem integral_exp_eq_primitive (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ u in (0 : ℝ)..x, (Real.exp (-c / u ^ 2) / u ^ j) * b u) =
      primitive c j b x := by
  rw [primitive, intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hx]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  simp only [integrand, edge_of_pos c hu.1]

theorem scale_eq_rpow (c : ℝ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    scale c j x = Real.exp (-c / x ^ 2) * x ^ (3 - (j : ℝ)) := by
  rw [scale, edge_of_pos c hx]
  calc
    (Real.exp (-c / x ^ 2) / x ^ j) * x ^ 3 =
        Real.exp (-c / x ^ 2) * (x ^ 3 / x ^ j) := by ring
    _ = _ := by
      rw [← Real.rpow_natCast x 3, ← Real.rpow_natCast x j, ← Real.rpow_sub hx]
      norm_num

/-- The manuscript's scalar primitive factorization in its original
exponential and real-power notation, with a genuine smooth extension. -/
theorem exists_smooth_factor_original {c : ℝ} (hc : 0 < c) (j : ℕ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ F 0 = b 0 / (2 * c) ∧
      ∀ x : ℝ, 0 < x →
        (∫ u in (0 : ℝ)..x, (Real.exp (-c / u ^ 2) / u ^ j) * b u) =
          Real.exp (-c / x ^ 2) * x ^ (3 - (j : ℝ)) * F x := by
  refine ⟨factor c j b, factor_contDiff hc j hb, factor_at_zero hc j b, ?_⟩
  intro x hx
  rw [integral_exp_eq_primitive c j b hx.le,
    primitive_eq_scale_mul_factor c j b hx, scale_eq_rpow c j hx]

theorem factor_sqrt_contDiffAt_zero {c : ℝ} (hc : 0 < c) (j : ℕ) {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hb0 : 0 < b 0) :
    ContDiffAt ℝ ∞ (fun x => Real.sqrt (factor c j b x)) 0 := by
  apply (factor_contDiff hc j hb).contDiffAt.sqrt
  rw [factor_at_zero hc j b]
  exact (div_pos hb0 (mul_pos (by norm_num) hc)).ne'

end NavierStokes.FlatPrimitiveFactor
