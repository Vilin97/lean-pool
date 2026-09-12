/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCutoff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual primitives of exponential-flat edges

This file studies the integral of `exp (-c / u²) * u⁻ʲ * b u` from zero.
The integrand uses the smooth zero extension from `FlatCutoff`.

In particular, smoothness of the primitive is distinct from smoothness of its
quotient by an exponentially small factor. The statements below keep those
obligations separate.
-/

@[expose] public section


noncomputable section

open Filter Topology Set MeasureTheory Polynomial
open scoped ContDiff
open NavierStokes.FlatCutoff

namespace NavierStokes.FlatPrimitive

/-- Integrand, given by `(edge c x / x ^ j) * b x`. -/
def integrand (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  (edge c x / x ^ j) * b x

/-- Primitive, given by `∫ u in (0 : ℝ)..x, integrand c j b u`. -/
def primitive (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, integrand c j b u

/-- The expected factor `exp(-c/x²) x^(3-j)`, written without truncated
natural subtraction and defined smoothly at zero. -/
def scale (c : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (edge c x / x ^ j) * x ^ 3

theorem integrand_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} {n : ℕ∞} (hb : ContDiff ℝ n b) :
    ContDiff ℝ n (integrand c j b) :=
  (edge_div_pow_contDiff hc j).mul hb

theorem integrand_continuous {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) : Continuous (integrand c j b) :=
  ((edge_div_pow_contDiff hc j : ContDiff ℝ ∞ _).continuous).mul hb

theorem primitive_hasDerivAt {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) (x : ℝ) :
    HasDerivAt (primitive c j b) (integrand c j b x) x := by
  have hf := integrand_continuous hc j hb
  exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem primitive_deriv {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) :
    deriv (primitive c j b) = integrand c j b := by
  funext x
  exact (primitive_hasDerivAt hc j hb x).deriv

theorem primitive_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (primitive c j b) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · exact fun x => (primitive_hasDerivAt hc j hb.continuous x).differentiableAt
  · rw [primitive_deriv hc j hb.continuous]
    exact integrand_contDiff hc j hb

@[simp] theorem primitive_zero (c : ℝ) (j : ℕ) (b : ℝ → ℝ) :
    primitive c j b 0 = 0 := by simp [primitive]

theorem primitive_of_nonpos (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x : ℝ} (hx : x ≤ 0) : primitive c j b x = 0 := by
  unfold primitive
  calc
    (∫ u in (0 : ℝ)..x, integrand c j b u) = ∫ _u in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : u ≤ 0 := (uIcc_of_ge hx ▸ hu).2
      simp [integrand, edge_of_nonpos c hu0]
    _ = 0 := intervalIntegral.integral_zero

/-- Smoothness and equality to zero on a closed half-line imply that every
actual derivative vanishes there. This does not assume the derivative values. -/
theorem iteratedDeriv_zero_on_nonpos {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (m : ℕ) :
    ∀ x : ℝ, x ≤ 0 → iteratedDeriv m f x = 0 := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using hzero
  | succ m ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    apply (uniqueDiffOn_Iic x x (mem_Iic.mpr le_rfl)).eq_deriv (Iic x)
      ((hf.differentiable_iteratedDeriv m (by
          exact_mod_cast ENat.natCast_lt_top m) x).hasDerivAt.hasDerivWithinAt)
    exact (hasDerivWithinAt_const x (Iic x) (0 : ℝ)).congr_of_mem
      (fun y hy => ih y (hy.trans hx)) (mem_Iic.mpr le_rfl)

theorem primitive_iteratedDeriv_zero {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (m : ℕ) :
    iteratedDeriv m (primitive c j b) 0 = 0 :=
  iteratedDeriv_zero_on_nonpos (primitive_contDiff hc j hb)
    (fun _x hx => primitive_of_nonpos c j b hx) m 0 le_rfl

/-- Exact fundamental theorem of calculus for the explicit derivative
polynomial family constructed in `FlatCutoff`. -/
theorem integral_derivativePolynomial {c : ℝ} (hc : 0 < c) (p : ℝ[X]) (x : ℝ) :
    (∫ u in (0 : ℝ)..x, polynomialEdge c (derivativePolynomial c p) u) =
      polynomialEdge c p x := by
  have hcont : Continuous (polynomialEdge c (derivativePolynomial c p)) :=
    (polynomialEdge_contDiff hc _ : ContDiff ℝ ∞ _).continuous
  simpa only [polynomialEdge_zero, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _hu => polynomialEdge_hasDerivAt hc p u) (hcont.intervalIntegrable 0 x)

theorem edge_hasDerivAt {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (edge c) (2 * c * edge c x / x ^ 3) x := by
  have h := polynomialEdge_hasDerivAt hc (1 : ℝ[X]) x
  rw [polynomialEdge_one] at h
  convert! h using 1
  simp [polynomialEdge, derivativePolynomial, div_eq_mul_inv, inv_pow]
  ring

theorem scale_contDiff {c : ℝ} (hc : 0 < c) (j : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (scale c j) :=
  (edge_div_pow_contDiff hc j).mul (contDiff_id.pow 3)

@[simp] theorem scale_zero (c : ℝ) (j : ℕ) : scale c j 0 = 0 := by simp [scale]

theorem scale_hasDerivAt {c : ℝ} (hc : 0 < c) (j : ℕ) (x : ℝ) :
    HasDerivAt (scale c j)
      ((edge c x / x ^ j) * (2 * c + (3 - (j : ℝ)) * x ^ 2)) x := by
  unfold scale
  by_cases hx : x = 0
  · subst x
    have h := (((edge_div_pow_contDiff hc j : ContDiff ℝ ∞ _).differentiable
      (by simp) 0).hasDerivAt).fun_mul ((hasDerivAt_id (0 : ℝ)).fun_pow 3)
    simpa [scale] using h
  · have h := (((edge_hasDerivAt hc x).fun_div ((hasDerivAt_id x).fun_pow j)
      (pow_ne_zero j hx)).fun_mul ((hasDerivAt_id x).fun_pow 3))
    simp only [id_eq] at h
    convert! h using 1
    cases j with
    | zero => simp; field_simp
    | succ j =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat, mul_one, pow_succ]
      field_simp; ring

/-- The coefficient produced when differentiating `scale c j * a`.
This is an explicit differential expression in the chosen smooth factor. -/
def sourceCoefficient (c : ℝ) (j : ℕ) (a : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * c + (3 - (j : ℝ)) * x ^ 2) * a x + x ^ 3 * deriv a x

theorem sourceCoefficient_contDiff (c : ℝ) (j : ℕ) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (sourceCoefficient c j a) := by
  have hd : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
  exact ((contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).mul ha).add
    ((contDiff_id.pow 3).mul hd)

/-- A genuine primitive factorization for the explicit family of coefficients
obtained from any smooth factor `a`, proved by the fundamental theorem of
calculus rather than assumed as a representation hypothesis. -/
theorem primitive_sourceCoefficient {c : ℝ} (hc : 0 < c) (j : ℕ)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (x : ℝ) :
    primitive c j (sourceCoefficient c j a) x = scale c j x * a x := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun y => scale c j y * a y)
      (integrand c j (sourceCoefficient c j a) u) u := by
    intro u
    convert! (scale_hasDerivAt hc j u).mul
      ((ha.differentiable (by simp) u).hasDerivAt) using 1
    simp only [integrand, sourceCoefficient, scale]
    ring
  have hcont := integrand_continuous hc j (sourceCoefficient_contDiff c j ha).continuous
  simpa only [primitive, scale_zero, zero_mul, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _hu => hderiv u)
      (hcont.intervalIntegrable 0 x)

/-- An exact integration-by-parts recurrence for every smooth coefficient.
The new coefficient is `(3-j) x² b + x³ b'`, which vanishes to at least
second order at the endpoint. -/
theorem primitive_recurrence {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (x : ℝ) :
    (2 * c) * primitive c j b x =
      scale c j x * b x - primitive c j (sourceCoefficient 0 j b) x := by
  have hf := integrand_continuous hc j hb.continuous
  have hr := integrand_continuous hc j (sourceCoefficient_contDiff 0 j hb).continuous
  have hcf : Continuous (fun u => (2 * c) * integrand c j b u) := continuous_const.mul hf
  have hsplit : primitive c j (sourceCoefficient c j b) x =
      (2 * c) * primitive c j b x + primitive c j (sourceCoefficient 0 j b) x := by
    unfold primitive
    calc
      (∫ u in (0 : ℝ)..x, integrand c j (sourceCoefficient c j b) u) =
          ∫ u in (0 : ℝ)..x,
            (2 * c) * integrand c j b u + integrand c j (sourceCoefficient 0 j b) u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        simp only [integrand, sourceCoefficient]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hcf.intervalIntegrable 0 x)
          (hr.intervalIntegrable 0 x), intervalIntegral.integral_const_mul]
  rw [primitive_sourceCoefficient hc j hb x] at hsplit
  linarith

/-- An exact constant-coefficient case of the claimed terminal factorization:
for `j = 3`, the remaining smooth factor is the constant `1 / (2c)`. -/
theorem primitive_three_one {c : ℝ} (hc : 0 < c) (x : ℝ) :
    primitive c 3 (fun _ => 1) x = edge c x / (2 * c) := by
  have hc2 : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hc.ne'
  have hderiv : ∀ u : ℝ, HasDerivAt (fun y => edge c y / (2 * c))
      (integrand c 3 (fun _ => 1) u) u := by
    intro u
    convert! (edge_hasDerivAt hc u).div_const (2 * c) using 1
    simp only [integrand, mul_one]
    rw [div_div, mul_comm (u ^ 3) (2 * c), mul_div_mul_left _ _ hc2]
  have hcont := integrand_continuous hc 3 (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  simpa only [primitive, edge_zero, zero_div, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _hu => hderiv u)
      (hcont.intervalIntegrable 0 x)

/-- The natural primitive scale is strictly positive inside the active edge. -/
theorem scale_pos (c : ℝ) (j : ℕ) {x : ℝ} (hx : 0 < x) : 0 < scale c j x :=
  mul_pos (div_pos (edge_pos c hx) (pow_pos hx j)) (pow_pos hx 3)

/-- The leading quotient limit for an arbitrary continuous coefficient.
This is a genuine asymptotic statement about the integral; smoothness of the
quotient to all orders is a stronger assertion. -/
theorem primitive_normalized_tendsto {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) :
    Tendsto (fun x => primitive c j b x / scale c j x) (𝓝[>] 0)
      (𝓝 (b 0 / (2 * c))) := by
  have h2c : 0 < 2 * c := mul_pos (by norm_num) hc
  have hDcont : Continuous (fun x : ℝ => 2 * c + (3 - (j : ℝ)) * x ^ 2) :=
    continuous_const.add (continuous_const.mul (continuous_id.pow 2))
  have hD : Tendsto (fun x : ℝ => 2 * c + (3 - (j : ℝ)) * x ^ 2)
      (𝓝[>] 0) (𝓝 (2 * c)) := by
    simpa using (hDcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hDpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < 2 * c + (3 - (j : ℝ)) * x ^ 2 :=
    hD.eventually (lt_mem_nhds h2c)
  have hF : Tendsto (primitive c j b) (𝓝[>] 0) (𝓝 0) := by
    simpa only [primitive_zero] using
      ((primitive_hasDerivAt hc j hb 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hS : Tendsto (scale c j) (𝓝[>] 0) (𝓝 0) := by
    simpa only [scale_zero] using
      (((scale_contDiff hc j : ContDiff ℝ ∞ _).continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
  refine HasDerivAt.lhopital_zero_nhdsGT
    (Eventually.of_forall fun x => primitive_hasDerivAt hc j hb x)
    (Eventually.of_forall fun x => scale_hasDerivAt hc j x) ?_ hF hS ?_
  · filter_upwards [self_mem_nhdsWithin, hDpos] with x hx hdx
    exact (mul_pos (div_pos (edge_pos c hx) (pow_pos hx j)) hdx).ne'
  · refine (((hb.tendsto 0).mono_left nhdsWithin_le_nhds).div hD h2c.ne').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hp : edge c x / x ^ j ≠ 0 := (div_pos (edge_pos c hx) (pow_pos hx j)).ne'
    exact (mul_div_mul_left (b x) (2 * c + (3 - (j : ℝ)) * x ^ 2) hp).symm

/-- The normalized factor with its rigorously identified endpoint value. -/
def normalizedPrimitive (c : ℝ) (j : ℕ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then b 0 / (2 * c) else primitive c j b x / scale c j x

theorem normalizedPrimitive_continuousWithinAt_zero {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) :
    ContinuousWithinAt (normalizedPrimitive c j b) (Ici 0) 0 := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto (normalizedPrimitive c j b) (𝓝[>] 0) (𝓝 (normalizedPrimitive c j b 0))
  rw [show normalizedPrimitive c j b 0 = b 0 / (2 * c) by simp [normalizedPrimitive]]
  refine (primitive_normalized_tendsto hc j hb).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [normalizedPrimitive, (show 0 < x from hx).ne']

/-- The actual integral factors on the closed positive half-line, with the
factor proved continuous at zero above. No smoothness conclusion is inferred
merely from this quotient definition. -/
theorem normalizedPrimitive_factorization (c : ℝ) (j : ℕ) (b : ℝ → ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    primitive c j b x = scale c j x * normalizedPrimitive c j b x := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    simp
  · have hs : scale c j x ≠ 0 := (scale_pos c j hpos).ne'
    simp only [normalizedPrimitive, ite_eq_right hpos.ne']
    field_simp

/-- A strictly positive endpoint coefficient gives an actual positive
normalized primitive on a sufficiently short terminal interval. -/
theorem primitive_normalized_eventually_pos {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) (hb0 : 0 < b 0) :
    ∀ᶠ x in 𝓝[>] 0, 0 < primitive c j b x / scale c j x :=
  (primitive_normalized_tendsto hc j hb).eventually
    (lt_mem_nhds (div_pos hb0 (mul_pos (by norm_num) hc)))

/-- The actual primitive vanishes faster than every natural power, even for
a merely continuous coefficient. This does not assume flatness of the
primitive or a factorization by a smooth function. -/
theorem primitive_div_pow_tendsto_zero {c : ℝ} (hc : 0 < c) (j : ℕ)
    {b : ℝ → ℝ} (hb : Continuous b) (loss : ℕ) :
    Tendsto (fun x => primitive c j b x / x ^ loss) (𝓝[>] 0) (𝓝 0) := by
  have hF : Tendsto (primitive c j b) (𝓝[>] 0) (𝓝 0) := by
    simpa only [primitive_zero] using
      ((primitive_hasDerivAt hc j hb 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  cases loss with
  | zero => simpa using hF
  | succ n =>
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hG : Tendsto (fun x : ℝ => x ^ (n + 1)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_id.fun_pow (n + 1)).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hE : Tendsto (fun x => edge c x / x ^ (j + n)) (𝓝[>] 0) (𝓝 0) :=
      (weighted_iteratedDeriv_tendsto_zero hc 0 (j + n)).mono_left nhdsWithin_le_nhds
    have hB : Tendsto (fun x => b x / (n + 1 : ℝ)) (𝓝[>] 0)
        (𝓝 (b 0 / (n + 1 : ℝ))) :=
      ((hb.tendsto 0).mono_left nhdsWithin_le_nhds).div_const _
    have hratio : Tendsto
        (fun x => integrand c j b x / ((n + 1 : ℝ) * x ^ n)) (𝓝[>] 0) (𝓝 0) := by
      have hlim := hE.mul hB
      simp only [zero_mul] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      dsimp [integrand]
      rw [pow_add]
      field_simp
    refine HasDerivAt.lhopital_zero_nhdsGT
      (Eventually.of_forall fun x => primitive_hasDerivAt hc j hb x)
      (Eventually.of_forall fun x => ?_)
      ?_ hF hG hratio
    · simpa using (hasDerivAt_id x).fun_pow (n + 1)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero hn (pow_ne_zero n (show 0 < x from hx).ne')

end NavierStokes.FlatPrimitive
