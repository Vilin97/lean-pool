/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.Certificates.EndpointBridge
public import LeanPool.Besicovitch.SixPoint.EndpointGeometry

/-!
# Rational tangent bounds for sibling incidences

This file proves the two-point tangent inequality used by the rational cells in the complete
sibling-incidence ledger. Its endpoint checks use only rational arithmetic and the certified
isolation interval for `barC`.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

private theorem norm_tangent {E : Type*} [SeminormedAddCommGroup E] (x : E) {r : ℝ}
    (hr : 0 < r) : ‖x‖ ≤ (‖x‖ ^ 2 + r ^ 2) / (2 * r) := by
  rw [le_div_iff₀ (by positivity : 0 < 2 * r)]
  nlinarith [sq_nonneg (‖x‖ - r)]

private theorem weighted_norm_tangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) (weight r : ℝ) (hr : 0 < r) (hweight : 0 ≤ weight) :
    weight * ‖x‖ ≤ weight / (2 * r) * (‖x‖ ^ 2 + r ^ 2) := by
  calc
    weight * ‖x‖ ≤ weight * ((‖x‖ ^ 2 + r ^ 2) / (2 * r)) :=
      mul_le_mul_of_nonneg_left (norm_tangent x hr) hweight
    _ = _ := by ring

private theorem weighted_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a • x + b • y‖ ^ 2 =
      (a + b) * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    real_inner_smul_left, real_inner_smul_right]
  ring

private theorem two_mul_norm_tangent {E : Type*} [SeminormedAddCommGroup E] (x : E)
    {r : ℝ} (hr : 0 < r) : 2 * ‖x‖ ≤ r + ‖x‖ ^ 2 / r := by
  have h := norm_tangent x hr
  calc
    2 * ‖x‖ ≤ 2 * ((‖x‖ ^ 2 + r ^ 2) / (2 * r)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = r + ‖x‖ ^ 2 / r := by field_simp; ring

private theorem quadratic_le_max_endpoints {a b d l x u : ℝ} (ha : 0 ≤ a)
    (hlx : l ≤ x) (hxu : x ≤ u) :
    a * x ^ 2 + b * x + d ≤ max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := by
  by_cases hlu : l = u
  · subst u
    have hx : x = l := le_antisymm hxu hlx
    subst x
    exact le_max_left _ _
  have hwidth : 0 < u - l := sub_pos.mpr (lt_of_le_of_ne (hlx.trans hxu) hlu)
  have hcurve : a * (x - l) * (x - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha (sub_nonneg.mpr hlx))
      (sub_nonpos.mpr hxu)
  have hleft := le_max_left (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d)
  have hright := le_max_right (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d)
  have hweighted := add_le_add
    (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hxu))
    (mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr hlx))
  apply (mul_le_mul_iff_of_pos_left hwidth).mp
  nlinarith

/-- A separable convex quadratic on the radial triangle is bounded at its three vertices. -/
theorem separableQuadratic_le_radial_vertices {a₁ a₂ b₁ b₂ d c t₁ t₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ht₁ : t₁ ≤ 1) (ht₂ : t₂ ≤ 1)
    (hsum : c ≤ t₁ + t₂) :
    a₁ * t₁ ^ 2 + b₁ * t₁ + a₂ * t₂ ^ 2 + b₂ * t₂ + d ≤
      max (a₁ + b₁ + a₂ + b₂ + d)
        (max (a₁ + b₁ + a₂ * (c - 1) ^ 2 + b₂ * (c - 1) + d)
          (a₁ * (c - 1) ^ 2 + b₁ * (c - 1) + a₂ + b₂ + d)) := by
  let value := fun x y ↦ a₁ * x ^ 2 + b₁ * x + a₂ * y ^ 2 + b₂ * y + d
  let v11 := value 1 1
  let v1c := value 1 (c - 1)
  let vc1 := value (c - 1) 1
  have ht₁Lower : c - 1 ≤ t₁ := by linarith
  have hsecond := quadratic_le_max_endpoints ha₂ (show c - t₁ ≤ t₂ by linarith) ht₂
    (b := b₂) (d := a₁ * t₁ ^ 2 + b₁ * t₁ + d)
  have hdiagonal := quadratic_le_max_endpoints (add_nonneg ha₁ ha₂) ht₁Lower ht₁
    (b := b₁ - 2 * a₂ * c - b₂)
    (d := a₂ * c ^ 2 + b₂ * c + d)
  have htop := quadratic_le_max_endpoints ha₁ ht₁Lower ht₁
    (b := b₁) (d := a₂ + b₂ + d)
  have hsecond' : value t₁ t₂ ≤ max (value t₁ (c - t₁)) (value t₁ 1) := by
    dsimp only [value]
    convert hsecond using 1 <;> ring_nf
  have hdiagonal' : value t₁ (c - t₁) ≤ max vc1 v1c := by
    dsimp only [value, vc1, v1c]
    convert hdiagonal using 1 <;> ring_nf
  have htop' : value t₁ 1 ≤ max vc1 v11 := by
    dsimp only [value, vc1, v11]
    convert htop using 1 <;> ring_nf
  have hfinal : value t₁ t₂ ≤ max v11 (max v1c vc1) := hsecond'.trans <| max_le
    (hdiagonal'.trans <| max_le
      (le_max_of_le_right (le_max_right _ _)) (le_max_of_le_right (le_max_left _ _)))
    (htop'.trans <| max_le
      (le_max_of_le_right (le_max_right _ _)) (le_max_left _ _))
  simpa [value, v11, v1c, vc1] using hfinal

/-- A positive quadratic coefficient gives a global tangent majorant for a weighted norm. -/
theorem weightedNorm_le_quadratic {E : Type*} [SeminormedAddCommGroup E]
    (x : E) (weight coefficient : ℝ) (hcoefficient : 0 < coefficient) :
    weight * ‖x‖ ≤ coefficient * ‖x‖ ^ 2 + weight ^ 2 / (4 * coefficient) := by
  have hsquare := sq_nonneg (2 * coefficient * ‖x‖ - weight)
  field_simp [hcoefficient.ne']
  nlinarith

private theorem gramTwoMulNormTangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) {radius : ℝ} (hradius : 0 < radius) :
    2 * ‖x‖ ≤ radius + ‖x‖ ^ 2 / radius := by
  have hsquare := sq_nonneg (‖x‖ - radius)
  field_simp [hradius.ne']
  nlinarith

private theorem gramWeightedNormSq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a • x + b • y‖ ^ 2 =
      (a + b) * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- The scalar upper function for a two-point Gram estimate. -/
def gramPairValue (c u₁ u₂ g₁ g₂ d₁ d₂ off sigma t₁ t₂ : ℝ) : ℝ :=
  (u₁ + (g₁ + g₂) * g₁ / sigma) * t₁ ^ 2 - d₁ * t₁ +
    (u₂ + (g₁ + g₂) * g₂ / sigma) * t₂ ^ 2 - d₂ * t₂ +
    sigma - (off + g₁ * g₂ / sigma) * c ^ 2

/-- The largest radial-vertex value in a two-point Gram estimate. -/
def gramPairMaximum (c u₁ u₂ g₁ g₂ d₁ d₂ off sigma : ℝ) : ℝ :=
  max (gramPairValue c u₁ u₂ g₁ g₂ d₁ d₂ off sigma 1 1)
    (max (gramPairValue c u₁ u₂ g₁ g₂ d₁ d₂ off sigma 1 (c - 1))
      (gramPairValue c u₁ u₂ g₁ g₂ d₁ d₂ off sigma (c - 1) 1))

/-- A separated pair in the unit ball is controlled by the three radial vertices. -/
theorem gramPairCore_le_vertices {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x₁ x₂ : E) (c u₁ u₂ g₁ g₂ d₁ d₂ off sigma : ℝ)
    (he : ‖e‖ = 1) (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hseparation : c ≤ ‖x₁ - x₂‖) (hc : 0 ≤ c) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂)
    (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) (hsigma : 0 < sigma) :
    u₁ * ‖x₁‖ ^ 2 + u₂ * ‖x₂‖ ^ 2 -
        2 * ⟪e, g₁ • x₁ + g₂ • x₂⟫_ℝ - d₁ * ‖x₁‖ - d₂ * ‖x₂‖ -
        off * c ^ 2 ≤ gramPairMaximum c u₁ u₂ g₁ g₂ d₁ d₂ off sigma := by
  let z := g₁ • x₁ + g₂ • x₂
  let Q := (g₁ + g₂) * (g₁ * ‖x₁‖ ^ 2 + g₂ * ‖x₂‖ ^ 2) -
    g₁ * g₂ * c ^ 2
  have hseparationSq : c ^ 2 ≤ ‖x₁ - x₂‖ ^ 2 := by
    nlinarith [norm_nonneg (x₁ - x₂)]
  have hzUpper : ‖z‖ ^ 2 ≤ Q := by
    rw [show ‖z‖ ^ 2 =
      (g₁ + g₂) * (g₁ * ‖x₁‖ ^ 2 + g₂ * ‖x₂‖ ^ 2) -
        g₁ * g₂ * ‖x₁ - x₂‖ ^ 2 by exact gramWeightedNormSq x₁ x₂ hg₁ hg₂]
    dsimp only [Q]
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_left hseparationSq (mul_nonneg hg₁ hg₂)) _
  have hinner := real_inner_le_norm (-e) z
  simp only [inner_neg_left, norm_neg, he, one_mul] at hinner
  have hnorm := gramTwoMulNormTangent z hsigma
  have hscaled := (div_le_div_iff_of_pos_right hsigma).2 hzUpper
  have horientation : -2 * ⟪e, z⟫_ℝ ≤ sigma + Q / sigma := by
    nlinarith
  have hsum : c ≤ ‖x₁‖ + ‖x₂‖ :=
    hseparation.trans (norm_sub_le x₁ x₂)
  have hvertices := separableQuadratic_le_radial_vertices
    (a₁ := u₁ + (g₁ + g₂) * g₁ / sigma)
    (a₂ := u₂ + (g₁ + g₂) * g₂ / sigma) (b₁ := -d₁) (b₂ := -d₂)
    (d := sigma - (off + g₁ * g₂ / sigma) * c ^ 2) (c := c)
    (t₁ := ‖x₁‖) (t₂ := ‖x₂‖) (by positivity) (by positivity) hx₁ hx₂ hsum
  have hpointwise :
      u₁ * ‖x₁‖ ^ 2 + u₂ * ‖x₂‖ ^ 2 - 2 * ⟪e, z⟫_ℝ -
          d₁ * ‖x₁‖ - d₂ * ‖x₂‖ - off * c ^ 2 ≤
        gramPairValue c u₁ u₂ g₁ g₂ d₁ d₂ off sigma ‖x₁‖ ‖x₂‖ := by
    dsimp only [gramPairValue, Q] at horientation ⊢
    ring_nf at horientation ⊢
    nlinarith
  dsimp only [z] at hpointwise
  apply hpointwise.trans
  unfold gramPairMaximum
  dsimp only [gramPairValue]
  ring_nf at hvertices ⊢
  exact hvertices

/-- The quadratic upper function in the two-point tangent estimate. -/
def pairTangentValue (c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma t₁ t₂ : ℝ) : ℝ :=
  let g₁ := A₁ / rho₁
  let g₂ := A₂ / rho₂
  A₁ / (2 * rho₁) * (1 + rho₁ ^ 2 + 4 * t₁ ^ 2) +
    A₂ / (2 * rho₂) * (1 + rho₂ ^ 2 + 4 * t₂ ^ 2) + sigma +
    ((g₁ + g₂) * (g₁ * t₁ ^ 2 + g₂ * t₂ ^ 2) - g₁ * g₂ * c ^ 2) /
      sigma - d₁ * t₁ - d₂ * t₂

/-- The largest of the three radial vertex values in the two-point tangent estimate. -/
def pairTangentMaximum (c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma : ℝ) : ℝ :=
  max (pairTangentValue c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma 1 1)
    (max (pairTangentValue c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma 1 (c - 1))
      (pairTangentValue c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma (c - 1) 1))

/-- Midpoint convexity bounds one cross distance by its two doubled-point distances. -/
theorem two_mul_crossDistance_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e p w : E) :
    2 * ‖e - p - w‖ ≤ ‖e - (2 : ℝ) • p‖ + ‖e - (2 : ℝ) • w‖ := by
  calc
    2 * ‖e - p - w‖ = ‖(2 : ℝ) • (e - p - w)‖ := by
      rw [norm_smul, Real.norm_ofNat]
    _ = ‖(e - (2 : ℝ) • p) + (e - (2 : ℝ) • w)‖ := by
      congr 1
      module
    _ ≤ _ := norm_add_le _ _

/-- A nonnegative four-entry cross-distance sum splits into two colorwise sums. -/
theorem weightedCrossDistances_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e p₁ p₂ w₁ w₂ : E) (a₁₁ a₁₂ a₂₁ a₂₂ : ℝ)
    (ha₁₁ : 0 ≤ a₁₁) (ha₁₂ : 0 ≤ a₁₂) (ha₂₁ : 0 ≤ a₂₁)
    (ha₂₂ : 0 ≤ a₂₂) :
    a₁₁ * ‖e - p₁ - w₁‖ + a₁₂ * ‖e - p₁ - w₂‖ +
        a₂₁ * ‖e - p₂ - w₁‖ + a₂₂ * ‖e - p₂ - w₂‖ ≤
      (a₁₁ + a₁₂) / 2 * ‖e - (2 : ℝ) • p₁‖ +
        (a₂₁ + a₂₂) / 2 * ‖e - (2 : ℝ) • p₂‖ +
        (a₁₁ + a₂₁) / 2 * ‖e - (2 : ℝ) • w₁‖ +
        (a₁₂ + a₂₂) / 2 * ‖e - (2 : ℝ) • w₂‖ := by
  have h₁₁ := mul_le_mul_of_nonneg_left (two_mul_crossDistance_le e p₁ w₁) ha₁₁
  have h₁₂ := mul_le_mul_of_nonneg_left (two_mul_crossDistance_le e p₁ w₂) ha₁₂
  have h₂₁ := mul_le_mul_of_nonneg_left (two_mul_crossDistance_le e p₂ w₁) ha₂₁
  have h₂₂ := mul_le_mul_of_nonneg_left (two_mul_crossDistance_le e p₂ w₂) ha₂₂
  nlinarith

private theorem norm_sub_two_smul_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x : E) :
    ‖e - (2 : ℝ) • x‖ ^ 2 = ‖e‖ ^ 2 + 4 * ‖x‖ ^ 2 - 4 * ⟪e, x⟫_ℝ := by
  rw [norm_sub_sq_real]
  simp only [norm_smul, Real.norm_ofNat, real_inner_smul_right]
  ring

/-- Rational two-point tangent estimate on two separated points of the unit ball. -/
theorem twoPointTangent_le_vertices {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x₁ x₂ : E) (c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma : ℝ)
    (he : ‖e‖ = 1) (hx₁ : ‖x₁‖ ≤ 1) (hx₂ : ‖x₂‖ ≤ 1)
    (hseparation : c ≤ ‖x₁ - x₂‖) (hc : 0 ≤ c) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hrho₁ : 0 < rho₁) (hrho₂ : 0 < rho₂) (hsigma : 0 < sigma) :
    A₁ * ‖e - (2 : ℝ) • x₁‖ + A₂ * ‖e - (2 : ℝ) • x₂‖ -
        d₁ * ‖x₁‖ - d₂ * ‖x₂‖ ≤
      pairTangentMaximum c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma := by
  let g₁ := A₁ / rho₁
  let g₂ := A₂ / rho₂
  let z := g₁ • x₁ + g₂ • x₂
  let Q := (g₁ + g₂) * (g₁ * ‖x₁‖ ^ 2 + g₂ * ‖x₂‖ ^ 2) -
    g₁ * g₂ * c ^ 2
  have hg₁ : 0 ≤ g₁ := div_nonneg hA₁ hrho₁.le
  have hg₂ : 0 ≤ g₂ := div_nonneg hA₂ hrho₂.le
  have hseparationSq : c ^ 2 ≤ ‖x₁ - x₂‖ ^ 2 := by
    nlinarith [norm_nonneg (x₁ - x₂)]
  have hzUpper : ‖z‖ ^ 2 ≤ Q := by
    rw [show ‖z‖ ^ 2 = (g₁ + g₂) * (g₁ * ‖x₁‖ ^ 2 + g₂ * ‖x₂‖ ^ 2) -
      g₁ * g₂ * ‖x₁ - x₂‖ ^ 2 by exact weighted_norm_sq x₁ x₂ hg₁ hg₂]
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_left hseparationSq (mul_nonneg hg₁ hg₂)) _
  have horientation : -2 * ⟪e, z⟫_ℝ ≤ sigma + Q / sigma := by
    have hinner := real_inner_le_norm (-e) z
    simp only [inner_neg_left, norm_neg, he, one_mul] at hinner
    have hnorm : 2 * ‖z‖ ≤ sigma + ‖z‖ ^ 2 / sigma :=
      two_mul_norm_tangent z hsigma
    have hscaled := (div_le_div_iff_of_pos_right hsigma).2 hzUpper
    nlinarith
  have htangent₁ := weighted_norm_tangent (e - (2 : ℝ) • x₁) A₁ rho₁ hrho₁ hA₁
  have htangent₂ := weighted_norm_tangent (e - (2 : ℝ) • x₂) A₂ rho₂ hrho₂ hA₂
  have hpointwise :
      A₁ * ‖e - (2 : ℝ) • x₁‖ + A₂ * ‖e - (2 : ℝ) • x₂‖ -
          d₁ * ‖x₁‖ - d₂ * ‖x₂‖ ≤
        pairTangentValue c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma ‖x₁‖ ‖x₂‖ := by
    rw [norm_sub_two_smul_sq e x₁] at htangent₁
    rw [norm_sub_two_smul_sq e x₂] at htangent₂
    simp only [he, one_pow] at htangent₁ htangent₂
    dsimp only [z, Q, g₁, g₂] at horientation
    simp only [inner_add_right, real_inner_smul_right] at horientation
    dsimp only [pairTangentValue, g₁, g₂]
    ring_nf at htangent₁ htangent₂ horientation ⊢
    nlinarith
  have hsum : c ≤ ‖x₁‖ + ‖x₂‖ :=
    hseparation.trans (norm_sub_le x₁ x₂)
  let a₁ := 2 * A₁ / rho₁ + (g₁ + g₂) * g₁ / sigma
  let a₂ := 2 * A₂ / rho₂ + (g₁ + g₂) * g₂ / sigma
  let b₁ := -d₁
  let b₂ := -d₂
  let constant := A₁ / (2 * rho₁) * (1 + rho₁ ^ 2) +
    A₂ / (2 * rho₂) * (1 + rho₂ ^ 2) + sigma - g₁ * g₂ * c ^ 2 / sigma
  have ha₁ : 0 ≤ a₁ := by positivity
  have ha₂ : 0 ≤ a₂ := by positivity
  have hvertices := separableQuadratic_le_radial_vertices ha₁ ha₂ hx₁ hx₂ hsum
    (b₁ := b₁) (b₂ := b₂) (d := constant)
  apply hpointwise.trans
  unfold pairTangentMaximum
  let value := fun t₁ t₂ ↦
    a₁ * t₁ ^ 2 + b₁ * t₁ + a₂ * t₂ ^ 2 + b₂ * t₂ + constant
  have hvalue (t₁ t₂ : ℝ) :
      pairTangentValue c A₁ A₂ d₁ d₂ rho₁ rho₂ sigma t₁ t₂ = value t₁ t₂ := by
    dsimp only [pairTangentValue, value, a₁, a₂, b₁, b₂, constant, g₁, g₂]
    field_simp [hrho₁.ne', hrho₂.ne', hsigma.ne']
    ring
  rw [hvalue ‖x₁‖ ‖x₂‖, hvalue 1 1, hvalue 1 (c - 1), hvalue (c - 1) 1]
  simpa only [value, one_pow, mul_one] using hvertices

local macro "verify_pair_tangent_maximum" : tactic => `(tactic|
  (simp only [pairTangentMaximum, max_le_iff]
   rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
   constructor
   · norm_num [pairTangentValue]
     nlinarith [sq_nonneg (barC - 1)]
   constructor
   · norm_num [pairTangentValue]
     nlinarith [sq_nonneg (barC - 1)]
   · norm_num [pairTangentValue]
     nlinarith [sq_nonneg (barC - 1)]))

private theorem tangentMaximum_e0s1_red :
    pairTangentMaximum barC (29 / 4) (15 / 4) (13 * barC / 2) (13 * barC / 2)
      (2903 / 1000) (2104 / 1000) (2599 / 1000) ≤ 1687 / 125 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e0s1_blue :
    pairTangentMaximum barC (29 / 4) (15 / 4) (7 * (barC - 1) / 2)
      (7 * (barC + 1) / 2) (2910 / 1000) (2220 / 1000) (2669 / 1000) ≤
        21643 / 1000 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e0s2_red :
    pairTangentMaximum barC (9 / 4) (5 / 4) (3 * barC / 2) (3 * barC / 2)
      (2904 / 1000) (2675 / 1000) (920 / 1000) ≤ 229 / 40 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e0s2_blue :
    pairTangentMaximum barC (9 / 4) (5 / 4) (barC - 1) (barC + 1)
      (2901 / 1000) (2495 / 1000) (890 / 1000) ≤ 1781 / 250 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e0s3_red :
    pairTangentMaximum barC 23 (59 / 2) (27 * (barC + 1)) (27 * (barC - 1))
      (1999 / 1000) (2813 / 1000) (10791 / 1000) ≤ 7871 / 100 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e0s3_blue :
    pairTangentMaximum barC (73 / 2) 16 (41 * (barC - 1) / 2)
      (41 * (barC + 1) / 2) (2908 / 1000) (1739 / 1000) (11850 / 1000) ≤
        19511 / 200 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e1s1_red :
    pairTangentMaximum barC 7 (7 / 2) (6 * barC) (6 * barC)
      (2903 / 1000) (2116 / 1000) (2499 / 1000) ≤ 13433 / 1000 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e1s1_blue :
    pairTangentMaximum barC (7 / 2) 7 (7 * (barC + 1) / 2)
      (7 * (barC - 1) / 2) (2102 / 1000) (2896 / 1000) (2524 / 1000) ≤
        2547 / 125 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e1s3_red :
    pairTangentMaximum barC 7 (19 / 2) (8 * (barC + 1)) (8 * (barC - 1))
      (2024 / 1000) (2832 / 1000) (3439 / 1000) ≤ 12917 / 500 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e1s3_blue :
    pairTangentMaximum barC (11 / 2) 11 (11 * (barC + 1) / 2)
      (11 * (barC - 1) / 2) (2113 / 1000) (2915 / 1000) (3895 / 1000) ≤
        16009 / 500 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s1s1_red :
    pairTangentMaximum barC (13 / 2) (13 / 2) (6 * barC) (6 * barC)
      (2807 / 1000) (2808 / 1000) (3337 / 1000) ≤ 993 / 50 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s1s1_blue :
    pairTangentMaximum barC (13 / 2) (13 / 2) (6 * barC) (6 * barC)
      (2808 / 1000) (2806 / 1000) (3338 / 1000) ≤ 993 / 50 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s2s2_red :
    pairTangentMaximum barC (9 / 2) (9 / 2) (4 * barC) (4 * barC)
      (2807 / 1000) (2808 / 1000) (2310 / 1000) ≤ 1772 / 125 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s2s2_blue :
    pairTangentMaximum barC (9 / 2) (9 / 2) (4 * barC) (4 * barC)
      (2808 / 1000) (2808 / 1000) (2310 / 1000) ≤ 1772 / 125 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e1s2_red :
    pairTangentMaximum barC (13 / 4) (7 / 4) (7 * barC / 2) (7 * barC / 2)
      (2889 / 1000) (1919 / 1000) (1109 / 1000) ≤ 4833 / 1000 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_e1s2_blue :
    pairTangentMaximum barC (7 / 4) (13 / 4) (3 * (barC + 1) / 2)
      (3 * (barC - 1) / 2) (2373 / 1000) (2901 / 1000) (1238 / 1000) ≤
        5009 / 500 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s0s1_red :
    pairTangentMaximum barC (7 / 4) (7 / 4) (5 * barC / 2) (5 * barC / 2)
      (2580 / 1000) (2580 / 1000) (804 / 1000) ≤ 2967 / 1000 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s0s1_blue :
    pairTangentMaximum barC (9 / 4) (5 / 4) (barC - 1) (barC + 1)
      (2902 / 1000) (2491 / 1000) (893 / 1000) ≤ 1781 / 250 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s0s2_red :
    pairTangentMaximum barC (7 / 4) (7 / 4) (5 * barC / 2) (5 * barC / 2)
      (2584 / 1000) (2584 / 1000) (801 / 1000) ≤ 1483 / 500 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s0s2_blue :
    pairTangentMaximum barC (9 / 4) (5 / 4) (barC - 1) (barC + 1)
      (2897 / 1000) (2493 / 1000) (892 / 1000) ≤ 1781 / 250 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s1s2_red :
    pairTangentMaximum barC (7 / 4) (7 / 4) (5 * barC / 2) (5 * barC / 2)
      (2583 / 1000) (2583 / 1000) (802 / 1000) ≤ 1483 / 500 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_s1s2_blue :
    pairTangentMaximum barC (7 / 4) (7 / 4) barC barC
      (2804 / 1000) (2808 / 1000) (897 / 1000) ≤ 3527 / 500 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_adjacentFirst_red :
    pairTangentMaximum barC (9 / 4) (1 / 2) (7 * (barC - 1) / 8)
      (7 * (barC + 1) / 8) (49 / 16) (5 / 4) (13 / 20) ≤ 742013 / 125000 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_adjacentFirst_blue :
    pairTangentMaximum barC (11 / 8) (11 / 8) (7 * (barC - 1) / 8)
      (7 * (barC + 1) / 8) (351 / 125) (351 / 125) (353 / 500) ≤
        2647153 / 500000 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_adjacentSecond_red :
    pairTangentMaximum barC (11 / 8) (11 / 8) (7 * (barC + 1) / 8)
      (7 * (barC - 1) / 8) (2808 / 1000) (2808 / 1000) (706 / 1000) ≤
        2647153 / 500000 := by
  verify_pair_tangent_maximum

private theorem tangentMaximum_adjacentSecond_blue :
    pairTangentMaximum barC (9 / 4) (1 / 2) (7 * (barC - 1) / 8)
      (7 * (barC + 1) / 8) (2973 / 1000) (1247 / 1000) (660 / 1000) ≤
        237273 / 40000 := by
  verify_pair_tangent_maximum

/-- The rational tangent separator for the `E0/S1` incidence representative. -/
theorem tangentCertificate_e0s1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    29 / 2 * ‖e - p₁ - w₁‖ + 15 / 2 * ‖e - p₂ - w₂‖ -
        13 * barC / 2 * ‖p₁‖ - 13 * barC / 2 * ‖p₂‖ -
        7 * (barC - 1) / 2 * ‖w₁‖ - 7 * (barC + 1) / 2 * ‖w₂‖ - 7 +
        51 / 2 * barC - 34 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ (29 / 2) 0 0 (15 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (29 / 4) (15 / 4)
    (13 * barC / 2) (13 * barC / 2) (2903 / 1000) (2104 / 1000) (2599 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (29 / 4) (15 / 4)
    (7 * (barC - 1) / 2) (7 * (barC + 1) / 2) (2910 / 1000) (2220 / 1000)
    (2669 / 1000) he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hconstant : 1687 / 125 + 21643 / 1000 - 7 + 51 / 2 * barC -
      34 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_e0s1_red, tangentMaximum_e0s1_blue]

/-- The rational tangent separator for the `E0/S2` incidence representative. -/
theorem tangentCertificate_e0s2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    3 * ‖e - p₁ - w₁‖ + 3 / 2 * ‖e - p₁ - w₂‖ +
        3 / 2 * ‖e - p₂ - w₁‖ + ‖e - p₂ - w₂‖ -
        3 * barC / 2 * ‖p₁‖ - 3 * barC / 2 * ‖p₂‖ -
        (barC - 1) * ‖w₁‖ - (barC + 1) * ‖w₂‖ - 2 + 8 * barC -
        23 / 2 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 3 (3 / 2) (3 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (9 / 4) (5 / 4)
    (3 * barC / 2) (3 * barC / 2) (2904 / 1000) (2675 / 1000) (920 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (9 / 4) (5 / 4)
    (barC - 1) (barC + 1) (2901 / 1000) (2495 / 1000) (890 / 1000)
    he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hconstant : 229 / 40 + 1781 / 250 - 2 + 8 * barC -
      23 / 2 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_e0s2_red, tangentMaximum_e0s2_blue]

/-- The rational tangent separator for the `E0/S3` incidence representative. -/
theorem tangentCertificate_e0s3 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    46 * ‖e - p₁ - w₁‖ + 27 * ‖e - p₂ - w₁‖ + 32 * ‖e - p₂ - w₂‖ -
        27 * (barC + 1) * ‖p₁‖ - 27 * (barC - 1) * ‖p₂‖ -
        41 * (barC - 1) / 2 * ‖w₁‖ - 41 * (barC + 1) / 2 * ‖w₂‖ - 41 +
        251 / 2 * barC - 325 / 2 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 46 0 27 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC 23 (59 / 2)
    (27 * (barC + 1)) (27 * (barC - 1)) (1999 / 1000) (2813 / 1000)
    (10791 / 1000) he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (73 / 2) 16
    (41 * (barC - 1) / 2) (41 * (barC + 1) / 2) (2908 / 1000) (1739 / 1000)
    (11850 / 1000) he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hconstant : 7871 / 100 + 19511 / 200 - 41 + 251 / 2 * barC -
      325 / 2 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_e0s3_red, tangentMaximum_e0s3_blue]

/-- The rational tangent separator for the `E1/S1` incidence representative. -/
theorem tangentCertificate_e1s1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    7 * ‖e - p₁ - w₁‖ + 7 * ‖e - p₁ - w₂‖ + 7 * ‖e - p₂ - w₂‖ -
        6 * barC * ‖p₁‖ - 6 * barC * ‖p₂‖ -
        7 * (barC + 1) / 2 * ‖w₁‖ - 7 * (barC - 1) / 2 * ‖w₂‖ - 7 +
        49 / 2 * barC - 65 / 2 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 7 7 0 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC 7 (7 / 2) (6 * barC)
    (6 * barC) (2903 / 1000) (2116 / 1000) (2499 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (7 / 2) 7
    (7 * (barC + 1) / 2) (7 * (barC - 1) / 2) (2102 / 1000) (2896 / 1000)
    (2524 / 1000) he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hconstant : 13433 / 1000 + 2547 / 125 - 7 + 49 / 2 * barC -
      65 / 2 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_e1s1_red, tangentMaximum_e1s1_blue]

/-- The rational tangent separator for the `E1/S3` incidence representative. -/
theorem tangentCertificate_e1s3 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    3 * ‖e - p₁ - w₁‖ + 11 * ‖e - p₁ - w₂‖ +
        8 * ‖e - p₂ - w₁‖ + 11 * ‖e - p₂ - w₂‖ -
        8 * (barC + 1) * ‖p₁‖ - 8 * (barC - 1) * ‖p₂‖ -
        11 * (barC + 1) / 2 * ‖w₁‖ - 11 * (barC - 1) / 2 * ‖w₂‖ - 11 +
        77 / 2 * barC - 105 / 2 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 3 11 8 11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC 7 (19 / 2)
    (8 * (barC + 1)) (8 * (barC - 1)) (2024 / 1000) (2832 / 1000)
    (3439 / 1000) he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (11 / 2) 11
    (11 * (barC + 1) / 2) (11 * (barC - 1) / 2) (2113 / 1000) (2915 / 1000)
    (3895 / 1000) he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hconstant : 12917 / 500 + 16009 / 500 - 11 + 77 / 2 * barC -
      105 / 2 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_e1s3_red, tangentMaximum_e1s3_blue]

/-- The rational tangent separator for the `S1/S1` incidence representative. -/
theorem tangentCertificate_s1s1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    13 * ‖e - p₁ - w₁‖ + 13 * ‖e - p₂ - w₂‖ -
        6 * barC * ‖p₁‖ - 6 * barC * ‖p₂‖ -
        6 * barC * ‖w₁‖ - 6 * barC * ‖w₂‖ + 26 * barC - 40 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 13 0 0 13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (13 / 2) (13 / 2)
    (6 * barC) (6 * barC) (2807 / 1000) (2808 / 1000) (3337 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (13 / 2) (13 / 2)
    (6 * barC) (6 * barC) (2808 / 1000) (2806 / 1000) (3338 / 1000)
    he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hconstant : 993 / 50 + 993 / 50 + 26 * barC - 40 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_s1s1_red, tangentMaximum_s1s1_blue]

/-- The rational tangent separator for the `S2/S2` incidence representative. -/
theorem tangentCertificate_s2s2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    ‖e - p₁ - w₁‖ + 8 * ‖e - p₁ - w₂‖ +
        8 * ‖e - p₂ - w₁‖ + ‖e - p₂ - w₂‖ -
        4 * barC * ‖p₁‖ - 4 * barC * ‖p₂‖ -
        4 * barC * ‖w₁‖ - 4 * barC * ‖w₂‖ + 18 * barC - 28 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 1 8 8 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (9 / 2) (9 / 2)
    (4 * barC) (4 * barC) (2807 / 1000) (2808 / 1000) (2310 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (9 / 2) (9 / 2)
    (4 * barC) (4 * barC) (2808 / 1000) (2808 / 1000) (2310 / 1000)
    he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hconstant : 1772 / 125 + 1772 / 125 + 18 * barC - 28 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_s2s2_red, tangentMaximum_s2s2_blue]

/-- The rational tangent separator for the `E1/S2` incidence representative. -/
theorem tangentCertificate_e1s2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    13 / 2 * ‖e - p₁ - w₂‖ + 7 / 2 * ‖e - p₂ - w₁‖ -
        7 * barC / 2 * ‖p₁‖ - 7 * barC / 2 * ‖p₂‖ -
        3 * (barC + 1) / 2 * ‖w₁‖ - 3 * (barC - 1) / 2 * ‖w₂‖ - 3 +
        23 / 2 * barC - 15 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 0 (13 / 2) (7 / 2) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (13 / 4) (7 / 4)
    (7 * barC / 2) (7 * barC / 2) (2889 / 1000) (1919 / 1000) (1109 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (7 / 4) (13 / 4)
    (3 * (barC + 1) / 2) (3 * (barC - 1) / 2) (2373 / 1000) (2901 / 1000)
    (1238 / 1000) he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hconstant : 4833 / 1000 + 5009 / 500 - 3 + 23 / 2 * barC -
      15 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_e1s2_red, tangentMaximum_e1s2_blue]

/-- The rational tangent separator for the `S0/S1` incidence representative. -/
theorem tangentCertificate_s0s1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    7 / 2 * ‖e - p₁ - w₁‖ + ‖e - p₂ - w₁‖ +
        5 / 2 * ‖e - p₂ - w₂‖ - 5 * barC / 2 * ‖p₁‖ -
        5 * barC / 2 * ‖p₂‖ - (barC - 1) * ‖w₁‖ -
        (barC + 1) * ‖w₂‖ + 7 * barC - 21 / 2 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ (7 / 2) 0 1 (5 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (7 / 4) (7 / 4)
    (5 * barC / 2) (5 * barC / 2) (2580 / 1000) (2580 / 1000) (804 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (9 / 4) (5 / 4)
    (barC - 1) (barC + 1) (2902 / 1000) (2491 / 1000) (893 / 1000)
    he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hconstant : 2967 / 1000 + 1781 / 250 + 7 * barC -
      21 / 2 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_s0s1_red, tangentMaximum_s0s1_blue]

/-- The rational tangent separator for the `S0/S2` incidence representative. -/
theorem tangentCertificate_s0s2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    ‖e - p₁ - w₁‖ + 5 / 2 * ‖e - p₁ - w₂‖ +
        7 / 2 * ‖e - p₂ - w₁‖ - 5 * barC / 2 * ‖p₁‖ -
        5 * barC / 2 * ‖p₂‖ - (barC - 1) * ‖w₁‖ -
        (barC + 1) * ‖w₂‖ + 7 * barC - 21 / 2 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 1 (5 / 2) (7 / 2) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (7 / 4) (7 / 4)
    (5 * barC / 2) (5 * barC / 2) (2584 / 1000) (2584 / 1000) (801 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (9 / 4) (5 / 4)
    (barC - 1) (barC + 1) (2897 / 1000) (2493 / 1000) (892 / 1000)
    he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hconstant : 1483 / 500 + 1781 / 250 + 7 * barC -
      21 / 2 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_s0s2_red, tangentMaximum_s0s2_blue]

/-- The rational tangent separator for the `S1/S2` incidence representative. -/
theorem tangentCertificate_s1s2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    ‖e - p₁ - w₁‖ + 5 / 2 * ‖e - p₁ - w₂‖ +
        5 / 2 * ‖e - p₂ - w₁‖ + ‖e - p₂ - w₂‖ -
        5 * barC / 2 * ‖p₁‖ - 5 * barC / 2 * ‖p₂‖ -
        barC * ‖w₁‖ - barC * ‖w₂‖ + 7 * barC - 21 / 2 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ 1 (5 / 2) (5 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (7 / 4) (7 / 4)
    (5 * barC / 2) (5 * barC / 2) (2583 / 1000) (2583 / 1000) (802 / 1000)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (7 / 4) (7 / 4) barC barC
    (2804 / 1000) (2808 / 1000) (897 / 1000) he hw₁ hw₂ hwsep barC_pos.le
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hconstant : 1483 / 500 + 3527 / 500 + 7 * barC -
      21 / 2 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_s1s2_red, tangentMaximum_s1s2_blue]

/-- The rational tangent separator for the first adjacent endpoint orbit. -/
theorem tangentCertificate_adjacentFirst {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    11 / 4 * ‖e - p₁ - w₁‖ + 7 / 4 * ‖e - p₁ - w₂‖ +
        ‖e - p₂ - w₂‖ - 7 * (barC - 1) / 8 * ‖p₁‖ -
        7 * (barC + 1) / 8 * ‖p₂‖ - 7 * (barC - 1) / 8 * ‖w₁‖ -
        7 * (barC + 1) / 8 * ‖w₂‖ - 7 / 2 + 29 / 4 * barC -
        37 / 4 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ (11 / 4) (7 / 4) 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (9 / 4) (1 / 2)
    (7 * (barC - 1) / 8) (7 * (barC + 1) / 8) (49 / 16) (5 / 4) (13 / 20)
    he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (11 / 8) (11 / 8)
    (7 * (barC - 1) / 8) (7 * (barC + 1) / 8) (351 / 125) (351 / 125)
    (353 / 500) he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hconstant : 742013 / 125000 + 2647153 / 500000 - 7 / 2 +
      29 / 4 * barC - 37 / 4 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_adjacentFirst_red, tangentMaximum_adjacentFirst_blue]

/-- The rational tangent separator for the second adjacent endpoint orbit. -/
theorem tangentCertificate_adjacentSecond {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hpsep : barC ≤ ‖p₁ - p₂‖) (hwsep : barC ≤ ‖w₁ - w₂‖) :
    11 / 4 * ‖e - p₁ - w₁‖ + 7 / 4 * ‖e - p₂ - w₁‖ +
        ‖e - p₂ - w₂‖ - 7 * (barC + 1) / 8 * ‖p₁‖ -
        7 * (barC - 1) / 8 * ‖p₂‖ - 7 * (barC - 1) / 8 * ‖w₁‖ -
        7 * (barC + 1) / 8 * ‖w₂‖ - 7 / 2 + 29 / 4 * barC -
        37 / 4 * barC ^ 2 < 0 := by
  have hmid := weightedCrossDistances_le e p₁ p₂ w₁ w₂ (11 / 4) 0 (7 / 4) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp := twoPointTangent_le_vertices e p₁ p₂ barC (11 / 8) (11 / 8)
    (7 * (barC + 1) / 8) (7 * (barC - 1) / 8) (2808 / 1000) (2808 / 1000)
    (706 / 1000) he hp₁ hp₂ hpsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hw := twoPointTangent_le_vertices e w₁ w₂ barC (9 / 4) (1 / 2)
    (7 * (barC - 1) / 8) (7 * (barC + 1) / 8) (2973 / 1000) (1247 / 1000)
    (660 / 1000) he hw₁ hw₂ hwsep barC_pos.le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hconstant : 2647153 / 500000 + 237273 / 40000 - 7 / 2 +
      29 / 4 * barC - 37 / 4 * barC ^ 2 < 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 1)]
  nlinarith [tangentMaximum_adjacentSecond_red, tangentMaximum_adjacentSecond_blue]

end LeanPool.Besicovitch
