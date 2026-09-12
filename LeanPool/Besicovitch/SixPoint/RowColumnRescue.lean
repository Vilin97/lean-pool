/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.Certificates.EndpointBridge
public import LeanPool.Besicovitch.SixPoint.EndpointGeometry
public import LeanPool.Besicovitch.SixPoint.SiblingTriangle

/-!
# The row and column rescue

This file proves the first strict exit in the endpoint failure tree. A row or column obstruction
for the four-child packing forces the corresponding root against the full opposite triangle to
have nonnegative score.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

private def rowRho1 : ℝ := 361 / 125

private def rowRho2 : ℝ := 64 / 25

private def rowRho3 : ℝ := 1937 / 1000

private def rowSigma : ℝ := 601 / 100

private def rowEta : ℝ := 567 / 100

private def rowK1 : ℝ := 5 / rowRho1

private def rowK2 : ℝ := 5 / rowRho2

private def rowK3 : ℝ := (9 / 2) / rowRho3

private def rowK : ℝ := rowK1 + rowK2

private def rowA1 : ℝ := rowK1 + rowK3 + rowK * rowK1 / rowSigma

private def rowA2 : ℝ := rowK2 + rowK * rowK2 / rowSigma

private def rowPositiveConstant (c : ℝ) : ℝ :=
  rowK1 * (2 + rowRho1 ^ 2) + rowK2 * (2 + rowRho2 ^ 2) +
    rowK3 * (1 + rowRho3 ^ 2) + rowSigma +
    (rowK ^ 2 - rowK1 * rowK2 * c ^ 2) / rowSigma

private def rowConstant (c : ℝ) : ℝ :=
  -10 * (4 * c ^ 2 - 3 * c + 2) - 9 * (c - 1) - (9 / 2) * c * (c - 1) +
    rowPositiveConstant c

private def rowQuadratic1 : ℝ :=
  rowA1 + (rowA1 + rowA2) * rowA1 / rowEta

private def rowQuadratic2 : ℝ :=
  rowA2 + (rowA1 + rowA2) * rowA2 / rowEta

private def rowBase (c : ℝ) : ℝ :=
  rowConstant c + rowEta - rowA1 * rowA2 * c ^ 2 / rowEta

private def rowUpper (c t₁ t₂ : ℝ) : ℝ :=
  rowConstant c + rowA1 * t₁ ^ 2 + rowA2 * t₂ ^ 2 + rowEta +
    ((rowA1 + rowA2) * (rowA1 * t₁ ^ 2 + rowA2 * t₂ ^ 2) -
      rowA1 * rowA2 * c ^ 2) / rowEta -
    (9 / 2) * (c - 1) * t₁ - (9 / 2) * (c + 1) * t₂

private theorem rowUpper_eq_quadratic (c t₁ t₂ : ℝ) :
    rowUpper c t₁ t₂ =
      rowBase c + rowQuadratic1 * t₁ ^ 2 + rowQuadratic2 * t₂ ^ 2 -
        (9 / 2) * (c - 1) * t₁ - (9 / 2) * (c + 1) * t₂ := by
  simp only [rowUpper, rowBase, rowQuadratic1, rowQuadratic2]
  ring

private theorem norm_tangent {E : Type*} [SeminormedAddCommGroup E] (x : E) {r : ℝ}
    (hr : 0 < r) : ‖x‖ ≤ (‖x‖ ^ 2 + r ^ 2) / (2 * r) := by
  rw [le_div_iff₀ (by positivity : 0 < 2 * r)]
  nlinarith [sq_nonneg (‖x‖ - r)]

private theorem weighted_norm_tangent {E : Type*} [SeminormedAddCommGroup E]
    (x : E) (weight r k : ℝ) (hr : 0 < r) (hrelation : k = weight / (2 * r))
    (hweight : 0 ≤ weight) : weight * ‖x‖ ≤ k * (‖x‖ ^ 2 + r ^ 2) := by
  calc
    weight * ‖x‖ ≤ weight * ((‖x‖ ^ 2 + r ^ 2) / (2 * r)) :=
      mul_le_mul_of_nonneg_left (norm_tangent x hr) hweight
    _ = _ := by rw [hrelation]; ring

private theorem weighted_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a • x + b • y‖ ^ 2 =
      (a + b) * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    real_inner_smul_left, real_inner_smul_right]
  ring

private theorem norm_sub_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e p w : E) :
    ‖e - p - w‖ ^ 2 = ‖e‖ ^ 2 + ‖p‖ ^ 2 + ‖w‖ ^ 2 - 2 * ⟪e, p⟫_ℝ -
      2 * ⟪e, w⟫_ℝ + 2 * ⟪p, w⟫_ℝ := by
  rw [show e - p - w = e - (p + w) by abel, norm_sub_sq_real, norm_add_sq_real]
  simp only [inner_add_right]
  ring

private theorem two_mul_norm_tangent {E : Type*} [SeminormedAddCommGroup E] (x : E) {r : ℝ}
    (hr : 0 < r) : 2 * ‖x‖ ≤ r + ‖x‖ ^ 2 / r := by
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
  have hleft : a * l ^ 2 + b * l + d ≤
      max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := le_max_left _ _
  have hright : a * u ^ 2 + b * u + d ≤
      max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := le_max_right _ _
  have hcurve : a * (x - l) * (x - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha (sub_nonneg.mpr hlx))
      (sub_nonpos.mpr hxu)
  have hleftWeight : 0 ≤ u - x := sub_nonneg.mpr hxu
  have hrightWeight : 0 ≤ x - l := sub_nonneg.mpr hlx
  have hsecant :
      (u - l) * (a * x ^ 2 + b * x + d) ≤
        (u - x) * (a * l ^ 2 + b * l + d) +
          (x - l) * (a * u ^ 2 + b * u + d) := by
    nlinarith
  have hbound :
      (u - x) * (a * l ^ 2 + b * l + d) +
          (x - l) * (a * u ^ 2 + b * u + d) ≤
        (u - l) * max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := by
    nlinarith [mul_le_mul_of_nonneg_left hleft hleftWeight,
      mul_le_mul_of_nonneg_left hright hrightWeight]
  exact (mul_le_mul_iff_of_pos_left hwidth).mp (hsecant.trans hbound)

private theorem rowUpper_le_vertices {c t₁ t₂ : ℝ} (ht₁_one : t₁ ≤ 1)
    (ht₂_one : t₂ ≤ 1) (hsum : c ≤ t₁ + t₂) :
    rowUpper c t₁ t₂ ≤
      max (rowUpper c 1 1) (max (rowUpper c 1 (c - 1)) (rowUpper c (c - 1) 1)) := by
  have hquadratic1 : 0 ≤ rowQuadratic1 := by
    norm_num [rowQuadratic1, rowA1, rowA2, rowK, rowK1, rowK2, rowK3, rowRho1,
      rowRho2, rowRho3, rowSigma, rowEta]
  have hquadratic2 : 0 ≤ rowQuadratic2 := by
    norm_num [rowQuadratic2, rowA1, rowA2, rowK, rowK1, rowK2, rowK3, rowRho1,
      rowRho2, rowRho3, rowSigma, rowEta]
  have ht₁_lower : c - 1 ≤ t₁ := by linarith
  have ht₂_lower : c - 1 ≤ t₂ := by linarith
  have hsecond :
      rowUpper c t₁ t₂ ≤ max (rowUpper c t₁ (c - t₁)) (rowUpper c t₁ 1) := by
    have h := quadratic_le_max_endpoints hquadratic2
      (show c - t₁ ≤ t₂ by linarith) ht₂_one
        (b := -(9 / 2) * (c + 1))
        (d := rowBase c + rowQuadratic1 * t₁ ^ 2 - (9 / 2) * (c - 1) * t₁)
    rw [rowUpper_eq_quadratic, rowUpper_eq_quadratic, rowUpper_eq_quadratic]
    convert h using 1 <;> ring_nf
  have hdiagonal :
      rowUpper c t₁ (c - t₁) ≤
        max (rowUpper c (c - 1) 1) (rowUpper c 1 (c - 1)) := by
    have h := quadratic_le_max_endpoints (add_nonneg hquadratic1 hquadratic2)
      ht₁_lower ht₁_one
      (b := -2 * rowQuadratic2 * c - (9 / 2) * (c - 1) + (9 / 2) * (c + 1))
      (d := rowBase c + rowQuadratic2 * c ^ 2 - (9 / 2) * (c + 1) * c)
    rw [rowUpper_eq_quadratic, rowUpper_eq_quadratic, rowUpper_eq_quadratic]
    convert h using 1 <;> ring_nf
  have htop :
      rowUpper c t₁ 1 ≤ max (rowUpper c (c - 1) 1) (rowUpper c 1 1) := by
    have h := quadratic_le_max_endpoints hquadratic1 ht₁_lower ht₁_one
        (b := -(9 / 2) * (c - 1))
        (d := rowBase c + rowQuadratic2 - (9 / 2) * (c + 1))
    rw [rowUpper_eq_quadratic, rowUpper_eq_quadratic, rowUpper_eq_quadratic]
    convert h using 1 <;> ring_nf
  refine hsecond.trans (max_le ?_ ?_)
  · exact hdiagonal.trans <| max_le
      (le_max_right _ _ |>.trans <| le_max_right _ _)
      (le_max_left _ _ |>.trans <| le_max_right _ _)
  · exact htop.trans <| max_le
      (le_max_right _ _ |>.trans <| le_max_right _ _)
      (le_max_left _ _)

private theorem rowUpper_vertices_lt :
    max (rowUpper barC 1 1)
      (max (rowUpper barC 1 (barC - 1)) (rowUpper barC (barC - 1) 1)) <
        -8 / 25 := by
  rw [max_lt_iff, max_lt_iff]
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  constructor
  · norm_num [rowUpper, rowConstant, rowPositiveConstant, rowA1, rowA2, rowK,
      rowK1, rowK2, rowK3,
      rowRho1, rowRho2, rowRho3, rowSigma, rowEta] at hlower hupper ⊢
    nlinarith [sq_nonneg (barC - 13866128436518096 / 10 ^ 16)]
  · constructor
    · norm_num [rowUpper, rowConstant, rowPositiveConstant, rowA1, rowA2, rowK,
        rowK1, rowK2, rowK3,
        rowRho1, rowRho2, rowRho3, rowSigma, rowEta] at hlower hupper ⊢
      nlinarith [sq_nonneg (barC - 13866128436518096 / 10 ^ 16)]
    · norm_num [rowUpper, rowConstant, rowPositiveConstant, rowA1, rowA2, rowK,
        rowK1, rowK2, rowK3,
        rowRho1, rowRho2, rowRho3, rowSigma, rowEta] at hlower hupper ⊢
      nlinarith [sq_nonneg (barC - 13866128436518100 / 10 ^ 16)]

private theorem row_preconditioner_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p w₁ w₂ : E) (hp : ‖p‖ ≤ 1)
    (he : ‖e‖ = 1) (hseparation : barC ≤ ‖w₁ - w₂‖) :
    2 * ⟪p, rowK1 • w₁ + rowK2 • w₂ - rowK • e⟫_ℝ ≤ rowSigma +
      (rowK * (rowK1 * ‖w₁‖ ^ 2 + rowK2 * ‖w₂‖ ^ 2) -
        rowK1 * rowK2 * barC ^ 2 + rowK ^ 2 -
        2 * rowK * ⟪e, rowK1 • w₁ + rowK2 • w₂⟫_ℝ) / rowSigma := by
  let z := rowK1 • w₁ + rowK2 • w₂ - rowK • e
  have hk1 : 0 ≤ rowK1 := by norm_num [rowK1, rowRho1]
  have hk2 : 0 ≤ rowK2 := by norm_num [rowK2, rowRho2]
  have hK : 0 ≤ rowK := add_nonneg hk1 hk2
  have hseparation_sq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hpz : 2 * ⟪p, z⟫_ℝ ≤ 2 * ‖z‖ := by
    have hinner := real_inner_le_norm p z
    nlinarith [norm_nonneg z, mul_le_mul_of_nonneg_right hp (norm_nonneg z)]
  have hz_eq :
      ‖z‖ ^ 2 = rowK * (rowK1 * ‖w₁‖ ^ 2 + rowK2 * ‖w₂‖ ^ 2) -
        rowK1 * rowK2 * ‖w₁ - w₂‖ ^ 2 + rowK ^ 2 -
        2 * rowK * ⟪e, rowK1 • w₁ + rowK2 • w₂⟫_ℝ := by
    dsimp only [z]
    rw [norm_sub_sq_real, weighted_norm_sq w₁ w₂ hk1 hk2]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK, he,
      real_inner_smul_right]
    rw [real_inner_comm (rowK1 • w₁ + rowK2 • w₂) e]
    simp only [rowK]
    ring
  have hz_upper :
      ‖z‖ ^ 2 ≤ rowK * (rowK1 * ‖w₁‖ ^ 2 + rowK2 * ‖w₂‖ ^ 2) -
        rowK1 * rowK2 * barC ^ 2 + rowK ^ 2 -
        2 * rowK * ⟪e, rowK1 • w₁ + rowK2 • w₂⟫_ℝ := by
    have hproduct := mul_le_mul_of_nonneg_left hseparation_sq (mul_nonneg hk1 hk2)
    nlinarith
  have hsigma : 0 < rowSigma := by norm_num [rowSigma]
  have hpz_upper : 2 * ⟪p, z⟫_ℝ ≤ rowSigma + ‖z‖ ^ 2 / rowSigma :=
    hpz.trans (two_mul_norm_tangent z hsigma)
  have hz_scaled := (div_le_div_iff_of_pos_right hsigma).2 hz_upper
  dsimp only [z] at hpz_upper ⊢
  nlinarith

private theorem row_tangent_sq_expansion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p w₁ w₂ : E) (he : ‖e‖ = 1) :
    rowK1 * (‖e - p - w₁‖ ^ 2 + rowRho1 ^ 2) +
        rowK2 * (‖e - p - w₂‖ ^ 2 + rowRho2 ^ 2) +
          rowK3 * (‖e - w₁‖ ^ 2 + rowRho3 ^ 2) =
      rowK1 * (1 + rowRho1 ^ 2) + rowK2 * (1 + rowRho2 ^ 2) +
        rowK3 * (1 + rowRho3 ^ 2) + (rowK1 + rowK3) * ‖w₁‖ ^ 2 +
        rowK2 * ‖w₂‖ ^ 2 - 2 * ⟪e, (rowK1 + rowK3) • w₁ + rowK2 • w₂⟫_ℝ +
        rowK * ‖p‖ ^ 2 +
          2 * ⟪p, rowK1 • w₁ + rowK2 • w₂ - rowK • e⟫_ℝ := by
  rw [norm_sub_sub_sq e p w₁, norm_sub_sub_sq e p w₂, norm_sub_sq_real e w₁]
  simp only [he, one_pow, inner_sub_right, inner_add_right, real_inner_smul_right]
  rw [real_inner_comm p e]
  simp only [rowK]
  ring

private theorem row_tangent_sum_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p w₁ w₂ : E) (he : ‖e‖ = 1) (hp : ‖p‖ ≤ 1)
    (hseparation : barC ≤ ‖w₁ - w₂‖) :
    10 * ‖e - p - w₁‖ + 10 * ‖e - p - w₂‖ + 9 * ‖e - w₁‖ ≤
      rowPositiveConstant barC + rowA1 * ‖w₁‖ ^ 2 + rowA2 * ‖w₂‖ ^ 2 -
        2 * ⟪e, rowA1 • w₁ + rowA2 • w₂⟫_ℝ := by
  have htangent1 := weighted_norm_tangent (e - p - w₁) 10 rowRho1 rowK1
    (by norm_num [rowRho1])
    (by norm_num [rowK1, rowRho1]) (by norm_num)
  have htangent2 := weighted_norm_tangent (e - p - w₂) 10 rowRho2 rowK2
    (by norm_num [rowRho2])
    (by norm_num [rowK2, rowRho2]) (by norm_num)
  have htangent3 := weighted_norm_tangent (e - w₁) 9 rowRho3 rowK3
    (by norm_num [rowRho3])
    (by norm_num [rowK3, rowRho3]) (by norm_num)
  have htangentSum :
      10 * ‖e - p - w₁‖ + 10 * ‖e - p - w₂‖ + 9 * ‖e - w₁‖ ≤
        rowK1 * (‖e - p - w₁‖ ^ 2 + rowRho1 ^ 2) +
          rowK2 * (‖e - p - w₂‖ ^ 2 + rowRho2 ^ 2) +
            rowK3 * (‖e - w₁‖ ^ 2 + rowRho3 ^ 2) := by linarith
  have hpz := row_preconditioner_inner_le e p w₁ w₂ hp he hseparation
  have hp_sq : ‖p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p]
  have hK : 0 ≤ rowK := by norm_num [rowK, rowK1, rowK2, rowRho1, rowRho2]
  have hkp : rowK * ‖p‖ ^ 2 ≤ rowK := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp_sq hK
  calc
    _ ≤ _ := htangentSum
    _ = _ := row_tangent_sq_expansion e p w₁ w₂ he
    _ ≤ rowK1 * (1 + rowRho1 ^ 2) + rowK2 * (1 + rowRho2 ^ 2) +
        rowK3 * (1 + rowRho3 ^ 2) + (rowK1 + rowK3) * ‖w₁‖ ^ 2 +
        rowK2 * ‖w₂‖ ^ 2 - 2 * ⟪e, (rowK1 + rowK3) • w₁ + rowK2 • w₂⟫_ℝ +
        rowK + (rowSigma +
          (rowK * (rowK1 * ‖w₁‖ ^ 2 + rowK2 * ‖w₂‖ ^ 2) -
            rowK1 * rowK2 * barC ^ 2 + rowK ^ 2 -
            2 * rowK * ⟪e, rowK1 • w₁ + rowK2 • w₂⟫_ℝ) / rowSigma) := by linarith
    _ = _ := by
      simp only [rowPositiveConstant, rowA1, rowA2, rowK, inner_add_right,
        real_inner_smul_right]
      ring

private theorem row_orientation_le_upper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e w₁ w₂ : E) (he : ‖e‖ = 1)
    (hseparation : barC ≤ ‖w₁ - w₂‖) :
    rowPositiveConstant barC + rowA1 * ‖w₁‖ ^ 2 + rowA2 * ‖w₂‖ ^ 2 -
        2 * ⟪e, rowA1 • w₁ + rowA2 • w₂⟫_ℝ ≤
      rowPositiveConstant barC + rowA1 * ‖w₁‖ ^ 2 + rowA2 * ‖w₂‖ ^ 2 +
        rowEta + ((rowA1 + rowA2) * (rowA1 * ‖w₁‖ ^ 2 + rowA2 * ‖w₂‖ ^ 2) -
          rowA1 * rowA2 * barC ^ 2) / rowEta := by
  have hk1 : 0 ≤ rowK1 := by norm_num [rowK1, rowRho1]
  have hk2 : 0 ≤ rowK2 := by norm_num [rowK2, rowRho2]
  have hk3 : 0 ≤ rowK3 := by norm_num [rowK3, rowRho3]
  have hK : 0 ≤ rowK := add_nonneg hk1 hk2
  have ha1 : 0 ≤ rowA1 := add_nonneg (add_nonneg hk1 hk3) <|
    div_nonneg (mul_nonneg hK hk1) (by norm_num [rowSigma])
  have ha2 : 0 ≤ rowA2 := add_nonneg hk2 <|
    div_nonneg (mul_nonneg hK hk2) (by norm_num [rowSigma])
  let u := rowA1 • w₁ + rowA2 • w₂
  have hseparation_sq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hu_sq : ‖u‖ ^ 2 ≤
      (rowA1 + rowA2) * (rowA1 * ‖w₁‖ ^ 2 + rowA2 * ‖w₂‖ ^ 2) -
        rowA1 * rowA2 * barC ^ 2 := by
    rw [show ‖u‖ ^ 2 =
      (rowA1 + rowA2) * (rowA1 * ‖w₁‖ ^ 2 + rowA2 * ‖w₂‖ ^ 2) -
        rowA1 * rowA2 * ‖w₁ - w₂‖ ^ 2 by
      exact weighted_norm_sq w₁ w₂ ha1 ha2]
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_left hseparation_sq (mul_nonneg ha1 ha2)) _
  have horientation : -2 * ⟪e, u⟫_ℝ ≤ rowEta + ‖u‖ ^ 2 / rowEta := by
    have hinner := real_inner_le_norm (-e) u
    simp only [inner_neg_left, norm_neg, he, one_mul] at hinner
    calc
      -2 * ⟪e, u⟫_ℝ = 2 * (-⟪e, u⟫_ℝ) := by ring
      _ ≤ 2 * ‖u‖ := mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ rowEta + ‖u‖ ^ 2 / rowEta := two_mul_norm_tangent u (by norm_num [rowEta])
  have heta : 0 < rowEta := by norm_num [rowEta]
  have hu_scaled := (div_le_div_iff_of_pos_right heta).2 hu_sq
  dsimp only [u] at horientation hu_scaled
  nlinarith

private theorem rowWeighted_le_upper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p w₁ w₂ : E) (he : ‖e‖ = 1) (hp : ‖p‖ ≤ 1)
    (hseparation : barC ≤ ‖w₁ - w₂‖) :
    10 * (‖e - p - w₁‖ + ‖e - p - w₂‖ - (4 * barC ^ 2 - 3 * barC + 2)) +
        9 * (‖e - w₁‖ - (barC - 1 +
          ((barC - 1) * (‖w₁‖ + barC) + (barC + 1) * ‖w₂‖) / 2)) ≤
      rowUpper barC ‖w₁‖ ‖w₂‖ := by
  have htangent := row_tangent_sum_le e p w₁ w₂ he hp hseparation
  have horientation := row_orientation_le_upper e w₁ w₂ he hseparation
  simp only [rowUpper, rowConstant] at ⊢
  linarith

private theorem rowWeighted_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e p w₁ w₂ : E) (he : ‖e‖ = 1) (hp : ‖p‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hseparation : barC ≤ ‖w₁ - w₂‖) :
    10 * (‖e - p - w₁‖ + ‖e - p - w₂‖ - (4 * barC ^ 2 - 3 * barC + 2)) +
        9 * (‖e - w₁‖ - (barC - 1 +
          ((barC - 1) * (‖w₁‖ + barC) + (barC + 1) * ‖w₂‖) / 2)) < 0 := by
  have hsum : barC ≤ ‖w₁‖ + ‖w₂‖ :=
    hseparation.trans (norm_sub_le w₁ w₂)
  have hupper := rowWeighted_le_upper e p w₁ w₂ he hp hseparation
  have hvertices := rowUpper_le_vertices hw₁ hw₂ hsum
  exact (hupper.trans hvertices).trans_lt (rowUpper_vertices_lt.trans (by norm_num))

/-- A four-child row obstruction is incompatible with the corresponding root-triangle endpoint. -/
theorem row_obstruction_excludes_root_triangle_endpoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p w₁ w₂ : E) (he : ‖e‖ = 1) (hp : ‖p‖ ≤ 1)
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hseparation : barC ≤ ‖w₁ - w₂‖)
    (hrow : 4 * barC ^ 2 - 3 * barC + 2 ≤
      ‖e - p - w₁‖ + ‖e - p - w₂‖) :
    ‖e - w₁‖ < barC - 1 +
      ((barC - 1) * (‖w₁‖ + barC) + (barC + 1) * ‖w₂‖) / 2 := by
  have hweighted := rowWeighted_lt e p w₁ w₂ he hp hw₁ hw₂ hseparation
  by_contra hendpoint
  rw [not_lt] at hendpoint
  nlinarith

/-- Support `17`: the red root of radius one against the canonical blue triangle. -/
def redRootBlueTrianglePacking (configuration : SixPointConfiguration)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    SixPointPacking configuration where
  support := {(.red, .root), (.blue, .root), (.blue, .left), (.blue, .right)}
  meets_color color := by
    cases color
    · exact ⟨.root, by simp⟩
    · exact ⟨.root, by simp⟩
  radius i := by
    rcases i with ⟨⟨color, label⟩, hlabel⟩
    cases color <;> cases label
    · exact ⟨1, by norm_num, by norm_num⟩
    · simp at hlabel
    · simp at hlabel
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .root,
        canonicalTriangleRadius_le_one _ _ _ hblueLeft hblueRight .root⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .left,
        canonicalTriangleRadius_le_one _ _ _ hblueLeft hblueRight .left⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .right,
        canonicalTriangleRadius_le_one _ _ _ hblueLeft hblueRight .right⟩
  same_color_disjoint i j hij hcolor := by
    rcases i with ⟨⟨ci, li⟩, hi⟩
    rcases j with ⟨⟨cj, lj⟩, hj⟩
    simp only at hcolor
    subst cj
    cases ci
    · cases li
      · cases lj
        · exact (hij (Subtype.ext rfl)).elim
        · simp at hj
        · simp at hj
      · simp at hi
      · simp at hi
    · cases li <;> cases lj
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_left_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_left_add_right _ _ _).le
      · exact (hij (Subtype.ext rfl)).elim

/-- Support `71`: the blue root of radius one against the canonical red triangle. -/
def blueRootRedTrianglePacking (configuration : SixPointConfiguration)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    SixPointPacking configuration where
  support := {(.blue, .root), (.red, .root), (.red, .left), (.red, .right)}
  meets_color color := by
    cases color
    · exact ⟨.root, by simp⟩
    · exact ⟨.root, by simp⟩
  radius i := by
    rcases i with ⟨⟨color, label⟩, hlabel⟩
    cases color <;> cases label
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .root,
        canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .root⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .left,
        canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .left⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .right,
        canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .right⟩
    · exact ⟨1, by norm_num, by norm_num⟩
    · simp at hlabel
    · simp at hlabel
  same_color_disjoint i j hij hcolor := by
    rcases i with ⟨⟨ci, li⟩, hi⟩
    rcases j with ⟨⟨cj, lj⟩, hj⟩
    simp only at hcolor
    subst cj
    cases ci
    · cases li <;> cases lj
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_left_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_left_add_right _ _ _).le
      · exact (hij (Subtype.ext rfl)).elim
    · cases li
      · cases lj
        · exact (hij (Subtype.ext rfl)).elim
        · simp at hj
        · simp at hj
      · simp at hi
      · simp at hi

/-- The total radius of support `17` is one plus the blue semiperimeter. -/
theorem redRootBlueTrianglePacking_totalRadius (configuration : SixPointConfiguration)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    (redRootBlueTrianglePacking configuration hblueLeft hblueRight).totalRadius =
      1 + (dist (configuration .blue .root) (configuration .blue .left) +
        dist (configuration .blue .root) (configuration .blue .right) +
        dist (configuration .blue .left) (configuration .blue .right)) / 2 := by
  let packing := redRootBlueTrianglePacking configuration hblueLeft hblueRight
  let value : SixPointIndex → ℝ
    | (.red, .root) => 1
    | (.red, .left) => 0
    | (.red, .right) => 0
    | (.blue, label) => canonicalTriangleRadius (configuration .blue .root)
        (configuration .blue .left) (configuration .blue .right) label
  rw [SixPointPacking.totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, value i := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨color, label⟩, hi⟩ -
      cases color <;> cases label <;>
        simp [redRootBlueTrianglePacking, value] at hi ⊢
    _ = ∑ i ∈ packing.support, value i := Finset.sum_attach _ _
    _ = _ := by
      simp [packing, redRootBlueTrianglePacking, value, canonicalTriangleRadius]
      ring

/-- The total radius of support `71` is one plus the red semiperimeter. -/
theorem blueRootRedTrianglePacking_totalRadius (configuration : SixPointConfiguration)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    (blueRootRedTrianglePacking configuration hredLeft hredRight).totalRadius =
      1 + (dist (configuration .red .root) (configuration .red .left) +
        dist (configuration .red .root) (configuration .red .right) +
        dist (configuration .red .left) (configuration .red .right)) / 2 := by
  let packing := blueRootRedTrianglePacking configuration hredLeft hredRight
  let value : SixPointIndex → ℝ
    | (.red, label) => canonicalTriangleRadius (configuration .red .root)
        (configuration .red .left) (configuration .red .right) label
    | (.blue, .root) => 1
    | (.blue, .left) => 0
    | (.blue, .right) => 0
  rw [SixPointPacking.totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, value i := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨color, label⟩, hi⟩ -
      cases color <;> cases label <;>
        simp [blueRootRedTrianglePacking, value] at hi ⊢
    _ = ∑ i ∈ packing.support, value i := Finset.sum_attach _ _
    _ = _ := by
      simp [packing, blueRootRedTrianglePacking, value, canonicalTriangleRadius]
      ring

private def trianglePoint {X : Type*} (root left right : X) : SixPointLabel → X
  | .root => root
  | .left => left
  | .right => right

@[simp] private theorem trianglePoint_configuration (configuration : SixPointConfiguration)
    (color : SixPointColor) (label : SixPointLabel) :
    trianglePoint (configuration color .root) (configuration color .left)
      (configuration color .right) label = configuration color label := by
  cases label <;> rfl

private theorem redRootBlueTrianglePacking_radius_blue
    (configuration : SixPointConfiguration)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    (label : SixPointLabel)
    (hlabel : (.blue, label) ∈
      (redRootBlueTrianglePacking configuration hblueLeft hblueRight).support) :
    (redRootBlueTrianglePacking configuration hblueLeft hblueRight).radius
        ⟨(.blue, label), hlabel⟩ =
      canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
        (configuration .blue .right) label := by
  cases label <;> rfl

private theorem blueRootRedTrianglePacking_radius_red
    (configuration : SixPointConfiguration)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1)
    (label : SixPointLabel)
    (hlabel : (.red, label) ∈
      (blueRootRedTrianglePacking configuration hredLeft hredRight).support) :
    (blueRootRedTrianglePacking configuration hredLeft hredRight).radius
        ⟨(.red, label), hlabel⟩ =
      canonicalTriangleRadius (configuration .red .root) (configuration .red .left)
        (configuration .red .right) label := by
  cases label <;> rfl

private theorem canonicalTriangle_pair_le {X : Type*} [PseudoMetricSpace X]
    (root left right : X) (hleft : dist root left ≤ 1) (hright : dist root right ≤ 1)
    {target : ℝ} (htarget : 2 ≤ target)
    (hdist : ∀ leftLabel rightLabel,
      2 * dist (trianglePoint root left right leftLabel)
        (trianglePoint root left right rightLabel) ≤ target)
    (leftLabel rightLabel : SixPointLabel) :
    dist (trianglePoint root left right leftLabel) (trianglePoint root left right rightLabel) +
        canonicalTriangleRadius root left right leftLabel +
      canonicalTriangleRadius root left right rightLabel ≤ target := by
  cases leftLabel <;> cases rightLabel
  · simp only [trianglePoint, dist_self, zero_add]
    nlinarith [canonicalTriangleRadius_le_one root left right hleft hright .root]
  · simp only [trianglePoint]
    nlinarith [canonicalTriangleRadius_root_add_left root left right, hdist .root .left]
  · simp only [trianglePoint]
    nlinarith [canonicalTriangleRadius_root_add_right root left right, hdist .root .right]
  · simp only [trianglePoint]
    nlinarith [canonicalTriangleRadius_root_add_left root left right, hdist .left .root,
      dist_comm left root]
  · simp only [trianglePoint, dist_self, zero_add]
    nlinarith [canonicalTriangleRadius_le_one root left right hleft hright .left]
  · simp only [trianglePoint]
    have h := hdist .left .right
    simp only [trianglePoint] at h
    nlinarith [canonicalTriangleRadius_left_add_right root left right]
  · simp only [trianglePoint]
    nlinarith [canonicalTriangleRadius_root_add_right root left right, hdist .right .root,
      dist_comm right root]
  · simp only [trianglePoint]
    have h := hdist .right .left
    simp only [trianglePoint] at h
    nlinarith [canonicalTriangleRadius_left_add_right root left right, dist_comm right left]
  · simp only [trianglePoint, dist_self, zero_add]
    nlinarith [canonicalTriangleRadius_le_one root left right hleft hright .right]

private theorem triangle_pair_dist_le (configuration : SixPointConfiguration)
    (color : SixPointColor)
    (hleft : dist (configuration color .root) (configuration color .left) ≤ 1)
    (hright : dist (configuration color .root) (configuration color .right) ≤ 1)
    {target : ℝ} (htargetTwo : 2 ≤ target)
    (htargetSibling :
      2 * dist (configuration color .left) (configuration color .right) ≤ target) :
    ∀ leftLabel rightLabel,
      2 * dist (configuration color leftLabel) (configuration color rightLabel) ≤ target := by
  intro leftLabel rightLabel
  cases leftLabel <;> cases rightLabel
  · simpa using le_trans (by norm_num : (0 : ℝ) ≤ 2) htargetTwo
  · nlinarith [hleft]
  · nlinarith [hright]
  · rw [dist_comm]
    nlinarith [hleft]
  · simpa using le_trans (by norm_num : (0 : ℝ) ≤ 2) htargetTwo
  · exact htargetSibling
  · rw [dist_comm]
    nlinarith [hright]
  · simpa only [dist_comm] using htargetSibling
  · simpa using le_trans (by norm_num : (0 : ℝ) ≤ 2) htargetTwo

private theorem red_root_blue_triangle_cross_le (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) {target : ℝ}
    (hroot : 2 +
      (dist (configuration .blue .root) (configuration .blue .left) +
        dist (configuration .blue .root) (configuration .blue .right) -
          dist (configuration .blue .left) (configuration .blue .right)) / 2 ≤ target)
    (hleft :
      ‖configuration.rootDisplacement - configuration.bluePullback .left‖ + 1 +
        (dist (configuration .blue .root) (configuration .blue .left) +
          dist (configuration .blue .left) (configuration .blue .right) -
            dist (configuration .blue .root) (configuration .blue .right)) / 2 ≤ target)
    (hright :
      ‖configuration.rootDisplacement - configuration.bluePullback .right‖ + 1 +
        (dist (configuration .blue .root) (configuration .blue .right) +
          dist (configuration .blue .left) (configuration .blue .right) -
            dist (configuration .blue .root) (configuration .blue .left)) / 2 ≤ target) :
    ∀ label,
      dist (configuration .red .root) (configuration .blue label) + 1 +
        canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
          (configuration .blue .right) label ≤ target := by
  intro label
  cases label
  · simp only [canonicalTriangleRadius]
    rw [h.root_distance]
    simpa only [one_add_one_eq_two] using hroot
  · simp only [canonicalTriangleRadius, configuration.dist_red_blue_eq_norm]
    simpa only [SixPointConfiguration.redDisplacement, sub_self, sub_zero] using hleft
  · simp only [canonicalTriangleRadius, configuration.dist_red_blue_eq_norm]
    simpa only [SixPointConfiguration.redDisplacement, sub_self, sub_zero] using hright

private theorem blue_root_red_triangle_cross_le (configuration : SixPointConfiguration)
    (h : configuration.IsAdmissibleAt barS) {target : ℝ}
    (hroot : 2 +
      (dist (configuration .red .root) (configuration .red .left) +
        dist (configuration .red .root) (configuration .red .right) -
          dist (configuration .red .left) (configuration .red .right)) / 2 ≤ target)
    (hleft : ‖configuration.rootDisplacement - configuration.redDisplacement .left‖ + 1 +
      (dist (configuration .red .root) (configuration .red .left) +
        dist (configuration .red .left) (configuration .red .right) -
          dist (configuration .red .root) (configuration .red .right)) / 2 ≤ target)
    (hright : ‖configuration.rootDisplacement - configuration.redDisplacement .right‖ + 1 +
      (dist (configuration .red .root) (configuration .red .right) +
        dist (configuration .red .left) (configuration .red .right) -
          dist (configuration .red .root) (configuration .red .left)) / 2 ≤ target) :
    ∀ label,
      dist (configuration .blue .root) (configuration .red label) + 1 +
        canonicalTriangleRadius (configuration .red .root) (configuration .red .left)
          (configuration .red .right) label ≤ target := by
  intro label
  cases label
  · simp only [canonicalTriangleRadius, dist_comm (configuration .blue .root)]
    rw [h.root_distance]
    simpa only [one_add_one_eq_two] using hroot
  · simp only [canonicalTriangleRadius, dist_comm (configuration .blue .root),
      configuration.dist_red_blue_eq_norm]
    simpa only [SixPointConfiguration.bluePullback, sub_self, sub_zero] using hleft
  · simp only [canonicalTriangleRadius, dist_comm (configuration .blue .root),
      configuration.dist_red_blue_eq_norm]
    simpa only [SixPointConfiguration.bluePullback, sub_self, sub_zero] using hright

private theorem redRootBlueTrianglePacking_virtualDiameter_le
    (configuration : SixPointConfiguration)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    {target : ℝ} (hroot : 2 ≤ target)
    (hblue : ∀ leftLabel rightLabel,
      2 * dist (configuration .blue leftLabel) (configuration .blue rightLabel) ≤ target)
    (hcross : ∀ label,
      dist (configuration .red .root) (configuration .blue label) + 1 +
        canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
          (configuration .blue .right) label ≤ target) :
    (redRootBlueTrianglePacking configuration hblueLeft hblueRight).virtualDiameter ≤
      target := by
  let packing := redRootBlueTrianglePacking configuration hblueLeft hblueRight
  have hpair (i j : packing.support) :
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
        packing.radius i + packing.radius j ≤ target := by
    rcases i with ⟨⟨leftColor, leftLabel⟩, hleft⟩
    rcases j with ⟨⟨rightColor, rightLabel⟩, hright⟩
    cases leftColor <;> cases rightColor
    · cases leftLabel <;> cases rightLabel
      · dsimp [packing, redRootBlueTrianglePacking]
        simpa only [dist_self, zero_add, one_add_one_eq_two] using hroot
      all_goals simp [packing, redRootBlueTrianglePacking] at hleft hright
    · cases leftLabel
      · cases rightLabel
        · simpa [packing, redRootBlueTrianglePacking] using hcross .root
        · simpa [packing, redRootBlueTrianglePacking] using hcross .left
        · simpa [packing, redRootBlueTrianglePacking] using hcross .right
      · simp [packing, redRootBlueTrianglePacking] at hleft
      · simp [packing, redRootBlueTrianglePacking] at hleft
    · cases rightLabel
      · cases leftLabel
        · simpa [packing, redRootBlueTrianglePacking, dist_comm, add_comm, add_left_comm, add_assoc]
            using hcross .root
        · simpa [packing, redRootBlueTrianglePacking, dist_comm, add_comm, add_left_comm, add_assoc]
            using hcross .left
        · simpa [packing, redRootBlueTrianglePacking, dist_comm, add_comm, add_left_comm, add_assoc]
            using hcross .right
      · simp [packing, redRootBlueTrianglePacking] at hright
      · simp [packing, redRootBlueTrianglePacking] at hright
    · let hdist : ∀ leftLabel rightLabel,
          2 * dist (trianglePoint (configuration .blue .root) (configuration .blue .left)
            (configuration .blue .right) leftLabel)
            (trianglePoint (configuration .blue .root) (configuration .blue .left)
              (configuration .blue .right) rightLabel) ≤ target := by
        intro leftLabel rightLabel
        simpa only [trianglePoint_configuration] using hblue leftLabel rightLabel
      dsimp only [packing]
      rw [redRootBlueTrianglePacking_radius_blue configuration hblueLeft hblueRight
          leftLabel hleft,
        redRootBlueTrianglePacking_radius_blue configuration hblueLeft hblueRight
          rightLabel hright]
      simpa only [trianglePoint_configuration] using
        canonicalTriangle_pair_le (configuration .blue .root) (configuration .blue .left)
          (configuration .blue .right) hblueLeft hblueRight hroot hdist leftLabel rightLabel
  unfold SixPointPacking.virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  exact hpair i j

private theorem blueRootRedTrianglePacking_virtualDiameter_le
    (configuration : SixPointConfiguration)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1)
    {target : ℝ} (hroot : 2 ≤ target)
    (hred : ∀ leftLabel rightLabel,
      2 * dist (configuration .red leftLabel) (configuration .red rightLabel) ≤ target)
    (hcross : ∀ label,
      dist (configuration .blue .root) (configuration .red label) + 1 +
        canonicalTriangleRadius (configuration .red .root) (configuration .red .left)
          (configuration .red .right) label ≤ target) :
    (blueRootRedTrianglePacking configuration hredLeft hredRight).virtualDiameter ≤
      target := by
  let packing := blueRootRedTrianglePacking configuration hredLeft hredRight
  have hpair (i j : packing.support) :
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
        packing.radius i + packing.radius j ≤ target := by
    rcases i with ⟨⟨leftColor, leftLabel⟩, hleft⟩
    rcases j with ⟨⟨rightColor, rightLabel⟩, hright⟩
    cases leftColor <;> cases rightColor
    · let hdist : ∀ leftLabel rightLabel,
          2 * dist (trianglePoint (configuration .red .root) (configuration .red .left)
            (configuration .red .right) leftLabel)
            (trianglePoint (configuration .red .root) (configuration .red .left)
              (configuration .red .right) rightLabel) ≤ target := by
        intro leftLabel rightLabel
        simpa only [trianglePoint_configuration] using hred leftLabel rightLabel
      dsimp only [packing]
      rw [blueRootRedTrianglePacking_radius_red configuration hredLeft hredRight
          leftLabel hleft,
        blueRootRedTrianglePacking_radius_red configuration hredLeft hredRight
          rightLabel hright]
      simpa only [trianglePoint_configuration] using
        canonicalTriangle_pair_le (configuration .red .root) (configuration .red .left)
          (configuration .red .right) hredLeft hredRight hroot hdist leftLabel rightLabel
    · cases rightLabel
      · cases leftLabel
        · simpa [packing, blueRootRedTrianglePacking, dist_comm, add_comm, add_left_comm, add_assoc]
            using hcross .root
        · simpa [packing, blueRootRedTrianglePacking, dist_comm, add_comm, add_left_comm, add_assoc]
            using hcross .left
        · simpa [packing, blueRootRedTrianglePacking, dist_comm, add_comm, add_left_comm, add_assoc]
            using hcross .right
      · simp [packing, blueRootRedTrianglePacking] at hright
      · simp [packing, blueRootRedTrianglePacking] at hright
    · cases leftLabel
      · cases rightLabel
        · simpa [packing, blueRootRedTrianglePacking, add_assoc] using hcross .root
        · simpa [packing, blueRootRedTrianglePacking, add_assoc] using hcross .left
        · simpa [packing, blueRootRedTrianglePacking, add_assoc] using hcross .right
      · simp [packing, blueRootRedTrianglePacking] at hleft
      · simp [packing, blueRootRedTrianglePacking] at hleft
    · cases leftLabel <;> cases rightLabel
      · dsimp [packing, blueRootRedTrianglePacking]
        simpa only [dist_self, zero_add, one_add_one_eq_two] using hroot
      all_goals simp [packing, blueRootRedTrianglePacking] at hleft hright
  unfold SixPointPacking.virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  exact hpair i j

private theorem barC_row_rescue_gaps :
    0 < 3 * barC - 4 ∧ 0 < barC ^ 2 + (3 / 2) * barC - 3 ∧
      2 < barC * (1 + barC) := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num at hlower hupper ⊢
  constructor
  · linarith
  · constructor <;> nlinarith [sq_nonneg (barC - 1)]

private theorem root_triangle_target_bounds {E : Type*} [NormedAddCommGroup E]
    (e w₁ w₂ : E) (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1)
    (hM : barC ≤ ‖w₁ - w₂‖)
    (hleft : ‖e - w₁‖ < barC - 1 +
      ((barC - 1) * (‖w₁‖ + barC) + (barC + 1) * ‖w₂‖) / 2)
    (hright : ‖e - w₂‖ < barC - 1 +
      ((barC - 1) * (‖w₂‖ + barC) + (barC + 1) * ‖w₁‖) / 2) :
    let M := ‖w₁ - w₂‖
    let target := barC * (1 + (‖w₁‖ + ‖w₂‖ + M) / 2)
    2 ≤ target ∧ 2 * M ≤ target ∧
      2 + (‖w₁‖ + ‖w₂‖ - M) / 2 ≤ target ∧
      ‖e - w₁‖ + 1 + (‖w₁‖ + M - ‖w₂‖) / 2 ≤ target ∧
      ‖e - w₂‖ + 1 + (‖w₂‖ + M - ‖w₁‖) / 2 ≤ target := by
  dsimp only
  have hsum : ‖w₁ - w₂‖ ≤ ‖w₁‖ + ‖w₂‖ := norm_sub_le w₁ w₂
  have hsumTwo : ‖w₁‖ + ‖w₂‖ ≤ 2 := by linarith
  have hMtwo : ‖w₁ - w₂‖ ≤ 2 := hsum.trans hsumTwo
  have htargetLower :
      barC * (1 + ‖w₁ - w₂‖) ≤
        barC * (1 + (‖w₁‖ + ‖w₂‖ + ‖w₁ - w₂‖) / 2) := by
    apply mul_le_mul_of_nonneg_left _ barC_pos.le
    linarith
  have hcc := mul_le_mul_of_nonneg_left hM barC_pos.le
  have htargetTwo : 2 ≤
      barC * (1 + (‖w₁‖ + ‖w₂‖ + ‖w₁ - w₂‖) / 2) :=
    (barC_row_rescue_gaps.2.2.le.trans (by nlinarith)).trans htargetLower
  have hnegative : barC - 2 ≤ 0 := by linarith [one_lt_barC_and_barC_lt_two.2]
  have hMpart := mul_le_mul_of_nonpos_left hMtwo hnegative
  have htargetM : 2 * ‖w₁ - w₂‖ ≤
      barC * (1 + (‖w₁‖ + ‖w₂‖ + ‖w₁ - w₂‖) / 2) :=
    (show 2 * ‖w₁ - w₂‖ ≤ barC * (1 + ‖w₁ - w₂‖) by
      nlinarith [barC_row_rescue_gaps.1]).trans htargetLower
  have hMmul : barC * (barC + 1) ≤ barC * (‖w₁ - w₂‖ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) barC_pos.le
  have hMcoef := mul_le_mul_of_nonneg_left hM
    (sub_nonneg.mpr one_lt_barC_and_barC_lt_two.1.le)
  exact ⟨htargetTwo, htargetM, by nlinarith [barC_row_rescue_gaps.2.1],
    by nlinarith, by nlinarith⟩

private theorem row_obstruction_endpoint_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (redLabel : SixPointLabel) (hredLabel : redLabel ≠ .root)
    (hrow :
      2 + 2 * (barC - 1) *
          dist (configuration .red .left) (configuration .red .right) +
          (2 * barC - 1) *
            dist (configuration .blue .left) (configuration .blue .right) ≤
        dist (configuration .red redLabel) (configuration .blue .left) +
          dist (configuration .red redLabel) (configuration .blue .right)) :
    let e := configuration.rootDisplacement
    let w₁ := configuration.bluePullback .left
    let w₂ := configuration.bluePullback .right
    ‖e - w₁‖ < barC - 1 +
        ((barC - 1) * (‖w₁‖ + barC) + (barC + 1) * ‖w₂‖) / 2 ∧
      ‖e - w₂‖ < barC - 1 +
        ((barC - 1) * (‖w₂‖ + barC) + (barC + 1) * ‖w₁‖) / 2 := by
  dsimp only
  let p := configuration.redDisplacement redLabel
  have he := configuration.norm_rootDisplacement h
  have hp := configuration.norm_redDisplacement_le_one h hredLabel
  have hw₁ := configuration.norm_bluePullback_le_one h (by simp : SixPointLabel.left ≠ .root)
  have hw₂ := configuration.norm_bluePullback_le_one h (by simp : SixPointLabel.right ≠ .root)
  have hM : barC ≤
      ‖configuration.bluePullback .left - configuration.bluePullback .right‖ := by
    have hM' := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hM'
    exact hM'
  have hL := h.sibling_distance .red
  rw [barS, show 2 * (barC / 2) = barC by ring] at hL
  have hMdist : dist (configuration .blue .left) (configuration .blue .right) =
      ‖configuration.bluePullback .left - configuration.bluePullback .right‖ := by
    rw [← configuration.dist_bluePullback .left .right, dist_eq_norm]
  have hfactor1 : 0 ≤ 2 * (barC - 1) := by nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hfactor2 : 0 ≤ 2 * barC - 1 := by nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hredPart := mul_le_mul_of_nonneg_left hL hfactor1
  have hbluePart := mul_le_mul_of_nonneg_left hM hfactor2
  rw [hMdist, configuration.dist_red_blue_eq_norm redLabel .left,
    configuration.dist_red_blue_eq_norm redLabel .right] at hrow
  have hrowVector : 4 * barC ^ 2 - 3 * barC + 2 ≤
      ‖configuration.rootDisplacement - p - configuration.bluePullback .left‖ +
        ‖configuration.rootDisplacement - p - configuration.bluePullback .right‖ := by nlinarith
  exact ⟨row_obstruction_excludes_root_triangle_endpoint _ p _ _ he hp hw₁ hw₂ hM hrowVector,
    row_obstruction_excludes_root_triangle_endpoint _ p _ _ he hp hw₂ hw₁
      (by simpa [norm_sub_rev] using hM) (by simpa [add_comm] using hrowVector)⟩

private theorem column_obstruction_endpoint_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (blueLabel : SixPointLabel) (hblueLabel : blueLabel ≠ .root)
    (hcolumn :
      2 + 2 * (barC - 1) *
          dist (configuration .blue .left) (configuration .blue .right) +
          (2 * barC - 1) *
            dist (configuration .red .left) (configuration .red .right) ≤
        dist (configuration .red .left) (configuration .blue blueLabel) +
          dist (configuration .red .right) (configuration .blue blueLabel)) :
    let e := configuration.rootDisplacement
    let w₁ := configuration.redDisplacement .left
    let w₂ := configuration.redDisplacement .right
    ‖e - w₁‖ < barC - 1 +
        ((barC - 1) * (‖w₁‖ + barC) + (barC + 1) * ‖w₂‖) / 2 ∧
      ‖e - w₂‖ < barC - 1 +
        ((barC - 1) * (‖w₂‖ + barC) + (barC + 1) * ‖w₁‖) / 2 := by
  dsimp only
  let p := configuration.bluePullback blueLabel
  have he := configuration.norm_rootDisplacement h
  have hp := configuration.norm_bluePullback_le_one h hblueLabel
  have hw₁ := configuration.norm_redDisplacement_le_one h
    (by simp : SixPointLabel.left ≠ .root)
  have hw₂ := configuration.norm_redDisplacement_le_one h
    (by simp : SixPointLabel.right ≠ .root)
  have hM : barC ≤
      ‖configuration.redDisplacement .left - configuration.redDisplacement .right‖ := by
    have hM' := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hM'
    exact hM'
  have hblueSibling := h.sibling_distance .blue
  rw [barS, show 2 * (barC / 2) = barC by ring] at hblueSibling
  have hMdist : dist (configuration .red .left) (configuration .red .right) =
      ‖configuration.redDisplacement .left - configuration.redDisplacement .right‖ := by
    rw [← configuration.dist_redDisplacement .left .right, dist_eq_norm]
  have hfactor1 : 0 ≤ 2 * (barC - 1) := by nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hfactor2 : 0 ≤ 2 * barC - 1 := by nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hbluePart := mul_le_mul_of_nonneg_left hblueSibling hfactor1
  have hredPart := mul_le_mul_of_nonneg_left hM hfactor2
  rw [hMdist, configuration.dist_red_blue_eq_norm .left blueLabel,
    configuration.dist_red_blue_eq_norm .right blueLabel] at hcolumn
  have hcolumnVector : 4 * barC ^ 2 - 3 * barC + 2 ≤
      ‖configuration.rootDisplacement - p - configuration.redDisplacement .left‖ +
        ‖configuration.rootDisplacement - p - configuration.redDisplacement .right‖ := by
    dsimp only [p]
    rw [show configuration.rootDisplacement - configuration.bluePullback blueLabel -
        configuration.redDisplacement .left =
      configuration.rootDisplacement - configuration.redDisplacement .left -
        configuration.bluePullback blueLabel by abel]
    rw [show configuration.rootDisplacement - configuration.bluePullback blueLabel -
        configuration.redDisplacement .right =
      configuration.rootDisplacement - configuration.redDisplacement .right -
        configuration.bluePullback blueLabel by abel]
    nlinarith
  exact ⟨row_obstruction_excludes_root_triangle_endpoint _ p _ _ he hp hw₁ hw₂ hM
      hcolumnVector,
    row_obstruction_excludes_root_triangle_endpoint _ p _ _ he hp hw₂ hw₁
      (by simpa [norm_sub_rev] using hM) (by simpa [add_comm] using hcolumnVector)⟩

private theorem red_root_blue_triangle_target_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hleft :
      ‖configuration.rootDisplacement - configuration.bluePullback .left‖ < barC - 1 +
        ((barC - 1) * (‖configuration.bluePullback .left‖ + barC) +
          (barC + 1) * ‖configuration.bluePullback .right‖) / 2)
    (hright :
      ‖configuration.rootDisplacement - configuration.bluePullback .right‖ < barC - 1 +
        ((barC - 1) * (‖configuration.bluePullback .right‖ + barC) +
          (barC + 1) * ‖configuration.bluePullback .left‖) / 2) :
    let target := barC * (1 +
      (dist (configuration .blue .root) (configuration .blue .left) +
        dist (configuration .blue .root) (configuration .blue .right) +
          dist (configuration .blue .left) (configuration .blue .right)) / 2)
    2 ≤ target ∧
      2 * dist (configuration .blue .left) (configuration .blue .right) ≤ target ∧
      2 + (dist (configuration .blue .root) (configuration .blue .left) +
        dist (configuration .blue .root) (configuration .blue .right) -
          dist (configuration .blue .left) (configuration .blue .right)) / 2 ≤ target ∧
      ‖configuration.rootDisplacement - configuration.bluePullback .left‖ + 1 +
        (dist (configuration .blue .root) (configuration .blue .left) +
          dist (configuration .blue .left) (configuration .blue .right) -
            dist (configuration .blue .root) (configuration .blue .right)) / 2 ≤ target ∧
      ‖configuration.rootDisplacement - configuration.bluePullback .right‖ + 1 +
        (dist (configuration .blue .root) (configuration .blue .right) +
          dist (configuration .blue .left) (configuration .blue .right) -
            dist (configuration .blue .root) (configuration .blue .left)) / 2 ≤ target := by
  dsimp only
  have hw₁ := configuration.norm_bluePullback_le_one h
    (by simp : SixPointLabel.left ≠ .root)
  have hw₂ := configuration.norm_bluePullback_le_one h
    (by simp : SixPointLabel.right ≠ .root)
  have hMdist : dist (configuration .blue .left) (configuration .blue .right) =
      ‖configuration.bluePullback .left - configuration.bluePullback .right‖ := by
    rw [← configuration.dist_bluePullback .left .right, dist_eq_norm]
  have hb₁dist : dist (configuration .blue .root) (configuration .blue .left) =
      ‖configuration.bluePullback .left‖ := by
    simp [SixPointConfiguration.bluePullback, dist_eq_norm]
  have hb₂dist : dist (configuration .blue .root) (configuration .blue .right) =
      ‖configuration.bluePullback .right‖ := by
    simp [SixPointConfiguration.bluePullback, dist_eq_norm]
  have hM : barC ≤
      ‖configuration.bluePullback .left - configuration.bluePullback .right‖ := by
    have hM' := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hM'
    exact hM'
  rw [hb₁dist, hb₂dist, hMdist]
  exact root_triangle_target_bounds configuration.rootDisplacement
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    hw₁ hw₂ hM hleft hright

private theorem redRootBlueTrianglePacking_virtualDiameter_le_of_endpoint_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hleft :
      ‖configuration.rootDisplacement - configuration.bluePullback .left‖ < barC - 1 +
        ((barC - 1) * (‖configuration.bluePullback .left‖ + barC) +
          (barC + 1) * ‖configuration.bluePullback .right‖) / 2)
    (hright :
      ‖configuration.rootDisplacement - configuration.bluePullback .right‖ < barC - 1 +
        ((barC - 1) * (‖configuration.bluePullback .right‖ + barC) +
          (barC + 1) * ‖configuration.bluePullback .left‖) / 2) :
    (redRootBlueTrianglePacking configuration
      (h.child_distance .blue .left (by simp))
      (h.child_distance .blue .right (by simp))).virtualDiameter ≤
        barC * (1 +
          (dist (configuration .blue .root) (configuration .blue .left) +
            dist (configuration .blue .root) (configuration .blue .right) +
              dist (configuration .blue .left) (configuration .blue .right)) / 2) := by
  let target := barC * (1 +
    (dist (configuration .blue .root) (configuration .blue .left) +
      dist (configuration .blue .root) (configuration .blue .right) +
        dist (configuration .blue .left) (configuration .blue .right)) / 2)
  obtain ⟨htargetTwo, htargetSibling, hrootTarget, hleftTarget, hrightTarget⟩ :=
    red_root_blue_triangle_target_bounds configuration h hleft hright
  change 2 ≤ target at htargetTwo
  change
    2 * dist (configuration .blue .left) (configuration .blue .right) ≤ target at htargetSibling
  change _ ≤ target at hrootTarget hleftTarget hrightTarget
  have hblueLeft := h.child_distance .blue .left (by simp)
  have hblueRight := h.child_distance .blue .right (by simp)
  have hblue := triangle_pair_dist_le configuration .blue hblueLeft hblueRight
    htargetTwo htargetSibling
  have hcross := red_root_blue_triangle_cross_le configuration h hrootTarget
    hleftTarget hrightTarget
  exact redRootBlueTrianglePacking_virtualDiameter_le configuration hblueLeft hblueRight
    htargetTwo hblue hcross

private theorem redRootBlueTriangle_score_nonnegative_of_endpoint_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hleft :
      ‖configuration.rootDisplacement - configuration.bluePullback .left‖ < barC - 1 +
        ((barC - 1) * (‖configuration.bluePullback .left‖ + barC) +
          (barC + 1) * ‖configuration.bluePullback .right‖) / 2)
    (hright :
      ‖configuration.rootDisplacement - configuration.bluePullback .right‖ < barC - 1 +
        ((barC - 1) * (‖configuration.bluePullback .right‖ + barC) +
          (barC + 1) * ‖configuration.bluePullback .left‖) / 2) :
    0 ≤ (redRootBlueTrianglePacking configuration
      (h.child_distance .blue .left (by simp))
      (h.child_distance .blue .right (by simp))).score barS := by
  have hvirtual := redRootBlueTrianglePacking_virtualDiameter_le_of_endpoint_bounds
    configuration h hleft hright
  rw [SixPointPacking.score, redRootBlueTrianglePacking_totalRadius]
  simp only [barS]
  rw [show 2 * (barC / 2) = barC by ring]
  apply sub_nonneg.mpr
  apply (div_le_iff₀ barC_pos).2
  simpa only [mul_comm] using hvirtual

private theorem blue_root_red_triangle_target_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hleft :
      ‖configuration.rootDisplacement - configuration.redDisplacement .left‖ < barC - 1 +
        ((barC - 1) * (‖configuration.redDisplacement .left‖ + barC) +
          (barC + 1) * ‖configuration.redDisplacement .right‖) / 2)
    (hright :
      ‖configuration.rootDisplacement - configuration.redDisplacement .right‖ < barC - 1 +
        ((barC - 1) * (‖configuration.redDisplacement .right‖ + barC) +
          (barC + 1) * ‖configuration.redDisplacement .left‖) / 2) :
    let target := barC * (1 +
      (dist (configuration .red .root) (configuration .red .left) +
        dist (configuration .red .root) (configuration .red .right) +
          dist (configuration .red .left) (configuration .red .right)) / 2)
    2 ≤ target ∧
      2 * dist (configuration .red .left) (configuration .red .right) ≤ target ∧
      2 + (dist (configuration .red .root) (configuration .red .left) +
        dist (configuration .red .root) (configuration .red .right) -
          dist (configuration .red .left) (configuration .red .right)) / 2 ≤ target ∧
      ‖configuration.rootDisplacement - configuration.redDisplacement .left‖ + 1 +
        (dist (configuration .red .root) (configuration .red .left) +
          dist (configuration .red .left) (configuration .red .right) -
            dist (configuration .red .root) (configuration .red .right)) / 2 ≤ target ∧
      ‖configuration.rootDisplacement - configuration.redDisplacement .right‖ + 1 +
        (dist (configuration .red .root) (configuration .red .right) +
          dist (configuration .red .left) (configuration .red .right) -
            dist (configuration .red .root) (configuration .red .left)) / 2 ≤ target := by
  dsimp only
  have hw₁ := configuration.norm_redDisplacement_le_one h
    (by simp : SixPointLabel.left ≠ .root)
  have hw₂ := configuration.norm_redDisplacement_le_one h
    (by simp : SixPointLabel.right ≠ .root)
  have hMdist : dist (configuration .red .left) (configuration .red .right) =
      ‖configuration.redDisplacement .left - configuration.redDisplacement .right‖ := by
    rw [← configuration.dist_redDisplacement .left .right, dist_eq_norm]
  have hr₁dist : dist (configuration .red .root) (configuration .red .left) =
      ‖configuration.redDisplacement .left‖ := by
    rw [SixPointConfiguration.redDisplacement, norm_sub_rev, dist_eq_norm]
  have hr₂dist : dist (configuration .red .root) (configuration .red .right) =
      ‖configuration.redDisplacement .right‖ := by
    rw [SixPointConfiguration.redDisplacement, norm_sub_rev, dist_eq_norm]
  have hM : barC ≤
      ‖configuration.redDisplacement .left - configuration.redDisplacement .right‖ := by
    have hM' := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hM'
    exact hM'
  rw [hr₁dist, hr₂dist, hMdist]
  exact root_triangle_target_bounds configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    hw₁ hw₂ hM hleft hright

private theorem blueRootRedTrianglePacking_virtualDiameter_le_of_endpoint_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hleft :
      ‖configuration.rootDisplacement - configuration.redDisplacement .left‖ < barC - 1 +
        ((barC - 1) * (‖configuration.redDisplacement .left‖ + barC) +
          (barC + 1) * ‖configuration.redDisplacement .right‖) / 2)
    (hright :
      ‖configuration.rootDisplacement - configuration.redDisplacement .right‖ < barC - 1 +
        ((barC - 1) * (‖configuration.redDisplacement .right‖ + barC) +
          (barC + 1) * ‖configuration.redDisplacement .left‖) / 2) :
    (blueRootRedTrianglePacking configuration
      (h.child_distance .red .left (by simp))
      (h.child_distance .red .right (by simp))).virtualDiameter ≤
        barC * (1 +
          (dist (configuration .red .root) (configuration .red .left) +
            dist (configuration .red .root) (configuration .red .right) +
              dist (configuration .red .left) (configuration .red .right)) / 2) := by
  let target := barC * (1 +
    (dist (configuration .red .root) (configuration .red .left) +
      dist (configuration .red .root) (configuration .red .right) +
        dist (configuration .red .left) (configuration .red .right)) / 2)
  obtain ⟨htargetTwo, htargetSibling, hrootTarget, hleftTarget, hrightTarget⟩ :=
    blue_root_red_triangle_target_bounds configuration h hleft hright
  change 2 ≤ target at htargetTwo
  change
    2 * dist (configuration .red .left) (configuration .red .right) ≤ target at htargetSibling
  change _ ≤ target at hrootTarget hleftTarget hrightTarget
  have hredLeft := h.child_distance .red .left (by simp)
  have hredRight := h.child_distance .red .right (by simp)
  have hred := triangle_pair_dist_le configuration .red hredLeft hredRight
    htargetTwo htargetSibling
  have hcross := blue_root_red_triangle_cross_le configuration h hrootTarget
    hleftTarget hrightTarget
  exact blueRootRedTrianglePacking_virtualDiameter_le configuration hredLeft hredRight
    htargetTwo hred hcross

private theorem blueRootRedTriangle_score_nonnegative_of_endpoint_bounds
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hleft :
      ‖configuration.rootDisplacement - configuration.redDisplacement .left‖ < barC - 1 +
        ((barC - 1) * (‖configuration.redDisplacement .left‖ + barC) +
          (barC + 1) * ‖configuration.redDisplacement .right‖) / 2)
    (hright :
      ‖configuration.rootDisplacement - configuration.redDisplacement .right‖ < barC - 1 +
        ((barC - 1) * (‖configuration.redDisplacement .right‖ + barC) +
          (barC + 1) * ‖configuration.redDisplacement .left‖) / 2) :
    0 ≤ (blueRootRedTrianglePacking configuration
      (h.child_distance .red .left (by simp))
      (h.child_distance .red .right (by simp))).score barS := by
  have hvirtual := blueRootRedTrianglePacking_virtualDiameter_le_of_endpoint_bounds
    configuration h hleft hright
  rw [SixPointPacking.score, blueRootRedTrianglePacking_totalRadius]
  simp only [barS]
  rw [show 2 * (barC / 2) = barC by ring]
  apply sub_nonneg.mpr
  apply (div_le_iff₀ barC_pos).2
  simpa only [mul_comm] using hvirtual

/-- A row obstruction makes support `17` a nonnegative-score endpoint packing. -/
theorem red_root_blue_triangle_score_nonnegative_of_row_obstruction
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (redLabel : SixPointLabel) (hredLabel : redLabel ≠ .root)
    (hrow :
      2 + 2 * (barC - 1) *
          dist (configuration .red .left) (configuration .red .right) +
          (2 * barC - 1) *
            dist (configuration .blue .left) (configuration .blue .right) ≤
        dist (configuration .red redLabel) (configuration .blue .left) +
          dist (configuration .red redLabel) (configuration .blue .right)) :
    0 ≤ (redRootBlueTrianglePacking configuration
      (h.child_distance .blue .left (by simp))
      (h.child_distance .blue .right (by simp))).score barS := by
  obtain ⟨hleft, hright⟩ :=
    row_obstruction_endpoint_bounds configuration h redLabel hredLabel hrow
  exact redRootBlueTriangle_score_nonnegative_of_endpoint_bounds configuration h hleft hright

/-- A column obstruction makes support `71` a nonnegative-score endpoint packing. -/
theorem blue_root_red_triangle_score_nonnegative_of_column_obstruction
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (blueLabel : SixPointLabel) (hblueLabel : blueLabel ≠ .root)
    (hcolumn :
      2 + 2 * (barC - 1) *
          dist (configuration .blue .left) (configuration .blue .right) +
          (2 * barC - 1) *
            dist (configuration .red .left) (configuration .red .right) ≤
        dist (configuration .red .left) (configuration .blue blueLabel) +
          dist (configuration .red .right) (configuration .blue blueLabel)) :
    0 ≤ (blueRootRedTrianglePacking configuration
      (h.child_distance .red .left (by simp))
      (h.child_distance .red .right (by simp))).score barS := by
  obtain ⟨hleft, hright⟩ :=
    column_obstruction_endpoint_bounds configuration h blueLabel hblueLabel hcolumn
  exact blueRootRedTriangle_score_nonnegative_of_endpoint_bounds configuration h hleft hright

end LeanPool.Besicovitch
