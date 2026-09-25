/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedEstimates

/-! # Bounded Sharp Estimates -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Sharp contractive-branch majorant for bounded Riccati solutions

This leaf module solves the scalar quadratic inequality produced by the
interval/exterior Sylvester estimate.  On the contractive branch, the solution
norm is bounded by the smaller root of the Riccati majorant polynomial.

The result is stated in an algebraic square-root form.  This keeps the operator
argument independent of trigonometric normalization and exposes the exact
scalar endpoint needed by later continuation and branch-selection proofs.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The contractive branch of `d * t ≤ b * (1 + t ^ 2)` lies below the
smaller root of the associated quadratic polynomial. -/
theorem le_riccati_small_root_of_quadratic
    {b d t : ℝ}
    (hb : 0 ≤ b) (hd : 0 < d) (hsmall : 2 * b < d)
    (ht1 : t < 1)
    (hquad : d * t ≤ b * (1 + t ^ 2)) :
    t ≤ 2 * b / (d + Real.sqrt (d ^ 2 - 4 * b ^ 2)) := by
  have hsumpos : 0 < d + 2 * b := by
    nlinarith
  have hdiscpos : 0 < d ^ 2 - 4 * b ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hsmall) hsumpos
    nlinarith
  have hdisc : 0 ≤ d ^ 2 - 4 * b ^ 2 := le_of_lt hdiscpos
  let s : ℝ := Real.sqrt (d ^ 2 - 4 * b ^ 2)
  let r : ℝ := 2 * b / (d + s)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = d ^ 2 - 4 * b ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt hdisc
  have hden : 0 < d + s := by
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one hden).2
    linarith
  have hroot : b * (1 + r ^ 2) = d * r := by
    dsimp [r]
    field_simp [ne_of_gt hden]
    nlinarith [hs2]
  by_contra hnot
  have hrt : r < t := lt_of_not_ge hnot
  have hsum : t + r < 2 := by
    linarith
  have hcoef : b * (t + r) - d < 0 := by
    have hmul : b * (t + r) ≤ b * 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hsum) hb
    nlinarith
  have hfactor :
      b * (1 + t ^ 2) - d * t =
        (b * (1 + r ^ 2) - d * r) +
          (t - r) * (b * (t + r) - d) := by
    ring
  have hprod : (t - r) * (b * (t + r) - d) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hrt) hcoef
  have hneg : b * (1 + t ^ 2) - d * t < 0 := by
    rw [hfactor]
    nlinarith [hroot, hprod]
  nlinarith

/-- A contractive bounded Riccati solution lies below the smaller root of the
quadratic interval/exterior majorant. -/
theorem norm_riccati_solution_le_small_root_of_contractive_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    ‖X‖ ≤
      2 * ‖H.B01‖ /
        (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) := by
  apply le_riccati_small_root_of_quadratic
    (b := ‖H.B01‖) (d := d) (t := ‖X‖)
  · exact norm_nonneg H.B01
  · exact hd
  · exact hsmall
  · exact hXc
  · exact norm_riccati_solution_quadratic_le_of_spectrum_gap
      H hd hlr hA0spec hA1spec hX

/-- A finite-error sharp Riccati estimate evaluated on a normalized
near-singular pair.  The error is exactly the defect in the adjoint singular
relation `X* y = t x`.

In the exact singular-pair case (`eta = 0`, `s = t`) the conclusion is

`d * t <= ||B01|| * (1 - t^2)`.
-/
theorem riccati_near_singular_pair_bound
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d t s eta : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hs0 : 0 ≤ s) (hst : s ≤ t)
    (hA0 : ∀ z : E0, RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    {x : E0} {y : E1}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hXx : X x = (s : ℂ) • y)
    (hadj : ‖X.adjoint y - (t : ℂ) • x‖ ≤ eta) :
    d * s ≤ ‖H.B01‖ * (1 - s * t) +
      (‖H.A0‖ + s * ‖H.B01‖) * eta := by
  set e : E0 := X.adjoint y - (t : ℂ) • x with he
  have he_norm : ‖e‖ ≤ eta := by simpa [he] using hadj
  have hst1 : s * t < 1 := by
    have htt : t * t < 1 := by nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hst ht0) htt
  have hA1lower : d * s ≤ s * RCLike.re ⟪H.A1 y, y⟫_ℂ := by
    have hy := hA1 y
    rw [hynorm, one_pow, mul_one] at hy
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hy hs0
  have hA0cross : RCLike.re ⟪H.A0 x, X.adjoint y⟫_ℂ ≤ ‖H.A0‖ * eta := by
    have hadj_expand : X.adjoint y = (t : ℂ) • x + e := by
      rw [he]
      abel
    rw [hadj_expand, inner_add_right, map_add]
    have hmain : RCLike.re ⟪H.A0 x, (t : ℂ) • x⟫_ℂ ≤ 0 := by
      rw [inner_smul_right, ← Complex.real_smul, RCLike.smul_re]
      exact mul_nonpos_of_nonneg_of_nonpos ht0 (hA0 x)
    have herr : RCLike.re ⟪H.A0 x, e⟫_ℂ ≤ ‖H.A0‖ * eta := by
      calc
        RCLike.re ⟪H.A0 x, e⟫_ℂ ≤ ‖⟪H.A0 x, e⟫_ℂ‖ := RCLike.re_le_norm _
        _ ≤ ‖H.A0 x‖ * ‖e‖ := norm_inner_le_norm _ _
        _ ≤ (‖H.A0‖ * ‖x‖) * ‖e‖ := by
          exact mul_le_mul_of_nonneg_right (H.A0.le_opNorm x) (norm_nonneg e)
        _ ≤ (‖H.A0‖ * ‖x‖) * eta := by
          exact mul_le_mul_of_nonneg_left he_norm
            (mul_nonneg (norm_nonneg H.A0) (norm_nonneg x))
        _ = ‖H.A0‖ * eta := by rw [hxnorm, mul_one]
    linarith
  have hleft_lower :
      d * s - ‖H.A0‖ * eta ≤
        RCLike.re ⟪H.A1 (X x) - X (H.A0 x), y⟫_ℂ := by
    have hA1exact :
        RCLike.re ⟪H.A1 (X x), y⟫_ℂ =
          s * RCLike.re ⟪H.A1 y, y⟫_ℂ := by
      rw [hXx, map_smul, inner_smul_left, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re]
    have hA0exact :
        RCLike.re ⟪X (H.A0 x), y⟫_ℂ =
          RCLike.re ⟪H.A0 x, X.adjoint y⟫_ℂ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [inner_sub_left, map_sub, hA1exact, hA0exact]
    linarith
  have hpoint := (solvesRiccati_iff_pointwise H X).1 hX x
  have heq : H.A1 (X x) - X (H.A0 x) =
      X (H.B01 (X x)) - H.B10 x := by
    rw [map_add] at hpoint
    calc
      H.A1 (X x) - X (H.A0 x) =
          (H.B10 x + H.A1 (X x)) - (H.B10 x + X (H.A0 x)) := by abel
      _ = (X (H.A0 x) + X (H.B01 (X x))) -
          (H.B10 x + X (H.A0 x)) := by rw [hpoint]
      _ = X (H.B01 (X x)) - H.B10 x := by abel
  have hB10real :
      RCLike.re ⟪H.B10 x, y⟫_ℂ =
        RCLike.re ⟪H.B01 y, x⟫_ℂ := by
    rw [← RCLike.conj_re ⟪H.B10 x, y⟫_ℂ, inner_conj_symm,
      ← H.offDiagonalAdjoint x y]
  have hBexact :
      RCLike.re ⟪X (H.B01 (X x)) - H.B10 x, y⟫_ℂ =
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ +
          s * RCLike.re ⟪H.B01 y, e⟫_ℂ := by
    have hadj_expand : X.adjoint y = (t : ℂ) • x + e := by
      rw [he]
      abel
    have hXterm :
        RCLike.re ⟪X (H.B01 (X x)), y⟫_ℂ =
          s * (t * RCLike.re ⟪H.B01 y, x⟫_ℂ +
            RCLike.re ⟪H.B01 y, e⟫_ℂ) := by
      calc
        RCLike.re ⟪X (H.B01 (X x)), y⟫_ℂ =
            RCLike.re ⟪H.B01 (X x), X.adjoint y⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
        _ = s * RCLike.re ⟪H.B01 y, X.adjoint y⟫_ℂ := by
              rw [hXx, map_smul, inner_smul_left, Complex.conj_ofReal,
                ← Complex.real_smul, RCLike.smul_re]
        _ = s * (t * RCLike.re ⟪H.B01 y, x⟫_ℂ +
              RCLike.re ⟪H.B01 y, e⟫_ℂ) := by
              rw [hadj_expand, inner_add_right, map_add, inner_smul_right,
                ← Complex.real_smul, RCLike.smul_re]
    rw [inner_sub_left, map_sub, hXterm, hB10real]
    ring
  have hq : |RCLike.re ⟪H.B01 y, x⟫_ℂ| ≤ ‖H.B01‖ := by
    calc
      |RCLike.re ⟪H.B01 y, x⟫_ℂ| ≤ ‖⟪H.B01 y, x⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 y‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖y‖) * ‖x‖ := by
        gcongr
        exact H.B01.le_opNorm y
      _ = ‖H.B01‖ := by rw [hynorm, hxnorm, mul_one, mul_one]
  have herrB : |RCLike.re ⟪H.B01 y, e⟫_ℂ| ≤ ‖H.B01‖ * eta := by
    calc
      |RCLike.re ⟪H.B01 y, e⟫_ℂ| ≤ ‖⟪H.B01 y, e⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 y‖ * ‖e‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖y‖) * ‖e‖ := by
        exact mul_le_mul_of_nonneg_right (H.B01.le_opNorm y) (norm_nonneg e)
      _ ≤ (‖H.B01‖ * ‖y‖) * eta := by
        exact mul_le_mul_of_nonneg_left he_norm
          (mul_nonneg (norm_nonneg H.B01) (norm_nonneg y))
      _ = ‖H.B01‖ * eta := by rw [hynorm, mul_one]
  have hright_upper :
      RCLike.re ⟪X (H.B01 (X x)) - H.B10 x, y⟫_ℂ ≤
        ‖H.B01‖ * (1 - s * t) + s * ‖H.B01‖ * eta := by
    rw [hBexact]
    have hcoef : s * t - 1 ≤ 0 := by linarith
    have hfirst :
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ ≤
          ‖H.B01‖ * (1 - s * t) := by
      calc
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ
            ≤ |(s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ| :=
              le_abs_self _
        _ = |s * t - 1| * |RCLike.re ⟪H.B01 y, x⟫_ℂ| := by
              rw [abs_mul]
        _ ≤ (1 - s * t) * ‖H.B01‖ := by
              rw [abs_of_nonpos hcoef, neg_sub]
              exact mul_le_mul_of_nonneg_left hq (by linarith)
        _ = ‖H.B01‖ * (1 - s * t) := mul_comm _ _
    have hsecond :
        s * RCLike.re ⟪H.B01 y, e⟫_ℂ ≤ s * ‖H.B01‖ * eta := by
      calc
        s * RCLike.re ⟪H.B01 y, e⟫_ℂ
            ≤ s * |RCLike.re ⟪H.B01 y, e⟫_ℂ| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hs0
        _ ≤ s * (‖H.B01‖ * eta) :=
              mul_le_mul_of_nonneg_left herrB hs0
        _ = s * ‖H.B01‖ * eta := by ring
    linarith
  rw [heq] at hleft_lower
  have hmain : d * s - ‖H.A0‖ * eta ≤
      ‖H.B01‖ * (1 - s * t) + s * ‖H.B01‖ * eta :=
    hleft_lower.trans hright_upper
  nlinarith


/- Promoted from `Experimental/InfiniteDimensional/TanTwoTheta/BoundedRiccatiLimit.lean`
   under lane `EXP-PROMOTE-T2T` slice 2, 2026-07-30.  Verbatim. -/

/-- Close the finite-error near-singular-pair estimates at the operator norm.

The parameters `a` and `b` represent the diagonal and off-diagonal operator
norms occurring in the error term.  Their signs are immaterial in the positive
`t` branch because the whole right-hand side is passed to the limit; `b >= 0`
is used only to discharge the degenerate case `t = 0`.
-/
theorem sharp_riccati_bound_of_epsilon
    {d a b t : ℝ}
    (hb0 : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hε : ∀ ε ∈ Set.Ioo (0 : ℝ) t,
      d * (t - ε) ≤
        b * (1 - (t - ε) * t) +
          (a + t * b) * Real.sqrt (2 * t * ε)) :
    d * t ≤ b * (1 - t ^ 2) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simpa using hb0
  · have hev : ∀ ε ∈ Set.Ioo (0 : ℝ) t,
        d * t ≤ d * ε +
          (b * (1 - (t - ε) * t) +
            (a + t * b) * Real.sqrt (2 * t * ε)) := by
      intro ε hεmem
      have hstep := hε ε hεmem
      linarith
    have hcont : ContinuousWithinAt
        (fun ε : ℝ =>
          d * ε +
            (b * (1 - (t - ε) * t) +
              (a + t * b) * Real.sqrt (2 * t * ε)))
        (Set.Ioo 0 t) 0 := by
      apply Continuous.continuousWithinAt
      exact (continuous_const.mul continuous_id).add
        ((continuous_const.mul
          (continuous_const.sub
            ((continuous_const.sub continuous_id).mul continuous_const))).add
          (continuous_const.mul
            (Real.continuous_sqrt.comp
              ((continuous_const.mul continuous_const).mul continuous_id))))
    have hne : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo htpos.ne]
      exact ⟨le_refl 0, htpos.le⟩
    have hlim := ge_of_tendsto hcont
      (by filter_upwards [self_mem_nhdsWithin] with ε hεmem using hev ε hεmem)
    simpa [pow_two] using hlim

/- Promoted from `Experimental/InfiniteDimensional/TanTwoTheta/BoundedRiccatiNorm.lean`
   under lane `EXP-PROMOTE-T2T` slice 2, 2026-07-30.  Verbatim. -/

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A continuous linear map has a unit vector whose image norm is within every
positive amount below its operator norm. -/
theorem exists_unit_norm_apply_gt_sub
    (X : E0 →L[ℂ] E1) {ε : ℝ}
    (hε0 : 0 < ε) (hεt : ε < ‖X‖) :
    ∃ x : E0, ‖x‖ = 1 ∧ ‖X x‖ > ‖X‖ - ε := by
  by_contra h
  push Not at h
  have hop : ‖X‖ ≤ ‖X‖ - ε :=
    ContinuousLinearMap.opNorm_le_of_unit_norm
      (sub_nonneg.mpr hεt.le) (fun x hx => h x hx)
  linarith

/-- Squared adjoint-defect estimate for a normalized approximate singular pair.
The exact relation `X x = s y` fixes the cross term, while the operator norm
controls `X† y`. -/
theorem adjoint_defect_sq_le_of_normalized_pair
    (X : E0 →L[ℂ] E1) {x : E0} {y : E1} {s : ℝ}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hXx : X x = (s : ℂ) • y) :
    ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ^ 2 ≤
      2 * ‖X‖ * (‖X‖ - s) := by
  have hadj_norm : ‖X.adjoint y‖ ≤ ‖X‖ := by
    calc
      ‖X.adjoint y‖ ≤ ‖X.adjoint‖ * ‖y‖ := X.adjoint.le_opNorm y
      _ = ‖X‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map, hynorm, mul_one]
  have hadj_sq : ‖X.adjoint y‖ ^ 2 ≤ ‖X‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg X)).2 hadj_norm
  have hinner : RCLike.re ⟪X.adjoint y, x⟫_ℂ = s := by
    rw [ContinuousLinearMap.adjoint_inner_left, hXx, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hynorm]
    norm_num
  have hinner_scaled :
      RCLike.re ⟪X.adjoint y, (‖X‖ : ℂ) • x⟫_ℂ = ‖X‖ * s := by
    rw [inner_smul_right, ← Complex.real_smul, RCLike.smul_re, hinner]
  simp only [norm_sub_sq (𝕜 := ℂ), hinner_scaled, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg X), hxnorm, mul_one]
  nlinarith

/-- A near norm-attaining vector and its normalized image form an approximate
singular pair.  The adjoint defect is bounded by the square-root error naturally
produced by the polarization identity. -/
theorem exists_near_singular_pair
    (X : E0 →L[ℂ] E1) {ε : ℝ}
    (hε0 : 0 < ε) (hεt : ε < ‖X‖) :
    ∃ (x : E0) (y : E1) (s : ℝ),
      ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      ‖X‖ - ε < s ∧ s ≤ ‖X‖ ∧
      X x = (s : ℂ) • y ∧
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ≤
        Real.sqrt (2 * ‖X‖ * ε) := by
  obtain ⟨x, hxnorm, hxnear⟩ := exists_unit_norm_apply_gt_sub X hε0 hεt
  set s : ℝ := ‖X x‖ with hs
  have hspos : 0 < s := by
    have hsubpos : 0 < ‖X‖ - ε := sub_pos.mpr hεt
    exact hsubpos.trans hxnear
  set y : E1 := (((s⁻¹ : ℝ) : ℂ) • X x) with hy
  have hynorm : ‖y‖ = 1 := by
    rw [hy, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hspos.le), ← hs,
      inv_mul_cancel₀ hspos.ne']
  have hXx : X x = (s : ℂ) • y := by
    rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hspos.ne',
      Complex.ofReal_one, one_smul]
  have hsle : s ≤ ‖X‖ := by
    have h := X.le_opNorm x
    rw [hxnorm, mul_one] at h
    simpa [hs] using h
  have hdef_sq :=
    adjoint_defect_sq_le_of_normalized_pair X hxnorm hynorm hXx
  have hgap : ‖X‖ - s < ε := by linarith
  have hrad_le :
      2 * ‖X‖ * (‖X‖ - s) ≤ 2 * ‖X‖ * ε := by
    exact mul_le_mul_of_nonneg_left hgap.le
      (mul_nonneg (by norm_num) (norm_nonneg X))
  have hdef_sq' :
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ^ 2 ≤ 2 * ‖X‖ * ε :=
    hdef_sq.trans hrad_le
  have hrad0 : 0 ≤ 2 * ‖X‖ * ε :=
    mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg X)) hε0.le
  have hdef :
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ≤ Real.sqrt (2 * ‖X‖ * ε) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hrad0]
    exact hdef_sq'
  exact ⟨x, y, s, hxnorm, hynorm, hxnear, hsle, hXx, hdef⟩

/-- Sharp operator-norm inequality for a contractive bounded Riccati solution
under shifted ordered quadratic-form bounds. -/
theorem sharp_riccati_norm_bound
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0, RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    d * ‖X‖ ≤ ‖H.B01‖ * (1 - ‖X‖ ^ 2) := by
  apply sharp_riccati_bound_of_epsilon (a := ‖H.A0‖)
    (norm_nonneg H.B01) (norm_nonneg X) hXc
  intro ε hε
  obtain ⟨x, y, s, hxnorm, hynorm, hsnear, hsle, hXx, hdef⟩ :=
    exists_near_singular_pair X hε.1 hε.2
  have hs0 : 0 ≤ s := by
    have : 0 < ‖X‖ - ε := sub_pos.mpr hε.2
    linarith
  have hpair := riccati_near_singular_pair_bound
    (H := H) (d := d) (t := ‖X‖) (s := s)
    (eta := Real.sqrt (2 * ‖X‖ * ε))
    (norm_nonneg X) hXc hs0 hsle hA0 hA1 hX
    hxnorm hynorm hXx hdef
  have hlhs : d * (‖X‖ - ε) ≤ d * s :=
    mul_le_mul_of_nonneg_left hsnear.le hd0
  have hmul : (‖X‖ - ε) * ‖X‖ ≤ s * ‖X‖ :=
    mul_le_mul_of_nonneg_right hsnear.le (norm_nonneg X)
  have hfirst :
      ‖H.B01‖ * (1 - s * ‖X‖) ≤
        ‖H.B01‖ * (1 - (‖X‖ - ε) * ‖X‖) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg H.B01)
  have hsb : s * ‖H.B01‖ ≤ ‖X‖ * ‖H.B01‖ :=
    mul_le_mul_of_nonneg_right hsle (norm_nonneg H.B01)
  have hcoeff :
      (‖H.A0‖ + s * ‖H.B01‖) * Real.sqrt (2 * ‖X‖ * ε) ≤
        (‖H.A0‖ + ‖X‖ * ‖H.B01‖) * Real.sqrt (2 * ‖X‖ * ε) :=
    mul_le_mul_of_nonneg_right (add_le_add_right hsb ‖H.A0‖)
      (Real.sqrt_nonneg _)
  exact hlhs.trans <| hpair.trans <| add_le_add hfirst hcoeff

/- Promoted from `Experimental/InfiniteDimensional/TanTwoTheta/BoundedRiccatiShift.lean`
   under lane `EXP-PROMOTE-T2T` slice 2, 2026-07-30.  Verbatim. -/

/-- Shift both diagonal blocks by the same real scalar.  The off-diagonal
couplings are unchanged. -/
noncomputable def shiftBlockOperatorData
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1)) (c : ℝ) :
    BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1) where
  A0 := H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c
  A1 := H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c
  B01 := H.B01
  B10 := H.B10
  selfAdjoint0 := by
    have hA0 : IsSelfAdjoint H.A0 :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint0
    have hshift : IsSelfAdjoint
        (H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c) :=
      hA0.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hshift
  selfAdjoint1 := by
    have hA1 : IsSelfAdjoint H.A1 :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint1
    have hshift : IsSelfAdjoint
        (H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c) :=
      hA1.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hshift
  offDiagonalAdjoint := H.offDiagonalAdjoint

/-- The Riccati defect is invariant under a common real shift of the two
diagonal blocks. -/
theorem riccatiDefect_shiftBlockOperatorData
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c : ℝ) (X : E0 →L[ℂ] E1) :
    riccatiDefect (shiftBlockOperatorData H c) X = riccatiDefect H X := by
  let C0 : E0 →L[ℂ] E0 := algebraMap ℝ (E0 →L[ℂ] E0) c
  let C1 : E1 →L[ℂ] E1 := algebraMap ℝ (E1 →L[ℂ] E1) c
  have hscalar : C1 ∘L X = X ∘L C0 := by
    apply ContinuousLinearMap.ext
    intro u
    simp [C0, C1, Algebra.algebraMap_eq_smul_one]
  change
    (H.A1 - C1) ∘L X - X ∘L (H.A0 - C0) -
          X ∘L H.B01 ∘L X + H.B10 =
      H.A1 ∘L X - X ∘L H.A0 - X ∘L H.B01 ∘L X + H.B10
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hscalar]
  abel

/-- Solving the Riccati equation is invariant under a common real shift. -/
theorem solvesRiccati_shiftBlockOperatorData_iff
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c : ℝ) (X : E0 →L[ℂ] E1) :
    SolvesRiccati (shiftBlockOperatorData H c) X ↔ SolvesRiccati H X := by
  unfold SolvesRiccati
  rw [riccatiDefect_shiftBlockOperatorData]

private theorem re_inner_real_scalar_id
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (c : ℝ) (z : F) :
    RCLike.re
        ⟪(algebraMap ℝ (F →L[ℂ] F) c) z, z⟫_ℂ = c * ‖z‖ ^ 2 := by
  -- Left as a `rw` chain on purpose: `simp only` with this same list fails to synthesize an
  -- instance that `rw` obtains from the rewritten form; simp normalises before the instance
  -- argument is determined.
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- An upper form bound at `c` becomes nonpositivity after shifting by `c`. -/
theorem shiftBlockOperatorData_A0_nonpos
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c : ℝ)
    (hA0 : ∀ z : E0,
      RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2) :
    ∀ z : E0,
      RCLike.re ⟪(shiftBlockOperatorData H c).A0 z, z⟫_ℂ ≤ 0 := by
  intro z
  have hscalar := re_inner_real_scalar_id c z
  change RCLike.re
      ⟪(H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c) z, z⟫_ℂ ≤ 0
  rw [sub_apply, inner_sub_left, map_sub, hscalar]
  linarith [hA0 z]

/-- A lower form bound at `c + d` becomes a lower bound by `d` after shifting
by `c`. -/
theorem shiftBlockOperatorData_A1_lower
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c d : ℝ)
    (hA1 : ∀ z : E1,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ) :
    ∀ z : E1,
      d * ‖z‖ ^ 2 ≤
        RCLike.re ⟪(shiftBlockOperatorData H c).A1 z, z⟫_ℂ := by
  intro z
  have hscalar := re_inner_real_scalar_id c z
  change d * ‖z‖ ^ 2 ≤
      RCLike.re
        ⟪(H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c) z, z⟫_ℂ
  rw [sub_apply, inner_sub_left, map_sub, hscalar]
  linarith [hA1 z]

/-- Sharp norm inequality for a contractive Riccati solution under an ordered
quadratic-form gap centered at an arbitrary real scalar `c`. -/
theorem sharp_riccati_norm_bound_of_form_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {c d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0,
      RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2)
    (hA1 : ∀ z : E1,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    d * ‖X‖ ≤ ‖H.B01‖ * (1 - ‖X‖ ^ 2) := by
  have hXshift : SolvesRiccati (shiftBlockOperatorData H c) X :=
    (solvesRiccati_shiftBlockOperatorData_iff H c X).2 hX
  have hbound := sharp_riccati_norm_bound
    (shiftBlockOperatorData H c) hd0
    (shiftBlockOperatorData_A0_nonpos H c hA0)
    (shiftBlockOperatorData_A1_lower H c d hA1)
    hXshift hXc
  simpa [shiftBlockOperatorData] using hbound

end DavisKahanExt
end TauCeti
