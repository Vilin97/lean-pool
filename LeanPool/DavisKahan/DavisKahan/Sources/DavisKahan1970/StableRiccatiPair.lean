/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.DoubleAngleTangentOperator
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedSharpEstimates

/-!
# Stable paired-singular-vector Riccati estimate

The existing exact Section 7 proof retains the paired coefficient needed for a
Ky Fan sum, while the existing near-singular-pair proof replaces it by the
operator norm.  This file supplies the missing stable coefficient estimate.
Both singular equations may have residual at most `ε`; every error term is
written explicitly and vanishes with `ε`.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open DavisKahanExt
open ExactSinTheta

noncomputable section

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Explicit error in the stable scalar estimate. -/
def stablePairError
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (s ε : ℝ) : ℝ :=
  2 * (((‖B.A0‖ + ‖B.A1‖) * ε) +
      2 * s * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) /
    (1 - s ^ 2)

/-- The stable form of equation (7.6), retaining the paired coefficient.

For `ε = 0` this reduces to the existing exact singular-pair theorem.
-/
theorem stableSingularPair_doubleAngleTangent_le
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d s ε : ℝ} (_hd0 : 0 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hε0 : 0 ≤ ε)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    {x : E0} {y : E1}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hXx : ‖X x - (s : ℂ) • y‖ ≤ ε)
    (hXay : ‖X.adjoint y - (s : ℂ) • x‖ ≤ ε) :
    d * DavisKahan.TanTwoTheta.doubleAngleTangent s ≤
      2 * (-RCLike.re ⟪x, B.B01 y⟫_ℂ) + stablePairError B s ε := by
  set e0 : E1 := X x - (s : ℂ) • y with he0
  set e1 : E0 := X.adjoint y - (s : ℂ) • x with he1
  have he0norm : ‖e0‖ ≤ ε := by simpa [he0] using hXx
  have he1norm : ‖e1‖ ≤ ε := by simpa [he1] using hXay
  have hXexpand : X x = (s : ℂ) • y + e0 := by
    rw [he0]
    abel
  have hXadjExpand : X.adjoint y = (s : ℂ) • x + e1 := by
    rw [he1]
    abel
  have hden : 0 < 1 - s ^ 2 := by nlinarith

  have hA1err : |RCLike.re ⟪B.A1 e0, y⟫_ℂ| ≤ ‖B.A1‖ * ε := by
    calc
      |RCLike.re ⟪B.A1 e0, y⟫_ℂ| ≤ ‖⟪B.A1 e0, y⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
      _ ≤ ‖B.A1 e0‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖B.A1‖ * ‖e0‖) * ‖y‖ := by
        gcongr
        exact B.A1.le_opNorm e0
      _ ≤ (‖B.A1‖ * ε) * ‖y‖ := by
        gcongr
      _ = ‖B.A1‖ * ε := by rw [hynorm, mul_one]
  have re_ofReal_mul_complex (r : ℝ) (z : ℂ) :
      RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by
    simp [RCLike.re_to_complex]
  have re_ofReal_sq_mul_complex (r : ℝ) (z : ℂ) :
      RCLike.re ((r : ℂ) ^ 2 * z) = r ^ 2 * RCLike.re z := by
    rw [pow_two, mul_assoc, re_ofReal_mul_complex,
      re_ofReal_mul_complex]
    ring

  have hA0err : |RCLike.re ⟪B.A0 x, e1⟫_ℂ| ≤ ‖B.A0‖ * ε := by
    calc
      |RCLike.re ⟪B.A0 x, e1⟫_ℂ| ≤ ‖⟪B.A0 x, e1⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
      _ ≤ ‖B.A0 x‖ * ‖e1‖ := norm_inner_le_norm _ _
      _ ≤ (‖B.A0‖ * ‖x‖) * ‖e1‖ := by
        gcongr
        exact B.A0.le_opNorm x
      _ ≤ (‖B.A0‖ * ‖x‖) * ε := by
        gcongr
      _ = ‖B.A0‖ * ε := by rw [hxnorm, mul_one]

  have hA1lower :
      d * s - ‖B.A1‖ * ε ≤ RCLike.re ⟪B.A1 (X x), y⟫_ℂ := by
    have hy := hA1 y
    rw [hynorm, one_pow, mul_one] at hy
    have hA1expand :
        RCLike.re ⟪B.A1 (X x), y⟫_ℂ =
          s * RCLike.re ⟪B.A1 y, y⟫_ℂ +
            RCLike.re ⟪B.A1 e0, y⟫_ℂ := by
      simp only [hXexpand, map_add, map_smul, inner_add_left,
        inner_smul_left, Complex.conj_ofReal, map_add,
        re_ofReal_mul_complex]
    rw [hA1expand]
    have herrlower : -‖B.A1‖ * ε ≤ RCLike.re ⟪B.A1 e0, y⟫_ℂ := by
      simpa only [neg_mul] using neg_le_of_abs_le hA1err
    nlinarith [mul_le_mul_of_nonneg_left hy hs0]

  have hA0upper :
      RCLike.re ⟪X (B.A0 x), y⟫_ℂ ≤ ‖B.A0‖ * ε := by
    have hA0expand :
        RCLike.re ⟪X (B.A0 x), y⟫_ℂ =
          s * RCLike.re ⟪B.A0 x, x⟫_ℂ +
            RCLike.re ⟪B.A0 x, e1⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hXadjExpand,
        inner_add_right, inner_smul_right, map_add,
        re_ofReal_mul_complex]
    rw [hA0expand]
    have hmain : s * RCLike.re ⟪B.A0 x, x⟫_ℂ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs0 (hA0 x)
    have herr : RCLike.re ⟪B.A0 x, e1⟫_ℂ ≤ ‖B.A0‖ * ε :=
      (le_abs_self _).trans hA0err
    linarith

  have hleftLower :
      d * s - (‖B.A0‖ + ‖B.A1‖) * ε ≤
        RCLike.re ⟪B.A1 (X x) - X (B.A0 x), y⟫_ℂ := by
    rw [inner_sub_left, map_sub]
    linarith

  have hpoint := (solvesRiccati_iff_pointwise B X).1 hX x
  have heq : B.A1 (X x) - X (B.A0 x) =
      X (B.B01 (X x)) - B.B10 x := by
    rw [map_add] at hpoint
    calc
      B.A1 (X x) - X (B.A0 x) =
          (B.B10 x + B.A1 (X x)) -
            (B.B10 x + X (B.A0 x)) := by abel
      _ = (X (B.A0 x) + X (B.B01 (X x))) -
            (B.B10 x + X (B.A0 x)) := by rw [hpoint]
      _ = X (B.B01 (X x)) - B.B10 x := by abel

  have hB10real :
      RCLike.re ⟪B.B10 x, y⟫_ℂ =
        RCLike.re ⟪B.B01 y, x⟫_ℂ := by
    rw [← RCLike.conj_re ⟪B.B10 x, y⟫_ℂ, inner_conj_symm,
      ← B.offDiagonalAdjoint x y]

  have hBlin1 : |RCLike.re ⟪B.B01 y, e1⟫_ℂ| ≤ ‖B.B01‖ * ε := by
    calc
      |RCLike.re ⟪B.B01 y, e1⟫_ℂ| ≤ ‖⟪B.B01 y, e1⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
      _ ≤ ‖B.B01 y‖ * ‖e1‖ := norm_inner_le_norm _ _
      _ ≤ (‖B.B01‖ * ‖y‖) * ‖e1‖ := by
        gcongr
        exact B.B01.le_opNorm y
      _ ≤ (‖B.B01‖ * ‖y‖) * ε := by gcongr
      _ = ‖B.B01‖ * ε := by rw [hynorm, mul_one]
  have hBlin0 : |RCLike.re ⟪B.B01 e0, x⟫_ℂ| ≤ ‖B.B01‖ * ε := by
    calc
      |RCLike.re ⟪B.B01 e0, x⟫_ℂ| ≤ ‖⟪B.B01 e0, x⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
      _ ≤ ‖B.B01 e0‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖B.B01‖ * ‖e0‖) * ‖x‖ := by
        gcongr
        exact B.B01.le_opNorm e0
      _ ≤ (‖B.B01‖ * ε) * ‖x‖ := by gcongr
      _ = ‖B.B01‖ * ε := by rw [hxnorm, mul_one]
  have hBquad : |RCLike.re ⟪B.B01 e0, e1⟫_ℂ| ≤ ‖B.B01‖ * ε ^ 2 := by
    calc
      |RCLike.re ⟪B.B01 e0, e1⟫_ℂ| ≤ ‖⟪B.B01 e0, e1⟫_ℂ‖ :=
        RCLike.abs_re_le_norm _
      _ ≤ ‖B.B01 e0‖ * ‖e1‖ := norm_inner_le_norm _ _
      _ ≤ (‖B.B01‖ * ‖e0‖) * ‖e1‖ := by
        gcongr
        exact B.B01.le_opNorm e0
      _ ≤ (‖B.B01‖ * ε) * ε := by gcongr
      _ = ‖B.B01‖ * ε ^ 2 := by ring

  have hBexpand :
      RCLike.re ⟪X (B.B01 (X x)) - B.B10 x, y⟫_ℂ =
        (s ^ 2 - 1) * RCLike.re ⟪B.B01 y, x⟫_ℂ +
          s * RCLike.re ⟪B.B01 y, e1⟫_ℂ +
          s * RCLike.re ⟪B.B01 e0, x⟫_ℂ +
          RCLike.re ⟪B.B01 e0, e1⟫_ℂ := by
    have hXterm :
        RCLike.re ⟪X (B.B01 (X x)), y⟫_ℂ =
          s ^ 2 * RCLike.re ⟪B.B01 y, x⟫_ℂ +
            s * RCLike.re ⟪B.B01 y, e1⟫_ℂ +
            s * RCLike.re ⟪B.B01 e0, x⟫_ℂ +
            RCLike.re ⟪B.B01 e0, e1⟫_ℂ := by
      calc
        RCLike.re ⟪X (B.B01 (X x)), y⟫_ℂ =
            RCLike.re ⟪B.B01 (X x), X.adjoint y⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
        _ = RCLike.re
            ⟪B.B01 ((s : ℂ) • y + e0), (s : ℂ) • x + e1⟫_ℂ := by
              rw [hXexpand, hXadjExpand]
        _ = _ := by
              simp only [map_add, map_smul, inner_add_left, inner_add_right,
                inner_add_right, inner_smul_left, inner_smul_right,
                inner_smul_left, inner_smul_right,
                Complex.conj_ofReal]
              simp only [map_add, re_ofReal_mul_complex]
              ring
    rw [inner_sub_left, map_sub, hXterm, hB10real]
    ring

  have hrightUpper :
      RCLike.re ⟪X (B.B01 (X x)) - B.B10 x, y⟫_ℂ ≤
        (s ^ 2 - 1) * RCLike.re ⟪B.B01 y, x⟫_ℂ +
          2 * s * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2 := by
    rw [hBexpand]
    have h1 : s * RCLike.re ⟪B.B01 y, e1⟫_ℂ ≤
        s * (‖B.B01‖ * ε) := by
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hBlin1) hs0
    have h0 : s * RCLike.re ⟪B.B01 e0, x⟫_ℂ ≤
        s * (‖B.B01‖ * ε) := by
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hBlin0) hs0
    have hq : RCLike.re ⟪B.B01 e0, e1⟫_ℂ ≤ ‖B.B01‖ * ε ^ 2 :=
      (le_abs_self _).trans hBquad
    linarith

  rw [heq] at hleftLower
  have hraw :
      d * s ≤ -(1 - s ^ 2) * RCLike.re ⟪B.B01 y, x⟫_ℂ +
        ((‖B.A0‖ + ‖B.A1‖) * ε +
          2 * s * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) := by
    have := hleftLower.trans hrightUpper
    linarith
  have hre : RCLike.re ⟪B.B01 y, x⟫_ℂ =
      RCLike.re ⟪x, B.B01 y⟫_ℂ := inner_re_symm _ _
  rw [hre] at hraw
  unfold DavisKahan.TanTwoTheta.doubleAngleTangent stablePairError
  rw [show d * (2 * s / (1 - s ^ 2)) =
      (2 * (d * s)) / (1 - s ^ 2) by ring]
  rw [div_le_iff₀ hden]
  calc
    2 * (d * s) ≤
        2 * (-(1 - s ^ 2) * RCLike.re ⟪x, B.B01 y⟫_ℂ +
          ((‖B.A0‖ + ‖B.A1‖) * ε +
            2 * s * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2)) :=
      mul_le_mul_of_nonneg_left hraw (by norm_num)
    _ = (2 * (-RCLike.re ⟪x, B.B01 y⟫_ℂ) +
          2 * (((‖B.A0‖ + ‖B.A1‖) * ε) +
            2 * s * ‖B.B01‖ * ε + ‖B.B01‖ * ε ^ 2) /
              (1 - s ^ 2)) * (1 - s ^ 2) := by
      field_simp [hden.ne']

end

end DavisKahan
end TauCeti
