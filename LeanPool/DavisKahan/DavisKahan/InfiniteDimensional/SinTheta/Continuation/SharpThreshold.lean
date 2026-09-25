/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Theorem

/-! # Sharp Threshold -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# The sharp scalar threshold for off-diagonal continuation

For a finite gap of width `d`, the standard off-diagonal spectral enclosure
moves a component by

`(sqrt (d^2 + 4 r^2) - d) / 2`.

The residual distance to the opposite component is therefore

`(3 d - sqrt (d^2 + 4 r^2)) / 2`.

This leaf isolates the scalar content of the sharp continuation threshold.  It
proves that the residual margin is positive exactly in the regime needed by
the Davis--Kahan branch argument, and that the endpoint margin is a uniform
lower bound along the affine path `A + t H`, `0 ≤ t ≤ 1`.

No spectral enclosure is asserted here.  Later continuation leaves should
supply the operator-theoretic enclosure and use these lemmas only for the
scalar optimization.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open Set

universe v

/-- Residual separation left by the standard finite-gap off-diagonal spectral
enclosure with original gap `d` and perturbation size `r`. -/
noncomputable def offDiagonalContinuationMargin (d r : ℝ) : ℝ :=
  (3 * d - Real.sqrt (d ^ 2 + 4 * r ^ 2)) / 2

/-- The scalar heart of the `sqrt 2 * d` threshold. -/
theorem sqrt_gap_radius_lt_three_mul_of_lt_sqrtTwo_mul
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hsmall : r < Real.sqrt 2 * d) :
    Real.sqrt (d ^ 2 + 4 * r ^ 2) < 3 * d := by
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2d_nonneg : 0 ≤ Real.sqrt 2 * d :=
    mul_nonneg hsqrt2_nonneg hd.le
  have hrsq : r ^ 2 < (Real.sqrt 2 * d) ^ 2 :=
    (sq_lt_sq₀ hr hsqrt2d_nonneg).2 hsmall
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hrsq
  have hradicand : 0 ≤ d ^ 2 + 4 * r ^ 2 := by positivity
  have hthree_nonneg : 0 ≤ 3 * d := by positivity
  apply (sq_lt_sq₀ (Real.sqrt_nonneg _) hthree_nonneg).1
  rw [Real.sq_sqrt hradicand]
  nlinarith

/-- The residual continuation margin is positive below the sharp threshold. -/
theorem offDiagonalContinuationMargin_pos
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hsmall : r < Real.sqrt 2 * d) :
    0 < offDiagonalContinuationMargin d r := by
  have hroot :=
    sqrt_gap_radius_lt_three_mul_of_lt_sqrtTwo_mul hd hr hsmall
  dsimp [offDiagonalContinuationMargin]
  linarith

/-- Increasing the perturbation size can only decrease the residual
continuation margin. -/
theorem offDiagonalContinuationMargin_anti
    {d r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) :
    offDiagonalContinuationMargin d R ≤
      offDiagonalContinuationMargin d r := by
  have hR0 : 0 ≤ R := hr.trans hR
  have hrsq : r ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ hr hR0).2 hR
  have hrad : d ^ 2 + 4 * r ^ 2 ≤ d ^ 2 + 4 * R ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hrad
  dsimp [offDiagonalContinuationMargin]
  linarith

section OperatorPath

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- Along `A + t H`, the endpoint residual margin is a common lower bound for
all `t ∈ [0,1]`. -/
theorem offDiagonalContinuationMargin_norm_le_path
    (Hpert : H →L[ℂ] H) {d t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    offDiagonalContinuationMargin d ‖Hpert‖ ≤
      offDiagonalContinuationMargin d (t * ‖Hpert‖) := by
  have hnorm : 0 ≤ ‖Hpert‖ := norm_nonneg Hpert
  have htNorm : 0 ≤ t * ‖Hpert‖ := mul_nonneg ht.1 hnorm
  have hle : t * ‖Hpert‖ ≤ ‖Hpert‖ := by
    have haux : 0 ≤ (1 - t) * ‖Hpert‖ :=
      mul_nonneg (sub_nonneg.mpr ht.2) hnorm
    nlinarith
  exact offDiagonalContinuationMargin_anti htNorm hle

omit [CompleteSpace H] in
/-- The sharp endpoint hypothesis gives a positive residual margin at every
point of the affine perturbation path. -/
theorem offDiagonalContinuationMargin_path_pos
    (Hpert : H →L[ℂ] H) {d t : ℝ}
    (hd : 0 < d) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ‖Hpert‖ < Real.sqrt 2 * d) :
    0 < offDiagonalContinuationMargin d (t * ‖Hpert‖) := by
  have hend : 0 < offDiagonalContinuationMargin d ‖Hpert‖ :=
    offDiagonalContinuationMargin_pos hd (norm_nonneg Hpert) hsmall
  exact hend.trans_le
    (offDiagonalContinuationMargin_norm_le_path Hpert ht)

end OperatorPath

end DavisKahanExt
end TauCeti
