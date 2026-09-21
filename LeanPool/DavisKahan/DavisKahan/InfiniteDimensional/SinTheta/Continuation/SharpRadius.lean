/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpThreshold

/-! # Sharp Radius -/

open TauCeti.DavisKahan.Angle


/-!
# Sharp off-diagonal enclosure radius

The finite-gap off-diagonal continuation argument uses the displacement

`(sqrt (d^2 + 4 r^2) - d) / 2`.

This leaf relates that displacement to the residual continuation margin from
`ContinuationSharpThreshold`, proves uniform control along the affine path,
and records the scalar interval-versus-exterior separation estimate that the
operator-theoretic spectral enclosure will consume.

No spectral inclusion is asserted here.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open Set

universe v

/-- The standard finite-gap off-diagonal spectral-enclosure displacement. -/
noncomputable def offDiagonalEnclosureRadius (d r : ℝ) : ℝ :=
  (Real.sqrt (d ^ 2 + 4 * r ^ 2) - d) / 2

/-- The residual continuation margin is exactly the original gap minus the
off-diagonal enclosure radius. -/
theorem offDiagonalContinuationMargin_eq_sub_enclosureRadius
    (d r : ℝ) :
    offDiagonalContinuationMargin d r =
      d - offDiagonalEnclosureRadius d r := by
  simp only [offDiagonalContinuationMargin, offDiagonalEnclosureRadius]
  ring

/-- The off-diagonal enclosure radius is nonnegative for a nonnegative gap. -/
theorem offDiagonalEnclosureRadius_nonneg
    {d r : ℝ} (hd : 0 ≤ d) :
    0 ≤ offDiagonalEnclosureRadius d r := by
  have hrad : 0 ≤ d ^ 2 + 4 * r ^ 2 := by positivity
  have hsq : d ^ 2 ≤ (Real.sqrt (d ^ 2 + 4 * r ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hrad]
    nlinarith [sq_nonneg r]
  have hle : d ≤ Real.sqrt (d ^ 2 + 4 * r ^ 2) :=
    (sq_le_sq₀ hd (Real.sqrt_nonneg _)).1 hsq
  simp only [offDiagonalEnclosureRadius]
  linarith

/-- Below the sharp `sqrt 2 * d` threshold, the enclosure displacement is
strictly smaller than the original gap. -/
theorem offDiagonalEnclosureRadius_lt_gap
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hsmall : r < Real.sqrt 2 * d) :
    offDiagonalEnclosureRadius d r < d := by
  have hmargin : 0 < offDiagonalContinuationMargin d r :=
    offDiagonalContinuationMargin_pos hd hr hsmall
  rw [offDiagonalContinuationMargin_eq_sub_enclosureRadius] at hmargin
  linarith

/-- Increasing perturbation size increases the off-diagonal enclosure radius. -/
theorem offDiagonalEnclosureRadius_mono
    {d r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) :
    offDiagonalEnclosureRadius d r ≤ offDiagonalEnclosureRadius d R := by
  have hmargin := offDiagonalContinuationMargin_anti (d := d) hr hR
  rw [offDiagonalContinuationMargin_eq_sub_enclosureRadius,
    offDiagonalContinuationMargin_eq_sub_enclosureRadius] at hmargin
  linarith

section OperatorPath

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- The endpoint enclosure radius controls every point of the affine path. -/
theorem offDiagonalEnclosureRadius_path_le_norm
    (Hpert : H →L[ℂ] H) {d t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    offDiagonalEnclosureRadius d (t * ‖Hpert‖) ≤
      offDiagonalEnclosureRadius d ‖Hpert‖ := by
  have hnorm : 0 ≤ ‖Hpert‖ := norm_nonneg Hpert
  have htNorm : 0 ≤ t * ‖Hpert‖ := mul_nonneg ht.1 hnorm
  have hle : t * ‖Hpert‖ ≤ ‖Hpert‖ := by
    have haux : 0 ≤ (1 - t) * ‖Hpert‖ :=
      mul_nonneg (sub_nonneg.mpr ht.2) hnorm
    nlinarith
  exact offDiagonalEnclosureRadius_mono htNorm hle

omit [CompleteSpace H] in
/-- Under the endpoint sharp threshold, every pathwise enclosure displacement
is strictly below the original gap. -/
theorem offDiagonalEnclosureRadius_path_lt_gap
    (Hpert : H →L[ℂ] H) {d t : ℝ}
    (hd : 0 < d) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ‖Hpert‖ < Real.sqrt 2 * d) :
    offDiagonalEnclosureRadius d (t * ‖Hpert‖) < d := by
  exact (offDiagonalEnclosureRadius_path_le_norm Hpert ht).trans_lt
    (offDiagonalEnclosureRadius_lt_gap hd (norm_nonneg Hpert) hsmall)

end OperatorPath

/-- An interval enlarged by the off-diagonal enclosure radius remains
separated from the original exterior by the residual continuation margin. -/
theorem offDiagonal_enlargedInterval_separated_from_exterior
    {left right d r x y : ℝ}
    (hx : x ∈ Set.Icc
      (left - offDiagonalEnclosureRadius d r)
      (right + offDiagonalEnclosureRadius d r))
    (hy : y ≤ left - d ∨ right + d ≤ y) :
    offDiagonalContinuationMargin d r ≤ |x - y| := by
  rw [offDiagonalContinuationMargin_eq_sub_enclosureRadius]
  rcases hy with hy | hy
  · have hgap : d - offDiagonalEnclosureRadius d r ≤ x - y := by
      linarith [hx.1]
    exact hgap.trans (le_abs_self (x - y))
  · have hgap : d - offDiagonalEnclosureRadius d r ≤ y - x := by
      linarith [hx.2]
    calc
      d - offDiagonalEnclosureRadius d r ≤ y - x := hgap
      _ = -(x - y) := by ring
      _ ≤ |x - y| := neg_le_abs (x - y)

/-- Path-uniform version of the enlarged-interval/exterior separation. -/
theorem offDiagonal_path_enlargedInterval_separated_from_exterior
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (Hpert : H →L[ℂ] H)
    {left right d t x y : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc
      (left - offDiagonalEnclosureRadius d (t * ‖Hpert‖))
      (right + offDiagonalEnclosureRadius d (t * ‖Hpert‖)))
    (hy : y ≤ left - d ∨ right + d ≤ y) :
    offDiagonalContinuationMargin d ‖Hpert‖ ≤ |x - y| := by
  exact (offDiagonalContinuationMargin_norm_le_path Hpert ht).trans
    (offDiagonal_enlargedInterval_separated_from_exterior hx hy)

end DavisKahanExt
end TauCeti
