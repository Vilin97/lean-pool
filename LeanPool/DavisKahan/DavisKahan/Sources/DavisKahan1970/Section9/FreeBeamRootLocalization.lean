/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamRootExclusion
public import Mathlib.Tactic

/-!
# Reduction of free-beam root localization to scalar certificates

The operator campaign only needs a reusable certificate that the first positive
root of `cos beta * cosh beta = 1` lies above `4.73`.  This file isolates the
remaining scalar analysis into small sign and exclusion obligations.

It deliberately does not claim a numerical transcendental estimate that has
not yet been proved.  Instead it supplies exact constructors showing which
finite set of scalar facts is sufficient for `PositiveRootLocalization`.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Classical

noncomputable section

open FreeBeam

/-- Continuity of the characteristic function. -/
theorem continuous_characteristic :
    Continuous FreeBeam.characteristic := by
  unfold FreeBeam.characteristic
  exact (Real.continuous_cos.mul Real.continuous_cosh).sub continuous_const

/-- The characteristic equation in its usual multiplicative form. -/
theorem characteristic_eq_zero_iff (beta : ℝ) :
    FreeBeam.characteristic beta = 0 ↔
      Real.cos beta * Real.cosh beta = 1 := by
  unfold FreeBeam.characteristic
  exact sub_eq_zero

/-- No root can occur where cosine is nonpositive. -/
theorem characteristic_lt_zero_of_cos_nonpos
    {beta : ℝ} (hcos : Real.cos beta ≤ 0) :
    FreeBeam.characteristic beta < 0 := by
  unfold FreeBeam.characteristic
  have hcosh : 0 < Real.cosh beta := Real.cosh_pos beta
  have hprod : Real.cos beta * Real.cosh beta ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcos hcosh.le
  linarith

/-- Sign exclusion version of the preceding result. -/
theorem characteristic_ne_zero_of_cos_nonpos
    {beta : ℝ} (hcos : Real.cos beta ≤ 0) :
    FreeBeam.characteristic beta ≠ 0 :=
  ne_of_lt (characteristic_lt_zero_of_cos_nonpos hcos)

/-- A strict upper bound on `cos beta * cosh beta` excludes a root. -/
theorem characteristic_ne_zero_of_product_lt_one
    {beta : ℝ} (h : Real.cos beta * Real.cosh beta < 1) :
    FreeBeam.characteristic beta ≠ 0 := by
  unfold FreeBeam.characteristic
  linarith

/-- A strict lower bound on `cos beta * cosh beta` excludes a root. -/
theorem characteristic_ne_zero_of_one_lt_product
    {beta : ℝ} (h : 1 < Real.cos beta * Real.cosh beta) :
    FreeBeam.characteristic beta ≠ 0 := by
  unfold FreeBeam.characteristic
  linarith

/-- Exact certificate that a displayed root is the first positive root. -/
structure FirstPositiveRootCertificate where
  /-- The smallest positive root of the free-beam characteristic equation. -/
  root : ℝ
  root_pos : 0 < root
  root_equation :
    FreeBeam.characteristic root = 0
  no_smaller_positive_root : ∀ beta : ℝ,
    0 < beta → beta < root →
      FreeBeam.characteristic beta ≠ 0
  lower_bound : (473 : ℝ) / 100 < root

/-- The scalar first-root certificate supplies the interface consumed by the
operator-theoretic development. -/
noncomputable def FirstPositiveRootCertificate.toPositiveRootLocalization
    (C : FirstPositiveRootCertificate) :
    FreeBeam.PositiveRootLocalization where
  firstPositiveRoot := C.root
  firstPositiveRoot_pos := C.root_pos
  firstPositiveRoot_characteristic := C.root_equation
  minimal := by
    intro beta hbeta hroot
    by_contra hle
    have hlt : beta < C.root := lt_of_not_ge hle
    exact C.no_smaller_positive_root beta hbeta hlt hroot
  lower_bound := C.lower_bound

/-- It is enough to exclude roots on `(0, lower]`, then on `(lower, root)`. -/
noncomputable def firstPositiveRootCertificateOfSplitExclusion
    {root lower : ℝ}
    (hroot_pos : 0 < root)
    (hroot : FreeBeam.characteristic root = 0)
    (hsmall : ∀ beta : ℝ, 0 < beta → beta ≤ lower →
      FreeBeam.characteristic beta ≠ 0)
    (hmiddle : ∀ beta : ℝ, lower < beta → beta < root →
      FreeBeam.characteristic beta ≠ 0)
    (h473 : (473 : ℝ) / 100 < root) :
    FirstPositiveRootCertificate where
  root := root
  root_pos := hroot_pos
  root_equation := hroot
  no_smaller_positive_root := by
    intro beta hbeta hbeta_root
    by_cases hle : beta ≤ lower
    · exact hsmall beta hbeta hle
    · exact hmiddle beta (lt_of_not_ge hle) hbeta_root
  lower_bound := h473

/-- A sign partition can discharge a root-exclusion interval pointwise. -/
theorem root_exclusion_of_pointwise_sign
    {S : Set ℝ}
    (hsign : ∀ beta ∈ S,
      Real.cos beta ≤ 0 ∨
      Real.cos beta * Real.cosh beta < 1 ∨
      1 < Real.cos beta * Real.cosh beta) :
    ∀ beta ∈ S,
      FreeBeam.characteristic beta ≠ 0 := by
  intro beta hbeta
  rcases hsign beta hbeta with hcos | hlt | hgt
  · exact characteristic_ne_zero_of_cos_nonpos hcos
  · exact characteristic_ne_zero_of_product_lt_one hlt
  · exact characteristic_ne_zero_of_one_lt_product hgt

/-- Any completed first-root certificate gives the numerical eigenvalue bound
used by the free-beam application. -/
theorem positive_root_pow_four_gt_five_hundred_of_certificate
    (C : FirstPositiveRootCertificate)
    {beta : ℝ} (hbeta : 0 < beta)
    (hroot : FreeBeam.characteristic beta = 0) :
    500 < beta ^ 4 :=
  FreeBeam.positive_root_fourth_power_gt_five_hundred
    C.toPositiveRootLocalization hbeta hroot

/-! ## The numerical estimate, unconditionally

`FreeBeamRootExclusion` proves `cos beta * cosh beta < 1` on all of `(0, 4.73]`,
so the characteristic function simply has no root there.  That makes the
certificate machinery above unnecessary for the one thing the free-beam
application actually needs: the two theorems below carry no hypothesis, and in
particular do not assume that a first root exists.

`positive_root_pow_four_gt_five_hundred_of_certificate` is retained because it
records the reduction, but every consumer should prefer
`five_hundred_lt_pow_four_of_characteristic_eq_zero`.
-/

/-- **Every positive root of the free-beam characteristic function exceeds
`4.73`.**  There is nothing to localize: `cos beta * cosh beta < 1` throughout
`(0, 4.73]`, so the characteristic function is negative there. -/
theorem four_seventy_three_lt_of_characteristic_eq_zero {beta : ℝ}
    (hbeta : 0 < beta)
    (hroot : FreeBeam.characteristic beta = 0) :
    (473 : ℝ) / 100 < beta := by
  by_contra hcon
  exact absurd hroot (characteristic_ne_zero_of_product_lt_one
    (DavisKahan1970.Section9.cos_mul_cosh_lt_one_of_le_four_seventy_three hbeta
      (not_lt.mp hcon)))

/-- **Davis--Kahan 1970 Section 9: the free-beam eigenvalue bound, with no
certificate.**

Every positive characteristic root has fourth power above `500`.  Since the
free-beam eigenvalues are exactly the fourth powers of the positive roots, this
is the paper's `alpha_3 > 500` -- and the margin is genuinely thin, the first
root being `4.7300407...` with `4.7300407^4 = 500.56...`. -/
theorem five_hundred_lt_pow_four_of_characteristic_eq_zero {beta : ℝ}
    (hbeta : 0 < beta)
    (hroot : FreeBeam.characteristic beta = 0) :
    500 < beta ^ 4 := by
  have h473 := four_seventy_three_lt_of_characteristic_eq_zero hbeta hroot
  have hpow : ((473 : ℝ) / 100) ^ 4 < beta ^ 4 :=
    pow_lt_pow_left₀ h473 (by norm_num) (by norm_num)
  have hnum :=
    FreeBeam.four_seventy_three_pow_four_gt_five_hundred
  linarith

end

end Classical
end FreeBeam
end DavisKahan
end TauCeti
