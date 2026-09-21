/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorFiniteQ

/-! # Homogenization Error Closed -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open scoped ENNReal MatrixOrder BigOperators

/-!
# Closed finite-q homogenization-error bounds

This file packages the deterministic summation step in the form used by the
Section 5.7 minimal-scale corollary: once every scale response is controlled by
one algebraic envelope, the whole finite-`q` multiscale error is controlled by
the same envelope.
-/

noncomputable section

/-- Closed finite-`q` `\mathcal E` control from one scale-by-scale envelope.

The displayed right-hand side is the geometric summation constant times the
`q`-power of the single envelope.  In applications `R` is the collapsed
minimal-scale factor, for instance `sqrt ((3^m / X)^(-alpha))`. -/
theorem homogenizationErrorFinite_le_of_scaleResponseEnvelope
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r tau delta q A R : ℝ}
    (hdelta : delta = r - tau / 2)
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale Q (n - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 ≤
        A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) :
    Ch02.HomogenizationError Q n r
        Ch02.MultiscaleExponent.infinity (.finite q) a a0 ≤
      Real.rpow
        (Ch02.geometricDiscount r q *
          (Ch02.geometricDiscount delta q)⁻¹ *
          Real.rpow A q * Real.rpow R q)
        (1 / q) := by
  simpa [Ch02.HomogenizationError] using
    homogenizationErrorFinite_infinity_le_of_scaleResponse_le
      (Q := Q) (n := n) hn a a0
      (r := r) (tau := tau) (delta := delta) (q := q)
      (A := A) (R := R)
      hdelta hrq hdeltaq hq hA hR hscale

/-- Same as `homogenizationErrorFinite_le_of_scaleResponseEnvelope`, with the
geometric constant pulled out of the `q`-root. -/
theorem homogenizationErrorFinite_le_const_mul_of_scaleResponseEnvelope
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r tau delta q A R : ℝ}
    (hdelta : delta = r - tau / 2)
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale Q (n - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 ≤
        A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) :
    let Cgeom : ℝ :=
      Real.rpow
        (Ch02.geometricDiscount r q *
          (Ch02.geometricDiscount delta q)⁻¹)
        (1 / q);
    Ch02.HomogenizationError Q n r
        Ch02.MultiscaleExponent.infinity (.finite q) a a0 ≤
      Cgeom * A * R := by
  let G : ℝ :=
    Ch02.geometricDiscount r q * (Ch02.geometricDiscount delta q)⁻¹
  let Cgeom : ℝ := Real.rpow G (1 / q)
  have hG_nonneg : 0 ≤ G := by
    have hdisc_r_nonneg : 0 ≤ Ch02.geometricDiscount r q := by
      simpa [Ch02.geometricDiscount_eq_old] using
        Homogenization.geometricDiscount_nonneg hrq
    have hdisc_delta_pos : 0 < Ch02.geometricDiscount delta q := by
      simpa [Ch02.geometricDiscount_eq_old] using
        Homogenization.geometricDiscount_pos hdeltaq
    dsimp [G]
    positivity
  have hmain :=
    homogenizationErrorFinite_le_of_scaleResponseEnvelope
      (Q := Q) (n := n) hn a a0
      (r := r) (tau := tau) (delta := delta) (q := q)
      (A := A) (R := R)
      hdelta hrq hdeltaq hq hA hR hscale
  have hAq_nonneg : 0 ≤ Real.rpow A q := Real.rpow_nonneg hA q
  have hRq_nonneg : 0 ≤ Real.rpow R q := Real.rpow_nonneg hR q
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have hA_root : Real.rpow (Real.rpow A q) (1 / q) = A := by
    rw [one_div]
    exact Real.rpow_rpow_inv hA hq_ne
  have hR_root : Real.rpow (Real.rpow R q) (1 / q) = R := by
    rw [one_div]
    exact Real.rpow_rpow_inv hR hq_ne
  have hroot :
      Real.rpow (G * Real.rpow A q * Real.rpow R q) (1 / q) =
        Cgeom * A * R := by
    have hmul₁ :
        Real.rpow (G * Real.rpow A q * Real.rpow R q) (1 / q) =
          Real.rpow (G * Real.rpow A q) (1 / q) *
            Real.rpow (Real.rpow R q) (1 / q) := by
      simpa [mul_assoc] using
        Real.mul_rpow
          (x := G * Real.rpow A q) (y := Real.rpow R q) (z := 1 / q)
          (mul_nonneg hG_nonneg hAq_nonneg) hRq_nonneg
    have hmul₂ :
        Real.rpow (G * Real.rpow A q) (1 / q) =
          Real.rpow G (1 / q) *
            Real.rpow (Real.rpow A q) (1 / q) := by
      simpa using
        Real.mul_rpow
          (x := G) (y := Real.rpow A q) (z := 1 / q)
          hG_nonneg hAq_nonneg
    rw [hmul₁, hmul₂, hA_root, hR_root]
  exact hmain.trans (by simpa [G, Cgeom] using le_of_eq hroot)

/-- Closed finite-`q` control on a whole cube. -/
theorem homogenizationErrorOnCube_le_of_scaleResponseEnvelope
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r tau delta q A R : ℝ}
    (hdelta : delta = r - tau / 2)
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 ≤
        A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) :
    Ch02.HomogenizationErrorOnCube Q r
        Ch02.MultiscaleExponent.infinity (.finite q) a a0 ≤
      Real.rpow
        (Ch02.geometricDiscount r q *
          (Ch02.geometricDiscount delta q)⁻¹ *
          Real.rpow A q * Real.rpow R q)
        (1 / q) := by
  simpa [Ch02.HomogenizationErrorOnCube] using
    homogenizationErrorFinite_le_of_scaleResponseEnvelope
      (Q := Q) (n := Q.scale) le_rfl a a0
      (r := r) (tau := tau) (delta := delta) (q := q)
      (A := A) (R := R)
      hdelta hrq hdeltaq hq hA hR hscale

/-- Whole-cube version with the geometric constant pulled out. -/
theorem homogenizationErrorOnCube_le_const_mul_of_scaleResponseEnvelope
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r tau delta q A R : ℝ}
    (hdelta : delta = r - tau / 2)
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 ≤
        A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) :
    let Cgeom : ℝ :=
      Real.rpow
        (Ch02.geometricDiscount r q *
          (Ch02.geometricDiscount delta q)⁻¹)
        (1 / q);
    Ch02.HomogenizationErrorOnCube Q r
        Ch02.MultiscaleExponent.infinity (.finite q) a a0 ≤
      Cgeom * A * R := by
  simpa [Ch02.HomogenizationErrorOnCube] using
    homogenizationErrorFinite_le_const_mul_of_scaleResponseEnvelope
      (Q := Q) (n := Q.scale) le_rfl a a0
      (r := r) (tau := tau) (delta := delta) (q := q)
      (A := A) (R := R)
      hdelta hrq hdeltaq hq hA hR hscale

/-- Origin-cube version with the minimal-scale factor already collapsed into
`X`.  This is the deterministic target shape for the Section 5.7 stochastic
corollary. -/
theorem homogenizationErrorOnOriginCube_le_of_scaleResponseMinimalEnvelope
    {d : ℕ} [NeZero d] {m : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r tau delta q A X alpha : ℝ}
    (hdelta : delta = r - tau / 2)
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hA : 0 ≤ A) (hX : 0 < X)
    (hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ))
          (((m : ℕ) : ℤ) - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 ≤
        A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / X) ^ (-alpha))) :
    Ch02.HomogenizationErrorOnCube (originCube d ((m : ℕ) : ℤ)) r
        Ch02.MultiscaleExponent.infinity (.finite q) a a0 ≤
      Real.rpow
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount delta q)⁻¹)
          (1 / q) *
        A * Real.sqrt (((3 : ℝ) ^ m / X) ^ (-alpha)) := by
  have hbase_pos : 0 < (3 : ℝ) ^ m / X :=
    div_pos (by positivity) hX
  have hR : 0 ≤ Real.sqrt (((3 : ℝ) ^ m / X) ^ (-alpha)) := by
    positivity
  exact
    homogenizationErrorOnCube_le_const_mul_of_scaleResponseEnvelope
      (Q := originCube d ((m : ℕ) : ℤ)) a a0
      (r := r) (tau := tau) (delta := delta) (q := q)
      (A := A) (R := Real.sqrt (((3 : ℝ) ^ m / X) ^ (-alpha)))
      hdelta hrq hdeltaq hq hA hR hscale

end

end Section57
end Ch05
end Book
end Homogenization
