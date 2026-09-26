/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.Assembly
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.P4Integrability
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup.ScaleBounds

/-! # Normalized Cutoff -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# NormalizedCutoff

Concrete normalized cutoff used in the first Section 5.3 lemma.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- The normalized quantitative cutoff used in Section 5.3. -/
noncomputable def section53NormalizedCutoff {d : ℕ} (Q : TriadicCube d) : Vec d → ℝ :=
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  fun x => (cubeAverage Q η)⁻¹ * η x

/-- Pointwise bound for the normalized Section 5.3 cutoff. -/
noncomputable def section53CutoffBound {d : ℕ} (Q : TriadicCube d) : ℝ :=
  let η : Vec d → ℝ :=
    QuantitativeCubeCutoff.canonicalFun Q (1 / 2 : ℝ) (3 / 4 : ℝ)
  (cubeAverage Q η)⁻¹

/-- Average oscillation constant for the normalized Section 5.3 cutoff. -/
noncomputable def section53CutoffOscillationConstant {d : ℕ} (Q : TriadicCube d) : ℝ :=
  section53CutoffBound Q *
    (quantitativeCubeCutoffGradientConst d /
      (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q))

/-- Descendant scale separation at depth `j`. -/
noncomputable def section53CutoffScaleSep {d : ℕ} (Q : TriadicCube d) (j : ℕ) : ℝ :=
  cubeScaleFactor Q / (3 : ℝ) ^ j

/-- Dual Besov bound for the normalized Section 5.3 cutoff. -/
noncomputable def section53CutoffDualBound {d : ℕ} (Q : TriadicCube d) (r : ℝ) : ℝ :=
  cubeBesovScaleWeight r Q *
    (cubeScaleFactor Q * section53CutoffOscillationConstant Q + section53CutoffBound Q)

/-- Derivative bound for the scalar-gradient cutoff field. -/
noncomputable def section53CutoffDerivativeBound {d : ℕ} (Q : TriadicCube d) : ℝ :=
  section53CutoffBound Q *
    (quantitativeCubeCutoffHessianConst d /
      ((((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q) ^ 2))

/-- Product coefficient used after selecting the concrete normalized cutoff.
The deterministic product estimate is first proved for the unnormalized
negative Besov norms.  This coefficient includes exactly the two parent-scale
factors needed to convert that estimate back to the note-normalized Ch4 weak
norms used in the manuscript RHS. -/
noncomputable def section53CutoffProductCoeff {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s t : ℝ) : ℝ :=
  max
    (cutoffProductScaledWeakNormCoeff Q s t (section53CutoffDerivativeBound Q)
      (scalarCutoffGradientField (section53NormalizedCutoff Q)) *
        cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q) 0

theorem section53CutoffBound_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ section53CutoffBound Q := by
  dsimp [section53CutoffBound]
  exact inv_nonneg.mpr (le_of_lt (cubeAverage_quantitativeCubeCutoff_canonicalFun_pos Q))

/-- The normalized Section 5.3 cutoff amplitude is bounded by a
dimension-only constant. -/
theorem section53CutoffBound_le_two_pow_card {d : ℕ} (Q : TriadicCube d) :
    section53CutoffBound Q ≤ (2 : ℝ) ^ d := by
  simpa [section53CutoffBound] using
    inv_cubeAverage_quantitativeCubeCutoff_canonicalFun_le_two_pow_card Q

theorem section53CutoffOscillationConstant_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ section53CutoffOscillationConstant Q := by
  dsimp [section53CutoffOscillationConstant]
  refine mul_nonneg (section53CutoffBound_nonneg Q) ?_
  refine div_nonneg (quantitativeCubeCutoffGradientConst_nonneg d) ?_
  have hrad : 0 < cubeRadius Q := cubeRadius_pos Q
  nlinarith

theorem section53CutoffDualBound_nonneg {d : ℕ} (Q : TriadicCube d) (r : ℝ) :
    0 ≤ section53CutoffDualBound Q r := by
  dsimp [section53CutoffDualBound]
  refine mul_nonneg (cubeBesovScaleWeight_nonneg r Q) ?_
  exact add_nonneg
    (mul_nonneg (cubeScaleFactor_nonneg Q) (section53CutoffOscillationConstant_nonneg Q))
    (section53CutoffBound_nonneg Q)

theorem section53CutoffDerivativeBound_nonneg {d : ℕ} (Q : TriadicCube d) :
    0 ≤ section53CutoffDerivativeBound Q := by
  dsimp [section53CutoffDerivativeBound]
  refine mul_nonneg (section53CutoffBound_nonneg Q) ?_
  exact div_nonneg (quantitativeCubeCutoffHessianConst_nonneg d) (sq_nonneg _)

theorem section53CutoffDerivativeBound_mul_scaleFactor_sq_eq
    {d : ℕ} (Q : TriadicCube d) :
    section53CutoffDerivativeBound Q * (cubeScaleFactor Q) ^ 2 =
      64 * quantitativeCubeCutoffHessianConst d * section53CutoffBound Q := by
  have hr : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
  dsimp [section53CutoffDerivativeBound]
  rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
  field_simp [hr]
  ring

theorem cubeScaleFactor_mul_section53CutoffDerivativeBound_eq
    {d : ℕ} (Q : TriadicCube d) :
    cubeScaleFactor Q * section53CutoffDerivativeBound Q =
      (64 * quantitativeCubeCutoffHessianConst d * section53CutoffBound Q) *
        cubeBesovScaleWeight 1 Q := by
  have hsq := section53CutoffDerivativeBound_mul_scaleFactor_sq_eq Q
  have hscale_ne : cubeScaleFactor Q ≠ 0 := by
    have hpos : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    exact hpos.ne'
  unfold cubeBesovScaleWeight
  rw [Real.rpow_neg_one]
  field_simp [hscale_ne]
  nlinarith [hsq]

theorem cubeLpNorm_section53NormalizedCutoff_gradient_le
    {d : ℕ} (Q : TriadicCube d) :
    cubeLpNorm Q ∞ (scalarCutoffGradientField (section53NormalizedCutoff Q)) ≤
      (8 * quantitativeCubeCutoffGradientConst d * section53CutoffBound Q) *
        cubeBesovScaleWeight 1 Q := by
  have hraw :=
    cubeLpNorm_infty_scalarCutoffGradientField_normalized_quantitativeCubeCutoff_canonicalFun_le Q
  have hEq :
      section53CutoffBound Q *
          (quantitativeCubeCutoffGradientConst d /
            (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)) =
        (8 * quantitativeCubeCutoffGradientConst d * section53CutoffBound Q) *
          cubeBesovScaleWeight 1 Q := by
    have hr : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
    unfold cubeBesovScaleWeight
    rw [Real.rpow_neg_one]
    rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
    field_simp [hr]
    ring
  calc
    cubeLpNorm Q ∞ (scalarCutoffGradientField (section53NormalizedCutoff Q))
        ≤
      section53CutoffBound Q *
        (quantitativeCubeCutoffGradientConst d /
          (((3 / 4 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)) := by
        simpa [section53NormalizedCutoff, section53CutoffBound] using hraw
    _ =
      (8 * quantitativeCubeCutoffGradientConst d * section53CutoffBound Q) *
        cubeBesovScaleWeight 1 Q := hEq

theorem section53CutoffProductCoeff_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s t : ℝ) :
    0 ≤ section53CutoffProductCoeff Q s t := by
  exact le_max_right _ _

/-- The normalized cutoff oscillation coefficient has the exact descendant
scale decay.  The only remaining size information is the normalized cutoff
amplitude `section53CutoffBound Q`. -/
theorem section53CutoffOscillationConstant_mul_scaleSep_eq
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    section53CutoffOscillationConstant Q * section53CutoffScaleSep Q j =
      (8 * quantitativeCubeCutoffGradientConst d * section53CutoffBound Q) *
        ((3 : ℝ) ^ j)⁻¹ := by
  have hr : cubeRadius Q ≠ 0 := (cubeRadius_pos Q).ne'
  have hpow : (3 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)
  dsimp [section53CutoffOscillationConstant, section53CutoffScaleSep]
  rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
  field_simp [hr, hpow]
  ring

/-- The complete linear cutoff coefficient that appears in the first
Section 5.3 expected RHS is bounded by a dimension-only constant.  This is the
coefficient-weighted form where the Besov scale weights cancel. -/
theorem section53_linearCutoffCoeff_le_dimensional
    {d : ℕ} (Q : TriadicCube d) {r : ℝ}
    (_hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1) :
    (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + r) *
          cubeBesovScaleWeight (-r) Q * section53CutoffDualBound Q r) ≤
      (d : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
  have hosc :
      cubeScaleFactor Q * section53CutoffOscillationConstant Q =
        8 * quantitativeCubeCutoffGradientConst d * section53CutoffBound Q := by
    have h :=
      section53CutoffOscillationConstant_mul_scaleSep_eq (d := d) Q 0
    simpa [section53CutoffScaleSep, mul_assoc, mul_left_comm, mul_comm] using h
  have hcut :
      cubeScaleFactor Q * section53CutoffOscillationConstant Q +
          section53CutoffBound Q ≤
        (8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d := by
    have hB := section53CutoffBound_le_two_pow_card Q
    have hcoef_nonneg :
        0 ≤ 8 * quantitativeCubeCutoffGradientConst d + 1 := by
      have hG : 0 ≤ quantitativeCubeCutoffGradientConst d :=
        quantitativeCubeCutoffGradientConst_nonneg d
      nlinarith
    calc
      cubeScaleFactor Q * section53CutoffOscillationConstant Q +
          section53CutoffBound Q =
        (8 * quantitativeCubeCutoffGradientConst d + 1) *
          section53CutoffBound Q := by
          rw [hosc]
          ring
      _ ≤ (8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d :=
          mul_le_mul_of_nonneg_left hB hcoef_nonneg
  have hcut_nonneg :
      0 ≤ cubeScaleFactor Q * section53CutoffOscillationConstant Q +
          section53CutoffBound Q := by
    exact add_nonneg
      (mul_nonneg (cubeScaleFactor_nonneg Q)
        (section53CutoffOscillationConstant_nonneg Q))
      (section53CutoffBound_nonneg Q)
  have hdual :
      cubeBesovScaleWeight (-r) Q * section53CutoffDualBound Q r =
        cubeScaleFactor Q * section53CutoffOscillationConstant Q +
          section53CutoffBound Q := by
    calc
      cubeBesovScaleWeight (-r) Q * section53CutoffDualBound Q r =
          (cubeBesovScaleWeight (-r) Q * cubeBesovScaleWeight r Q) *
            (cubeScaleFactor Q * section53CutoffOscillationConstant Q +
              section53CutoffBound Q) := by
            simp [section53CutoffDualBound]
            ring
      _ =
          cubeScaleFactor Q * section53CutoffOscillationConstant Q +
            section53CutoffBound Q := by
            rw [cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight]
            ring
  have hpow :
      (3 : ℝ) ^ ((d : ℝ) + r) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + r) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hpow_upper_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hmain :
      (3 : ℝ) ^ ((d : ℝ) + r) *
          (cubeScaleFactor Q * section53CutoffOscillationConstant Q +
            section53CutoffBound Q) ≤
        (3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d) :=
    mul_le_mul hpow hcut hcut_nonneg hpow_upper_nonneg
  have hinner :
      (3 : ℝ) ^ ((d : ℝ) + r) *
          cubeBesovScaleWeight (-r) Q * section53CutoffDualBound Q r =
        (3 : ℝ) ^ ((d : ℝ) + r) *
          (cubeScaleFactor Q * section53CutoffOscillationConstant Q +
            section53CutoffBound Q) := by
    calc
      (3 : ℝ) ^ ((d : ℝ) + r) *
          cubeBesovScaleWeight (-r) Q * section53CutoffDualBound Q r =
        (3 : ℝ) ^ ((d : ℝ) + r) *
          (cubeBesovScaleWeight (-r) Q * section53CutoffDualBound Q r) := by ring
      _ =
        (3 : ℝ) ^ ((d : ℝ) + r) *
          (cubeScaleFactor Q * section53CutoffOscillationConstant Q +
            section53CutoffBound Q) := by rw [hdual]
  calc
    (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + r) *
          cubeBesovScaleWeight (-r) Q * section53CutoffDualBound Q r)
        =
      (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + r) *
          (cubeScaleFactor Q * section53CutoffOscillationConstant Q +
            section53CutoffBound Q)) := by
          rw [hinner]
    _ ≤
      (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
          exact mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
    _ =
      (d : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
          simp

private theorem cubeBesovScaleWeight_originCube_nat_le_one
    {d : ℕ} (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    cubeBesovScaleWeight r (originCube d (m : ℤ)) ≤ 1 := by
  unfold cubeBesovScaleWeight
  rw [cubeScaleFactor_originCube]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 3)
      (by exact_mod_cast Nat.zero_le m : (0 : ℤ) ≤ (m : ℤ)))
    (by linarith)

/-- The cutoff-dual coefficient that multiplies the integral of the
note-normalized weak norm is bounded by a dimension-only constant on origin
cubes.  This is the coefficient form used in the coarse-fluctuation RHS
conversion. -/
theorem section53_linearCutoffCoeff_origin_le_dimensional
    {d : ℕ} (m : ℕ) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1) :
    (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + r) *
          section53CutoffDualBound (originCube d (m : ℤ)) r) ≤
      (d : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
  let Q : TriadicCube d := originCube d (m : ℤ)
  have hosc :
      cubeScaleFactor Q * section53CutoffOscillationConstant Q =
        8 * quantitativeCubeCutoffGradientConst d * section53CutoffBound Q := by
    have h :=
      section53CutoffOscillationConstant_mul_scaleSep_eq (d := d) Q 0
    simpa [section53CutoffScaleSep, mul_assoc, mul_left_comm, mul_comm] using h
  have hcut :
      cubeScaleFactor Q * section53CutoffOscillationConstant Q +
          section53CutoffBound Q ≤
        (8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d := by
    have hB := section53CutoffBound_le_two_pow_card Q
    have hcoef_nonneg :
        0 ≤ 8 * quantitativeCubeCutoffGradientConst d + 1 := by
      have hG : 0 ≤ quantitativeCubeCutoffGradientConst d :=
        quantitativeCubeCutoffGradientConst_nonneg d
      nlinarith
    calc
      cubeScaleFactor Q * section53CutoffOscillationConstant Q +
          section53CutoffBound Q =
        (8 * quantitativeCubeCutoffGradientConst d + 1) *
          section53CutoffBound Q := by
          rw [hosc]
          ring
      _ ≤ (8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d :=
          mul_le_mul_of_nonneg_left hB hcoef_nonneg
  have hcut_nonneg :
      0 ≤ cubeScaleFactor Q * section53CutoffOscillationConstant Q +
          section53CutoffBound Q := by
    exact add_nonneg
      (mul_nonneg (cubeScaleFactor_nonneg Q)
        (section53CutoffOscillationConstant_nonneg Q))
      (section53CutoffBound_nonneg Q)
  have hK_nonneg :
      0 ≤ (8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d := by
    exact hcut_nonneg.trans hcut
  have hdual :
      section53CutoffDualBound Q r ≤
        (8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d := by
    have hweight : cubeBesovScaleWeight r Q ≤ 1 := by
      simpa [Q] using
        cubeBesovScaleWeight_originCube_nat_le_one (d := d) m hr_nonneg
    calc
      section53CutoffDualBound Q r =
          cubeBesovScaleWeight r Q *
            (cubeScaleFactor Q * section53CutoffOscillationConstant Q +
              section53CutoffBound Q) := by
            simp [section53CutoffDualBound]
      _ ≤
          1 * ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d) :=
            mul_le_mul hweight hcut hcut_nonneg zero_le_one
      _ =
          (8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d := by ring
  have hpow :
      (3 : ℝ) ^ ((d : ℝ) + r) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hpow_upper_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hmain :
      (3 : ℝ) ^ ((d : ℝ) + r) * section53CutoffDualBound Q r ≤
        (3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d) :=
    mul_le_mul hpow hdual (section53CutoffDualBound_nonneg Q r) hpow_upper_nonneg
  calc
    (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + r) * section53CutoffDualBound Q r)
        ≤
      (Fintype.card (Fin d) : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
          exact mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
    _ =
      (d : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + 1) *
          ((8 * quantitativeCubeCutoffGradientConst d + 1) * (2 : ℝ) ^ d)) := by
          simp

/-- A weighted bound and a bound on a nonnegative factor remain valid after
multiplication by the same nonnegative scalar coefficients. -/
private theorem scalar_product_le_of_weighted_bound
    {A K P n x X v w z : ℝ}
    (hweighted : A * (v * w * z) ≤ K) (hx : x ≤ X)
    (hx_nonneg : 0 ≤ x) (hK_nonneg : 0 ≤ K)
    (hP_nonneg : 0 ≤ P) (hn_nonneg : 0 ≤ n) :
    A * P * (n * (x * v)) * w * z ≤ K * P * (n * X) := by
  have hproduct := mul_le_mul hweighted hx hx_nonneg hK_nonneg
  calc
    A * P * (n * (x * v)) * w * z = (P * n) * ((A * (v * w * z)) * x) := by ring
    _ ≤ (P * n) * (K * X) :=
      mul_le_mul_of_nonneg_left hproduct (mul_nonneg hP_nonneg hn_nonneg)
    _ = K * P * (n * X) := by ring

/-- The concrete cutoff-product coefficient is bounded by a dimension-only
constant on origin cubes in the Section 5.3 exponent range.  The proof keeps
the scale cancellation explicit:
the derivative and gradient cutoff sizes contribute one factor of
`cubeBesovScaleWeight 1`, while the product coefficient contributes
`cubeBesovScaleWeight (-(1 - s - t))`; their product is
`cubeBesovScaleWeight (s + t) ≤ 1` on origin cubes. -/
theorem section53CutoffProductCoeff_origin_le_dimensional
    {d : ℕ} [NeZero d] (m : ℕ) {s t : ℝ}
    (hs_nonneg : 0 ≤ s) (hst_nonneg : 0 ≤ s + t) :
    section53CutoffProductCoeff (originCube d (m : ℤ)) s t ≤
      (((128 * quantitativeCubeCutoffHessianConst d +
              24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d) *
        (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
              (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
          ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1))) := by
  let Q : TriadicCube d := originCube d (m : ℤ)
  let A : ℝ :=
    2 * cubeScaleFactor Q * section53CutoffDerivativeBound Q +
      3 * cubeLpNorm Q ∞ (scalarCutoffGradientField (section53NormalizedCutoff Q))
  let Kcut : ℝ :=
    (128 * quantitativeCubeCutoffHessianConst d +
      24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d
  let Poinc : ℝ :=
    (Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      (Fintype.card (Fin d) : ℝ)
  let Flux : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + (1 - s)) *
        cubeBesovScaleWeight (-(1 - s - t)) Q)
  have hH_nonneg : 0 ≤ quantitativeCubeCutoffHessianConst d :=
    quantitativeCubeCutoffHessianConst_nonneg d
  have hG_nonneg : 0 ≤ quantitativeCubeCutoffGradientConst d :=
    quantitativeCubeCutoffGradientConst_nonneg d
  have hKcut_nonneg : 0 ≤ Kcut := by
    dsimp [Kcut]
    have hpow : 0 ≤ (2 : ℝ) ^ d := by positivity
    nlinarith
  have hW1_nonneg : 0 ≤ cubeBesovScaleWeight 1 Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  have hD_le :
      cubeScaleFactor Q * section53CutoffDerivativeBound Q ≤
        (64 * quantitativeCubeCutoffHessianConst d * (2 : ℝ) ^ d) *
          cubeBesovScaleWeight 1 Q := by
    have hEq := cubeScaleFactor_mul_section53CutoffDerivativeBound_eq Q
    have hB := section53CutoffBound_le_two_pow_card Q
    have hcoef : 0 ≤ 64 * quantitativeCubeCutoffHessianConst d := by
      nlinarith
    calc
      cubeScaleFactor Q * section53CutoffDerivativeBound Q =
          (64 * quantitativeCubeCutoffHessianConst d * section53CutoffBound Q) *
            cubeBesovScaleWeight 1 Q := hEq
      _ ≤
          (64 * quantitativeCubeCutoffHessianConst d * (2 : ℝ) ^ d) *
            cubeBesovScaleWeight 1 Q := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hB hcoef) hW1_nonneg
  have hGrad_le :
      cubeLpNorm Q ∞ (scalarCutoffGradientField (section53NormalizedCutoff Q)) ≤
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          cubeBesovScaleWeight 1 Q := by
    have hbase := cubeLpNorm_section53NormalizedCutoff_gradient_le Q
    have hB := section53CutoffBound_le_two_pow_card Q
    have hcoef : 0 ≤ 8 * quantitativeCubeCutoffGradientConst d := by
      nlinarith
    calc
      cubeLpNorm Q ∞ (scalarCutoffGradientField (section53NormalizedCutoff Q))
          ≤
        (8 * quantitativeCubeCutoffGradientConst d * section53CutoffBound Q) *
          cubeBesovScaleWeight 1 Q := hbase
      _ ≤
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          cubeBesovScaleWeight 1 Q := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB hcoef) hW1_nonneg
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (cubeScaleFactor_nonneg Q))
        (section53CutoffDerivativeBound_nonneg Q))
      (mul_nonneg (by norm_num) (cubeLpNorm_nonneg Q ∞ _))
  have hA_le :
      A ≤ Kcut * cubeBesovScaleWeight 1 Q := by
    dsimp [A, Kcut]
    nlinarith [hD_le, hGrad_le]
  have hWprod :
      cubeBesovScaleWeight 1 Q * cubeBesovScaleWeight (-(1 - s - t)) Q =
        cubeBesovScaleWeight (s + t) Q := by
    rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
    ring_nf
  have hWst_le : cubeBesovScaleWeight (s + t) Q ≤ 1 := by
    simpa [Q] using
      cubeBesovScaleWeight_originCube_nat_le_one (d := d) m hst_nonneg
  have hWneg_nonneg : 0 ≤ cubeBesovScaleWeight (-(1 - s - t)) Q :=
    cubeBesovScaleWeight_nonneg (-(1 - s - t)) Q
  have hA_weight_le :
      A * cubeBesovScaleWeight (-(1 - s - t)) Q ≤ Kcut := by
    calc
      _ ≤ (Kcut * cubeBesovScaleWeight 1 Q) *
          cubeBesovScaleWeight (-(1 - s - t)) Q :=
        mul_le_mul_of_nonneg_right hA_le hWneg_nonneg
      _ = Kcut * cubeBesovScaleWeight (s + t) Q := by rw [mul_assoc, hWprod]
      _ ≤ Kcut := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hWst_le hKcut_nonneg
  have hpow_flux :
      (3 : ℝ) ^ ((d : ℝ) + (1 - s)) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
    linarith
  have hpow_flux_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + (1 - s)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hpow_upper_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hPoinc_nonneg : 0 ≤ Poinc := by
    dsimp [Poinc]
    exact mul_nonneg
      (mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg Q) hpow_upper_nonneg)
      (Nat.cast_nonneg _)
  have hFlux_nonneg : 0 ≤ Flux := by
    dsimp [Flux]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hpow_flux_nonneg hWneg_nonneg)
  have hcore :
      A * Poinc * Flux ≤
        Kcut * Poinc *
          ((Fintype.card (Fin d) : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    have hbound := scalar_product_le_of_weighted_bound
      (A := A) (K := Kcut) (v := cubeBesovScaleWeight (-(1 - s - t)) Q)
      (w := 1) (z := 1) (by simpa only [mul_one] using hA_weight_le)
      hpow_flux hpow_flux_nonneg hKcut_nonneg hPoinc_nonneg
      (Nat.cast_nonneg (Fintype.card (Fin d)))
    simpa only [Flux, mul_one] using hbound
  have hdim :
      Kcut * Poinc *
          ((Fintype.card (Fin d) : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1)) =
        (((128 * quantitativeCubeCutoffHessianConst d +
                24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d) *
          (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1))) := by
    simp [Kcut, Poinc, Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant]
  have hW_s_nonneg : 0 ≤ cubeBesovScaleWeight (-s) Q :=
    cubeBesovScaleWeight_nonneg (-s) Q
  have hW_t_nonneg : 0 ≤ cubeBesovScaleWeight (-t) Q :=
    cubeBesovScaleWeight_nonneg (-t) Q
  have hweights_cancel :
      cubeBesovScaleWeight 1 Q *
          cubeBesovScaleWeight (-(1 - s - t)) Q *
          cubeBesovScaleWeight (-s) Q *
          cubeBesovScaleWeight (-t) Q = 1 := by
    rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add,
      cubeBesovScaleWeight_mul_eq_scaleWeight_add,
      cubeBesovScaleWeight_mul_eq_scaleWeight_add]
    rw [show (1 : ℝ) + -(1 - s - t) + -s + -t = 0 by ring]
    simp [cubeBesovScaleWeight]
  have hcore_scaled :
      A * Poinc * Flux *
          cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q ≤
        Kcut * Poinc *
          ((Fintype.card (Fin d) : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    have hweight_nonneg :
        0 ≤ cubeBesovScaleWeight (-(1 - s - t)) Q *
          cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q :=
      mul_nonneg (mul_nonneg hWneg_nonneg hW_s_nonneg) hW_t_nonneg
    have hweighted :
        A * (cubeBesovScaleWeight (-(1 - s - t)) Q *
          cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q) ≤ Kcut := by
      calc
        _ ≤ (Kcut * cubeBesovScaleWeight 1 Q) *
            (cubeBesovScaleWeight (-(1 - s - t)) Q *
              cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q) :=
          mul_le_mul_of_nonneg_right hA_le hweight_nonneg
        _ = Kcut * (cubeBesovScaleWeight 1 Q *
            cubeBesovScaleWeight (-(1 - s - t)) Q *
            cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q) := by ring
        _ = Kcut := by rw [hweights_cancel, mul_one]
    simpa only [Flux] using
      scalar_product_le_of_weighted_bound hweighted hpow_flux hpow_flux_nonneg
        hKcut_nonneg hPoinc_nonneg (Nat.cast_nonneg (Fintype.card (Fin d)))
  have hinside :
      cutoffProductScaledWeakNormCoeff Q s t (section53CutoffDerivativeBound Q)
          (scalarCutoffGradientField (section53NormalizedCutoff Q)) *
          cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q ≤
        (((128 * quantitativeCubeCutoffHessianConst d +
                24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d) *
          (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1))) := by
    calc
      cutoffProductScaledWeakNormCoeff Q s t (section53CutoffDerivativeBound Q)
          (scalarCutoffGradientField (section53NormalizedCutoff Q)) *
          cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q =
        A * Poinc * Flux *
          cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q := by
          simp [cutoffProductScaledWeakNormCoeff, A, Poinc, Flux]
      _ ≤ Kcut * Poinc *
            ((Fintype.card (Fin d) : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1)) := hcore_scaled
      _ =
        (((128 * quantitativeCubeCutoffHessianConst d +
                24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d) *
          (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1))) := hdim
  have hRhs_nonneg :
      0 ≤
        (((128 * quantitativeCubeCutoffHessianConst d +
                24 * quantitativeCubeCutoffGradientConst d) * (2 : ℝ) ^ d) *
          (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1))) := by
    rw [← hdim]
    exact mul_nonneg (mul_nonneg hKcut_nonneg hPoinc_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) hpow_upper_nonneg)
  exact max_le hinside hRhs_nonneg

/-- The first Section 5.3 expectation assembly after selecting the concrete
normalized quantitative cutoff.  The remaining hypotheses are law-facing
integrability/moment facts for the Ch4 observables. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_normalizedCutoff
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (hs_lt_one : s < 1) (ht : 0 < t)
    (hst : s + t ≤ 1)
    (p q p0 q0 : Vec d)
    (hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P) :
    let Q : TriadicCube d := originCube d m
    let j : ℕ := Int.toNat (m - k)
    Ch04.expectedResponseJCubeSet P Q p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        (1 + section53CutoffBound Q)
        (section53CutoffOscillationConstant Q)
        (section53CutoffScaleSep Q j)
        (section53CutoffDualBound Q s)
        (section53CutoffDualBound Q t)
        (section53CutoffProductCoeff Q s t)
        p q p0 q0 := by
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - k)
  let : IsProbabilityMeasure P := hP.isProbability
  have hbasic := normalized_quantitativeCubeCutoff_canonicalFun_basic_controls Q
  rcases hbasic with ⟨hMean, hφ_meas, hφ_bound, hφ_smooth, hφ_compact, hφ_sub⟩
  have hosc :=
    normalized_quantitativeCubeCutoff_canonicalFun_descendant_average_oscillation_controls Q j
  rcases hosc with ⟨hCutRaw, hOscRaw⟩
  have hgradControls := normalized_quantitativeCubeCutoff_canonicalFun_gradient_controls Q
  rcases hgradControls with ⟨hcutoffGradient, hcutoffSmooth, hcutoffDerivRaw⟩
  have hC : 0 ≤ 1 + section53CutoffBound Q := by
    linarith [section53CutoffBound_nonneg Q]
  have hCut :
      ∀ R ∈ descendantsAtDepth Q j,
        |1 - cubeAverage R (section53NormalizedCutoff Q)| ≤
          1 + section53CutoffBound Q := by
    intro R hR
    simpa [section53NormalizedCutoff, section53CutoffBound] using hCutRaw R hR
  have hMean' : cubeAverage Q (section53NormalizedCutoff Q) = 1 := by
    simpa [section53NormalizedCutoff] using hMean
  have hφ_meas' :
      AEStronglyMeasurable (section53NormalizedCutoff Q) (volumeMeasureOn (cubeSet Q)) := by
    simpa [section53NormalizedCutoff] using hφ_meas
  have hφ_bound' :
      ∀ᵐ x ∂ volumeMeasureOn (cubeSet Q),
        ‖section53NormalizedCutoff Q x‖ ≤ section53CutoffBound Q := by
    simpa [section53NormalizedCutoff, section53CutoffBound] using hφ_bound
  have hOscPoint :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ x ∂ volumeMeasureOn (cubeSet R),
          |cubeAverage R (section53NormalizedCutoff Q) - section53NormalizedCutoff Q x| ≤
            section53CutoffOscillationConstant Q * section53CutoffScaleSep Q j := by
    intro R hR
    exact (hOscRaw R hR).mono fun x hx => by
      calc
        |cubeAverage R (section53NormalizedCutoff Q) - section53NormalizedCutoff Q x|
            ≤ cubeScaleFactor R * section53CutoffOscillationConstant Q := by
              simpa [section53NormalizedCutoff, section53CutoffBound,
                section53CutoffOscillationConstant] using hx
        _ = section53CutoffOscillationConstant Q * section53CutoffScaleSep Q j := by
              rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
              simp [section53CutoffScaleSep]
              ring
  have hφ_smooth' : ContDiff ℝ (⊤ : ℕ∞) (section53NormalizedCutoff Q) := by
    simpa [section53NormalizedCutoff] using hφ_smooth
  have hφ_compact' : HasCompactSupport (section53NormalizedCutoff Q) := by
    simpa [section53NormalizedCutoff] using hφ_compact
  have hφ_sub' : tsupport (section53NormalizedCutoff Q) ⊆ openCubeSet Q := by
    simpa [section53NormalizedCutoff] using hφ_sub
  have ht_le_one : t ≤ 1 := by
    linarith
  have hφDualS :
      ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (section53NormalizedCutoff Q) ≤
          section53CutoffDualBound Q s := by
    intro N
    simpa [section53NormalizedCutoff, section53CutoffBound,
      section53CutoffOscillationConstant, section53CutoffDualBound] using
      cubeBesovDualTestNorm_normalized_quantitativeCubeCutoff_canonicalFun_le
        Q (le_of_lt hs_lt_one) N
  have hφDualT :
      ∀ N : ℕ,
        cubeBesovDualTestNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (section53NormalizedCutoff Q) ≤
          section53CutoffDualBound Q t := by
    intro N
    simpa [section53NormalizedCutoff, section53CutoffBound,
      section53CutoffOscillationConstant, section53CutoffDualBound] using
      cubeBesovDualTestNorm_normalized_quantitativeCubeCutoff_canonicalFun_le
        Q ht_le_one N
  have hφMem :
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (section53NormalizedCutoff Q) := by
    simpa [section53NormalizedCutoff] using
      cubeBesovDualLocalMemLpGlobal_normalized_quantitativeCubeCutoff_canonicalFun Q
  have hcutoffGradient' :
      MemLp (scalarCutoffGradientField (section53NormalizedCutoff Q)) ∞
        (normalizedCubeMeasure Q) := by
    simpa [section53NormalizedCutoff] using hcutoffGradient
  have hcutoffSmooth' :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField (section53NormalizedCutoff Q) x i) := by
    intro i
    simpa [section53NormalizedCutoff] using hcutoffSmooth i
  have hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => scalarCutoffGradientField (section53NormalizedCutoff Q) x i) z‖ ≤
          section53CutoffDerivativeBound Q := by
    intro i z hz
    simpa [section53NormalizedCutoff, section53CutoffBound,
      section53CutoffDerivativeBound] using hcutoffDerivRaw i z hz
  have hProductCoeff :
      cutoffProductScaledWeakNormCoeff Q s t (section53CutoffDerivativeBound Q)
          (scalarCutoffGradientField (section53NormalizedCutoff Q)) *
          cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight (-t) Q ≤
        section53CutoffProductCoeff Q s t := by
    exact le_max_left _ _
  have hCprod : 0 ≤ section53CutoffProductCoeff Q s t := by
    exact section53CutoffProductCoeff_nonneg Q s t
  have hOneSq : Integrable (fun _ : RegCoeffField d => (1 : ℝ) ^ 2) P := by
    simp
  have hGradWeak :
      Integrable
        (fun a : RegCoeffField d =>
          Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun) P := by
    have hprod :=
      integrable_mul_of_integrable_sq_of_ae_nonneg
        (μ := P)
        (X := fun a : RegCoeffField d =>
          Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun)
        (Y := fun _ : RegCoeffField d => (1 : ℝ))
        (by simpa [Q] using hGradSq) hOneSq
        (canonicalScalarResponseGradientWeakNormCubeSet_nonneg_ae hP Q hs p q p0)
        (by filter_upwards with a; norm_num)
    simpa using hprod
  have hFluxWeak :
      Integrable
        (fun a : RegCoeffField d =>
          Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun) P := by
    have hprod :=
      integrable_mul_of_integrable_sq_of_ae_nonneg
        (μ := P)
        (X := fun a : RegCoeffField d =>
          Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun)
        (Y := fun _ : RegCoeffField d => (1 : ℝ))
        (by simpa [Q] using hFluxSq) hOneSq
        (canonicalScalarResponseFluxWeakNormCubeSet_nonneg_ae hP Q ht p q q0)
        (by filter_upwards with a; norm_num)
    simpa using hprod
  change
    Ch04.expectedResponseJCubeSet P Q p q - (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        (1 + section53CutoffBound Q) (section53CutoffOscillationConstant Q)
        (section53CutoffScaleSep Q j) (section53CutoffDualBound Q s)
        (section53CutoffDualBound Q t) (section53CutoffProductCoeff Q s t)
        p q p0 q0
  exact
    expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_cutoffControls
      hP hstat hk_nonneg hkm hs hs_lt_one ht hst
      (section53NormalizedCutoff Q)
      (1 + section53CutoffBound Q) (section53CutoffBound Q)
      (section53CutoffOscillationConstant Q) (section53CutoffScaleSep Q j)
      (section53CutoffDualBound Q s) (section53CutoffDualBound Q t)
      (section53CutoffDerivativeBound Q) (section53CutoffProductCoeff Q s t)
      p q p0 q0 hC hCprod hCut hMean' hφ_meas' hφ_bound' hOscPoint
      hφ_smooth' hφ_compact' hφ_sub' (section53CutoffDerivativeBound_nonneg Q)
      (section53CutoffDualBound_nonneg Q s) (section53CutoffDualBound_nonneg Q t)
      hφDualS hφDualT hφMem hcutoffGradient' hcutoffSmooth' hcutoffDeriv hProductCoeff
      hParent hJ hGradWeak hFluxWeak hGradSq hFluxSq

/-- Normalized-cutoff assembly with the response integrability facts supplied
from the Section 5.2 `(P4)` integrability theorem and Ch4 stationarity.  The
remaining inputs are exactly the two square-integrability facts for the scalar
maximizer weak norms. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_normalizedCutoff_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (hs_lt_one : s < 1) (ht : 0 < t)
    (hst : s + t ≤ 1)
    (p q p0 q0 : Vec d)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P) :
    let Q : TriadicCube d := originCube d m
    let j : ℕ := Int.toNat (m - k)
    Ch04.expectedResponseJCubeSet P Q p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        (1 + section53CutoffBound Q)
        (section53CutoffOscillationConstant Q)
        (section53CutoffScaleSep Q j)
        (section53CutoffDualBound Q s)
        (section53CutoffDualBound Q t)
        (section53CutoffProductCoeff Q s t)
        p q p0 q0 := by
  let Q : TriadicCube d := originCube d m
  have hm_nonneg : 0 ≤ m := le_trans hk_nonneg hkm
  have hBlockM_nat :
      Integrable
        (Ch04.coarseFullBlockMatrixAtCube
          (originCube d ((Int.toNat m : ℕ) : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 (Int.toNat m)
  have hBlockM :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d m)) P := by
    simpa [Int.toNat_of_nonneg hm_nonneg] using hBlockM_nat
  have hParent :
      Integrable (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d m) p q hBlockM
  have hBlockK_nat :
      Integrable
        (Ch04.coarseFullBlockMatrixAtCube
          (originCube d ((Int.toNat k : ℕ) : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 (Int.toNat k)
  have hBlockK :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d k)) P := by
    simpa [Int.toNat_of_nonneg hk_nonneg] using hBlockK_nat
  have hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) k →
      Integrable (Ch04.restrictionResponseJObservableCubeSet R p q) P := by
    intro R hR
    have hBlockR :
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P :=
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hk_nonneg hkm hR hBlockK
    exact
      hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p q hBlockR
  exact
    expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_normalizedCutoff
      hP hstat hk_nonneg hkm hs hs_lt_one ht hst p q p0 q0
      hParent hJ hGradSq hFluxSq

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
