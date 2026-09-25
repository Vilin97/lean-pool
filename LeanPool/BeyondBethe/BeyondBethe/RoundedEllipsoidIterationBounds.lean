/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RoundedEllipsoidBitBounds
public import Mathlib.Tactic

/-! # Rounded Ellipsoid Iteration Bounds -/

@[expose] public section

namespace BeyondBethe

/-!
# Iterated size bounds

This file turns the one-step determinant and magnitude estimates into a
uniform precision bound for every state in a regular rounded-cut sequence.
The bound is independent of feasibility: it uses only nonsingularity and
nonzero cuts.
-/

def adaptiveRoundedEllipsoidIterate {d : ℕ} :
    RationalEllipsoidState d → List (Fin d → ℚ) → RationalEllipsoidState d
  | E, [] => E
  | E, a :: cuts => adaptiveRoundedEllipsoidIterate
      (adaptiveRoundedEllipsoidCentralUpdate E a) cuts

def AdaptiveCutSequenceRegular {d : ℕ} :
    RationalEllipsoidState d → List (Fin d → ℚ) → Prop
  | _, [] => True
  | E, a :: cuts =>
      rationalPulledBackNormal E a ≠ 0 ∧
        AdaptiveCutSequenceRegular
          (adaptiveRoundedEllipsoidCentralUpdate E a) cuts

theorem adaptiveRoundedEllipsoidIterate_append {d : ℕ}
    (E : RationalEllipsoidState d)
    (xs ys : List (Fin d → ℚ)) :
    adaptiveRoundedEllipsoidIterate E (xs ++ ys) =
      adaptiveRoundedEllipsoidIterate
        (adaptiveRoundedEllipsoidIterate E xs) ys := by
  induction xs generalizing E with
  | nil => simp [adaptiveRoundedEllipsoidIterate]
  | cons a xs ih =>
      simp only [List.cons_append, adaptiveRoundedEllipsoidIterate]
      exact ih _

theorem AdaptiveCutSequenceRegular.append_singleton {d : ℕ}
    (E : RationalEllipsoidState d) (xs : List (Fin d → ℚ))
    (a : Fin d → ℚ)
    (hregular : AdaptiveCutSequenceRegular E xs)
    (ha : rationalPulledBackNormal
      (adaptiveRoundedEllipsoidIterate E xs) a ≠ 0) :
    AdaptiveCutSequenceRegular E (xs ++ [a]) := by
  induction xs generalizing E with
  | nil => exact ⟨ha, by simp [AdaptiveCutSequenceRegular]⟩
  | cons b xs ih =>
      exact ⟨hregular.1, ih _ hregular.2 ha⟩

theorem AdaptiveCutSequenceRegular.prefix_and_next {d : ℕ}
    (E : RationalEllipsoidState d) (pre suffix : List (Fin d → ℚ))
    (a : Fin d → ℚ)
    (hregular : AdaptiveCutSequenceRegular E (pre ++ a :: suffix)) :
    AdaptiveCutSequenceRegular E pre ∧
      rationalPulledBackNormal
        (adaptiveRoundedEllipsoidIterate E pre) a ≠ 0 := by
  induction pre generalizing E with
  | nil =>
      exact ⟨by simp [AdaptiveCutSequenceRegular], hregular.1⟩
  | cons b pre ih =>
      have htail := ih
        (adaptiveRoundedEllipsoidCentralUpdate E b) hregular.2
      exact ⟨⟨hregular.1, htail.1⟩, htail.2⟩

theorem quarter_abs_det_le_adaptiveRoundedCentralUpdate_rat {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    (1 / 4 : ℚ) * abs (Matrix.det E.basis) ≤
      abs (Matrix.det
        (adaptiveRoundedEllipsoidCentralUpdate E a).basis) := by
  have hreal := quarter_abs_det_le_adaptiveRoundedCentralUpdate
    hd E a hdet hb
  have hcast :
      ((((1 / 4 : ℚ) * abs (Matrix.det E.basis) : ℚ) : ℚ) : ℝ) ≤
        ((abs (Matrix.det
          (adaptiveRoundedEllipsoidCentralUpdate E a).basis) : ℚ) : ℝ) := by
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat]
    exact_mod_cast hreal
  exact Rat.cast_le.mp hcast

theorem half_abs_det_le_rationalEllipsoidCentralUpdate {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    (1 / 2 : ℚ) * abs (Matrix.det E.basis) ≤
      abs (Matrix.det (rationalEllipsoidCentralUpdate E a).basis) := by
  let q : ℚ := rationalEllipsoidPerpScale d ^ (d - 1) *
    rationalEllipsoidParallelScale d
  have hq : (1 / 2 : ℚ) ≤ q := by
    have hperp : (1 : ℚ) ≤ rationalEllipsoidPerpScale d := by
      rw [rationalEllipsoidPerpScale]
      norm_num
      positivity
    have hpow : (1 : ℚ) ≤
        rationalEllipsoidPerpScale d ^ (d - 1) := one_le_pow₀ hperp
    have hparallel : (3 / 4 : ℚ) ≤
        rationalEllipsoidParallelScale d :=
      rationalEllipsoidParallelScale_ge_three_quarters hd
    dsimp only [q]
    calc
      (1 / 2 : ℚ) ≤ 1 * (3 / 4 : ℚ) := by norm_num
      _ ≤ rationalEllipsoidPerpScale d ^ (d - 1) *
          rationalEllipsoidParallelScale d :=
        mul_le_mul hpow hparallel (by norm_num) (by positivity)
  have hq0 : 0 ≤ q := hq.trans' (by norm_num)
  rw [det_rationalEllipsoidCentralUpdate hd E a hb, abs_mul,
    abs_of_nonneg hq0]
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hq (abs_nonneg (Matrix.det E.basis)))

theorem dyadicMesh_succ_eq_half_mul (L : ℕ) :
    dyadicMesh (L + 1) = (1 / 2 : ℚ) * dyadicMesh L := by
  unfold dyadicMesh
  rw [pow_add]
  norm_num

theorem rationalEllipsoidCentralUpdate_dyadic_det_lower {d L : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis)) :
    dyadicMesh (L + 1) ≤
      abs (Matrix.det (rationalEllipsoidCentralUpdate E a).basis) := by
  rw [dyadicMesh_succ_eq_half_mul]
  exact (mul_le_mul_of_nonneg_left hdetLower (by norm_num)).trans
    (half_abs_det_le_rationalEllipsoidCentralUpdate hd E a hb)

theorem rationalEllipsoidExactGrowthFactor_le_two_pow (d : ℕ) :
    (6 * d : ℚ) ≤ (2 : ℚ) ^ (3 + d) := by
  have hd := natCast_le_two_pow_self d
  calc
    (6 * d : ℚ) ≤ 8 * (2 : ℚ) ^ d := by nlinarith
    _ = (2 : ℚ) ^ (3 + d) := by
      rw [show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_add]

theorem rationalEllipsoidCentralUpdate_two_pow_state_magnitude_upper
    {d K : ℕ} (hd : 0 < d) (E : RationalEllipsoidState d)
    (a : Fin d → ℚ) (hb : rationalPulledBackNormal E a ≠ 0)
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K) :
    rationalStateAbsBound (rationalEllipsoidCentralUpdate E a) ≤
      (2 : ℚ) ^ (K + 3 + d) := by
  have hstep := rationalStateAbsBound_centralUpdate_le hd E a hb
  have hfactor := rationalEllipsoidExactGrowthFactor_le_two_pow d
  have hstate0 : 0 ≤ rationalStateAbsBound E := by
    linarith [rationalStateAbsBound_two_le E]
  calc
    rationalStateAbsBound (rationalEllipsoidCentralUpdate E a) ≤
        6 * d * rationalStateAbsBound E := hstep
    _ ≤ (2 : ℚ) ^ (3 + d) * (2 : ℚ) ^ K :=
      mul_le_mul hfactor hM hstate0 (by positivity)
    _ = (2 : ℚ) ^ (K + 3 + d) := by
      rw [← pow_add]
      congr 1
      omega

/-- Precision used inside the next rounded update.  This is the missing
intermediate-state estimate: precision is computed after the exact central
cut and before the state is rounded. -/
theorem rationalEllipsoidCentralUpdate_precision_upper
    {d L K : ℕ} (hd : 0 < d) (E : RationalEllipsoidState d)
    (a : Fin d → ℚ) (hb : rationalPulledBackNormal E a ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K) :
    roundedEllipsoidPrecision (rationalEllipsoidCentralUpdate E a) ≤
      (L + 1) + roundedEllipsoidDenominatorExponent d (K + 3 + d) + 2 := by
  apply roundedEllipsoidPrecision_le_of_magnitude_bounds hd
  · exact rationalEllipsoidCentralUpdate_dyadic_det_lower
      hd E a hb hdetLower
  · exact (rationalMatrixAbsBound_le_rationalStateAbsBound
      (rationalEllipsoidCentralUpdate E a)).trans
        (rationalEllipsoidCentralUpdate_two_pow_state_magnitude_upper
          hd E a hb hM)

def roundedEllipsoidNextPrecisionBound (d L K t : ℕ) : ℕ :=
  (L + 2 * t + 1) +
    roundedEllipsoidDenominatorExponent d
      (K + t * (6 + 3 * d) + 3 + d) + 2

theorem adaptiveRoundedEllipsoidIterate_det_lower {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0) (cuts : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E cuts) :
    (1 / 4 : ℚ) ^ cuts.length * abs (Matrix.det E.basis) ≤
      abs (Matrix.det (adaptiveRoundedEllipsoidIterate E cuts).basis) := by
  induction cuts generalizing E with
  | nil => simp [adaptiveRoundedEllipsoidIterate]
  | cons a cuts ih =>
      have hb := hregular.1
      let E' := adaptiveRoundedEllipsoidCentralUpdate E a
      have hdet' : Matrix.det E'.basis ≠ 0 :=
        det_adaptiveRoundedEllipsoidCentralUpdate_ne_zero hd E a hdet hb
      have hstep := quarter_abs_det_le_adaptiveRoundedCentralUpdate_rat
        hd E a hdet hb
      have htail := ih E' hdet' hregular.2
      rw [adaptiveRoundedEllipsoidIterate, List.length_cons, pow_succ]
      calc
        (1 / 4 : ℚ) ^ cuts.length * (1 / 4) *
            abs (Matrix.det E.basis) =
          (1 / 4 : ℚ) ^ cuts.length *
            ((1 / 4) * abs (Matrix.det E.basis)) := by ring
        _ ≤ (1 / 4 : ℚ) ^ cuts.length * abs (Matrix.det E'.basis) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ abs (Matrix.det
            (adaptiveRoundedEllipsoidIterate E' cuts).basis) := htail

theorem adaptiveRoundedEllipsoidIterate_magnitude_upper {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d)
    (cuts : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E cuts) :
    rationalMatrixAbsBound
        (adaptiveRoundedEllipsoidIterate E cuts).basis ≤
      (25 * d ^ 3 : ℚ) ^ cuts.length *
        rationalMatrixAbsBound E.basis := by
  induction cuts generalizing E with
  | nil => simp [adaptiveRoundedEllipsoidIterate]
  | cons a cuts ih =>
      have hb := hregular.1
      let E' := adaptiveRoundedEllipsoidCentralUpdate E a
      have hstep := rationalMatrixAbsBound_adaptiveCentralUpdate_le
        hd E a hb
      have htail := ih E' hregular.2
      rw [adaptiveRoundedEllipsoidIterate, List.length_cons, pow_succ]
      calc
        rationalMatrixAbsBound
            (adaptiveRoundedEllipsoidIterate E' cuts).basis ≤
          (25 * d ^ 3 : ℚ) ^ cuts.length *
            rationalMatrixAbsBound E'.basis := htail
        _ ≤ (25 * d ^ 3 : ℚ) ^ cuts.length *
            (25 * d ^ 3 * rationalMatrixAbsBound E.basis) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (25 * d ^ 3 : ℚ) ^ cuts.length *
            (25 * d ^ 3) * rationalMatrixAbsBound E.basis := by ring

/-- The same iteration estimate for the center and basis together.  This is
the quantity needed to bound the encoding of every stored ellipsoid state. -/
theorem adaptiveRoundedEllipsoidIterate_state_magnitude_upper {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d)
    (cuts : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E cuts) :
    rationalStateAbsBound (adaptiveRoundedEllipsoidIterate E cuts) ≤
      (42 * d ^ 3 : ℚ) ^ cuts.length * rationalStateAbsBound E := by
  induction cuts generalizing E with
  | nil => simp [adaptiveRoundedEllipsoidIterate]
  | cons a cuts ih =>
      have hb := hregular.1
      let E' := adaptiveRoundedEllipsoidCentralUpdate E a
      have hstep := rationalStateAbsBound_adaptiveCentralUpdate_le
        hd E a hb
      have htail := ih E' hregular.2
      rw [adaptiveRoundedEllipsoidIterate, List.length_cons, pow_succ]
      calc
        rationalStateAbsBound (adaptiveRoundedEllipsoidIterate E' cuts) ≤
            (42 * d ^ 3 : ℚ) ^ cuts.length *
              rationalStateAbsBound E' := htail
        _ ≤ (42 * d ^ 3 : ℚ) ^ cuts.length *
              (42 * d ^ 3 * rationalStateAbsBound E) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (42 * d ^ 3 : ℚ) ^ cuts.length *
              (42 * d ^ 3) * rationalStateAbsBound E := by ring

theorem dyadicMesh_add_two_mul (L t : ℕ) :
    dyadicMesh (L + 2 * t) =
      (1 / 4 : ℚ) ^ t * dyadicMesh L := by
  unfold dyadicMesh
  rw [pow_add, pow_mul]
  norm_num only [pow_two]
  rw [show (1 / 4 : ℚ) ^ t = 1 / (4 : ℚ) ^ t by
    simp only [one_div, inv_pow]]
  ring

theorem adaptiveRoundedEllipsoidIterate_dyadic_det_lower {d L : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (cuts : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E cuts) :
    dyadicMesh (L + 2 * cuts.length) ≤
      abs (Matrix.det (adaptiveRoundedEllipsoidIterate E cuts).basis) := by
  rw [dyadicMesh_add_two_mul]
  calc
    (1 / 4 : ℚ) ^ cuts.length * dyadicMesh L ≤
        (1 / 4 : ℚ) ^ cuts.length * abs (Matrix.det E.basis) :=
      mul_le_mul_of_nonneg_left hdetLower (by positivity)
    _ ≤ abs (Matrix.det
        (adaptiveRoundedEllipsoidIterate E cuts).basis) :=
      adaptiveRoundedEllipsoidIterate_det_lower hd E hdet cuts hregular

theorem roundedEllipsoidGrowthFactor_le_two_pow (d : ℕ) :
    (25 * d ^ 3 : ℚ) ≤ (2 : ℚ) ^ (5 + 3 * d) := by
  have hd := natCast_le_two_pow_self d
  have hd3 : (d : ℚ) ^ 3 ≤ ((2 : ℚ) ^ d) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hd 3
  calc
    (25 * d ^ 3 : ℚ) ≤ 32 * ((2 : ℚ) ^ d) ^ 3 := by
      nlinarith [show (0 : ℚ) ≤ (d : ℚ) ^ 3 by positivity]
    _ = (2 : ℚ) ^ (5 + 3 * d) := by
      rw [show (32 : ℚ) = 2 ^ 5 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega

theorem roundedEllipsoidStateGrowthFactor_le_two_pow (d : ℕ) :
    (42 * d ^ 3 : ℚ) ≤ (2 : ℚ) ^ (6 + 3 * d) := by
  have hd := natCast_le_two_pow_self d
  have hd3 : (d : ℚ) ^ 3 ≤ ((2 : ℚ) ^ d) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hd 3
  calc
    (42 * d ^ 3 : ℚ) ≤ 64 * ((2 : ℚ) ^ d) ^ 3 := by
      nlinarith [show (0 : ℚ) ≤ (d : ℚ) ^ 3 by positivity]
    _ = (2 : ℚ) ^ (6 + 3 * d) := by
      rw [show (64 : ℚ) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega

def roundedEllipsoidMagnitudeExponent (d K t : ℕ) : ℕ :=
  K + t * (5 + 3 * d)

def roundedEllipsoidStateMagnitudeExponent (d K t : ℕ) : ℕ :=
  K + t * (6 + 3 * d)

theorem adaptiveRoundedEllipsoidIterate_two_pow_magnitude_upper
    {d K : ℕ} (hd : 0 < d) (E : RationalEllipsoidState d)
    (hM : rationalMatrixAbsBound E.basis ≤ (2 : ℚ) ^ K)
    (cuts : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E cuts) :
    rationalMatrixAbsBound
        (adaptiveRoundedEllipsoidIterate E cuts).basis ≤
      (2 : ℚ) ^ roundedEllipsoidMagnitudeExponent d K cuts.length := by
  have hiter := adaptiveRoundedEllipsoidIterate_magnitude_upper
    hd E cuts hregular
  have hfactor := roundedEllipsoidGrowthFactor_le_two_pow d
  have hpow : (25 * d ^ 3 : ℚ) ^ cuts.length ≤
      ((2 : ℚ) ^ (5 + 3 * d)) ^ cuts.length :=
    pow_le_pow_left₀ (by positivity) hfactor cuts.length
  calc
    rationalMatrixAbsBound
        (adaptiveRoundedEllipsoidIterate E cuts).basis ≤
      (25 * d ^ 3 : ℚ) ^ cuts.length *
        rationalMatrixAbsBound E.basis := hiter
    _ ≤ ((2 : ℚ) ^ (5 + 3 * d)) ^ cuts.length *
        (2 : ℚ) ^ K :=
      mul_le_mul hpow hM (rationalMatrixAbsBound_pos E.basis).le
        (by positivity)
    _ = (2 : ℚ) ^
        roundedEllipsoidMagnitudeExponent d K cuts.length := by
      rw [← pow_mul, ← pow_add]
      rw [roundedEllipsoidMagnitudeExponent]
      congr 1
      ring

theorem adaptiveRoundedEllipsoidIterate_two_pow_state_magnitude_upper
    {d K : ℕ} (hd : 0 < d) (E : RationalEllipsoidState d)
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K)
    (cuts : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E cuts) :
    rationalStateAbsBound (adaptiveRoundedEllipsoidIterate E cuts) ≤
      (2 : ℚ) ^
        roundedEllipsoidStateMagnitudeExponent d K cuts.length := by
  have hiter := adaptiveRoundedEllipsoidIterate_state_magnitude_upper
    hd E cuts hregular
  have hfactor := roundedEllipsoidStateGrowthFactor_le_two_pow d
  have hpow : (42 * d ^ 3 : ℚ) ^ cuts.length ≤
      ((2 : ℚ) ^ (6 + 3 * d)) ^ cuts.length :=
    pow_le_pow_left₀ (by positivity) hfactor cuts.length
  have hstate0 : 0 ≤ rationalStateAbsBound E := by
    linarith [rationalStateAbsBound_two_le E]
  calc
    rationalStateAbsBound (adaptiveRoundedEllipsoidIterate E cuts) ≤
        (42 * d ^ 3 : ℚ) ^ cuts.length *
          rationalStateAbsBound E := hiter
    _ ≤ ((2 : ℚ) ^ (6 + 3 * d)) ^ cuts.length * (2 : ℚ) ^ K :=
      mul_le_mul hpow hM hstate0 (by positivity)
    _ = (2 : ℚ) ^
        roundedEllipsoidStateMagnitudeExponent d K cuts.length := by
      rw [← pow_mul, ← pow_add]
      rw [roundedEllipsoidStateMagnitudeExponent]
      congr 1
      ring

/-- Uniform bound for the proof-specification precision of the next exact
central cut after any regular prefix.  A machine implementation may pass any
a-priori scheduled precision at least this large. -/
theorem adaptiveRoundedEllipsoidIterate_next_precision_upper
    {d L K : ℕ} (hd : 0 < d) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (hM : rationalStateAbsBound E ≤ (2 : ℚ) ^ K)
    (pre : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E pre)
    (a : Fin d → ℚ)
    (ha : rationalPulledBackNormal
      (adaptiveRoundedEllipsoidIterate E pre) a ≠ 0) :
    roundedEllipsoidPrecision
        (rationalEllipsoidCentralUpdate
          (adaptiveRoundedEllipsoidIterate E pre) a) ≤
      roundedEllipsoidNextPrecisionBound d L K pre.length := by
  have hdetPrefix := adaptiveRoundedEllipsoidIterate_dyadic_det_lower
    hd E hdet hdetLower pre hregular
  have hMPrefix :=
    adaptiveRoundedEllipsoidIterate_two_pow_state_magnitude_upper
      hd E hM pre hregular
  have h := rationalEllipsoidCentralUpdate_precision_upper hd
    (adaptiveRoundedEllipsoidIterate E pre) a ha hdetPrefix hMPrefix
  simpa only [roundedEllipsoidNextPrecisionBound,
    roundedEllipsoidStateMagnitudeExponent] using h

/-- Explicit polynomial precision bound at every reachable state. -/
theorem adaptiveRoundedEllipsoidIterate_precision_upper
    {d L K : ℕ} (hd : 0 < d) (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det E.basis))
    (hM : rationalMatrixAbsBound E.basis ≤ (2 : ℚ) ^ K)
    (cuts : List (Fin d → ℚ))
    (hregular : AdaptiveCutSequenceRegular E cuts) :
    roundedEllipsoidPrecision (adaptiveRoundedEllipsoidIterate E cuts) ≤
      (L + 2 * cuts.length) +
        roundedEllipsoidDenominatorExponent d
          (roundedEllipsoidMagnitudeExponent d K cuts.length) + 2 := by
  exact roundedEllipsoidPrecision_le_of_magnitude_bounds hd _
    (adaptiveRoundedEllipsoidIterate_dyadic_det_lower
      hd E hdet hdetLower cuts hregular)
    (adaptiveRoundedEllipsoidIterate_two_pow_magnitude_upper
      hd E hM cuts hregular)

end BeyondBethe
