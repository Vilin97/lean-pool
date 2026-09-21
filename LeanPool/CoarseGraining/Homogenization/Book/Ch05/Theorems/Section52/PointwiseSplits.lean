/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.Weights

/-! # Pointwise Splits -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: PointwiseSplits

Pointwise upper and lower finite-one decompositions.
-/

theorem sq_add_le_weighted_sum_add_tail_sq_div
    {L T A W V : ℝ}
    (hV : 0 < V) (hA : 0 ≤ A)
    (hW : 0 ≤ W) (hWV : W + V ≤ 1)
    (hLsq : L ^ 2 ≤ W * A) :
    (L + T) ^ 2 ≤ A + T ^ 2 / V := by
  by_cases hWpos : 0 < W
  · have hV_nonneg : 0 ≤ V := hV.le
    have hWinv_nonneg : 0 ≤ W⁻¹ := inv_nonneg.mpr hWpos.le
    have hVinv_nonneg : 0 ≤ V⁻¹ := inv_nonneg.mpr hV.le
    have hLsq_div : L ^ 2 / W ≤ A := by
      rw [div_le_iff₀ hWpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hLsq
    have hcross :
        2 * L * T ≤ V / W * L ^ 2 + W / V * T ^ 2 := by
      have hsq : 0 ≤
          (Real.sqrt (V / W) * L - Real.sqrt (W / V) * T) ^ 2 :=
        sq_nonneg _
      have hVW_nonneg : 0 ≤ V / W := div_nonneg hV.le hWpos.le
      have hWV_nonneg : 0 ≤ W / V := div_nonneg hW hV.le
      have hprod :
          Real.sqrt (V / W) * Real.sqrt (W / V) = 1 := by
        have hmul : (V / W) * (W / V) = 1 := by
          field_simp [hV.ne', hWpos.ne']
        rw [← Real.sqrt_mul hVW_nonneg, hmul, Real.sqrt_one]
      have hsq_expanded :
          0 ≤ V / W * L ^ 2 - 2 * L * T + W / V * T ^ 2 := by
        have hsq_eq :
            (Real.sqrt (V / W) * L - Real.sqrt (W / V) * T) ^ 2 =
              V / W * L ^ 2 - 2 * L * T + W / V * T ^ 2 := by
          rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt hVW_nonneg,
            Real.sq_sqrt hWV_nonneg]
          calc
            V / W * L ^ 2 - 2 * (Real.sqrt (V / W) * L) *
                (Real.sqrt (W / V) * T) + W / V * T ^ 2 =
              V / W * L ^ 2 -
                  2 * (Real.sqrt (V / W) * Real.sqrt (W / V)) * (L * T) +
                W / V * T ^ 2 := by ring
            _ = V / W * L ^ 2 - 2 * L * T + W / V * T ^ 2 := by
              rw [hprod]
              ring
        simpa [hsq_eq] using hsq
      nlinarith
    have hcoeffL :
        1 + V / W ≤ W⁻¹ := by
      rw [div_eq_mul_inv]
      have hmul := mul_le_mul_of_nonneg_right hWV hWinv_nonneg
      have hW_mul_inv : W * W⁻¹ = 1 := by field_simp [hWpos.ne']
      have hV_mul_inv : V * W⁻¹ = V / W := by rw [div_eq_mul_inv]
      linarith
    have hcoeffT :
        1 + W / V ≤ V⁻¹ := by
      rw [div_eq_mul_inv]
      have hmul := mul_le_mul_of_nonneg_right hWV hVinv_nonneg
      have hV_mul_inv : V * V⁻¹ = 1 := by field_simp [hV.ne']
      have hW_mul_inv : W * V⁻¹ = W / V := by rw [div_eq_mul_inv]
      linarith
    calc
      (L + T) ^ 2 = L ^ 2 + 2 * L * T + T ^ 2 := by ring
      _ ≤ L ^ 2 + (V / W * L ^ 2 + W / V * T ^ 2) + T ^ 2 := by
          linarith
      _ = (1 + V / W) * L ^ 2 + (1 + W / V) * T ^ 2 := by ring
      _ ≤ W⁻¹ * L ^ 2 + V⁻¹ * T ^ 2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcoeffL (sq_nonneg L))
            (mul_le_mul_of_nonneg_right hcoeffT (sq_nonneg T))
      _ = L ^ 2 / W + T ^ 2 / V := by ring
      _ ≤ A + T ^ 2 / V := by
          linarith
  · have hW_zero : W = 0 := le_antisymm (le_of_not_gt hWpos) hW
    have hLsq_zero : L ^ 2 = 0 := by
      have hnonneg : 0 ≤ L ^ 2 := sq_nonneg L
      have hle : L ^ 2 ≤ 0 := by simpa [hW_zero] using hLsq
      exact le_antisymm hle hnonneg
    have hL_zero : L = 0 := sq_eq_zero_iff.mp hLsq_zero
    have hV_le_one : V ≤ 1 := by linarith
    have hT_sq_nonneg : 0 ≤ T ^ 2 := sq_nonneg T
    have hT_sq_le_div : T ^ 2 ≤ T ^ 2 / V := by
      rw [le_div_iff₀ hV]
      nlinarith
    calc
      (L + T) ^ 2 = T ^ 2 := by simp [hL_zero]
      _ ≤ T ^ 2 / V := hT_sq_le_div
      _ ≤ A + T ^ 2 / V := by exact le_add_of_nonneg_left hA

noncomputable def upperSmallSqrtTailCoeffField {d : ℕ} [NeZero d]
    (m : ℕ) (s : ℝ) (a : RegCoeffField d) : ℝ :=
  ∑' j : ℕ,
    geometricWeight s 1 (j + m) *
      Real.rpow
        (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ)

theorem maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {k : ℤ} (hk : k ≤ Q.scale) :
    0 ≤ Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q k a := by
  classical
  by_cases ha : Ch04.AELocallyUniformlyEllipticField a
  · simpa [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha] using
      Ch02.maxDescendantBMatrixNormAtScale_nonneg Q hk
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
  · simp [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha]

theorem upperSmallSqrtTailCoeffField_nonneg
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (a : RegCoeffField d) :
    0 ≤ upperSmallSqrtTailCoeffField (d := d) m s a := by
  unfold upperSmallSqrtTailCoeffField
  refine tsum_nonneg fun j => ?_
  exact mul_nonneg (geometricWeight_nonneg (j + m) (by simpa using hs))
    (Real.rpow_nonneg
      (maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le
        (originCube d (m : ℤ)) a (by simp [originCube])) _)

theorem LambdaSqCoeffField_originCube_finite_one_le_two_upperSmallSqrtTail_sq_add_two_largeScale_sum
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : RegCoeffField d) :
    Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a ≤
      2 * upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 +
        2 *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                (originCube d (m : ℤ)) n a) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let F : ℤ → ℝ := fun n =>
    Real.rpow (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a) (1 / 2 : ℝ)
  let S : ℝ := ∑' l : ℕ, geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))
  let L : ℝ :=
    ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * F n
  let T : ℝ :=
    ∑' l : ℕ,
      geometricWeight s 1 (l + m) * F ((m : ℤ) - ((l + m : ℕ) : ℤ))
  have hsumF :
      Summable (fun l : ℕ =>
        geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) := by
    simpa [F, Q, originCube, Ch02.geometricWeight_eq_old] using
      Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale
        (Q := Q) a hs
  have hsplit : S = L + T := by
    simpa [S, L, T] using
      section52_tsum_weighted_scale_function_eq_largeScaleSet_sum_add_tail
        s m F hsumF
  have hLambda_eq :
      Ch04.LambdaSqCoeffField Q s (.finite 1) a = S ^ 2 := by
    simpa [S, F, Q, originCube, Ch02.geometricWeight_eq_old] using
      Ch04.RestrictionLawCarrier.LambdaSqCoeffField_finite_one_eq_tsum_sq Q a s
  have hLsq :
      L ^ 2 ≤
        ∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a := by
    let H : ℤ → ℝ := fun n =>
      if n ≤ (m : ℤ) then
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a
      else
        0
    have hfinite :=
      section52_sq_finset_sum_weighted_rpow_half_le_finset_sum_weighted
        (s := section52LargeScaleSet m)
        (w := section52LargeScaleWeight s m)
        (H := H)
        (fun n => section52LargeScaleWeight_nonneg m hs.le n)
        (fun n => by
          by_cases hn : n ≤ (m : ℤ)
          · simp [H, hn]
            exact maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le Q a hn
          · simp [H, hn])
        (section52LargeScaleWeight_sum_le_one hs m)
    have hleft :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * Real.rpow (H n) (1 / 2 : ℝ)) = L := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle, F]
    have hright :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * H n) =
          ∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle]
    rw [hleft, hright] at hfinite
    exact hfinite
  have htail_eq : T = upperSmallSqrtTailCoeffField (d := d) m s a := by
    unfold T upperSmallSqrtTailCoeffField
    congr with j
    have hscale : (m : ℤ) - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
      omega
    rw [hscale]
  have hsq_add : (L + T) ^ 2 ≤ 2 * T ^ 2 + 2 * L ^ 2 := by
    nlinarith [sq_nonneg (L - T)]
  calc
    Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a =
        S ^ 2 := by
          simpa [Q] using hLambda_eq
    _ = (L + T) ^ 2 := by rw [hsplit]
    _ ≤ 2 * T ^ 2 +
        2 *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a) := by
          nlinarith
    _ =
      2 * upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 +
        2 *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                (originCube d (m : ℤ)) n a) := by
          simp [Q, htail_eq]

theorem LambdaSqCoeffField_originCube_finite_one_le_upperSmallSqrtTail_sq_div_add_largeScale_sum
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : RegCoeffField d) :
    Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a ≤
      upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m +
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
              (originCube d (m : ℤ)) n a) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let F : ℤ → ℝ := fun n =>
    Real.rpow (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a) (1 / 2 : ℝ)
  let S : ℝ := ∑' l : ℕ, geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))
  let L : ℝ :=
    ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * F n
  let T : ℝ :=
    ∑' l : ℕ,
      geometricWeight s 1 (l + m) * F ((m : ℤ) - ((l + m : ℕ) : ℤ))
  let W : ℝ := ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n
  let A : ℝ :=
    ∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a
  let V : ℝ := section52SmallTailWeight s m
  have hsumF :
      Summable (fun l : ℕ =>
        geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) := by
    simpa [F, Q, originCube, Ch02.geometricWeight_eq_old] using
      Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale
        (Q := Q) a hs
  have hsplit : S = L + T := by
    simpa [S, L, T] using
      section52_tsum_weighted_scale_function_eq_largeScaleSet_sum_add_tail
        s m F hsumF
  have hLambda_eq :
      Ch04.LambdaSqCoeffField Q s (.finite 1) a = S ^ 2 := by
    simpa [S, F, Q, originCube, Ch02.geometricWeight_eq_old] using
      Ch04.RestrictionLawCarrier.LambdaSqCoeffField_finite_one_eq_tsum_sq Q a s
  have hLsq :
      L ^ 2 ≤ W * A := by
    let H : ℤ → ℝ := fun n =>
      if n ≤ (m : ℤ) then
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q n a
      else
        0
    have hfinite :=
      section52_sq_finset_sum_weighted_rpow_half_le_weight_sum_mul_finset_sum_weighted
        (s := section52LargeScaleSet m)
        (w := section52LargeScaleWeight s m)
        (H := H)
        (fun n => section52LargeScaleWeight_nonneg m hs.le n)
        (fun n => by
          by_cases hn : n ≤ (m : ℤ)
          · simp [H, hn]
            exact maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le Q a hn
          · simp [H, hn])
    have hleft :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * Real.rpow (H n) (1 / 2 : ℝ)) = L := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle, F]
    have hright :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * H n) = A := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle]
    rw [hleft, hright] at hfinite
    simpa [W, A] using hfinite
  have htail_eq : T = upperSmallSqrtTailCoeffField (d := d) m s a := by
    unfold T upperSmallSqrtTailCoeffField
    congr with j
    have hscale : (m : ℤ) - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
      omega
    rw [hscale]
  have hV_pos : 0 < V := by
    dsimp [V]
    have hsum_total := section52LargeScaleWeight_sum_add_smallTailWeight_eq_one hs m
    have hprefix_succ_le_one :
        (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) ≤ 1 :=
      calc
        (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) ≤
            ∑' l : ℕ, geometricWeight s 1 l :=
          (summable_geometricWeight_one hs).sum_le_tsum (Finset.range (m + 1))
            (fun l _hl => geometricWeight_nonneg l (by simpa using hs.le))
        _ = 1 := tsum_geometricWeight_one_eq_one hs
    have hlast_pos : 0 < geometricWeight s 1 m :=
      geometricWeight_pos m (by simpa using hs)
    have hprefix_succ_eq :
        (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) =
          (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) +
            geometricWeight s 1 m := by
      rw [Finset.sum_range_succ]
      rw [← section52LargeScaleWeight_sum_eq_prefix_sum]
    have hW_lt_one :
        (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) < 1 := by
      linarith
    linarith
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun n _hn => section52LargeScaleWeight_nonneg m hs.le n
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun n hn =>
      mul_nonneg (section52LargeScaleWeight_nonneg m hs.le n)
        (maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le Q a
          (section52LargeScaleSet_mem_le_m hn))
  have hWV_le : W + V ≤ 1 := by
    have h := section52LargeScaleWeight_sum_add_smallTailWeight_eq_one hs m
    simpa [W, V] using h.le
  have hsq :
      (L + T) ^ 2 ≤ A + T ^ 2 / V :=
    sq_add_le_weighted_sum_add_tail_sq_div hV_pos hA_nonneg hW_nonneg hWV_le hLsq
  calc
    Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a =
        S ^ 2 := by
          simpa [Q] using hLambda_eq
    _ = (L + T) ^ 2 := by rw [hsplit]
    _ ≤ A + T ^ 2 / V := hsq
    _ =
      upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m +
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
              (originCube d (m : ℤ)) n a) := by
        simp [A, V, Q, htail_eq, add_comm]

noncomputable def lowerSmallSqrtTailCoeffField {d : ℕ} [NeZero d]
    (m : ℕ) (s : ℝ) (a : RegCoeffField d) : ℝ :=
  ∑' j : ℕ,
    geometricWeight s 1 (j + m) *
      Real.rpow
        (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ)

theorem maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {k : ℤ} (hk : k ≤ Q.scale) :
    0 ≤ Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q k a := by
  classical
  by_cases ha : Ch04.AELocallyUniformlyEllipticField a
  · simpa [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha] using
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
  · simp [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha]

theorem lowerSmallSqrtTailCoeffField_nonneg
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (a : RegCoeffField d) :
    0 ≤ lowerSmallSqrtTailCoeffField (d := d) m s a := by
  unfold lowerSmallSqrtTailCoeffField
  refine tsum_nonneg fun j => ?_
  exact mul_nonneg (geometricWeight_nonneg (j + m) (by simpa using hs))
    (Real.rpow_nonneg
      (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le
        (originCube d (m : ℤ)) a (by simp [originCube])) _)

theorem lambdaSqCoeffField_originCube_finite_one_inv_le_two_lowerSmallSqrtTail_sq_add_two_largeScale_sum
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : RegCoeffField d) :
    (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹ ≤
      2 * lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 +
        2 *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                (originCube d (m : ℤ)) n a) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let F : ℤ → ℝ := fun n =>
    Real.rpow
      (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a)
      (1 / 2 : ℝ)
  let S : ℝ := ∑' l : ℕ, geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))
  let L : ℝ :=
    ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * F n
  let T : ℝ :=
    ∑' l : ℕ,
      geometricWeight s 1 (l + m) * F ((m : ℤ) - ((l + m : ℕ) : ℤ))
  have hsumF :
      Summable (fun l : ℕ =>
        geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) := by
    simpa [F, Q, originCube, Ch02.geometricWeight_eq_old] using
      Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (Q := Q) a hs
  have hsplit : S = L + T := by
    simpa [S, L, T] using
      section52_tsum_weighted_scale_function_eq_largeScaleSet_sum_add_tail
        s m F hsumF
  have hlambdaInv_eq :
      (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹ = S ^ 2 := by
    have h :=
      Ch04.RestrictionLawCarrier.lambdaSqCoeffField_finite_one_eq_tsum_sq_inv Q a hs
    simpa [S, F, Q, originCube, Ch02.geometricWeight_eq_old] using congrArg Inv.inv h
  have hLsq :
      L ^ 2 ≤
        ∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a := by
    let H : ℤ → ℝ := fun n =>
      if n ≤ (m : ℤ) then
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a
      else
        0
    have hfinite :=
      section52_sq_finset_sum_weighted_rpow_half_le_finset_sum_weighted
        (s := section52LargeScaleSet m)
        (w := section52LargeScaleWeight s m)
        (H := H)
        (fun n => section52LargeScaleWeight_nonneg m hs.le n)
        (fun n => by
          by_cases hn : n ≤ (m : ℤ)
          · simp [H, hn]
            exact maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le
              Q a hn
          · simp [H, hn])
        (section52LargeScaleWeight_sum_le_one hs m)
    have hleft :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * Real.rpow (H n) (1 / 2 : ℝ)) = L := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle, F]
    have hright :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * H n) =
          ∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle]
    rw [hleft, hright] at hfinite
    exact hfinite
  have htail_eq : T = lowerSmallSqrtTailCoeffField (d := d) m s a := by
    unfold T lowerSmallSqrtTailCoeffField
    congr with j
    have hscale : (m : ℤ) - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
      omega
    rw [hscale]
  have hsq_add : (L + T) ^ 2 ≤ 2 * T ^ 2 + 2 * L ^ 2 := by
    nlinarith [sq_nonneg (L - T)]
  calc
    (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹ =
        S ^ 2 := by
          simpa [Q] using hlambdaInv_eq
    _ = (L + T) ^ 2 := by rw [hsplit]
    _ ≤ 2 * T ^ 2 +
        2 *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a) := by
          nlinarith
    _ =
      2 * lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 +
        2 *
          (∑ n ∈ section52LargeScaleSet m,
            section52LargeScaleWeight s m n *
              Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                (originCube d (m : ℤ)) n a) := by
          simp [Q, htail_eq]

theorem lambdaSqCoeffField_originCube_finite_one_inv_le_lowerSmallSqrtTail_sq_div_add_largeScale_sum
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : RegCoeffField d) :
    (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹ ≤
      lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m +
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d (m : ℤ)) n a) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let F : ℤ → ℝ := fun n =>
    Real.rpow
      (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a)
      (1 / 2 : ℝ)
  let S : ℝ := ∑' l : ℕ, geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))
  let L : ℝ :=
    ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * F n
  let T : ℝ :=
    ∑' l : ℕ,
      geometricWeight s 1 (l + m) * F ((m : ℤ) - ((l + m : ℕ) : ℤ))
  let W : ℝ := ∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n
  let A : ℝ :=
    ∑ n ∈ section52LargeScaleSet m,
      section52LargeScaleWeight s m n *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a
  let V : ℝ := section52SmallTailWeight s m
  have hsumF :
      Summable (fun l : ℕ =>
        geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) := by
    simpa [F, Q, originCube, Ch02.geometricWeight_eq_old] using
      Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (Q := Q) a hs
  have hsplit : S = L + T := by
    simpa [S, L, T] using
      section52_tsum_weighted_scale_function_eq_largeScaleSet_sum_add_tail
        s m F hsumF
  have hlambdaInv_eq :
      (Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹ = S ^ 2 := by
    have h :=
      Ch04.RestrictionLawCarrier.lambdaSqCoeffField_finite_one_eq_tsum_sq_inv Q a hs
    simpa [S, F, Q, originCube, Ch02.geometricWeight_eq_old] using congrArg Inv.inv h
  have hLsq :
      L ^ 2 ≤ W * A := by
    let H : ℤ → ℝ := fun n =>
      if n ≤ (m : ℤ) then
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q n a
      else
        0
    have hfinite :=
      section52_sq_finset_sum_weighted_rpow_half_le_weight_sum_mul_finset_sum_weighted
        (s := section52LargeScaleSet m)
        (w := section52LargeScaleWeight s m)
        (H := H)
        (fun n => section52LargeScaleWeight_nonneg m hs.le n)
        (fun n => by
          by_cases hn : n ≤ (m : ℤ)
          · simp [H, hn]
            exact maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le
              Q a hn
          · simp [H, hn])
    have hleft :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * Real.rpow (H n) (1 / 2 : ℝ)) = L := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle, F]
    have hright :
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n * H n) = A := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hnle : n ≤ (m : ℤ) := section52LargeScaleSet_mem_le_m hn
      simp [H, hnle]
    rw [hleft, hright] at hfinite
    simpa [W, A] using hfinite
  have htail_eq : T = lowerSmallSqrtTailCoeffField (d := d) m s a := by
    unfold T lowerSmallSqrtTailCoeffField
    congr with j
    have hscale : (m : ℤ) - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
      omega
    rw [hscale]
  have hV_pos : 0 < V := by
    dsimp [V]
    have hsum_total := section52LargeScaleWeight_sum_add_smallTailWeight_eq_one hs m
    have hprefix_succ_le_one :
        (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) ≤ 1 :=
      calc
        (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) ≤
            ∑' l : ℕ, geometricWeight s 1 l :=
          (summable_geometricWeight_one hs).sum_le_tsum (Finset.range (m + 1))
            (fun l _hl => geometricWeight_nonneg l (by simpa using hs.le))
        _ = 1 := tsum_geometricWeight_one_eq_one hs
    have hlast_pos : 0 < geometricWeight s 1 m :=
      geometricWeight_pos m (by simpa using hs)
    have hprefix_succ_eq :
        (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) =
          (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) +
            geometricWeight s 1 m := by
      rw [Finset.sum_range_succ]
      rw [← section52LargeScaleWeight_sum_eq_prefix_sum]
    have hW_lt_one :
        (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) < 1 := by
      linarith
    linarith
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun n _hn => section52LargeScaleWeight_nonneg m hs.le n
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun n hn =>
      mul_nonneg (section52LargeScaleWeight_nonneg m hs.le n)
        (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le Q a
          (section52LargeScaleSet_mem_le_m hn))
  have hWV_le : W + V ≤ 1 := by
    have h := section52LargeScaleWeight_sum_add_smallTailWeight_eq_one hs m
    simpa [W, V] using h.le
  have hsq :
      (L + T) ^ 2 ≤ A + T ^ 2 / V :=
    sq_add_le_weighted_sum_add_tail_sq_div hV_pos hA_nonneg hW_nonneg hWV_le hLsq
  calc
    (Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) s (.finite 1) a)⁻¹ =
        S ^ 2 := by
          simpa [Q] using hlambdaInv_eq
    _ = (L + T) ^ 2 := by rw [hsplit]
    _ ≤ A + T ^ 2 / V := hsq
    _ =
      lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 /
          section52SmallTailWeight s m +
        (∑ n ∈ section52LargeScaleSet m,
          section52LargeScaleWeight s m n *
            Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d (m : ℤ)) n a) := by
        simp [A, V, Q, htail_eq, add_comm]

end

end Section52
end Ch05
end Book
end Homogenization
