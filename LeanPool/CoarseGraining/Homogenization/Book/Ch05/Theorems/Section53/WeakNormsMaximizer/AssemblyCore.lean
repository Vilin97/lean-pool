/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.LowScales
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds

/-! # Assembly Core -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace WeakNormsMaximizer

/-!
# Assembly for the weak-norm maximizer lemma

This file assembles the finite-depth deterministic weak-norm bounds from:

* the high/low weak-norm split;
* the high-scale response-defect controls;
* the low-scale parent-response tails.

The finite-depth estimates are kept private for now.  The public manuscript
surface will be added after the scale-indexed RHS conversion and supremum step.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- A harmless dimension constant for the deterministic weak-norm maximizer
bound.  It is deliberately oversized: it absorbs the accepted leading factor
`2`, the high-scale factor `4`, and the geometric-tail constants. -/
def section53WeakNormMaximizerConst (d : ℕ) : ℝ :=
  100 * ((d : ℝ) + 1)

theorem section53WeakNormMaximizerConst_nonneg (d : ℕ) :
    0 ≤ section53WeakNormMaximizerConst d := by
  unfold section53WeakNormMaximizerConst
  have hd : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  nlinarith

theorem ten_le_section53WeakNormMaximizerConst (d : ℕ) :
    10 ≤ section53WeakNormMaximizerConst d := by
  unfold section53WeakNormMaximizerConst
  have hd : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  nlinarith

theorem five_mul_succ_le_section53WeakNormMaximizerConst (d : ℕ) :
    5 * ((d : ℝ) + 1) ≤ section53WeakNormMaximizerConst d := by
  unfold section53WeakNormMaximizerConst
  have hd : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  nlinarith

theorem two_le_section53WeakNormMaximizerConst (d : ℕ) :
    2 ≤ section53WeakNormMaximizerConst d :=
  (by norm_num : (2 : ℝ) ≤ 10).trans (ten_le_section53WeakNormMaximizerConst d)

theorem sqrt_vecNormSq_le_succ_mul_norm {d : ℕ} (v : Vec d) :
    Real.sqrt (vecNormSq v) ≤ ((d : ℝ) + 1) * ‖v‖ := by
  have hsum :
      vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    rw [vecNormSq, vecDot]
    calc
      (∑ i : Fin d, v i * v i) = ∑ i : Fin d, v i ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      _ ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        have hcoord_abs : |v i| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
        have hcoord_sq : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
          nlinarith [abs_nonneg (v i), norm_nonneg v]
        simpa [sq_abs, pow_two] using hcoord_sq
      _ = (Fintype.card (Fin d) : ℝ) * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (d : ℝ) * ‖v‖ ^ 2 := by
        simp
  have hsq :
      vecNormSq v ≤ (((d : ℝ) + 1) * ‖v‖) ^ (2 : ℕ) := by
    have hd : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hnorm_sq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have hd_le : (d : ℝ) ≤ ((d : ℝ) + 1) ^ (2 : ℕ) := by
      nlinarith
    nlinarith
  exact (Real.sqrt_le_iff).2 ⟨mul_nonneg (by positivity) (norm_nonneg v), hsq⟩

private theorem gradientMismatchTermAtScale_nonneg {d : ℕ} [NeZero d]
    (m k : ℤ) (s s' : ℝ) (p q : Vec d) (a : RegCoeffField d) :
    0 ≤ gradientMismatchTermAtScale m k s s' p q a := by
  unfold gradientMismatchTermAtScale
  refine mul_nonneg (Real.sqrt_nonneg _) ?_
  refine Finset.sum_nonneg ?_
  intro n _hn
  exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (Real.sqrt_nonneg _)

theorem fluxMismatchTermAtScale_nonneg {d : ℕ} [NeZero d]
    (m k : ℤ) (t t' : ℝ) (p q : Vec d) (a : RegCoeffField d) :
    0 ≤ fluxMismatchTermAtScale m k t t' p q a := by
  unfold fluxMismatchTermAtScale
  refine mul_nonneg (Real.sqrt_nonneg _) ?_
  refine Finset.sum_nonneg ?_
  intro n _hn
  exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (Real.sqrt_nonneg _)

theorem inv_one_sub_rpow_three_neg_le_five_inv {r : ℝ}
    (hr : 0 < r) (hr_le : r ≤ 1) :
    (1 - Real.rpow (3 : ℝ) (-r))⁻¹ ≤ 5 * r⁻¹ :=
  Ch02.inv_one_sub_rpow_three_neg_le_five_inv hr hr_le

private theorem descendantsAverage_zero_vecNormSq {d : ℕ} (Q : TriadicCube d) (j : ℕ) :
    descendantsAverage Q j (fun _R => vecNormSq (0 : Vec d)) = 0 := by
  rw [descendantsAverage_const_eq]
  simp [vecNormSq, vecDot]

private theorem sum_range_filter_lt_le_range {N L : ℕ} {f : ℕ → ℝ}
    (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L), f j) ≤
      ∑ j ∈ Finset.range L, f j := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    exact Finset.mem_range.mpr ((Finset.mem_filter.mp hj).2)
  · intro j _hj _hnot
    exact hf j

private theorem sum_range_to_Icc_descending {k m : ℤ} (hkm : k ≤ m)
    (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (Int.toNat (m - k)), F j) =
      ∑ n ∈ Finset.Icc (k + 1) m, F (Int.toNat (m - n)) := by
  classical
  refine Finset.sum_bij (fun j _hj => m - (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
    have hj_lt_nat : j < Int.toNat (m - k) := Finset.mem_range.mp hj
    have hj_lt : (j : ℤ) < m - k := by
      have hj_lt' : (j : ℤ) < ((Int.toNat (m - k) : ℕ) : ℤ) := by
        exact_mod_cast hj_lt_nat
      simpa [hL] using hj_lt'
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro j₁ _hj₁ j₂ _hj₂ h
    have h' : m - (j₁ : ℤ) = m - (j₂ : ℤ) := by simpa using h
    have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by omega
    exact_mod_cast hcast
  · intro n hn
    have hn_low : k + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_high : n ≤ m := (Finset.mem_Icc.mp hn).2
    refine ⟨Int.toNat (m - n), ?_, ?_⟩
    · have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
        Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
      have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hmn_lt : m - n < m - k := by omega
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      apply Finset.mem_range.mpr
      have hcast : ((Int.toNat (m - n) : ℕ) : ℤ) <
          ((Int.toNat (m - k) : ℕ) : ℤ) := by
        simpa [hto, hL] using hmn_lt
      exact_mod_cast hcast
    · have hmn_nonneg : 0 ≤ m - n := sub_nonneg.mpr hn_high
      have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg hmn_nonneg
      change m - ((Int.toNat (m - n) : ℕ) : ℤ) = n
      rw [hto]
      omega
  · intro j hj
    have harg : Int.toNat (m - (m - (j : ℤ))) = j := by
      have hsub : m - (m - (j : ℤ)) = (j : ℤ) := by ring
      simp [hsub]
    simp

private theorem canonicalScalarResponseGradientWeakNormCubeSet_le_of_partialBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d)
    (a : RegCoeffField d) {B : ℝ}
    (hB :
      ∀ N : ℕ,
        Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a.toFun ≤ B) :
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun ≤ B := by
  unfold Ch04.canonicalScalarResponseGradientWeakNormCubeSet
  refine csSup_le ?_ ?_
  · exact ⟨Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s 0 p q p0 a.toFun,
      ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

private theorem canonicalScalarResponseFluxWeakNormCubeSet_le_of_partialBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (t : ℝ) (p q q0 : Vec d)
    (a : RegCoeffField d) {B : ℝ}
    (hB :
      ∀ N : ℕ,
        Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0 a.toFun ≤ B) :
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun ≤ B := by
  unfold Ch04.canonicalScalarResponseFluxWeakNormCubeSet
  refine csSup_le ?_ ?_
  · exact ⟨Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q t 0 p q q0 a.toFun,
      ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

private theorem gradientWeakNormPartial_le_depthRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (N L : ℕ) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hgap : 0 < s - s')
    (p q p0 : Vec d) :
    Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a.toFun ≤
      2 *
        ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt
                (descendantsAverage Q j fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))) +
          (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
                Real.sqrt
                  (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                    Q j p q)) +
      2 *
        (((2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
            (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)) +
          (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
            Real.sqrt (vecNormSq (-p0))) := by
  have hsplit :=
    canonicalScalarResponseGradientWeakNormPartialCubeSet_le_highLowSplit
      a ha Q s N L hs p q p0
  let high : ℕ → Prop := fun j => j < L
  let avgTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt
        (descendantsAverage Q j fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))
  let mismatchTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt
        (descendantsAverage Q j fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun))
  let zeroTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d))
  let lowSum : ℝ :=
    ∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
      cubeBesovNegativeVectorDepthSeminorm Q s
        (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q) j
  let constTail : ℝ :=
    (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
      Real.sqrt (vecNormSq (-p0))
  let mismatchRHS : ℝ :=
    (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
      ∑ j ∈ (Finset.range (N + 1)).filter high,
        Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
          Real.sqrt
            (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
              Q j p q)
  let lowRHS : ℝ :=
    (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
      (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)
  have hzero : ∀ j, zeroTerm j = 0 := by
    intro j
    dsimp [zeroTerm]
    rw [descendantsAverage_zero_vecNormSq]
    simp
  have hsplit' :
      Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a.toFun ≤
        (∑ j ∈ (Finset.range (N + 1)).filter high,
            2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j)) +
          2 * (lowSum + constTail) := by
    simpa [high, avgTerm, mismatchTerm, zeroTerm, lowSum, constTail] using hsplit
  have hhigh_rewrite :
      (∑ j ∈ (Finset.range (N + 1)).filter high,
          2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j)) =
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) +
            ∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) := by
    calc
      (∑ j ∈ (Finset.range (N + 1)).filter high,
          2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j))
          =
        ∑ j ∈ (Finset.range (N + 1)).filter high,
          (2 * avgTerm j + 2 * mismatchTerm j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [hzero j]
          ring
      _ =
        (∑ j ∈ (Finset.range (N + 1)).filter high, 2 * avgTerm j) +
          ∑ j ∈ (Finset.range (N + 1)).filter high, 2 * mismatchTerm j := by
          rw [← Finset.sum_add_distrib]
      _ =
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) +
            ∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
  have hmismatch :
      (∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) ≤ mismatchRHS := by
    simpa [high, mismatchTerm, mismatchRHS] using
      gradientHighMismatchSum_le_lambdaSqCoeffField_responseDefectSum
        a ha Q N high hs' p q
  have hlow : lowSum ≤ lowRHS := by
    simpa [high, lowSum, lowRHS] using
      gradientLowScaleDepthSum_le_lambdaSqCoeffField_responseJ
        a ha Q N L hs' hgap p q
  calc
    Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a.toFun
        ≤
          (∑ j ∈ (Finset.range (N + 1)).filter high,
              2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j)) +
            2 * (lowSum + constTail) := hsplit'
    _ =
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) +
            ∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) +
          2 * (lowSum + constTail) := by
          rw [hhigh_rewrite]
    _ ≤
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) + mismatchRHS) +
          2 * (lowRHS + constTail) := by
          nlinarith [hmismatch, hlow]
    _ =
      2 *
        ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt
                (descendantsAverage Q j fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))) +
          (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
                Real.sqrt
                  (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                    Q j p q)) +
      2 *
        (((2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
            (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)) +
          (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
            Real.sqrt (vecNormSq (-p0))) := by
          simp [high, avgTerm, mismatchRHS, lowRHS, constTail]

private theorem fluxWeakNormPartial_le_depthRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (N L : ℕ) {t t' : ℝ}
    (ht : 0 < t) (ht' : 0 < t') (hgap : 0 < t - t')
    (p q q0 : Vec d) :
    Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0 a.toFun ≤
      2 *
        ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
            Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
              Real.sqrt
                (descendantsAverage Q j fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))) +
          (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
                Real.sqrt
                  (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                    Q j p q)) +
      2 *
        (((2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
            (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)) +
          (Real.rpow (3 : ℝ) (-t * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
            Real.sqrt (vecNormSq (-q0))) := by
  have hsplit :=
    canonicalScalarResponseFluxWeakNormPartialCubeSet_le_highLowSplit
      a ha Q t N L ht p q q0
  let high : ℕ → Prop := fun j => j < L
  let avgTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
      Real.sqrt
        (descendantsAverage Q j fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))
  let mismatchTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
      Real.sqrt
        (descendantsAverage Q j fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q a.toFun -
              Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun))
  let zeroTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
      Real.sqrt (descendantsAverage Q j fun _R => vecNormSq (0 : Vec d))
  let lowSum : ℝ :=
    ∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ j < L),
      cubeBesovNegativeVectorDepthSeminorm Q t
        (JUpperBoundWeakNorms.canonicalMaximizerFluxOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q) j
  let constTail : ℝ :=
    (Real.rpow (3 : ℝ) (-t * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
      Real.sqrt (vecNormSq (-q0))
  let mismatchRHS : ℝ :=
    (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
      ∑ j ∈ (Finset.range (N + 1)).filter high,
        Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
          Real.sqrt
            (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
              Q j p q)
  let lowRHS : ℝ :=
    (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
      (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)
  have hzero : ∀ j, zeroTerm j = 0 := by
    intro j
    dsimp [zeroTerm]
    rw [descendantsAverage_zero_vecNormSq]
    simp
  have hsplit' :
      Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0 a.toFun ≤
        (∑ j ∈ (Finset.range (N + 1)).filter high,
            2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j)) +
          2 * (lowSum + constTail) := by
    simpa [high, avgTerm, mismatchTerm, zeroTerm, lowSum, constTail] using hsplit
  have hhigh_rewrite :
      (∑ j ∈ (Finset.range (N + 1)).filter high,
          2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j)) =
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) +
            ∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) := by
    calc
      (∑ j ∈ (Finset.range (N + 1)).filter high,
          2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j))
          =
        ∑ j ∈ (Finset.range (N + 1)).filter high,
          (2 * avgTerm j + 2 * mismatchTerm j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [hzero j]
          ring
      _ =
        (∑ j ∈ (Finset.range (N + 1)).filter high, 2 * avgTerm j) +
          ∑ j ∈ (Finset.range (N + 1)).filter high, 2 * mismatchTerm j := by
          rw [← Finset.sum_add_distrib]
      _ =
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) +
            ∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
  have hmismatch :
      (∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) ≤ mismatchRHS := by
    simpa [high, mismatchTerm, mismatchRHS] using
      fluxHighMismatchSum_le_LambdaSqCoeffField_responseDefectSum
        a ha Q N high ht' p q
  have hlow : lowSum ≤ lowRHS := by
    simpa [high, lowSum, lowRHS] using
      fluxLowScaleDepthSum_le_LambdaSqCoeffField_responseJ
        a ha Q N L ht' hgap p q
  calc
    Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0 a.toFun
        ≤
          (∑ j ∈ (Finset.range (N + 1)).filter high,
              2 * (avgTerm j + mismatchTerm j + zeroTerm j + zeroTerm j)) +
            2 * (lowSum + constTail) := hsplit'
    _ =
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) +
            ∑ j ∈ (Finset.range (N + 1)).filter high, mismatchTerm j) +
          2 * (lowSum + constTail) := by
          rw [hhigh_rewrite]
    _ ≤
        2 *
          ((∑ j ∈ (Finset.range (N + 1)).filter high, avgTerm j) + mismatchRHS) +
          2 * (lowRHS + constTail) := by
          nlinarith [hmismatch, hlow]
    _ =
      2 *
        ((∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
            Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
              Real.sqrt
                (descendantsAverage Q j fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))) +
          (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L),
              Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
                Real.sqrt
                  (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                    Q j p q)) +
      2 *
        (((2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
            (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)) +
          (Real.rpow (3 : ℝ) (-t * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
            Real.sqrt (vecNormSq (-q0))) := by
          simp [high, avgTerm, mismatchRHS, lowRHS, constTail]

private theorem gradientWeakNorm_le_depthRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (L : ℕ) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hgap : 0 < s - s')
    (p q p0 : Vec d) :
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun ≤
      2 *
        ((∑ j ∈ Finset.range L,
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.sqrt
                (descendantsAverage Q j fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))) +
          (2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
            ∑ j ∈ Finset.range L,
              Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
                Real.sqrt
                  (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                    Q j p q)) +
      2 *
        (((2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)) *
            (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)) +
          (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
            Real.sqrt (vecNormSq (-p0))) := by
  let avgTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      Real.sqrt
        (descendantsAverage Q j fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))
  let defectTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
      Real.sqrt
        (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
          Q j p q)
  let coeff : ℝ := 2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)
  let lowTail : ℝ :=
    coeff *
      (Real.rpow (3 : ℝ) (-(s - s') * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)
  let constTail : ℝ :=
    (Real.rpow (3 : ℝ) (-s * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
      Real.sqrt (vecNormSq (-p0))
  refine
    canonicalScalarResponseGradientWeakNormCubeSet_le_of_partialBound
      Q s p q p0 a ?_
  intro N
  have hpartial :=
    gradientWeakNormPartial_le_depthRHS a ha Q N L hs hs' hgap p q p0
  have havg_nonneg : ∀ j, 0 ≤ avgTerm j := by
    intro j
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.sqrt_nonneg _)
  have hdefect_nonneg : ∀ j, 0 ≤ defectTerm j := by
    intro j
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.sqrt_nonneg _)
  have havg :
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L), avgTerm j) ≤
        ∑ j ∈ Finset.range L, avgTerm j :=
    sum_range_filter_lt_le_range (N := N) (L := L) havg_nonneg
  have hdefect :
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L), defectTerm j) ≤
        ∑ j ∈ Finset.range L, defectTerm j :=
    sum_range_filter_lt_le_range (N := N) (L := L) hdefect_nonneg
  have hcoeff_nonneg : 0 ≤ coeff := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hdefect_coeff :
      coeff *
          (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L), defectTerm j) ≤
        coeff * ∑ j ∈ Finset.range L, defectTerm j :=
    mul_le_mul_of_nonneg_left hdefect hcoeff_nonneg
  have hmain :
      Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a.toFun ≤
        2 * ((∑ j ∈ Finset.range L, avgTerm j) +
            coeff * ∑ j ∈ Finset.range L, defectTerm j) +
          2 * (lowTail + constTail) := by
    nlinarith [hpartial, havg, hdefect_coeff]
  simpa [avgTerm, defectTerm, coeff, lowTail, constTail] using hmain

private theorem fluxWeakNorm_le_depthRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (L : ℕ) {t t' : ℝ}
    (ht : 0 < t) (ht' : 0 < t') (hgap : 0 < t - t')
    (p q q0 : Vec d) :
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun ≤
      2 *
        ((∑ j ∈ Finset.range L,
            Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
              Real.sqrt
                (descendantsAverage Q j fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))) +
          (2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
            ∑ j ∈ Finset.range L,
              Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
                Real.sqrt
                  (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                    Q j p q)) +
      2 *
        (((2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)) *
            (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)) +
          (Real.rpow (3 : ℝ) (-t * (L : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
            Real.sqrt (vecNormSq (-q0))) := by
  let avgTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
      Real.sqrt
        (descendantsAverage Q j fun R =>
          vecNormSq
            (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))
  let defectTerm : ℕ → ℝ := fun j =>
    Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
      Real.sqrt
        (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
          Q j p q)
  let coeff : ℝ := 2 * Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)
  let lowTail : ℝ :=
    coeff *
      (Real.rpow (3 : ℝ) (-(t - t') * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
        Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)
  let constTail : ℝ :=
    (Real.rpow (3 : ℝ) (-t * (L : ℝ)) *
        (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
      Real.sqrt (vecNormSq (-q0))
  refine
    canonicalScalarResponseFluxWeakNormCubeSet_le_of_partialBound
      Q t p q q0 a ?_
  intro N
  have hpartial :=
    fluxWeakNormPartial_le_depthRHS a ha Q N L ht ht' hgap p q q0
  have havg_nonneg : ∀ j, 0 ≤ avgTerm j := by
    intro j
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.sqrt_nonneg _)
  have hdefect_nonneg : ∀ j, 0 ≤ defectTerm j := by
    intro j
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.sqrt_nonneg _)
  have havg :
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L), avgTerm j) ≤
        ∑ j ∈ Finset.range L, avgTerm j :=
    sum_range_filter_lt_le_range (N := N) (L := L) havg_nonneg
  have hdefect :
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L), defectTerm j) ≤
        ∑ j ∈ Finset.range L, defectTerm j :=
    sum_range_filter_lt_le_range (N := N) (L := L) hdefect_nonneg
  have hcoeff_nonneg : 0 ≤ coeff := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hdefect_coeff :
      coeff *
          (∑ j ∈ (Finset.range (N + 1)).filter (fun j => j < L), defectTerm j) ≤
        coeff * ∑ j ∈ Finset.range L, defectTerm j :=
    mul_le_mul_of_nonneg_left hdefect hcoeff_nonneg
  have hmain :
      Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0 a.toFun ≤
        2 * ((∑ j ∈ Finset.range L, avgTerm j) +
            coeff * ∑ j ∈ Finset.range L, defectTerm j) +
          2 * (lowTail + constTail) := by
    nlinarith [hpartial, havg, hdefect_coeff]
  simpa [avgTerm, defectTerm, coeff, lowTail, constTail] using hmain

theorem gradientWeakNorm_le_scaleGeometricRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℤ} (hkm : k ≤ m) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hgap : 0 < s - s')
    (p q p0 : Vec d) :
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet
        (originCube d m) s p q p0 a ≤
      2 *
        (gradientAverageTermAtScale m k s p q p0 a +
          2 * gradientMismatchTermAtScale m k s s' p q a) +
      2 *
        (((2 * Real.sqrt
              ((Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹)) *
            (Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a)) +
          (Real.rpow (3 : ℝ) (-s * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
            Real.sqrt (vecNormSq (-p0))) := by
  let Q : TriadicCube d := originCube d m
  let L : ℕ := Int.toNat (m - k)
  have hraw :=
    gradientWeakNorm_le_depthRHS a ha Q L hs hs' hgap p q p0
  have hAvg :
      (∑ j ∈ Finset.range L,
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt
              (descendantsAverage Q j fun R =>
                vecNormSq
                  (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0))) =
        ∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-s * (Int.toNat (m - n) : ℝ)) *
            Real.sqrt
              (descendantsAverage Q (Int.toNat (m - n)) fun R =>
                vecNormSq
                  (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0)) := by
    simpa [L] using
      sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j =>
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt
              (descendantsAverage Q j fun R =>
                vecNormSq
                  (Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun - p0)))
  have hDefect :
      (∑ j ∈ Finset.range L,
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
            Real.sqrt
              (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                Q j p q)) =
        ∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ)) *
            Real.sqrt (responseDefectAverageAtScale m n p q a) := by
    have h :=
      sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j =>
          Real.rpow (3 : ℝ) (-(s - s') * (j : ℝ)) *
            Real.sqrt
              (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                Q j p q))
    simpa [Q, L, responseDefectAverageAtScale_eq_responseJPartitionDefectOnDependentFamily
      a ha] using h
  rw [hAvg, hDefect] at hraw
  simpa [Q, L, gradientAverageTermAtScale, gradientMismatchTermAtScale,
    mul_assoc] using hraw

theorem fluxWeakNorm_le_scaleGeometricRHS
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℤ} (hkm : k ≤ m) {t t' : ℝ}
    (ht : 0 < t) (ht' : 0 < t') (hgap : 0 < t - t')
    (p q q0 : Vec d) :
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet
        (originCube d m) t p q q0 a ≤
      2 *
        (fluxAverageTermAtScale m k t p q q0 a +
          2 * fluxMismatchTermAtScale m k t t' p q a) +
      2 *
        (((2 * Real.sqrt
              (Ch04.LambdaSqCoeffField (originCube d m) t' (.finite 1) a)) *
            (Real.rpow (3 : ℝ) (-(t - t') * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a)) +
          (Real.rpow (3 : ℝ) (-t * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
            Real.sqrt (vecNormSq (-q0))) := by
  let Q : TriadicCube d := originCube d m
  let L : ℕ := Int.toNat (m - k)
  have hraw :=
    fluxWeakNorm_le_depthRHS a ha Q L ht ht' hgap p q q0
  have hAvg :
      (∑ j ∈ Finset.range L,
          Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
            Real.sqrt
              (descendantsAverage Q j fun R =>
                vecNormSq
                  (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0))) =
        ∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-t * (Int.toNat (m - n) : ℝ)) *
            Real.sqrt
              (descendantsAverage Q (Int.toNat (m - n)) fun R =>
                vecNormSq
                  (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0)) := by
    simpa [L] using
      sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j =>
          Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
            Real.sqrt
              (descendantsAverage Q j fun R =>
                vecNormSq
                  (Ch04.canonicalScalarResponseFluxAverageCubeSet R R p q a.toFun - q0)))
  have hDefect :
      (∑ j ∈ Finset.range L,
          Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
            Real.sqrt
              (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                Q j p q)) =
        ∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-(t - t') * (Int.toNat (m - n) : ℝ)) *
            Real.sqrt (responseDefectAverageAtScale m n p q a) := by
    have h :=
      sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j =>
          Real.rpow (3 : ℝ) (-(t - t') * (j : ℝ)) *
            Real.sqrt
              (JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
                Q j p q))
    simpa [Q, L, responseDefectAverageAtScale_eq_responseJPartitionDefectOnDependentFamily
      a ha] using h
  rw [hAvg, hDefect] at hraw
  simpa [Q, L, fluxAverageTermAtScale, fluxMismatchTermAtScale,
    mul_assoc] using hraw

theorem gradientScaleGeometricRHS_le_two_gradientRHSAtScale
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    {k m : ℤ} {s s' : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hgap : 0 < s - s') (hgap_le : s - s' ≤ 1)
    (p q p0 : Vec d) :
      2 *
        (gradientAverageTermAtScale m k s p q p0 a +
          2 * gradientMismatchTermAtScale m k s s' p q a) +
      2 *
        (((2 * Real.sqrt
              ((Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹)) *
            (Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a)) +
          (Real.rpow (3 : ℝ) (-s * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹) *
            Real.sqrt (vecNormSq (-p0))) ≤
        2 *
          gradientRHSAtScale (section53WeakNormMaximizerConst d)
            m k s s' p q p0 a := by
  let C : ℝ := section53WeakNormMaximizerConst d
  let Q : TriadicCube d := originCube d m
  let A : ℝ := gradientAverageTermAtScale m k s p q p0 a
  let M : ℝ := gradientMismatchTermAtScale m k s s' p q a
  let Low : ℝ := gradientLowScaleTailAtScale m k s s' p q a
  let Const : ℝ := gradientConstantTailAtScale m k s p0
  let lam : ℝ := Real.sqrt ((Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹)
  let tailGap : ℝ := Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ))
  let discGap : ℝ := (1 - Real.rpow (3 : ℝ) (-(s - s')))⁻¹
  let sqrtJ : ℝ := Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)
  let tailS : ℝ := Real.rpow (3 : ℝ) (-s * (Int.toNat (m - k) : ℝ))
  let discS : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let sqrtP : ℝ := Real.sqrt (vecNormSq (-p0))
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using gradientMismatchTermAtScale_nonneg m k s s' p q a
  have hM_le : 2 * M ≤ C * M := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [C] using two_le_section53WeakNormMaximizerConst d) hM_nonneg
  have hdiscGap : discGap ≤ 5 * (s - s')⁻¹ := by
    simpa [discGap] using inv_one_sub_rpow_three_neg_le_five_inv hgap hgap_le
  have hdiscS : discS ≤ 5 * s⁻¹ := by
    simpa [discS] using inv_one_sub_rpow_three_neg_le_five_inv hs hs_le
  have htailGap_nonneg : 0 ≤ tailGap := by
    dsimp [tailGap]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    exact Real.sqrt_nonneg _
  have hsqrtJ_nonneg : 0 ≤ sqrtJ := by
    dsimp [sqrtJ]
    exact Real.sqrt_nonneg _
  have hLowBase_nonneg : 0 ≤ (s - s')⁻¹ * tailGap * lam * sqrtJ := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (inv_nonneg.mpr hgap.le) htailGap_nonneg) hlam_nonneg)
      hsqrtJ_nonneg
  have hLowGeom_le :
      (2 * lam) * (tailGap * discGap) * sqrtJ ≤ C * Low := by
    have hstep :
        (2 * lam) * (tailGap * discGap) * sqrtJ ≤
          (2 * lam) * (tailGap * (5 * (s - s')⁻¹)) * sqrtJ := by
      gcongr
    calc
      (2 * lam) * (tailGap * discGap) * sqrtJ
          ≤ (2 * lam) * (tailGap * (5 * (s - s')⁻¹)) * sqrtJ := hstep
      _ = 10 * ((s - s')⁻¹ * tailGap * lam * sqrtJ) := by ring
      _ ≤ C * ((s - s')⁻¹ * tailGap * lam * sqrtJ) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [C] using ten_le_section53WeakNormMaximizerConst d)
            hLowBase_nonneg
      _ = C * Low := by
          simp [Low, gradientLowScaleTailAtScale, Q, lam, tailGap, sqrtJ]
  have hsqrtP : sqrtP ≤ ((d : ℝ) + 1) * ‖p0‖ := by
    simpa [sqrtP, norm_neg] using sqrt_vecNormSq_le_succ_mul_norm (-p0)
  have htailS_nonneg : 0 ≤ tailS := by
    dsimp [tailS]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have htailS_discBound_nonneg : 0 ≤ tailS * (5 * s⁻¹) := by
    exact mul_nonneg htailS_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (5 : ℝ)) (inv_nonneg.mpr hs.le))
  have hConstBase_nonneg : 0 ≤ s⁻¹ * tailS * ‖p0‖ := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hs.le) htailS_nonneg) (norm_nonneg p0)
  have hConstGeom_le :
      tailS * discS * sqrtP ≤ C * Const := by
    calc
      tailS * discS * sqrtP
          ≤ tailS * (5 * s⁻¹) * (((d : ℝ) + 1) * ‖p0‖) := by
            gcongr
      _ = (5 * ((d : ℝ) + 1)) * (s⁻¹ * tailS * ‖p0‖) := by ring
      _ ≤ C * (s⁻¹ * tailS * ‖p0‖) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [C] using five_mul_succ_le_section53WeakNormMaximizerConst d)
            hConstBase_nonneg
      _ = C * Const := by
          simp [Const, gradientConstantTailAtScale, tailS]
  have hmain :
      2 * (A + 2 * M) + 2 *
          (((2 * lam) * (tailGap * discGap) * sqrtJ) +
            tailS * discS * sqrtP) ≤
        2 * (A + C * M + C * Low + C * Const) := by
    nlinarith [hM_le, hLowGeom_le, hConstGeom_le]
  simpa [C, Q, A, M, Low, Const, lam, tailGap, discGap, sqrtJ, tailS, discS, sqrtP,
    gradientRHSAtScale, mul_assoc] using hmain


end

end WeakNormsMaximizer
end Section53
end Ch05
end Book
end Homogenization
