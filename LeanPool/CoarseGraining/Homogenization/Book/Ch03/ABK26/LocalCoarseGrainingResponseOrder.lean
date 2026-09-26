/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingResponse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# Order lowering for the local coarse-graining response

The frozen local theorem uses a `q = 2` response at the local order and the
parent-truncated response at a smaller order.  This module supplies that
order-lowering step before the existing exact descendant localization.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped BigOperators ENNReal

noncomputable section

private theorem homogenizationErrorOnCube_infinity_two_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    0 ≤ Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
  unfold Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
    Ch02.HomogenizationErrorFinite
  apply Real.rpow_nonneg
  refine tsum_nonneg fun n => mul_nonneg ?_ ?_
  · simpa [Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (2 : ℝ)) n
        (by nlinarith))
  · exact Real.rpow_nonneg
      (Ch02.scaleResponseAtScale_infinity_nonneg Q (by omega) a a0) _

/-- For the finite `q = 2` homogenization error, lowering the fractional
order can only increase the on-cube error. -/
theorem homogenizationErrorOnCube_infinity_two_le_of_lt
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 ≤
      Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) a a0 := by
  let H : ℕ → ℝ := fun n =>
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0
  have hmono : Monotone H := by
    intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by omega
    exact Ch02.maxDescendantNormalizedBlockResponseAtScale_le_of_le Q hkl
      (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le m)) a a0
  have hnonneg : ∀ n : ℕ, 0 ≤ H n := by
    intro n
    exact Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)) a a0
  have hsumOld : Summable (fun n : ℕ =>
      Homogenization.geometricWeight t 2 n * H n) := by
    simpa [H, Ch02.geometricWeight_eq_old] using
      Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 ht
  have hseriesOld := Homogenization.tsum_geometricWeight_le_of_monotone
    hmono hnonneg (q := (2 : ℝ)) (by norm_num) ht hts hsumOld
  have hseries :
      ∑' n : ℕ, Ch02.geometricWeight s 2 n * H n ≤
        ∑' n : ℕ, Ch02.geometricWeight t 2 n * H n := by
    simpa [Ch02.geometricWeight_eq_old] using hseriesOld
  have hs : 0 < s := lt_trans ht hts
  have hsq :
      (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 ≤
        (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) a a0) ^ 2 := by
    rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0,
      Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q ht a a0]
    exact hseries
  exact le_of_sq_le_sq hsq (homogenizationErrorOnCube_infinity_two_nonneg Q a a0 ht)

/-- A descendant's local finite-`q = 2` response at order `s` is controlled
by the canonical parent-truncated response at every smaller positive order
`t`, with the existing exact triadic localization factor evaluated at `t`. -/
theorem rootPointwise_descendant_infinity_two_le_parent_of_lt
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} {k : ℤ} (hkn : k ≤ n) (hR : R ∈ descendantsAtScale Q k)
    (t s : FractionalOrder) (hts : t.1 < s.1) :
    ENNReal.ofReal (Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 2)
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ≤
      ENNReal.ofReal (Real.rpow 3 (t.1 * (Int.toNat (n - k) : ℝ))) *
        Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 t := by
  calc
    ENNReal.ofReal (Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 2)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ≤
        ENNReal.ofReal (Ch02.HomogenizationErrorOnCube R t.1 .infinity (.finite 2)
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) :=
      ENNReal.ofReal_le_ofReal
        (homogenizationErrorOnCube_infinity_two_le_of_lt R
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) t.2.1 hts)
    _ ≤ ENNReal.ofReal (Real.rpow 3 (t.1 * (Int.toNat (n - k) : ℝ))) *
        Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 t :=
      rootPointwise_descendant_infinity_two_le_parent Q n hn a sigma0 hsigma0 hkn hR t

end

end ABK26
end Ch03
end Book
end Homogenization
