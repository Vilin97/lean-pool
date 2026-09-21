/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingNegativeAssembly
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingOneCube
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingForcing
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingResponseOrder
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingAssemblyAlgebra

/-!
# Local finite-`p` coarse-graining assembly

This is the source-facing assembly point for the frozen local finite-`p`
coarse-graining theorem.  The reusable input modules deliberately keep the
negative-series expansion, descendant restriction, response localization, and
forcing summation separate; this file only combines those literal carriers.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped BigOperators ENNReal

noncomputable section

/-- A one-cube response maximum is invariant under a coefficient-family
comparison available on that cube alone. -/
private theorem normalizedBlockResponseMax_eq_of_localAEEq
    {d : ℕ} [NeZero d] {A B : Book.Ch02.TriadicCoeffFamily d}
    {S : TriadicCube d} (hS : Book.Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S))
    (a0 : Mat d) :
    Book.Ch02.normalizedBlockResponseMax S A a0 =
      Book.Ch02.normalizedBlockResponseMax S B a0 := by
  unfold Book.Ch02.normalizedBlockResponseMax
  rw [show Book.Ch02.normalizedBlockResponseValueSet S A a0 =
      Book.Ch02.normalizedBlockResponseValueSet S B a0 by
    unfold Book.Ch02.normalizedBlockResponseValueSet
    ext x
    constructor <;> rintro ⟨e, he, rfl⟩ <;>
      refine ⟨e, he, ?_⟩ <;>
      rw [Book.Ch02.doubledResponseJ_eq_ofAEEq hS]]

/-- The endpoint scale response on a root cube needs only a.e. comparison on
the descendants at that particular scale. -/
private theorem scaleResponseAtScale_infinity_eq_of_descendantAEEq
    {d : ℕ} [NeZero d] {A B : Book.Ch02.TriadicCoeffFamily d}
    (R : TriadicCube d) (k : ℤ)
    (h : ∀ S : TriadicCube d, S ∈ descendantsAtScale R k →
      Book.Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S))
    (a0 : Mat d) :
    Book.Ch02.scaleResponseAtScale R k .infinity A a0 =
      Book.Ch02.scaleResponseAtScale R k .infinity B a0 := by
  unfold Book.Ch02.scaleResponseAtScale
  change
    (Book.Ch02.finsetSupReal (descendantsAtScale R k)
      (fun S => Book.Ch02.normalizedBlockResponseMax S A a0)) ^ (1 / 2 : ℝ) =
      (Book.Ch02.finsetSupReal (descendantsAtScale R k)
        (fun S => Book.Ch02.normalizedBlockResponseMax S B a0)) ^ (1 / 2 : ℝ)
  congr 1
  apply Book.Ch02.finsetSupReal_congr
  intro S hS
  exact normalizedBlockResponseMax_eq_of_localAEEq (h S hS) a0

/-- An endpoint homogenization error on `R` is invariant under coefficient
comparison on every descendant of `R`; no global family equality is used. -/
private theorem homogenizationErrorOnCube_infinity_eq_of_descendantAEEq
    {d : ℕ} [NeZero d] {A B : Book.Ch02.TriadicCoeffFamily d}
    (R : TriadicCube d)
    (h : ∀ (k : ℤ) (S : TriadicCube d), S ∈ descendantsAtScale R k →
      Book.Ch02.CoeffOn.AEEq (A.coeffOn S) (B.coeffOn S))
    (t : ℝ) (p : Book.Ch02.MultiscaleExponent) (a0 : Mat d) :
    Book.Ch02.HomogenizationErrorOnCube R t .infinity p A a0 =
      Book.Ch02.HomogenizationErrorOnCube R t .infinity p B a0 := by
  unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
  cases p with
  | finite q =>
      unfold Book.Ch02.HomogenizationErrorFinite
      change
        (∑' j : ℕ, Book.Ch02.geometricWeight t q j *
          (Book.Ch02.scaleResponseAtScale R (R.scale - (j : ℤ)) .infinity A a0) ^ q) ^
            (1 / q) =
          (∑' j : ℕ, Book.Ch02.geometricWeight t q j *
            (Book.Ch02.scaleResponseAtScale R (R.scale - (j : ℤ)) .infinity B a0) ^ q) ^
              (1 / q)
      congr 1
      apply tsum_congr
      intro j
      rw [scaleResponseAtScale_infinity_eq_of_descendantAEEq R
        (R.scale - (j : ℤ)) (fun S hS => h _ S hS) a0]
  | infinity =>
      unfold Book.Ch02.HomogenizationErrorInfinity
      apply congrArg sSup
      ext x
      constructor <;> rintro ⟨j, rfl⟩ <;>
        refine ⟨j, ?_⟩ <;>
        rw [scaleResponseAtScale_infinity_eq_of_descendantAEEq R
          (R.scale - (j : ℤ)) (fun S hS => h _ S hS) a0]

/-- The canonical pointwise family rooted at a descendant and the one rooted
at its parent agree for all response computations below that descendant.
The comparison is deliberately local: their representatives need not agree
outside the descendant. -/
private theorem rootPointwiseCoeffFamily_on_descendant_eq_parent
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k) (t : ℝ)
    (p : Book.Ch02.MultiscaleExponent) (a0 : Mat d) :
    Book.Ch02.HomogenizationErrorOnCube R t .infinity p
      (rootPointwiseCoeffFamily R
        (a.restrictToSubcube
          (openCubeSet_subset_of_mem_descendantsAtScale hk hR))) a0 =
      Book.Ch02.HomogenizationErrorOnCube R t .infinity p
        (rootPointwiseCoeffFamily Q a) a0 := by
  apply homogenizationErrorOnCube_infinity_eq_of_descendantAEEq R _ t p a0
  intro l S hS
  let hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  have hSQ : S ∈ descendantsAtScale Q l :=
    mem_descendantsAtScale_trans hR hS
  have hlQ : l ≤ Q.scale :=
    descendant_scale_le_of_mem_descendantsAtScale hSQ
  have hlR : l ≤ R.scale :=
    descendant_scale_le_of_mem_descendantsAtScale hS
  have hlocal := rootPointwiseCoeffFamily_descendant_aeeq R
    (a.restrictToSubcube hRQ) hlR hS
  have htrans := Book.Ch02.CoeffOn.restrictToSubcube_trans_aeeq a hRQ
    (openCubeSet_subset_of_mem_descendantsAtScale hlR hS)
  have hparent := rootPointwiseCoeffFamily_descendant_aeeq Q a hlQ hSQ
  exact hlocal.trans (htrans.trans hparent.symm)

/-- The source forcing and weak equation restrict together to every physical
descendant used in the outer local average. -/
private theorem localCoarseGraining_descendant_source_data
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    {s2 : FractionalOrder} {p : FiniteLpExponent} {g : Vec d → Vec d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)}
    {u : H1Function (openCubeSet Q)}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k)
    (hg : MemCubeEuclideanFullWsp Q s2 p g)
    (hu : IsForcedEquation Q a u g) :
    MemCubeEuclideanFullWsp R s2 p g ∧
      IsForcedEquation R
        (a.restrictToSubcube
          (openCubeSet_subset_of_mem_descendantsAtScale hk hR))
        (restrictH1ToSubcube u
          (openCubeSet_subset_of_mem_descendantsAtScale hk hR)) g := by
  exact ⟨MemCubeEuclideanFullWsp.onDescendant hk hR hg,
    IsForcedEquation.restrictToDescendant hk hR hu⟩

/-- Re-rooting the coefficient representative on a physical descendant does
not alter its response error.  This is the local a.e. invariance bridge used
when the one-cube theorem is inserted in the parent-scale series. -/
private theorem localCoarseGraining_descendant_response_re_root
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k)
    (t : ℝ) (p : Book.Ch02.MultiscaleExponent) (a0 : Mat d) :
    Book.Ch02.HomogenizationErrorOnCube R t .infinity p
      (rootPointwiseCoeffFamily R
        (a.restrictToSubcube
          (openCubeSet_subset_of_mem_descendantsAtScale hk hR))) a0 =
      Book.Ch02.HomogenizationErrorOnCube R t .infinity p
        (rootPointwiseCoeffFamily Q a) a0 :=
  rootPointwiseCoeffFamily_on_descendant_eq_parent Q a hk hR t p a0

/-- The `q = 1` local response contribution is localized at the exact
physical descendant scale. -/
private theorem localCoarseGraining_descendant_response_one
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n k : ℤ)
    (hn : n ≤ Q.scale) (hkn : k ≤ n)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale Q k)
    (s1 : FractionalOrder) :
    ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R s1.1 .infinity
      (.finite 1) (rootPointwiseCoeffFamily Q a)
        (scalarMatrix (d := d) sigma0)) ≤
      ENNReal.ofReal (Real.rpow 3
        (s1.1 * (Int.toNat (n - k) : ℝ))) *
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
          Q n hn a sigma0 hsigma0 s1 := by
  exact rootPointwise_descendant_infinity_one_le_parent
    Q n hn a sigma0 hsigma0 hkn hR s1

/-- The one-cube `q = 1` error at the local order is first lowered to the
source order before the parent-truncated response localization is used. -/
private theorem localCoarseGraining_descendant_response_one_of_lt
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n k : ℤ)
    (hn : n ≤ Q.scale) (hkn : k ≤ n)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale Q k)
    (s1 s : FractionalOrder) (hs1s : s1.1 < s.1) :
    ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R s.1 .infinity
      (.finite 1) (rootPointwiseCoeffFamily Q a)
        (scalarMatrix (d := d) sigma0)) ≤
      ENNReal.ofReal (Real.rpow 3
        (s1.1 * (Int.toNat (n - k) : ℝ))) *
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
          Q n hn a sigma0 hsigma0 s1 := by
  calc
    ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R s.1 .infinity
        (.finite 1) (rootPointwiseCoeffFamily Q a)
          (scalarMatrix (d := d) sigma0)) ≤
        ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R s1.1 .infinity
          (.finite 1) (rootPointwiseCoeffFamily Q a)
            (scalarMatrix (d := d) sigma0)) :=
      ENNReal.ofReal_le_ofReal
        (Book.Ch02.homogenizationErrorOnCube_infinity_one_le_of_lt R
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
          s1.2.1 hs1s)
    _ ≤ _ := localCoarseGraining_descendant_response_one Q n k hn hkn
      a sigma0 hsigma0 hR s1

/-- The `q = 2` local response contribution is first lowered in order and
then localized by the canonical parent response. -/
private theorem localCoarseGraining_descendant_response_two
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n k : ℤ)
    (hn : n ≤ Q.scale) (hkn : k ≤ n)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale Q k)
    (s1 s : FractionalOrder) (hs1s : s1.1 < s.1) :
    ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R
      (fractionalOrderHalf s).1 .infinity (.finite 2)
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ≤
      ENNReal.ofReal (Real.rpow 3
        ((fractionalOrderHalf s1).1 * (Int.toNat (n - k) : ℝ))) *
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
          Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1) := by
  apply rootPointwise_descendant_infinity_two_le_parent_of_lt
    Q n hn a sigma0 hsigma0 hkn hR (fractionalOrderHalf s1)
      (fractionalOrderHalf s)
  simpa only [fractionalOrderHalf_value] using (div_lt_div_of_pos_right hs1s (by norm_num : (0 : ℝ) < 2))

/-- The local flux-defect carrier used by the negative Besov definition is
definitionally the flux field in the one-cube theorem after restricting to
the physical descendant. -/
private theorem localCoarseGraining_descendant_fluxDefect_eq
    {d : ℕ} [NeZero d] {Q R : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)}
    {sigma0 : ℝ} {u : H1Function (openCubeSet Q)}
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
      (u.grad x)) =
      fluxDefect (a.restrictToSubcube hRQ).toCoeffField
        (scalarMatrix (d := d) sigma0)
        (restrictH1ToSubcube u hRQ).toCubeSet.grad := by
  funext x
  simp only [fluxDefect, Book.Ch02.CoeffOn.restrictToSubcube_toCoeffField,
    sub_matVecMul]
  simp only [H1Function.grad_toCubeSet, restrictH1ToSubcube_grad]

/-- The public one-cube estimate, transported from restricted source data to
the parent-rooted response carrier.  This is the pointwise input for the
physical-scale negative-Besov assembly. -/
private theorem localCoarseGraining_descendant_oneCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s s2 : FractionalOrder) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (hss2 : s.1 < s2.1)
    (g : Vec d → Vec d) (hg : MemCubeEuclideanFullWsp Q s2 p g)
    (u : H1Function (openCubeSet Q)) (hu : IsForcedEquation Q a u g)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale Q k) :
    ENNReal.ofReal ‖cubeAverageVec R
      (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
        (u.grad x))‖ ≤
      ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
        (ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
            ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R s.1 .infinity
              (.finite 1) (rootPointwiseCoeffFamily Q a)
              (scalarMatrix (d := d) sigma0)) *
            localSymmetricEnergyENorm R
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale hk hR))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale hk hR)) +
          ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
            (1 + ENNReal.ofReal
              (Book.Ch02.HomogenizationErrorOnCube R (s.1 / 2) .infinity
                (.finite 2) (rootPointwiseCoeffFamily Q a)
                (scalarMatrix (d := d) sigma0)) ^ 2) *
            ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) := by
  let hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  obtain ⟨hgR, huR⟩ := localCoarseGraining_descendant_source_data hk hR hg hu
  have hone := ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_localCoarseGrainingOneCube
    (R := R) (a := a.restrictToSubcube hRQ)
    (u := restrictH1ToSubcube u hRQ) (g := g) sigma0 hsigma0 s s2 p hp hss2 hgR huR
  have hOne := localCoarseGraining_descendant_response_re_root Q a hk hR s.1
    (.finite 1) (scalarMatrix (d := d) sigma0)
  have hTwo := localCoarseGraining_descendant_response_re_root Q a hk hR (s.1 / 2)
    (.finite 2) (scalarMatrix (d := d) sigma0)
  rw [hOne, hTwo] at hone
  simpa only [localCoarseGraining_descendant_fluxDefect_eq hRQ] using hone

/-- A finite neutral factor used while enlarging the final dimension-only
assembly constant.  The actual one-cube and forcing factors are inserted only
through their public seams. -/
private theorem localCoarseGraining_neutralConstant_lt_top :
    (1 : ℝ≥0∞) < ∞ := by
  norm_num

/-- The outer finite-`p` root is subadditive.  Keeping this elementary
calculation here makes the two sources of the final RHS explicit instead of
hiding an extra hypothesis in an auxiliary norm. -/
private theorem ENNReal_rpow_inv_add_le_add_rpow_inv {r : ℝ}
    (hr : 1 ≤ r) (A B : ℝ≥0∞) :
    (A + B) ^ r⁻¹ ≤ A ^ r⁻¹ + B ^ r⁻¹ := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  apply ENNReal.rpow_add_le_add_rpow
  · exact inv_nonneg.mpr hrpos.le
  · exact (inv_le_one₀ hrpos).mpr hr

/-- Pulling a common nonnegative factor through the sole outer finite-`p`
root. -/
private theorem ENNReal_rpow_inv_mul_eq_mul_rpow_inv {r : ℝ}
    (hr : 0 < r) (C A : ℝ≥0∞) :
    (C ^ r * A) ^ r⁻¹ = C * A ^ r⁻¹ := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]

/-- A common factor in every term of a nonnegative series pulls through the
outer finite-`p` root. -/
private theorem ENNReal_rpow_inv_tsum_mul_rpow_eq {r : ℝ}
    (hr : 0 < r) (C : ℝ≥0∞) (F : ℕ → ℝ≥0∞) :
    (∑' j : ℕ, C ^ r * F j) ^ r⁻¹ = C * (∑' j : ℕ, F j) ^ r⁻¹ := by
  rw [ENNReal.tsum_mul_left]
  exact ENNReal_rpow_inv_mul_eq_mul_rpow_inv hr C _

/-- The scale normalizations in the source-facing RHS are the corresponding
`ENNReal` inverse and fractional powers. -/
private theorem localCoarseGraining_scale_normalizations
    {s sigma0 : ℝ} (hs : 0 < s) (hsigma0 : 0 < sigma0) :
    ENNReal.ofReal s⁻¹ = (ENNReal.ofReal s)⁻¹ ∧
      ENNReal.ofReal (Real.sqrt sigma0) =
        (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) ∧
      ENNReal.ofReal (Real.rpow s (-(9 / 2 : ℝ))) =
        (ENNReal.ofReal s) ^ (-(9 / 2 : ℝ)) := by
  constructor
  · exact ENNReal.ofReal_inv_of_pos hs
  constructor
  · rw [Real.sqrt_eq_rpow]
    exact (ENNReal.ofReal_rpow_of_pos hsigma0).symm
  · exact (ENNReal.ofReal_rpow_of_pos hs).symm

/-- At the physical descendant scale `n-j`, the parent-localization depth is
literally `j`. -/
private theorem localCoarseGraining_toNat_parent_depth
    (n : ℤ) (j : ℕ) :
    Int.toNat (n - (n - (j : ℤ))) = j := by
  rw [show n - (n - (j : ℤ)) = j by ring]
  simp

/-- A one-level response scale factor is at least one.  This absorbs the
unit part of the finite-`q = 2` envelope without creating another fractional
gap. -/
private theorem one_le_response_scaleFactor
    {s : FractionalOrder} (j : ℕ) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.rpow 3 (s.1 * (j : ℝ))) := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  exact Real.one_le_rpow (by norm_num) (mul_nonneg s.2.1.le (by positivity))

/-- Squaring the half-order response localization factor produces exactly
the full `s₁` physical-depth factor. -/
private theorem response_half_scaleFactor_sq_eq_full
    (s1 : FractionalOrder) (j : ℕ) :
    (ENNReal.ofReal (Real.rpow 3 ((s1.1 / 2) * (j : ℝ)))) ^ 2 =
      ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) := by
  have hhalf : 0 ≤ Real.rpow 3 ((s1.1 / 2) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [pow_two, ← ENNReal.ofReal_mul hhalf]
  congr 1
  calc
    Real.rpow 3 ((s1.1 / 2) * (j : ℝ)) *
        Real.rpow 3 ((s1.1 / 2) * (j : ℝ)) =
        Real.rpow 3 (((s1.1 / 2) * (j : ℝ)) + ((s1.1 / 2) * (j : ℝ))) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ = Real.rpow 3 (s1.1 * (j : ℝ)) := by
      congr 1
      ring

/-- After response localization, the quadratic `q = 2` envelope has the
same full `s₁` scale factor as the `q = 1` response term. -/
private theorem one_add_sq_mul_response_half_scale_le_full_scale_mul_one_add_sq
    {H : ℝ≥0∞} (s1 : FractionalOrder) (j : ℕ) :
    1 + (ENNReal.ofReal (Real.rpow 3 ((s1.1 / 2) * (j : ℝ))) * H) ^ 2 ≤
      ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * (1 + H ^ 2) := by
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 ((s1.1 / 2) * (j : ℝ)))
  have hT : (1 : ℝ≥0∞) ≤ T := by
    dsimp [T]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact Real.one_le_rpow (by norm_num)
      (mul_nonneg (div_nonneg s1.2.1.le (by norm_num)) (by positivity))
  have hT2 : T ^ 2 = ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) := by
    simpa only [T, fractionalOrderHalf_value] using
      response_half_scaleFactor_sq_eq_full s1 j
  have hT2one : (1 : ℝ≥0∞) ≤ T ^ 2 := by
    rw [← ENNReal.rpow_two]
    simpa only [ENNReal.one_rpow] using
      ENNReal.rpow_le_rpow hT (by norm_num : (0 : ℝ) ≤ 2)
  calc
    1 + (T * H) ^ 2 = 1 + T ^ 2 * H ^ 2 := by
      congr 1
      simpa only [ENNReal.rpow_two] using
        ENNReal.mul_rpow_of_nonneg T H (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ T ^ 2 * (1 + H ^ 2) := by
      calc
        1 + T ^ 2 * H ^ 2 ≤ T ^ 2 + T ^ 2 * H ^ 2 := by
          exact add_le_add hT2one le_rfl
        _ = T ^ 2 * (1 + H ^ 2) := by ring
    _ = ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * (1 + H ^ 2) := by
      rw [hT2]

/-- At depth `j` below the prescribed physical scale, the one-cube estimate
is controlled by the parent responses with a *single* `3^(s₁j)` factor on
each of its energy and forcing components. -/
private theorem localCoarseGraining_descendant_oneCube_parent_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s1 s s2 : FractionalOrder) (hs1s : s1.1 < s.1) (hss2 : s.1 < s2.1)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (g : Vec d → Vec d) (hg : MemCubeEuclideanFullWsp Q s2 p g)
    (u : H1Function (openCubeSet Q)) (hu : IsForcedEquation Q a u g)
    (j : ℕ) {R : TriadicCube d} (hR : R ∈ descendantsAtScale Q (n - (j : ℤ))) :
    ENNReal.ofReal ‖cubeAverageVec R
      (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
        (u.grad x))‖ ≤
      ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
        (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) *
          (ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
            Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
              Q n hn a sigma0 hsigma0 s1 *
            localSymmetricEnergyENorm R
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR)) +
          ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
            (1 +
              (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
            ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g))) := by
  let S : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ)))
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 ((s1.1 / 2) * (j : ℝ)))
  let H1 : ℝ≥0∞ := Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
    Q n hn a sigma0 hsigma0 s1
  let H2 : ℝ≥0∞ := Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
    Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)
  let E : ℝ≥0∞ := localSymmetricEnergyENorm R
    (a.restrictToSubcube
      (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR))
    (restrictH1ToSubcube u
      (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR))
  let B : ℝ≥0∞ := ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)
  have hone := localCoarseGraining_descendant_oneCube Q (n - (j : ℤ)) (by omega)
    a sigma0 hsigma0 s s2 p hp hss2 g hg u hu hR
  have h1 := localCoarseGraining_descendant_response_one_of_lt Q n (n - (j : ℤ)) hn
    (by omega) a sigma0 hsigma0 hR s1 s hs1s
  have h2 := localCoarseGraining_descendant_response_two Q n (n - (j : ℤ)) hn
    (by omega) a sigma0 hsigma0 hR s1 s hs1s
  rw [localCoarseGraining_toNat_parent_depth n j] at h1 h2
  change _ ≤ ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
    (S * (ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) * H1 * E +
      ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) * (1 + H2 ^ 2) * B))
  apply hone.trans
  apply mul_le_mul_right
  conv_rhs => rw [mul_add]
  apply add_le_add
  · calc
      ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
          ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R s.1 .infinity
            (.finite 1) (rootPointwiseCoeffFamily Q a)
            (scalarMatrix (d := d) sigma0)) * E ≤
          ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) * (S * H1) * E := by
            gcongr
      _ = S * (ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) * H1 * E) := by
        ring
  · have h2sq := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 2)
    have h2sq' : ENNReal.ofReal
        (Book.Ch02.HomogenizationErrorOnCube R (s.1 / 2) .infinity
          (.finite 2) (rootPointwiseCoeffFamily Q a)
          (scalarMatrix (d := d) sigma0)) ^ (2 : ℝ) ≤ (T * H2) ^ (2 : ℝ) := by
      simpa only [T, H2, fractionalOrderHalf_value] using h2sq
    have henv : 1 +
        ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R (s.1 / 2) .infinity
          (.finite 2) (rootPointwiseCoeffFamily Q a)
          (scalarMatrix (d := d) sigma0)) ^ 2 ≤ S * (1 + H2 ^ 2) := by
      calc
        1 + ENNReal.ofReal
            (Book.Ch02.HomogenizationErrorOnCube R (s.1 / 2) .infinity
              (.finite 2) (rootPointwiseCoeffFamily Q a)
              (scalarMatrix (d := d) sigma0)) ^ 2 ≤
            1 + (T * H2) ^ 2 := by
              rw [← ENNReal.rpow_two, ← ENNReal.rpow_two]
              simpa only [add_comm] using add_le_add_left h2sq' (1 : ℝ≥0∞)
        _ ≤ S * (1 + H2 ^ 2) := by
          simpa only [S, T] using
            one_add_sq_mul_response_half_scale_le_full_scale_mul_one_add_sq s1 j (H := H2)
    calc
      ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
          (1 + ENNReal.ofReal
            (Book.Ch02.HomogenizationErrorOnCube R (s.1 / 2) .infinity
              (.finite 2) (rootPointwiseCoeffFamily Q a)
              (scalarMatrix (d := d) sigma0)) ^ 2) * B ≤
          ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
            (S * (1 + H2 ^ 2)) * B := by gcongr
      _ = S * (ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
          (1 + H2 ^ 2) * B) := by ring

/-- Combining the negative-Besov weight with the one-cube response
localization factor gives precisely the `(s-s₁)` geometric discount. -/
private theorem localCoarseGraining_negative_weight_mul_response_scale_rpow
    (s1 s : FractionalOrder) (r : ℝ) (hr : 0 ≤ r) (j : ℕ) :
    ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
      (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ)))) ^ r =
      ENNReal.ofReal (Real.rpow 3
        (-((s.1 - s1.1) * r * (j : ℝ)))) := by
  have hleft : 0 ≤ Real.rpow 3 (-(s.1 * r * (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hresponse : 0 ≤ Real.rpow 3 (s1.1 * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [ENNReal.ofReal_rpow_of_nonneg hresponse hr]
  rw [← ENNReal.ofReal_mul hleft]
  congr 1
  have hpow : Real.rpow (Real.rpow 3 (s1.1 * (j : ℝ))) r =
      Real.rpow 3 ((s1.1 * (j : ℝ)) * r) :=
    (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
  rw [show Real.rpow 3 (s1.1 * (j : ℝ)) ^ r =
      Real.rpow 3 ((s1.1 * (j : ℝ)) * r) by exact hpow]
  have hmul : Real.rpow 3 (-(s.1 * r * (j : ℝ))) *
      Real.rpow 3 ((s1.1 * (j : ℝ)) * r) =
      Real.rpow 3 (-(s.1 * r * (j : ℝ)) + ((s1.1 * (j : ℝ)) * r)) :=
    (Real.rpow_add (by norm_num) _ _).symm
  rw [hmul]
  congr 1
  ring

/-- A constant factor pulls through a finite normalized physical-scale
descendant average. -/
private theorem localCoarseGraining_descendantsAtScale_average_mul_left
    {d : ℕ} (Q : TriadicCube d) (k : ℤ) (C : ℝ≥0∞)
    (F : TriadicCube d → ℝ≥0∞) :
    descendantsAtScaleENNAverage Q k (fun R => C * F R) =
      C * descendantsAtScaleENNAverage Q k F := by
  unfold descendantsAtScaleENNAverage
  rw [← Finset.mul_sum]
  ring

/-- The weighted physical-scale series of a response-localized component
factors into its fixed parent coefficient and the exact `(s-s₁)` series. -/
private theorem localCoarseGraining_weighted_component_factorization
    {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s1 s : FractionalOrder) (r : ℝ) (hr : 0 ≤ r)
    (P : ℝ≥0∞) (F : ℕ → TriadicCube d → ℝ≥0∞) :
    (∑' j : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
        descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
          (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * P * F j R) ^ r)) =
      P ^ r * ∑' j : ℕ,
        ENNReal.ofReal (Real.rpow 3
          (-((s.1 - s1.1) * r * (j : ℝ)))) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (F j R) ^ r) := by
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr]
  rw [localCoarseGraining_descendantsAtScale_average_mul_left]
  calc
    ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
        (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) ^ r * P ^ r *
          descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => F j R ^ r)) =
        P ^ r * (ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
          ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) ^ r) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => F j R ^ r) := by ring
    _ = P ^ r * (ENNReal.ofReal (Real.rpow 3
          (-((s.1 - s1.1) * r * (j : ℝ)))) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => F j R ^ r)) := by
      rw [localCoarseGraining_negative_weight_mul_response_scale_rpow s1 s r hr j]
      ring

/-- The response-localized forcing component is exactly the declared local
forcing aggregation after taking the finite power. -/
private theorem localCoarseGraining_forcing_series_eq_localForcing
    {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s1 s : FractionalOrder) (p : FiniteLpExponent)
    (P : ℝ≥0∞) (g : Vec d → Vec d) :
    (∑' j : ℕ,
      ENNReal.ofReal (Real.rpow 3
        (-(s.1 * p.exponent.toReal * (j : ℝ)))) *
        descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
          (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * P *
            ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
              p.exponent.toReal)) =
      P ^ p.exponent.toReal *
        (localCoarseGrainingForcingLp Q n s1 s p g) ^ p.exponent.toReal := by
  rw [localCoarseGraining_weighted_component_factorization Q n s1 s
    p.exponent.toReal (ENNReal.toReal_nonneg) P
    (fun _ R => ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g))]
  rw [localCoarseGrainingForcingLp_rpow_eq_powerEnergy]
  unfold localCoarseGrainingForcingPowerEnergy
  apply congrArg (fun X : ℝ≥0∞ => P ^ p.exponent.toReal * X)
  apply tsum_congr
  intro j
  congr 3
  ring

/-- The dependent restricted-energy summand has the same exact
factorization; this version works directly with the attached finite sum so
the restriction proof remains available. -/
private theorem localCoarseGraining_energy_series_eq_weightedEnergy
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q))
    (s1 s : FractionalOrder) (p : FiniteLpExponent)
    (P : ℝ≥0∞) :
    (∑' j : ℕ,
      ENNReal.ofReal (Real.rpow 3
        (-(s.1 * p.exponent.toReal * (j : ℝ)))) *
      ((descendantsAtScale Q (n - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
        (descendantsAtScale Q (n - (j : ℤ))).attach.sum (fun R =>
          (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * P *
            localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^
              p.exponent.toReal)) =
      P ^ p.exponent.toReal *
        (weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) ^ p.exponent.toReal := by
  rw [weightedLocalSymmetricEnergyLp_rpow_eq_tsum]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  let D : Finset (TriadicCube d) := descendantsAtScale Q (n - (j : ℤ))
  let S : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ)))
  let r : ℝ := p.exponent.toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hsum : D.attach.sum (fun R =>
      (S * P * localSymmetricEnergyENorm R.1
        (a.restrictToSubcube
          (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
        (restrictH1ToSubcube u
          (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) =
      S ^ r * P ^ r * D.attach.sum (fun R =>
        (localSymmetricEnergyENorm R.1
          (a.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
          (restrictH1ToSubcube u
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) := by
    calc
      D.attach.sum (fun R =>
          (S * P * localSymmetricEnergyENorm R.1
            (a.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
            (restrictH1ToSubcube u
              (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) =
          D.attach.sum (fun R => S ^ r * P ^ r *
            (localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) := by
            apply Finset.sum_congr rfl
            intro R _
            rw [ENNReal.mul_rpow_of_nonneg _ _ hr,
              ENNReal.mul_rpow_of_nonneg _ _ hr]
      _ = S ^ r * P ^ r * D.attach.sum (fun R =>
          (localSymmetricEnergyENorm R.1
            (a.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
            (restrictH1ToSubcube u
              (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) := by
            rw [Finset.mul_sum]
  change ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
      (D.card : ℝ≥0∞)⁻¹ * _ =
    P ^ r *
      (ENNReal.ofReal (Real.rpow 3
        (-((s.1 - s1.1) * r * (j : ℝ)))) *
        (D.card : ℝ≥0∞)⁻¹ * _)
  rw [hsum]
  calc
    ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
        (D.card : ℝ≥0∞)⁻¹ *
          (S ^ r * P ^ r * D.attach.sum (fun R =>
            (localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r)) =
        P ^ r * (ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) * S ^ r) *
          (D.card : ℝ≥0∞)⁻¹ * D.attach.sum (fun R =>
            (localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) := by ring
    _ = P ^ r * ENNReal.ofReal (Real.rpow 3
          (-((s.1 - s1.1) * r * (j : ℝ)))) *
          (D.card : ℝ≥0∞)⁻¹ * D.attach.sum (fun R =>
            (localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) := by
      rw [localCoarseGraining_negative_weight_mul_response_scale_rpow s1 s r hr j]
    _ = _ := by ring

/-- The convex finite-power triangle coefficient becomes at most `2` after
the single outer finite-`p` root. -/
private theorem localCoarseGraining_triangle_coefficient_root_le_two
    {r : ℝ} (hr : 1 ≤ r) :
    ((2 : ℝ≥0∞) ^ (r - 1)) ^ r⁻¹ ≤ 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hrpos.le
  have hexp : (r - 1) * r⁻¹ ≤ 1 := by
    calc
      (r - 1) * r⁻¹ = 1 - r⁻¹ := by field_simp [hrpos.ne']
      _ ≤ 1 := sub_le_self _ hinv
  calc
    ((2 : ℝ≥0∞) ^ (r - 1)) ^ r⁻¹ =
        (2 : ℝ≥0∞) ^ ((r - 1) * r⁻¹) := by rw [← ENNReal.rpow_mul]
    _ ≤ 2 ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 := ENNReal.rpow_one _

/-- The finite-power triangle is already available for one physical-scale
average; this wrapper only transports a pointwise one-cube bound into that
canonical form. -/
private theorem localCoarseGraining_one_scale_pointwise_add_bound
    {d : ℕ} (Q : TriadicCube d) (k : ℤ) {r : ℝ} (hr : 1 ≤ r)
    (K : ℝ≥0∞) (L E F : TriadicCube d → ℝ≥0∞)
    (h : ∀ R ∈ descendantsAtScale Q k, L R ≤ K * (E R + F R)) :
    descendantsAtScaleENNAverage Q k (fun R => (L R) ^ r) ≤
      K ^ r * (2 : ℝ≥0∞) ^ (r - 1) *
        (descendantsAtScaleENNAverage Q k (fun R => (E R) ^ r) +
          descendantsAtScaleENNAverage Q k (fun R => (F R) ^ r)) := by
  calc
    descendantsAtScaleENNAverage Q k (fun R => (L R) ^ r) ≤
        descendantsAtScaleENNAverage Q k (fun R => (K * (E R + F R)) ^ r) := by
      unfold descendantsAtScaleENNAverage
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro R hR
      exact ENNReal.rpow_le_rpow (h R hR) (by positivity)
    _ = K ^ r * descendantsAtScaleENNAverage Q k (fun R => (E R + F R) ^ r) := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ r)]
      exact localCoarseGraining_descendantsAtScale_average_mul_left Q k (K ^ r) _
    _ ≤ K ^ r * ((2 : ℝ≥0∞) ^ (r - 1) *
        (descendantsAtScaleENNAverage Q k (fun R => (E R) ^ r) +
          descendantsAtScaleENNAverage Q k (fun R => (F R) ^ r))) := by
      gcongr
      exact descendantsAtScaleENNAverage_rpow_add_le Q k hr E F
    _ = _ := by ring

/-- The final dimension-only coefficient simultaneously absorbs the outer
two-term finite-`p` triangle and the sharp `5 · 3^d` forcing factor. -/
private theorem two_mul_le_ten_mul_three_pow_dim
    {d : ℕ} (K : ℝ≥0∞) :
    2 * K ≤ (10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * K := by
  have hthree : (1 : ℝ≥0∞) ≤ (3 ^ d : ℝ≥0∞) := by
    exact one_le_pow₀ (by norm_num)
  calc
    2 * K = K * 2 := by ring
    _ ≤ K * (10 : ℝ≥0∞) := mul_le_mul_right (by norm_num) K
    _ = (10 : ℝ≥0∞) * K := by ring
    _ ≤ (10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * K := by
      have hcoef : (10 : ℝ≥0∞) ≤ 10 * (3 ^ d : ℝ≥0∞) := by
        calc
          (10 : ℝ≥0∞) = 10 * 1 := by ring
          _ ≤ 10 * (3 ^ d : ℝ≥0∞) := mul_le_mul_right hthree 10
      calc
        10 * K = K * 10 := by ring
        _ ≤ K * (10 * (3 ^ d : ℝ≥0∞)) := mul_le_mul_right hcoef K
        _ = 10 * (3 ^ d : ℝ≥0∞) * K := by ring

private theorem ten_mul_three_pow_dim_mul_lt_top
    {d : ℕ} (K : ℝ≥0∞) (hK : K < ∞) :
    (10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * K < ∞ := by
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top (by norm_num) (by simp)
  · exact hK

/-- The physical-scale series obtained from the pointwise one-cube theorem.
This is deliberately stated before taking the outer root: the two terms are
then exactly the energy and forcing series which the two preceding modules
already expose. -/
private theorem localCoarseGraining_outer_power_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s1 s s2 : FractionalOrder) (hs1s : s1.1 < s.1) (hss2 : s.1 < s2.1)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (g : Vec d → Vec d) (hg : MemCubeEuclideanFullWsp Q s2 p g)
    (u : H1Function (openCubeSet Q)) (hu : IsForcedEquation Q a u g) :
    (localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p) ^
        p.exponent.toReal ≤
      (ENNReal.ofReal (localCoarseGrainingOneCubeConstant d)) ^ p.exponent.toReal *
        (2 : ℝ≥0∞) ^ (p.exponent.toReal - 1) *
          ((ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
              Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                Q n hn a sigma0 hsigma0 s1) ^ p.exponent.toReal *
              (weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) ^
                p.exponent.toReal +
            (ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
              (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2)) ^
                p.exponent.toReal *
              (localCoarseGrainingForcingLp Q n s1 s p g) ^
                p.exponent.toReal) := by
  classical
  let r : ℝ := p.exponent.toReal
  let K : ℝ≥0∞ := ENNReal.ofReal (localCoarseGrainingOneCubeConstant d)
  let A : ℝ≥0∞ := ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0 hsigma0 s1
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
    (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
      Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2)
  let E : ℕ → TriadicCube d → ℝ≥0∞ := fun j R =>
    if hR : R ∈ descendantsAtScale Q (n - (j : ℤ)) then
      ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * A *
        localSymmetricEnergyENorm R
          (a.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR))
          (restrictH1ToSubcube u
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR))
    else 0
  let F : ℕ → TriadicCube d → ℝ≥0∞ := fun j R =>
    ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * B *
      ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)
  have hr : (1 : ℝ) ≤ r := by
    dsimp [r]
    exact le_trans (by norm_num) (ENNReal.toReal_mono p.lt_top.ne hp)
  have hlevel : ∀ j : ℕ,
      descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
        (ENNReal.ofReal ‖cubeAverageVec R
          (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
            (u.grad x))‖) ^ r) ≤
        K ^ r * (2 : ℝ≥0∞) ^ (r - 1) *
          (descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (E j R) ^ r) +
            descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (F j R) ^ r)) := by
    intro j
    apply localCoarseGraining_one_scale_pointwise_add_bound Q (n - (j : ℤ)) hr K (fun R =>
      ENNReal.ofReal ‖cubeAverageVec R
        (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
          (u.grad x))‖) (E j) (F j)
    intro R hR
    have hbound := localCoarseGraining_descendant_oneCube_parent_bound Q n hn a sigma0 hsigma0
      s1 s s2 hs1s hss2 p hp g hg u hu j hR
    calc
      ENNReal.ofReal ‖cubeAverageVec R
          (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
            (u.grad x))‖ ≤ K *
          (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) *
            (A * localSymmetricEnergyENorm R
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) hR)) +
              B * ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g))) := by
            simpa only [K, A, B] using hbound
      _ = K * (E j R + F j R) := by
        simp only [E, F, dif_pos hR]
        ring
  rw [localFluxDefectNegativeBesovLpAverage_rpow_eq_tsum_descendantsAtScale]
  calc
    (∑' j : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
        descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
          (ENNReal.ofReal ‖cubeAverageVec R
            (fun x => matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0)
              (u.grad x))‖) ^ r)) ≤
        ∑' j : ℕ,
          ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
            (K ^ r * (2 : ℝ≥0∞) ^ (r - 1) *
              (descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (E j R) ^ r) +
                descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (F j R) ^ r))) := by
          apply ENNReal.tsum_le_tsum
          intro j
          exact mul_le_mul_right (hlevel j) _
    _ = K ^ r * (2 : ℝ≥0∞) ^ (r - 1) *
          ((∑' j : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
              descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (E j R) ^ r)) +
            (∑' j : ℕ,
              ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
                descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (F j R) ^ r))) := by
          have hdistrib : (fun j : ℕ =>
              ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
                (K ^ r * (2 : ℝ≥0∞) ^ (r - 1) *
                  (descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (E j R) ^ r) +
                    descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (F j R) ^ r)))) =
              (fun (j : ℕ) => K ^ r * (2 : ℝ≥0∞) ^ (r - 1) *
                (ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
                  descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (E j R) ^ r) +
                  ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
                    descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (F j R) ^ r))) := by
            funext j
            ring
          rw [hdistrib]
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ = K ^ r * (2 : ℝ≥0∞) ^ (r - 1) *
          (A ^ r * (weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) ^ r +
            B ^ r * (localCoarseGrainingForcingLp Q n s1 s p g) ^ r) := by
          congr 3
          · have hE : (∑' j : ℕ,
                ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
                  descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R => (E j R) ^ r)) =
                (∑' j : ℕ,
                  ENNReal.ofReal (Real.rpow 3 (-(s.1 * r * (j : ℝ)))) *
                    ((descendantsAtScale Q (n - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
                      (descendantsAtScale Q (n - (j : ℤ))).attach.sum (fun R =>
                        (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * A *
                          localSymmetricEnergyENorm R.1
                            (a.restrictToSubcube
                              (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
                            (restrictH1ToSubcube u
                              (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r)) := by
              apply tsum_congr
              intro j
              unfold descendantsAtScaleENNAverage
              have hsum : (∑ R ∈ descendantsAtScale Q (n - (j : ℤ)), (E j R) ^ r) =
                  (descendantsAtScale Q (n - (j : ℤ))).attach.sum (fun R =>
                    (ENNReal.ofReal (Real.rpow 3 (s1.1 * (j : ℝ))) * A *
                      localSymmetricEnergyENorm R.1
                        (a.restrictToSubcube
                          (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
                        (restrictH1ToSubcube u
                          (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^ r) := by
                rw [← Finset.sum_attach]
                apply Finset.sum_congr rfl
                intro R hR
                simp only [E, dif_pos R.2]
              rw [hsum]
              ring
            rw [hE]
            simpa only [r] using
              localCoarseGraining_energy_series_eq_weightedEnergy Q n hn a u s1 s p A
          · simpa only [r, F, B] using
              localCoarseGraining_forcing_series_eq_localForcing Q n s1 s p B g
    _ = _ := by rfl

/-- Taking the one outer finite-`p` root leaves only the universal two-term
triangle factor. -/
private theorem localCoarseGraining_outer_root_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s1 s s2 : FractionalOrder) (hs1s : s1.1 < s.1) (hss2 : s.1 < s2.1)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (g : Vec d → Vec d) (hg : MemCubeEuclideanFullWsp Q s2 p g)
    (u : H1Function (openCubeSet Q)) (hu : IsForcedEquation Q a u g) :
    localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p ≤
      2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
        (ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
            Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
              Q n hn a sigma0 hsigma0 s1 *
            weightedLocalSymmetricEnergyLp Q n hn a u s1 s p +
          ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
            (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
              Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
            localCoarseGrainingForcingLp Q n s1 s p g) := by
  let r : ℝ := p.exponent.toReal
  let K : ℝ≥0∞ := ENNReal.ofReal (localCoarseGrainingOneCubeConstant d)
  let A : ℝ≥0∞ := ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
    Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0 hsigma0 s1
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
    (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
      Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2)
  let E : ℝ≥0∞ := weightedLocalSymmetricEnergyLp Q n hn a u s1 s p
  let F : ℝ≥0∞ := localCoarseGrainingForcingLp Q n s1 s p g
  have hr : (1 : ℝ) ≤ r := by
    dsimp [r]
    exact le_trans (by norm_num) (ENNReal.toReal_mono p.lt_top.ne hp)
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hrpos.le
  have hpow := localCoarseGraining_outer_power_bound Q n hn a sigma0 hsigma0
    s1 s s2 hs1s hss2 p hp g hg u hu
  have hroot : localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p =
      (localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p ^ r) ^ r⁻¹ := by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hrpos.ne', ENNReal.rpow_one]
  have hinner : (A ^ r * E ^ r + B ^ r * F ^ r) ^ r⁻¹ ≤ A * E + B * F := by
    calc
      (A ^ r * E ^ r + B ^ r * F ^ r) ^ r⁻¹ =
          ((A * E) ^ r + (B * F) ^ r) ^ r⁻¹ := by
            rw [ENNReal.mul_rpow_of_nonneg A E hrpos.le,
              ENNReal.mul_rpow_of_nonneg B F hrpos.le]
      _ ≤ ((A * E) ^ r) ^ r⁻¹ + ((B * F) ^ r) ^ r⁻¹ :=
        ENNReal_rpow_inv_add_le_add_rpow_inv hr ((A * E) ^ r) ((B * F) ^ r)
      _ = A * E + B * F := by
        rw [← ENNReal.rpow_mul (A * E) r r⁻¹,
          ← ENNReal.rpow_mul (B * F) r r⁻¹,
          mul_inv_cancel₀ hrpos.ne', ENNReal.rpow_one,
          ENNReal.rpow_one]
  calc
    localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p =
        (localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p ^ r) ^ r⁻¹ := hroot
    _ ≤ (K ^ r * (2 : ℝ≥0∞) ^ (r - 1) * (A ^ r * E ^ r + B ^ r * F ^ r)) ^ r⁻¹ := by
      apply ENNReal.rpow_le_rpow hpow hinv
    _ = K * ((2 : ℝ≥0∞) ^ (r - 1)) ^ r⁻¹ *
        (A ^ r * E ^ r + B ^ r * F ^ r) ^ r⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hinv,
        ENNReal.mul_rpow_of_nonneg _ _ hinv,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ hrpos.ne', ENNReal.rpow_one]
    _ ≤ K * 2 * (A * E + B * F) := by
      have hfac : K * ((2 : ℝ≥0∞) ^ (r - 1)) ^ r⁻¹ ≤ K * 2 :=
        mul_le_mul_right (localCoarseGraining_triangle_coefficient_root_le_two hr) K
      exact mul_le_mul hfac hinner (by positivity) (by positivity)
    _ = _ := by simp only [K, A, B, E, F]; ring

/-- The exact local finite-`p` coarse-graining theorem frozen in the Chapter
3 declaration anchors.  All regularity, trace, response, and summability
work is discharged internally through the one-cube and forcing seams. -/
theorem exists_localCoarseGrainingLp (d : ℕ) (hd : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (p : FiniteLpExponent), (2 : ℝ≥0∞) ≤ p.exponent →
      ∀ (m n : ℤ), ∀ (hnm : n < m),
      ∀ (s1 s s2 : FractionalOrder), s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Book.Ch02.CoeffOn
          (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ), ∀ (hsigma0 : 0 < sigma0),
      ∀ (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
      ∀ (u : H1Function (openCubeSet (originCube d m))),
        IsForcedEquation (originCube d m) a u g →
        localFluxDefectNegativeBesovLpAverage (originCube d m) n
            (by simpa [originCube] using hnm.le) a sigma0 u s p ≤
          localCoarseGrainingLpRHS C
            (originCube d m) n
            (by simpa [originCube] using hnm.le)
            a sigma0 hsigma0 g u s1 s s2 p := by
  let : NeZero d := ⟨by omega⟩
  let C : ℝ≥0∞ := (10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
    ENNReal.ofReal (localCoarseGrainingOneCubeConstant d)
  refine ⟨C, ?_, ?_⟩
  · apply ten_mul_three_pow_dim_mul_lt_top
    exact ENNReal.ofReal_lt_top
  intro p hp m n hnm s1 s s2 hs1s hss2 a sigma0 hsigma0 g hg u hu
  let Q : TriadicCube d := originCube d m
  have hn : n ≤ Q.scale := by simpa [Q, originCube] using hnm.le
  have hroot := localCoarseGraining_outer_root_bound Q n hn a sigma0 hsigma0
    s1 s s2 hs1s hss2 p hp g hg u hu
  have hforce := localCoarseGrainingForcingLp_le_five_mul_gap_inv_mul_scale_mul_overlap
    Q n hn s1 s s2 hs1s hss2 p hp g hg
  have hnorm := localCoarseGraining_scale_normalizations s.2.1 hsigma0
  have hroot' := hroot
  rw [hnorm.1, hnorm.2.1, hnorm.2.2] at hroot'
  unfold localCoarseGrainingLpRHS
  change localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p ≤ _
  calc
    localFluxDefectNegativeBesovLpAverage Q n hn a sigma0 u s p ≤
        2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
          ((ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
              Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                Q n hn a sigma0 hsigma0 s1 *
              weightedLocalSymmetricEnergyLp Q n hn a u s1 s p +
            (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
              (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
              localCoarseGrainingForcingLp Q n s1 s p g) := hroot'
    _ ≤ C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
          Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
            Q n hn a sigma0 hsigma0 s1 *
          weightedLocalSymmetricEnergyLp Q n hn a u s1 s p +
        C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
          (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
          (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
            Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
          ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
          cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g := by
        rw [show C = (10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
            ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) by rfl]
        have hcoef := two_mul_le_ten_mul_three_pow_dim
          (ENNReal.ofReal (localCoarseGrainingOneCubeConstant d)) (d := d)
        have henergy :
            2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
                ((ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
                  Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                    Q n hn a sigma0 hsigma0 s1 *
                  weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) ≤
              C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
                Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                  Q n hn a sigma0 hsigma0 s1 *
                weightedLocalSymmetricEnergyLp Q n hn a u s1 s p := by
          calc
            2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
                ((ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
                  Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                    Q n hn a sigma0 hsigma0 s1 *
                  weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) =
                ((ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
                  Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                    Q n hn a sigma0 hsigma0 s1 *
                  weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) *
                  (2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d)) := by ring
            _ ≤ ((ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
                  Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                    Q n hn a sigma0 hsigma0 s1 *
                  weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) *
                  ((10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
                    ENNReal.ofReal (localCoarseGrainingOneCubeConstant d)) :=
                mul_le_mul_right hcoef _
            _ = _ := by
              rw [show C = (10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
                  ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) by rfl]
              ring
        have hforcing :
            2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
                ((ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
                  (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                    Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
                  localCoarseGrainingForcingLp Q n s1 s p g) ≤
              C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
                (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
                (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                  Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
                ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
                cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g := by
          have hgap : ENNReal.ofReal ((s2.1 - s.1)⁻¹) =
              (ENNReal.ofReal (s2.1 - s.1))⁻¹ :=
            ENNReal.ofReal_inv_of_pos (by linarith)
          rw [hgap] at hforce
          calc
            2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
                ((ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
                  (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                    Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
                  localCoarseGrainingForcingLp Q n s1 s p g) ≤
                2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
                  ((ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
                    (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                      Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
                    ((5 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
                      (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
                      ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
                      cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g)) := by
                gcongr
            _ = _ := by
              rw [show C = (10 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
                  ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) by rfl]
              norm_num
              ring
        calc
          2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
              ((ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
                Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                  Q n hn a sigma0 hsigma0 s1 *
                weightedLocalSymmetricEnergyLp Q n hn a u s1 s p +
              (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
                (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                  Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
                localCoarseGrainingForcingLp Q n s1 s p g) =
              (2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
                ((ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
                  Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
                    Q n hn a sigma0 hsigma0 s1 *
                  weightedLocalSymmetricEnergyLp Q n hn a u s1 s p)) +
              (2 * ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
                ((ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
                  (1 + (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
                    Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
                  localCoarseGrainingForcingLp Q n s1 s p g)) := by ring
          _ ≤ _ := add_le_add henergy hforcing


end

end ABK26
end Ch03
end Book
end Homogenization
