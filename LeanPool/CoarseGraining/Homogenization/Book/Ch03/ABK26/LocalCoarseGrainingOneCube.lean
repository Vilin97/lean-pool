/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingPDE
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingResponse
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.FinitePToLegacyQTwo
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutions
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletCorrectedWeakFluxAveraged
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-!
# One-cube local coarse-graining bridge

This file packages the source weak equation in the half-open cube carrier
required by the legacy corrected weak-flux apex.  Its source-facing theorem
will consume the strict finite-`p` regularity bridge, while the response-series
summability remains internal to the canonical root coefficient family.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The depth-zero `q = 2` partial negative seminorm contains the square root
of the squared norm of the cube average. -/
private theorem sqrt_vecNormSq_cubeAverageVec_le_negativePartial_zero
    {d : ℕ} (R : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    Real.sqrt (vecNormSq (cubeAverageVec R F)) ≤
      cubeBesovNegativeVectorPartialSeminormTwo R s 0 F := by
  have hsq :
      (Real.sqrt (vecNormSq (cubeAverageVec R F))) ^ 2 ≤
        (cubeBesovNegativeVectorPartialSeminormTwo R s 0 F) ^ 2 := by
    rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
    simp [sq_cubeBesovNegativeVectorDepthSeminorm_depth_zero]
  exact le_of_sq_le_sq hsq
    (cubeBesovNegativeVectorPartialSeminormTwo_nonneg R s 0 F)

/-- The norm of a cube average is bounded by the full finite `q = 2`
negative Besov seminorm whenever the field is locally `L²`. -/
theorem ENNReal_ofReal_norm_cubeAverageVec_le_cubeBesovNegativeVectorSeminormTwo
    {d : ℕ} (R : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (F : Vec d → Vec d)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    ENNReal.ofReal ‖cubeAverageVec R F‖ ≤
      ENNReal.ofReal (cubeBesovNegativeVectorSeminormTwo R s F) := by
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖cubeAverageVec R F‖ ≤ Real.sqrt (vecNormSq (cubeAverageVec R F)) :=
      norm_le_sqrt_vecNormSq _
    _ ≤ cubeBesovNegativeVectorPartialSeminormTwo R s 0 F :=
      sqrt_vecNormSq_cubeAverageVec_le_negativePartial_zero R s F
    _ ≤ cubeBesovNegativeVectorSeminormTwo R s F :=
      cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove R s F
        (cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs F hF) 0

/-- Replacing a coefficient representative almost everywhere on a cube leaves
the average flux defect unchanged. -/
theorem cubeAverageVec_fluxDefect_eq_of_ae_eq_on_cubeSet
    {d : ℕ} (R : TriadicCube d) (a b : CoeffField d) (a0 : Mat d)
    (gradU : Vec d → Vec d)
    (hab : a =ᵐ[MeasureTheory.volume.restrict (cubeSet R)] b) :
    cubeAverageVec R (fluxDefect a a0 gradU) =
      cubeAverageVec R (fluxDefect b a0 gradU) := by
  apply cubeAverageVec_eq_of_ae_eq_on_cubeSet
  filter_upwards [hab] with x hx
  simp only [fluxDefect, hx]

/-- The scalar background has at most the explicit dimension loss needed to
compare the legacy Frobenius norm with the Chapter 2 operator normalization. -/
private theorem matNorm_scalarMatrix_le_dim_mul
    {d : ℕ} [NeZero d] {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    matNorm (scalarMatrix (d := d) sigma) ≤ (d : ℝ) * sigma := by
  have hmatrixNorm :
      Book.Ch02.matrixNorm (scalarMatrix (d := d) sigma) = sigma := by
    simp [Book.Ch02.matrixNorm, scalarMatrix, hsigma]
  calc
    matNorm (scalarMatrix (d := d) sigma) ≤
        (d : ℝ) * Book.Ch02.matrixNorm (scalarMatrix (d := d) sigma) :=
      Book.Ch02.matNorm_le_dim_mul_matrixNorm _
    _ = (d : ℝ) * sigma := by rw [hmatrixNorm]

/-- Square-root version of `matNorm_scalarMatrix_le_dim_mul`, stated with a
deliberately coarse dimension factor that is uniform for every `d ≥ 1`. -/
private theorem sqrt_matNorm_scalarMatrix_le_dim_mul_sqrt
    {d : ℕ} [NeZero d] {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    Real.sqrt (matNorm (scalarMatrix (d := d) sigma)) ≤
      (d : ℝ) * Real.sqrt sigma := by
  have hd : 1 ≤ (d : ℝ) := by
    norm_num [Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hnorm := matNorm_scalarMatrix_le_dim_mul (d := d) hsigma
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (le_trans zero_le_one hd) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (matNorm_nonneg _), mul_pow, Real.sq_sqrt hsigma]
  nlinarith [mul_nonneg (sub_nonneg.mpr hd) hsigma]

/-- Chapter 2's finite-`q = 2` ellipticity control in the exact form consumed
by the two forcing components of the one-cube flux RHS. -/
private theorem qtwo_weighted_ellipticity_envelope
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {t sigma : ℝ} (ht : 0 < t) (hsigma : 0 < sigma) :
    sigma⁻¹ * Book.Ch02.LambdaSq R t (.finite 2) a +
        sigma * (Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹ ≤
      4 * (Fintype.card (Fin d) : ℝ) *
        ((Book.Ch02.HomogenizationErrorOnCube R t .infinity (.finite 2) a
          (scalarMatrix (d := d) sigma)) ^ 2 + 1) := by
  exact Book.Ch02.weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one
    R a ht hsigma

/-- The product of the normalized upper and lower finite-`q = 2` ellipticity
factors is bounded by the source-normalized local `q = 2` error envelope. -/
private theorem qtwo_sqrt_weighted_product_le_envelope
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {t sigma : ℝ} (ht : 0 < t) (hsigma : 0 < sigma) :
    Real.sqrt (sigma⁻¹ * Book.Ch02.LambdaSq R t (.finite 2) a) *
        Real.sqrt (sigma * (Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹) ≤
      4 * (Fintype.card (Fin d) : ℝ) *
        ((Book.Ch02.HomogenizationErrorOnCube R t .infinity (.finite 2) a
          (scalarMatrix (d := d) sigma)) ^ 2 + 1) := by
  have hsum := qtwo_weighted_ellipticity_envelope R a ht hsigma
  have hupper : 0 ≤ sigma⁻¹ * Book.Ch02.LambdaSq R t (.finite 2) a :=
    mul_nonneg (inv_nonneg.mpr hsigma.le)
      (Book.Ch02.LambdaSq_nonneg R a ht (by norm_num))
  have hlower : 0 ≤ sigma * (Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹ :=
    mul_nonneg hsigma.le
      (inv_nonneg.mpr (Book.Ch02.lambdaSq_nonneg R a ht (by norm_num)))
  have hsq :
      (Real.sqrt (sigma⁻¹ * Book.Ch02.LambdaSq R t (.finite 2) a) -
        Real.sqrt (sigma * (Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹)) ^ 2 ≥ 0 :=
    sq_nonneg _
  have hupper_sq :
      Real.sqrt (sigma⁻¹ * Book.Ch02.LambdaSq R t (.finite 2) a) ^ 2 =
        sigma⁻¹ * Book.Ch02.LambdaSq R t (.finite 2) a :=
    Real.sq_sqrt hupper
  have hlower_sq :
      Real.sqrt (sigma * (Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹) ^ 2 =
        sigma * (Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹ :=
    Real.sq_sqrt hlower
  have hupper_sqrt :
      0 ≤ Real.sqrt (sigma⁻¹ * Book.Ch02.LambdaSq R t (.finite 2) a) :=
    Real.sqrt_nonneg _
  have hlower_sqrt :
      0 ≤ Real.sqrt (sigma * (Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹) :=
    Real.sqrt_nonneg _
  nlinarith

/-- The `q=1` response error at order `s` is bounded by the `q=2` response
error at order `s/2`.  Both errors use the same geometric probability weights
after this order/exponent change, so this is weighted Cauchy--Schwarz. -/
private theorem homogenizationErrorOnCube_infinity_one_le_infinity_two_half
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
      Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a a0 := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s 1 n
  let M : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale R (R.scale - (n : ℤ)) a a0
  have hw_nonneg : ∀ n, 0 ≤ w n := by
    intro n
    dsimp [w]
    simpa [Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) n
        (by nlinarith : 0 ≤ s * 1))
  have hM_nonneg : ∀ n, 0 ≤ M n := by
    intro n
    dsimp [M]
    exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg R
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  have hw_eq : ∀ n, w n = Book.Ch02.geometricWeight (s / 2) 2 n := by
    intro n
    dsimp [w]
    unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount
    congr 1 <;> ring_nf
  have hsumw : Summable w := by
    simpa only [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight (s := s) (q := (1 : ℝ))
        (by nlinarith : 0 < s * 1))
  have hsumWM : Summable (fun n => w n * M n) := by
    simpa only [M, hw_eq] using
      (Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        R a a0 (by positivity : 0 < s / 2))
  let f : ℕ → ℝ := fun n => Real.sqrt (w n)
  let g : ℕ → ℝ := fun n => Real.sqrt (w n * M n)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => Real.sqrt_nonneg _
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => Real.sqrt_nonneg _
  have hf_sq : ∀ n, f n ^ (2 : ℝ) = w n := by
    intro n
    dsimp [f]
    rw [Real.rpow_two, Real.sq_sqrt (hw_nonneg n)]
  have hg_sq : ∀ n, g n ^ (2 : ℝ) = w n * M n := by
    intro n
    dsimp [g]
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hw_nonneg n) (hM_nonneg n))]
  have hfg : ∀ n, f n * g n = w n * Real.sqrt (M n) := by
    intro n
    dsimp [f, g]
    rw [Real.sqrt_mul (hw_nonneg n)]
    calc
      Real.sqrt (w n) * (Real.sqrt (w n) * Real.sqrt (M n)) =
          (Real.sqrt (w n)) ^ 2 * Real.sqrt (M n) := by ring
      _ = w n * Real.sqrt (M n) := by rw [Real.sq_sqrt (hw_nonneg n)]
  have hfsum : Summable fun n => f n ^ (2 : ℝ) := by
    convert hsumw using 1
    ext n
    exact hf_sq n
  have hgsum : Summable fun n => g n ^ (2 : ℝ) := by
    convert hsumWM using 1
    ext n
    exact hg_sq n
  have hholder : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  have hcs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hholder hf_nonneg hg_nonneg hfsum hgsum
  have hweights : ∑' n, w n = 1 := by
    simpa only [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.tsum_geometricWeight_eq_one (s := s) (q := (1 : ℝ))
        (by nlinarith : 0 < s * 1))
  have hleft : ∑' n, f n * g n =
      Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 := by
    rw [Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
    apply tsum_congr
    intro n
    rw [hfg]
    dsimp [w, M]
    rw [Real.sqrt_eq_rpow]
  have hright : (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a a0 := by
    unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
      Book.Ch02.HomogenizationErrorFinite
    change (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (∑' n, Book.Ch02.geometricWeight (s / 2) 2 n *
        (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ)) ^
        (1 / (2 : ℝ))
    congr 1
    apply tsum_congr
    intro n
    rw [hg_sq, hw_eq]
    have hk : R.scale - (n : ℤ) ≤ R.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hresponse : M n =
        (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ) := by
      dsimp [M]
      calc
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale R (R.scale - (n : ℤ)) a a0 =
            (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ 2 :=
          (Book.Ch02.scaleResponseAtScale_infinity_sq_eq R hk a a0).symm
        _ = (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) ^ (2 : ℝ) :=
          (Real.rpow_two _).symm
    exact congrArg (fun x : ℝ => Book.Ch02.geometricWeight (s / 2) 2 n * x)
      hresponse
  rw [← hleft]
  calc
    ∑' n, f n * g n ≤
        (∑' n, f n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' n, g n ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hcs
    _ = Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a a0 := by
      have hfs : ∑' n, f n ^ (2 : ℝ) = 1 := by
        calc
          ∑' n, f n ^ (2 : ℝ) = ∑' n, w n := by
            apply tsum_congr
            exact hf_sq
          _ = 1 := hweights
      rw [hfs, Real.one_rpow, one_mul, hright]

/-- For `0 < s ≤ 1`, the common `s^{-9/2}` forcing scale dominates both
legacy forcing exponents. -/
private theorem rpow_neg_five_halves_le_rpow_neg_nine_halves
    {s : ℝ} (hs : 0 < s) (hs_one : s ≤ 1) :
    Real.rpow s (-(5 / 2 : ℝ)) ≤ Real.rpow s (-(9 / 2 : ℝ)) := by
  exact Real.rpow_le_rpow_of_exponent_ge hs hs_one (by norm_num)

private theorem rpow_neg_three_le_rpow_neg_nine_halves
    {s : ℝ} (hs : 0 < s) (hs_one : s ≤ 1) :
    Real.rpow s (-3 : ℝ) ≤ Real.rpow s (-(9 / 2 : ℝ)) := by
  exact Real.rpow_le_rpow_of_exponent_ge hs hs_one (by norm_num)

/-- The concrete positive `q = 2` seminorm is insensitive to the sign of a
locally square-integrable vector field.  This is recorded here because the
source weak equation uses `-g`, whereas the source statement displays `g`. -/
private theorem cubeBesovPositiveVectorSeminormTwo_neg_of_memLp
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeBesovPositiveVectorSeminormTwo Q s (fun x => -g x) =
      cubeBesovPositiveVectorSeminormTwo Q s g := by
  unfold cubeBesovPositiveVectorSeminormTwo
  have hpartial : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => -g x) =
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
    intro N
    unfold cubeBesovPositiveVectorPartialSeminormTwo
    refine congrArg Real.sqrt ?_
    apply Finset.sum_congr rfl
    intro j _
    unfold cubeBesovPositiveVectorDepthSeminorm
    apply congrArg (fun x : ℝ =>
      (Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.sqrt x) ^ 2)
    unfold cubeBesovPositiveVectorDepthAverage
    dsimp only [descendantsAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro R hR
    have hRmem : MeasureTheory.MemLp g 2 (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg
    have hzero : MeasureTheory.MemLp (0 : Vec d → Vec d) 2
        (normalizedCubeMeasure R) := by simp
    have havg : cubeAverageVec R (fun x => -g x) = -cubeAverageVec R g := by
      have hzeroavg : cubeAverageVec R (0 : Vec d → Vec d) = 0 := by
        funext i
        simp [cubeAverageVec, cubeAverage]
      simpa [hzeroavg] using
        (cubeAverageVec_sub_memLp R (0 : Vec d → Vec d) g hzero hRmem)
    have hfluct : cubeFluctuationVec R (fun x => -g x) =
        fun x => -(cubeFluctuationVec R g x) := by
      funext x
      rw [cubeFluctuationVec_apply, cubeFluctuationVec_apply, havg]
      abel
    rw [hfluct]
    unfold cubeLpNorm
    change (MeasureTheory.eLpNorm (-(cubeFluctuationVec R g)) 2
      (normalizedCubeMeasure R)).toReal ^ 2 = _
    rw [MeasureTheory.eLpNorm_neg]
  simp_rw [hpartial]

/-- The deterministic apex constant is uniform over the manuscript range
`0 < s ≤ 1`; we record the endpoint form used by the source envelope. -/
private theorem zeroTraceDirichletCorrectedWeakFluxApexConstant_le_one
    {d : ℕ} (s : ℝ) (_hs : 0 < s) (hs_one : s ≤ 1) :
    _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s ≤
      _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 := by
  have hdisplay :
      _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d s ≤
        _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d 1 := by
    unfold _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexDisplayScale
    have hpow :
        (3 : ℝ) ^ ((d : ℝ) + s) ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (by linarith)
    have hinner :
        (3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2 ≤
          (3 : ℝ) ^ ((d : ℝ) + 1) * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg 2)
    exact mul_le_mul_of_nonneg_left hinner (by exact_mod_cast Nat.zero_le d)
  unfold _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant
  nlinarith

/-- Exact `ENNReal` expansion of the legacy one-cube RHS once its four real
components have been certified nonnegative.  The components respectively
contain the local energy, the `q=1` response error, and the two finite-`q=2`
forcing/ellipticity terms. -/
private theorem ENNReal_ofReal_coarseFluxResponseRHSBound_eq_components
    {d : ℕ} (R : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (henergy : 0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU)
    (hresponse : 0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak : 0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare : 0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g) :
    ENNReal.ofReal (coarseFluxResponseRHSBound R a a0 s gradU g) =
      ENNReal.ofReal (coarseFluxResponseRHSEnergyBound R a a0 s gradU) +
        ENNReal.ofReal (coarseFluxResponseRHSResponseCorrectionBound R a a0 s g) +
        ENNReal.ofReal (coarseFluxResponseRHSWeakFluxCorrectionBound R a s g) +
        ENNReal.ofReal (coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g) := by
  rw [coarseFluxResponseRHSBound_eq_component_sum]
  conv_lhs =>
    rw [show
      coarseFluxResponseRHSEnergyBound R a a0 s gradU +
          coarseFluxResponseRHSResponseCorrectionBound R a a0 s g +
          coarseFluxResponseRHSWeakFluxCorrectionBound R a s g +
          coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g =
        (coarseFluxResponseRHSEnergyBound R a a0 s gradU +
          coarseFluxResponseRHSResponseCorrectionBound R a a0 s g) +
          (coarseFluxResponseRHSWeakFluxCorrectionBound R a s g +
            coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g) by ring]
  rw [ENNReal.ofReal_add (add_nonneg henergy hresponse) (add_nonneg hweak hpoincare),
    ENNReal.ofReal_add henergy hresponse, ENNReal.ofReal_add hweak hpoincare]
  ring

/-- Expand the nonnegative one-cube response RHS in `ℝ≥0∞`.  This makes its
local energy term, `q = 1` response-error term, and the two finite-`q = 2`
forcing/ellipticity terms separately available to a later positive-norm
aggregation argument. -/
theorem ENNReal_ofReal_coarseFluxResponseRHSBound_eq_components_of_bddAbove
    {d : ℕ} (R : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradU g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    ENNReal.ofReal (coarseFluxResponseRHSBound R a a0 s gradU g) =
      ENNReal.ofReal (coarseFluxResponseRHSEnergyBound R a a0 s gradU) +
        ENNReal.ofReal (coarseFluxResponseRHSResponseCorrectionBound R a a0 s g) +
        ENNReal.ofReal (coarseFluxResponseRHSWeakFluxCorrectionBound R a s g) +
        ENNReal.ofReal (coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g) := by
  exact ENNReal_ofReal_coarseFluxResponseRHSBound_eq_components R a a0 s gradU g
    (coarseFluxResponseRHSEnergyBound_nonneg R a a0 gradU hs)
    (coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove R a a0 g hs hgBdd)
    (coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove R a g hs hgBdd)
    (coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove R a a0 g hs hgBdd)

/-- Transport the source-sign convention and the open-cube weak equation to
the half-open cube used by the legacy response theorem. -/
private theorem isH1DirichletRhsWeakSolutionOn_cubeSet_neg_of_isForcedEquation
    {d : ℕ} [NeZero d] {R : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)}
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (h : IsForcedEquation R a u g) :
    IsH1DirichletRhsWeakSolutionOn a.toCoeffField (cubeSet R) u.toCubeSet
      (fun x => -g x) := by
  exact isH1DirichletRhsWeakSolutionOn_cubeSet_of_openCubeSet
    (Q := R) (a := a.toCoeffField) (u := u) (g := fun x => -g x)
    h.toIsH1DirichletRhsWeakSolutionOnNeg

/-- A weak solution is unchanged when its coefficient field is replaced by an
almost-everywhere equal representative on the integration cube. -/
private theorem isH1DirichletRhsWeakSolutionOn_congr_coeff_ae
    {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    {u : H1Function U} {g : Vec d → Vec d}
    (h : IsH1DirichletRhsWeakSolutionOn a U u g)
    (hab : a =ᵐ[MeasureTheory.volume.restrict U] b) :
    IsH1DirichletRhsWeakSolutionOn b U u g := by
  intro phi
  calc
    ∫ x in U, vecDot (matVecMul (b x) (u.grad x))
        (phi.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
        (phi.toH1Function.grad x) ∂MeasureTheory.volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hab] with x hx
        simp only [hx]
    _ = ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂MeasureTheory.volume :=
      h phi

/-- The public pointwise field built from the canonical root family agrees
with the original source coefficient on its cube. -/
private theorem publicCoeffField_rootPointwise_ae_eq_source_cubeSet
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)) :
    publicCoeffField R (rootPointwiseCoeffFamily R a) =ᵐ[
      MeasureTheory.volume.restrict (cubeSet R)] a.toCoeffField := by
  have hpublic := publicCoeffField_ae_eq_cubeSet R (rootPointwiseCoeffFamily R a)
  have hroot := rootPointwiseCoeffFamily_root_aeeq R a
  have hroot' : (rootPointwiseCoeffFamily R a).coeffOn R |>.toCoeffField =ᵐ[
      MeasureTheory.volume.restrict (cubeSet R)] a.toCoeffField := by
    simpa only [Book.Ch02.CoeffOn.AEEq, Book.Ch02.cubeDomain_coe,
      volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hroot
  exact hpublic.trans hroot'

/-- The source local energy has the same `ℝ≥0∞` square-root representative as
the public pointwise coefficient used internally by the response machinery. -/
private theorem ENNReal_ofReal_sqrt_cubeAverage_public_energy_eq_localSymmetricEnergy
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) :
    ENNReal.ofReal
      (Real.sqrt (cubeAverage R
        (coefficientEnergyDensity
          (publicCoeffField R (rootPointwiseCoeffFamily R a)) u.toCubeSet.grad))) =
      localSymmetricEnergyENorm R a u := by
  have hAeq := publicCoeffField_rootPointwise_ae_eq_source_cubeSet R a
  have havg :
      cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (rootPointwiseCoeffFamily R a)) u.toCubeSet.grad) =
        cubeAverage R (coefficientEnergyDensity a.toCoeffField u.grad) := by
    apply cubeAverage_eq_of_ae_eq_on_cubeSet
    filter_upwards [hAeq] with x hx
    simp only [coefficientEnergyDensity, H1Function.grad_toCubeSet]
    rw [hx]
  have havg_nonneg :
      0 ≤ cubeAverage R (coefficientEnergyDensity a.toCoeffField u.grad) := by
    rw [← havg]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn R
      _ u.toCubeSet.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet R (rootPointwiseCoeffFamily R a))
  rw [havg, localSymmetricEnergyENorm_eq_ofReal_cubeAverage_coefficientEnergyDensity]
  rw [Real.sqrt_eq_rpow]
  rw [← ENNReal.ofReal_rpow_of_nonneg]
  · exact havg_nonneg
  · norm_num

/-- The finite-`q=2` lower ellipticity factor is its elementary square-root
form.  Keeping this local avoids exporting a Chapter 5 assembly lemma merely
for one-cube scalar algebra. -/
private theorem poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv_local
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {t : ℝ} :
    poincareLowerEllipticityFactor R a t (.finite 2) =
      Real.sqrt ((Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹) := by
  have hleft :
      Real.sqrt ((Book.Ch02.lambdaSq R t (.finite 2) a)⁻¹) =
        Real.rpow (Book.Ch02.lambdaSq R t (.finite 2) a) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  have hExp : (-1 / 2 : ℝ) = (-(1 / 2 : ℝ)) := by ring
  simpa [poincareLowerEllipticityFactor, hExp] using hleft.symm

private theorem poincareUpperEllipticityFactor_finite_two_eq_sqrt_local
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {t : ℝ} :
    poincareUpperEllipticityFactor R a t (.finite 2) =
      Real.sqrt (Book.Ch02.LambdaSq R t (.finite 2) a) := by
  simp [poincareUpperEllipticityFactor, Real.sqrt_eq_rpow]

/-- The response-error/lower-ellipticity product is absorbed by the source
finite-`q=2` ellipticity envelope at order `s/2`. -/
private theorem sqrt_sigma_mul_lower_mul_homogenizationError_le_qtwo_envelope
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) (sigma : ℝ)
    {s : ℝ} (hs : 0 < s) (_hs_one : s ≤ 1) (hsigma : 0 < sigma) :
    Real.sqrt sigma *
        poincareLowerEllipticityFactor R a (s / 2) (.finite 2) *
        Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a
          (scalarMatrix (d := d) sigma) ≤
      4 * (Fintype.card (Fin d) : ℝ) *
        ((Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a
          (scalarMatrix (d := d) sigma)) ^ 2 + 1) := by
  let E : ℝ := Book.Ch02.HomogenizationErrorOnCube R (s / 2) .infinity (.finite 2) a
    (scalarMatrix (d := d) sigma)
  let L : ℝ := (Book.Ch02.lambdaSq R (s / 2) (.finite 2) a)⁻¹
  let X : ℝ := Real.sqrt (sigma * L)
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, Book.Ch02.HomogenizationErrorOnCube,
      Book.Ch02.HomogenizationError, Book.Ch02.HomogenizationErrorFinite]
    exact Real.rpow_nonneg (tsum_nonneg fun n =>
      mul_nonneg
        (by
          simpa [Book.Ch02.geometricWeight_eq_old] using
            Homogenization.geometricWeight_nonneg (s := s / 2) (q := (2 : ℝ)) n
              (by positivity : 0 ≤ (s / 2) * (2 : ℝ)))
        (Real.rpow_nonneg
          (Book.Ch02.scaleResponseAtScale_infinity_nonneg R
            (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
            (scalarMatrix (d := d) sigma)) _)) _
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr (Book.Ch02.lambdaSq_finite_nonneg R a (by positivity) (by norm_num))
  have hX_nonneg : 0 ≤ X := Real.sqrt_nonneg _
  have hweighted := qtwo_weighted_ellipticity_envelope R a (t := s / 2) (by positivity) hsigma
  have hXL_sq : X ^ 2 = sigma * L := by
    dsimp [X]
    rw [Real.sq_sqrt (mul_nonneg hsigma.le hL_nonneg)]
  have hX_sq : X ^ 2 ≤ 4 * (Fintype.card (Fin d) : ℝ) * (E ^ 2 + 1) := by
    rw [hXL_sq]
    have hupper : 0 ≤ sigma⁻¹ * Book.Ch02.LambdaSq R (s / 2) (.finite 2) a :=
      mul_nonneg (inv_nonneg.mpr hsigma.le)
        (Book.Ch02.LambdaSq_finite_nonneg R a (s := s / 2) (q := (2 : ℝ))
          (by positivity) (by norm_num : (1 : ℝ) ≤ 2))
    dsimp [E, L]
    simpa only [Book.Ch02.LambdaSq_finite, Book.Ch02.lambdaSq_finite] using
      (le_add_of_nonneg_left hupper).trans hweighted
  have hcard : 1 ≤ (Fintype.card (Fin d) : ℝ) := by
    norm_num [Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hXE : X * E ≤ 4 * (Fintype.card (Fin d) : ℝ) * (E ^ 2 + 1) := by
    have hyoung := two_mul_le_add_sq X E
    have hE_sq_le : E ^ 2 ≤ E ^ 2 + 1 := by linarith
    nlinarith [hX_sq]
  have herror := homogenizationErrorOnCube_infinity_one_le_infinity_two_half R a
    (scalarMatrix (d := d) sigma) hs
  have hroot :
      Real.sqrt sigma * poincareLowerEllipticityFactor R a (s / 2) (.finite 2) = X := by
    rw [poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv_local]
    dsimp [X, L]
    rw [Real.sqrt_mul hsigma.le]
  rw [hroot]
  exact (mul_le_mul_of_nonneg_left herror hX_nonneg).trans hXE

/-- A single explicit dimension-only envelope for the four one-cube terms.
The deterministic apex constant is evaluated at the fixed endpoint `1`, so
this quantity is uniform in every local fractional order. -/
noncomputable def localCoarseGrainingOneCubeConstant (d : ℕ) : ℝ :=
  64 * (d : ℝ) ^ 3 *
    (_root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 + 1)

private theorem localCoarseGrainingOneCubeConstant_nonneg (d : ℕ) :
    0 ≤ localCoarseGrainingOneCubeConstant d := by
  unfold localCoarseGrainingOneCubeConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg d) _))
    (add_nonneg
      (_root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg d 1)
      zero_le_one)

private theorem localCoarseGrainingOneCubeConstant_dominates_energy
    {d : ℕ} [NeZero d]
    (X : ℝ) (hX : 0 ≤ X) :
    (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ)) * X ≤
      localCoarseGrainingOneCubeConstant d * (X + 0) := by
  have hd : 1 ≤ (d : ℝ) := by
    norm_num [Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hM := _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg d 1
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    calc
      (d : ℝ) = (d : ℝ) * 1 := by ring
      _ ≤ (d : ℝ) * (d : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hd : 1 ≤ (d : ℝ) ^ 2) hd0
      _ = (d : ℝ) ^ 3 := by ring
  have hcoef : 2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ≤ localCoarseGrainingOneCubeConstant d := by
    unfold localCoarseGrainingOneCubeConstant
    have hd30 : 0 ≤ (d : ℝ) ^ 3 := pow_nonneg hd0 _
    calc
      2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ≤
          2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_left hd3 (mul_nonneg (by norm_num) hM)
      _ ≤ 64 * (d : ℝ) ^ 3 *
          (_root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 + 1) := by
        nlinarith
  simpa using mul_le_mul_of_nonneg_right hcoef hX

private theorem localCoarseGrainingOneCubeConstant_dominates_forcing
    {d : ℕ} [NeZero d]
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ)) * X +
        (24 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ^ 3) * Y ≤
      localCoarseGrainingOneCubeConstant d * (X + Y) := by
  have hd : 1 ≤ (d : ℝ) := by
    norm_num [Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hM := _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg d 1
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    calc
      (d : ℝ) = (d : ℝ) * 1 := by ring
      _ ≤ (d : ℝ) * (d : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hd : 1 ≤ (d : ℝ) ^ 2) hd0
      _ = (d : ℝ) ^ 3 := by ring
  have henergy : 2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ≤ localCoarseGrainingOneCubeConstant d := by
    unfold localCoarseGrainingOneCubeConstant
    have hd30 : 0 ≤ (d : ℝ) ^ 3 := pow_nonneg hd0 _
    calc
      2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ≤
          2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_left hd3 (mul_nonneg (by norm_num) hM)
      _ ≤ 64 * (d : ℝ) ^ 3 *
          (_root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 + 1) := by
        nlinarith
  have hforcing : 24 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ^ 3 ≤
      localCoarseGrainingOneCubeConstant d := by
    unfold localCoarseGrainingOneCubeConstant
    have hd30 : 0 ≤ (d : ℝ) ^ 3 := pow_nonneg hd0 _
    nlinarith
  calc
    (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ)) * X +
        (24 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1 * (d : ℝ) ^ 3) * Y ≤
      localCoarseGrainingOneCubeConstant d * X +
        localCoarseGrainingOneCubeConstant d * Y :=
      add_le_add (mul_le_mul_of_nonneg_right henergy hX)
        (mul_le_mul_of_nonneg_right hforcing hY)
    _ = localCoarseGrainingOneCubeConstant d * (X + Y) := by ring

/-- Apply the legacy corrected weak-flux apex once its entirely internal
half-open-cube carriers have been constructed.  This helper deliberately
keeps those carriers private: no source-facing hypothesis is introduced while
the `CoeffOn` response-summability bridge is unavailable. -/
private theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_legacyApex_of_legacyCarriers
    {d : ℕ} [NeZero d] {R : TriadicCube d}
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (aLegacy : CoeffField d) (a0 : Mat d) (s : ℝ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) aLegacy)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hweak : IsH1DirichletRhsWeakSolutionOn aLegacy (cubeSet R) u.toCubeSet
      (fun x => -g x))
    (hregularity : CubeVectorBesovHRegularity R s (fun x => -g x))
    (hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity aLegacy a0)) :
    cubeBesovNegativeVectorSeminormTwo R s
        (fluxDefect aLegacy a0 u.toCubeSet.grad) ≤
      2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
        coarseFluxResponseRHSBound R aLegacy a0 s u.toCubeSet.grad (fun x => -g x) :=
  _root_.Homogenization.ZeroTraceDirichletCorrectorData.cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_h1DirichletRhsWeakSolutionOn_correctedWeakFlux_averagedCorrectorEnergy
      (Q := R) (a := aLegacy) (a0 := a0) (s := s) (g := fun x => -g x)
      (v := u.toCubeSet) hs hs_le hEll ha0 ha0symm hweak hregularity hresponseSum

/-- Source-to-legacy carrier assembly for one cube.  The only remaining
input is the local positive-Besov regularity of the source; Packet F supplies
that bridge from the frozen finite-`p` source hypothesis. -/
private theorem cubeBesovNegativeVectorSeminormTwo_source_fluxDefect_le_legacyApex
    {d : ℕ} [NeZero d] {R : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)}
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (sigma0 s : ℝ) (hsigma0 : 0 < sigma0) (hs : 0 < s) (hs_le : s ≤ 1)
    (h : IsForcedEquation R a u g)
    (hregularity : CubeVectorBesovHRegularity R s (fun x => -g x)) :
    cubeBesovNegativeVectorSeminormTwo R s
        (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad) ≤
      2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
        coarseFluxResponseRHSBound R (publicCoeffField R (rootPointwiseCoeffFamily R a))
          (scalarMatrix (d := d) sigma0) s u.toCubeSet.grad (fun x => -g x) := by
  let aFam : CoeffFamily d := rootPointwiseCoeffFamily R a
  let A : CoeffField d := publicCoeffField R aFam
  have hAeq : A =ᵐ[MeasureTheory.volume.restrict (cubeSet R)] a.toCoeffField := by
    simpa only [A, aFam] using publicCoeffField_rootPointwise_ae_eq_source_cubeSet R a
  have hweakSource :
      IsH1DirichletRhsWeakSolutionOn a.toCoeffField (cubeSet R) u.toCubeSet
        (fun x => -g x) :=
    isH1DirichletRhsWeakSolutionOn_cubeSet_neg_of_isForcedEquation h
  have hweak :
      IsH1DirichletRhsWeakSolutionOn A (cubeSet R) u.toCubeSet
        (fun x => -g x) :=
    isH1DirichletRhsWeakSolutionOn_congr_coeff_ae hweakSource hAeq.symm
  have hEll : IsEllipticFieldOn (aFam.coeffOn R).lam (aFam.coeffOn R).Lam
      (cubeSet R) A := by
    simpa only [A] using publicCoeffField_isEllipticFieldOn_cubeSet R aFam
  have hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity A
            (scalarMatrix (d := d) sigma0)) := by
    simpa only [A] using
      homogenizationErrorOnCube_publicCoeffField_infinity_one_terms_summable
        aFam R (scalarMatrix (d := d) sigma0) hs
  have hApex := cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_legacyApex_of_legacyCarriers
    (u := u) (g := g) A (scalarMatrix (d := d) sigma0) s hs hs_le hEll
    (isEllipticMatrix_scalarMatrix hsigma0) (scalarMatrix_isSymm sigma0) hweak
    hregularity hresponseSum
  have hflux :
      fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad =ᵐ[
        MeasureTheory.volume.restrict (cubeSet R)]
      fluxDefect A (scalarMatrix (d := d) sigma0) u.toCubeSet.grad := by
    filter_upwards [hAeq] with x hx
    simp only [fluxDefect, hx]
  rw [cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet s hflux]
  exact hApex

private theorem memVectorL2_source_fluxDefect_openCubeSet
    {d : ℕ} (R : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)) (sigma0 : ℝ)
    (u : H1Function (openCubeSet R)) :
    MemVectorL2 (openCubeSet R)
      (fun x => matVecMul
        (a.toCoeffField x - scalarMatrix (d := d) sigma0) (u.grad x)) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain R) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet R) b.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Book.Ch02.cubeDomain R) a
  have hflux : MemVectorL2 (openCubeSet R)
      (fun x => matVecMul (b.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hscalar : MemVectorL2 (openCubeSet R)
      (fun x => sigma0 • u.grad x) :=
    u.grad_memVectorL2.const_smul sigma0
  have hsub := hflux.sub hscalar
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)] a.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain R) a
  apply (memLp_congr_ae ?_).mp
    (by simpa only [sub_matVecMul, matVecMul_scalarMatrix] using hsub)
  filter_upwards [hba] with x hx
  simp only [Pi.sub_apply, hx, sub_matVecMul, matVecMul_scalarMatrix]

/-- The source coefficient and weak-equation carriers already suffice to
control the cube-average flux defect by the deterministic one-cube RHS.  The
Besov regularity argument is deliberately private here: the strict finite-`p`
bridge will supply it from the frozen source carrier, rather than exposing a
legacy boundedness or summability premise in the eventual public theorem. -/
private theorem ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_legacyApex
    {d : ℕ} [NeZero d] {R : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)}
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (sigma0 s : ℝ) (hsigma0 : 0 < sigma0) (hs : 0 < s) (hs_le : s ≤ 1)
    (h : IsForcedEquation R a u g)
    (hregularity : CubeVectorBesovHRegularity R s (fun x => -g x)) :
    ENNReal.ofReal ‖cubeAverageVec R
        (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)‖ ≤
      ENNReal.ofReal
        (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
          coarseFluxResponseRHSBound R
            (publicCoeffField R (rootPointwiseCoeffFamily R a))
            (scalarMatrix (d := d) sigma0) s u.toCubeSet.grad (fun x => -g x)) := by
  have hmemOpen : MemVectorL2 (openCubeSet R)
      (fun x => matVecMul
        (a.toCoeffField x - scalarMatrix (d := d) sigma0) (u.grad x)) :=
    memVectorL2_source_fluxDefect_openCubeSet R a sigma0 u
  have hmemCube : MemVectorL2 (cubeSet R)
      (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad) := by
    simpa only [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet, fluxDefect,
      H1Function.grad_toCubeSet, sub_matVecMul] using! hmemOpen
  have hmem : MemLp
      (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R hmemCube
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖cubeAverageVec R
        (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)‖ ≤
        cubeBesovNegativeVectorSeminormTwo R s
          (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad) :=
      (ENNReal.ofReal_le_ofReal_iff
        (cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp R hs _ hmem)).mp
        (ENNReal_ofReal_norm_cubeAverageVec_le_cubeBesovNegativeVectorSeminormTwo
          R hs _ hmem)
    _ ≤ 2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
          coarseFluxResponseRHSBound R
            (publicCoeffField R (rootPointwiseCoeffFamily R a))
            (scalarMatrix (d := d) sigma0) s u.toCubeSet.grad (fun x => -g x) :=
      cubeBesovNegativeVectorSeminormTwo_source_fluxDefect_le_legacyApex
        sigma0 s hsigma0 hs hs_le h hregularity

/-- The source finite-`p` fractional-Sobolev datum supplies every regularity
input of the deterministic one-cube flux estimate.  In particular, this
public bridge has no auxiliary boundedness, summability, weak-solution, or
ellipticity hypotheses: each is constructed internally from `CoeffOn` and
`IsForcedEquation`. -/
theorem ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_legacyApex_of_memCubeEuclideanFullWsp
    {d : ℕ} [NeZero d] {R : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)}
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s s2 : FractionalOrder) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (hss2 : s.1 < s2.1)
    (hg : MemCubeEuclideanFullWsp R s2 p g)
    (h : IsForcedEquation R a u g) :
    ENNReal.ofReal ‖cubeAverageVec R
        (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)‖ ≤
      ENNReal.ofReal
        (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1 *
          coarseFluxResponseRHSBound R
            (publicCoeffField R (rootPointwiseCoeffFamily R a))
            (scalarMatrix (d := d) sigma0) s.1 u.toCubeSet.grad (fun x => -g x)) := by
  exact ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_legacyApex
    sigma0 s.1 hsigma0 s.2.1 s.2.2.le h
    (hg.toCubeVectorBesovHRegularity_neg_of_lt hp hss2)

/-- Exact four-component form of the source one-cube estimate.  This is the
direct handoff for the finite-`p` aggregation: the legacy boundedness witness
needed to expand the RHS is constructed from the strict source Sobolev
carrier, and is not exposed as a public premise. -/
theorem ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_legacyApex_components_of_memCubeEuclideanFullWsp
    {d : ℕ} [NeZero d] {R : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)}
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s s2 : FractionalOrder) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (hss2 : s.1 < s2.1)
    (hg : MemCubeEuclideanFullWsp R s2 p g)
    (h : IsForcedEquation R a u g) :
    ENNReal.ofReal ‖cubeAverageVec R
        (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)‖ ≤
      ENNReal.ofReal
        (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
        (ENNReal.ofReal (coarseFluxResponseRHSEnergyBound R
            (publicCoeffField R (rootPointwiseCoeffFamily R a))
            (scalarMatrix (d := d) sigma0) s.1 u.toCubeSet.grad) +
          ENNReal.ofReal (coarseFluxResponseRHSResponseCorrectionBound R
            (publicCoeffField R (rootPointwiseCoeffFamily R a))
            (scalarMatrix (d := d) sigma0) s.1 (fun x => -g x)) +
          ENNReal.ofReal (coarseFluxResponseRHSWeakFluxCorrectionBound R
            (publicCoeffField R (rootPointwiseCoeffFamily R a)) s.1 (fun x => -g x)) +
          ENNReal.ofReal (coarseFluxResponseRHSPoincareCorrectionBound R
            (publicCoeffField R (rootPointwiseCoeffFamily R a))
            (scalarMatrix (d := d) sigma0) s.1 (fun x => -g x))) := by
  let hreg : CubeVectorBesovHRegularity R s.1 (fun x => -g x) :=
    hg.toCubeVectorBesovHRegularity_neg_of_lt hp hss2
  let A : CoeffField d := publicCoeffField R (rootPointwiseCoeffFamily R a)
  let a0 : Mat d := scalarMatrix (d := d) sigma0
  let C : ℝ := 2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1
  let B : ℝ := coarseFluxResponseRHSBound R A a0 s.1 u.toCubeSet.grad (fun x => -g x)
  have hC : 0 ≤ C := mul_nonneg (by norm_num)
    (_root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg d s.1)
  have hB : 0 ≤ B := by
    dsimp [B, A, a0]
    exact coarseFluxResponseRHSBound_nonneg_of_bddAbove R
      (publicCoeffField R (rootPointwiseCoeffFamily R a))
      (scalarMatrix (d := d) sigma0) u.toCubeSet.grad (fun x => -g x)
      s.2.1 hreg.partialSeminorms_bddAbove
  have hsplit : ENNReal.ofReal B =
      ENNReal.ofReal (coarseFluxResponseRHSEnergyBound R A a0 s.1 u.toCubeSet.grad) +
        ENNReal.ofReal (coarseFluxResponseRHSResponseCorrectionBound R A a0 s.1 (fun x => -g x)) +
        ENNReal.ofReal (coarseFluxResponseRHSWeakFluxCorrectionBound R A s.1 (fun x => -g x)) +
        ENNReal.ofReal (coarseFluxResponseRHSPoincareCorrectionBound R A a0 s.1 (fun x => -g x)) := by
    dsimp [B]
    exact ENNReal_ofReal_coarseFluxResponseRHSBound_eq_components_of_bddAbove
      R A a0 u.toCubeSet.grad (fun x => -g x) s.2.1 hreg.partialSeminorms_bddAbove
  have hapex := ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_legacyApex_of_memCubeEuclideanFullWsp
    sigma0 hsigma0 s s2 p hp hss2 hg h
  calc
    ENNReal.ofReal ‖cubeAverageVec R
        (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)‖ ≤
        ENNReal.ofReal (C * B) := by simpa only [C, B, A, a0] using hapex
    _ = ENNReal.ofReal C * ENNReal.ofReal B := ENNReal.ofReal_mul hC
    _ = ENNReal.ofReal C *
        (ENNReal.ofReal (coarseFluxResponseRHSEnergyBound R A a0 s.1 u.toCubeSet.grad) +
          ENNReal.ofReal (coarseFluxResponseRHSResponseCorrectionBound R A a0 s.1 (fun x => -g x)) +
          ENNReal.ofReal (coarseFluxResponseRHSWeakFluxCorrectionBound R A s.1 (fun x => -g x)) +
          ENNReal.ofReal (coarseFluxResponseRHSPoincareCorrectionBound R A a0 s.1 (fun x => -g x))) := by rw [hsplit]
    _ = _ := by rfl

/-- Fully absorbed source-facing one-cube estimate.  The `q=1` response term
and all three ellipticity corrections are internal consequences of the
canonical root family; the displayed forcing seminorm has the manuscript sign
convention. -/
theorem ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_localCoarseGrainingOneCube
    {d : ℕ} [NeZero d] {R : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R)}
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s s2 : FractionalOrder) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (hss2 : s.1 < s2.1)
    (hg : MemCubeEuclideanFullWsp R s2 p g)
    (h : IsForcedEquation R a u g) :
    ENNReal.ofReal ‖cubeAverageVec R
        (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)‖ ≤
      ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) *
        (ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
            ENNReal.ofReal (Book.Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 1)
              (rootPointwiseCoeffFamily R a) (scalarMatrix (d := d) sigma0)) *
            localSymmetricEnergyENorm R a u +
          ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
            (1 + ENNReal.ofReal
              (Book.Ch02.HomogenizationErrorOnCube R (s.1 / 2) .infinity (.finite 2)
                (rootPointwiseCoeffFamily R a) (scalarMatrix (d := d) sigma0)) ^ 2) *
            ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) := by
  let A : CoeffField d := publicCoeffField R (rootPointwiseCoeffFamily R a)
  let a0 : Mat d := scalarMatrix (d := d) sigma0
  let H1 : ℝ := Book.Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 1)
    (rootPointwiseCoeffFamily R a) a0
  let H2 : ℝ := Book.Ch02.HomogenizationErrorOnCube R (s.1 / 2) .infinity (.finite 2)
    (rootPointwiseCoeffFamily R a) a0
  let E : ℝ := Real.sqrt (cubeAverage R (coefficientEnergyDensity A u.toCubeSet.grad))
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo R s.1 g
  let M : ℝ := _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d 1
  let X : ℝ := s.1⁻¹ * Real.sqrt sigma0 * H1 * E
  let Y : ℝ := Real.rpow s.1 (-(9 / 2 : ℝ)) * (H2 ^ 2 + 1) * B
  have hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo R s.1 N g) :=
    cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_memLp_finiteP
      R s s2 hss2 p hp g hg
  have hBneg : cubeBesovPositiveVectorSeminormTwo R s.1 (fun x => -g x) = B := by
    dsimp [B]
    exact cubeBesovPositiveVectorSeminormTwo_neg_of_memLp R s.1 g
      (MemCubeEuclideanFullWsp.memLpTwo hp hg)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove R s.1 g hBdd
  have hH1_nonneg : 0 ≤ H1 := by
    dsimp [H1, a0]
    exact Book.Ch02.HomogenizationErrorOnCube_infinity_one_nonneg R
      (rootPointwiseCoeffFamily R a) (scalarMatrix (d := d) sigma0) s.2.1
  have hH2_nonneg : 0 ≤ H2 := by
    dsimp [H2, a0, Book.Ch02.HomogenizationErrorOnCube,
      Book.Ch02.HomogenizationError, Book.Ch02.HomogenizationErrorFinite]
    apply Real.rpow_nonneg
    apply tsum_nonneg
    intro j
    apply mul_nonneg
    · simpa [Book.Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s.1 / 2) (q := (2 : ℝ)) j
          (by nlinarith [s.2.1.le] : 0 ≤ (s.1 / 2) * (2 : ℝ)))
    · exact Real.rpow_nonneg
        (Book.Ch02.scaleResponseAtScale_infinity_nonneg R (by omega)
          (rootPointwiseCoeffFamily R a) (scalarMatrix (d := d) sigma0)) _
  have hE_nonneg : 0 ≤ E := Real.sqrt_nonneg _
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hs_inv_nonneg : 0 ≤ s.1⁻¹ := inv_nonneg.mpr s.2.1.le
  have hrpow52_nonneg : 0 ≤ Real.rpow s.1 (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg s.2.1.le _
  have hrpow9_nonneg : 0 ≤ Real.rpow s.1 (-(9 / 2 : ℝ)) :=
    Real.rpow_nonneg s.2.1.le _
  have hrpow3_nonneg : 0 ≤ Real.rpow s.1 (-3 : ℝ) :=
    Real.rpow_nonneg s.2.1.le _
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (mul_nonneg (mul_nonneg hs_inv_nonneg (Real.sqrt_nonneg _)) hH1_nonneg) hE_nonneg
  have hY_nonneg : 0 ≤ Y := by
    dsimp [Y]
    exact mul_nonneg (mul_nonneg hrpow9_nonneg (by nlinarith [sq_nonneg H2])) hB_nonneg
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg d 1
  have hC : 2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1 ≤
      2 * M := by
    dsimp [M]
    exact mul_le_mul_of_nonneg_left
      (zeroTraceDirichletCorrectedWeakFluxApexConstant_le_one s.1 s.2.1 s.2.2.le)
      (by norm_num)
  have hmat : Real.sqrt (matNorm a0) ≤ (d : ℝ) * Real.sqrt sigma0 := by
    dsimp [a0]
    exact sqrt_matNorm_scalarMatrix_le_dim_mul_sqrt hsigma0.le
  have hpow52 : Real.rpow s.1 (-(5 / 2 : ℝ)) ≤ Real.rpow s.1 (-(9 / 2 : ℝ)) :=
    rpow_neg_five_halves_le_rpow_neg_nine_halves s.2.1 s.2.2.le
  have hpow3 : Real.rpow s.1 (-3 : ℝ) ≤ Real.rpow s.1 (-(9 / 2 : ℝ)) :=
    rpow_neg_three_le_rpow_neg_nine_halves s.2.1 s.2.2.le
  have hresponseEnvelope : Real.sqrt sigma0 *
      poincareLowerEllipticityFactor R (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2) * H1 ≤
      4 * (d : ℝ) * (H2 ^ 2 + 1) := by
    simpa only [H1, H2, a0, Fintype.card_fin] using
      sqrt_sigma_mul_lower_mul_homogenizationError_le_qtwo_envelope R
        (rootPointwiseCoeffFamily R a) sigma0 s.2.1 s.2.2.le hsigma0
  have hweakEnvelope :
      Real.sqrt (Book.Ch02.LambdaSq R (s.1 / 2) (.finite 2)
        (rootPointwiseCoeffFamily R a)) *
      Real.sqrt ((Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
        (rootPointwiseCoeffFamily R a))⁻¹) ≤
      4 * (d : ℝ) * (H2 ^ 2 + 1) := by
    have hnormalized := qtwo_sqrt_weighted_product_le_envelope R
      (rootPointwiseCoeffFamily R a) (t := s.1 / 2) (by linarith [s.2.1]) hsigma0
    have hcancel :
        Real.sqrt (sigma0⁻¹ * Book.Ch02.LambdaSq R (s.1 / 2) (.finite 2)
            (rootPointwiseCoeffFamily R a)) *
          Real.sqrt (sigma0 * (Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
            (rootPointwiseCoeffFamily R a))⁻¹) =
        Real.sqrt (Book.Ch02.LambdaSq R (s.1 / 2) (.finite 2)
            (rootPointwiseCoeffFamily R a)) *
          Real.sqrt ((Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
            (rootPointwiseCoeffFamily R a))⁻¹) := by
      rw [Real.sqrt_mul (inv_nonneg.mpr hsigma0.le),
        Real.sqrt_mul hsigma0.le, Real.sqrt_inv]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hsigma0)]
    rw [hcancel] at hnormalized
    simpa only [H2, a0, Fintype.card_fin] using hnormalized
  have hpoincareEnvelope : sigma0 *
      (Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
        (rootPointwiseCoeffFamily R a))⁻¹ ≤
      4 * (d : ℝ) * (H2 ^ 2 + 1) := by
    have hweighted := qtwo_weighted_ellipticity_envelope R
      (rootPointwiseCoeffFamily R a) (t := s.1 / 2) (by linarith [s.2.1]) hsigma0
    have hupper : 0 ≤ sigma0⁻¹ * Book.Ch02.LambdaSq R (s.1 / 2) (.finite 2)
        (rootPointwiseCoeffFamily R a) :=
      mul_nonneg (inv_nonneg.mpr hsigma0.le)
        (Book.Ch02.LambdaSq_finite_nonneg R (rootPointwiseCoeffFamily R a)
          (by linarith [s.2.1]) (by norm_num))
    simpa only [H2, a0, Fintype.card_fin] using (le_add_of_nonneg_left hupper).trans hweighted
  have hH1eq : HomogenizationErrorOnCube R s.1 .infinity (.finite 1) A a0 = H1 := by
    dsimp [A, H1]
    exact homogenizationErrorOnCube_publicCoeffField_infinity_one_eq_ch02
      (rootPointwiseCoeffFamily R a) R s.1 a0
  have hlowerBridge : Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) ≤
      (d : ℝ) * poincareLowerEllipticityFactor R (rootPointwiseCoeffFamily R a)
        (s.1 / 2) (.finite 2) := by
    dsimp [A]
    exact sqrt_lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_poincareLowerEllipticityFactor
      R (rootPointwiseCoeffFamily R a) (by linarith [s.2.1])
  have hupperBridge : Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) ≤
      (d : ℝ) * poincareUpperEllipticityFactor R (rootPointwiseCoeffFamily R a)
        (s.1 / 2) (.finite 2) := by
    dsimp [A]
    exact sqrt_LambdaSq_publicCoeffField_finite_two_le_dim_mul_poincareUpperEllipticityFactor
      R (rootPointwiseCoeffFamily R a) (by linarith [s.2.1])
  have hinvBridge : (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹ ≤
      (d : ℝ) * (Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
        (rootPointwiseCoeffFamily R a))⁻¹ := by
    dsimp [A]
    simpa [lambdaSq, Book.Ch02.lambdaSq, Real.rpow_neg_one] using
      lambdaSq_publicCoeffField_finite_two_inv_le_dim_mul_public_rpow_neg_one
        R (rootPointwiseCoeffFamily R a) (s := s.1 / 2) (by linarith [s.2.1])
  have hupper_nonneg : 0 ≤ poincareUpperEllipticityFactor R
      (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2) := by
    rw [poincareUpperEllipticityFactor_finite_two_eq_sqrt_local]
    exact Real.sqrt_nonneg _
  have hlower_nonneg : 0 ≤ poincareLowerEllipticityFactor R
      (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2) := by
    rw [poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv_local]
    exact Real.sqrt_nonneg _
  have hresponseRaw : Real.sqrt (matNorm a0) *
      Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1 ≤
      4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1) := by
    have hprod : Real.sqrt (matNorm a0) *
        Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) ≤
        ((d : ℝ) * Real.sqrt sigma0) *
          ((d : ℝ) * poincareLowerEllipticityFactor R
            (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2)) :=
      mul_le_mul hmat hlowerBridge (Real.sqrt_nonneg _)
        (mul_nonneg hd_nonneg (Real.sqrt_nonneg _))
    calc
      Real.sqrt (matNorm a0) *
          Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1 ≤
          (((d : ℝ) * Real.sqrt sigma0) *
            ((d : ℝ) * poincareLowerEllipticityFactor R
              (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2))) * H1 :=
        mul_le_mul_of_nonneg_right hprod hH1_nonneg
      _ = (d : ℝ) ^ 2 *
          (Real.sqrt sigma0 * poincareLowerEllipticityFactor R
            (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2) * H1) := by ring
      _ ≤ (d : ℝ) ^ 2 * (4 * (d : ℝ) * (H2 ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hresponseEnvelope (sq_nonneg _)
      _ = 4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1) := by ring
  have hweakRaw : Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
      Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) ≤
      4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1) := by
    have hprod : Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
        Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) ≤
        ((d : ℝ) * poincareUpperEllipticityFactor R
          (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2)) *
        ((d : ℝ) * poincareLowerEllipticityFactor R
          (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2)) :=
      mul_le_mul hupperBridge hlowerBridge (Real.sqrt_nonneg _)
        (mul_nonneg hd_nonneg hupper_nonneg)
    have hpublic : poincareUpperEllipticityFactor R (rootPointwiseCoeffFamily R a)
        (s.1 / 2) (.finite 2) * poincareLowerEllipticityFactor R
          (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2) ≤
        4 * (d : ℝ) * (H2 ^ 2 + 1) := by
      rw [poincareUpperEllipticityFactor_finite_two_eq_sqrt_local,
        poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv_local]
      exact hweakEnvelope
    calc
      Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
          Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) ≤
          ((d : ℝ) * poincareUpperEllipticityFactor R
            (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2)) *
          ((d : ℝ) * poincareLowerEllipticityFactor R
            (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2)) := hprod
      _ = (d : ℝ) ^ 2 *
          (poincareUpperEllipticityFactor R (rootPointwiseCoeffFamily R a)
            (s.1 / 2) (.finite 2) * poincareLowerEllipticityFactor R
              (rootPointwiseCoeffFamily R a) (s.1 / 2) (.finite 2)) := by ring
      _ ≤ (d : ℝ) ^ 2 * (4 * (d : ℝ) * (H2 ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hpublic (sq_nonneg _)
      _ = 4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1) := by ring
  have hpoincareRaw : matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹ ≤
      4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1) := by
    have hmatRaw : matNorm a0 ≤ (d : ℝ) * sigma0 := by
      dsimp [a0]
      exact matNorm_scalarMatrix_le_dim_mul hsigma0.le
    have hprod : matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹ ≤
        ((d : ℝ) * sigma0) * ((d : ℝ) *
          (Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
            (rootPointwiseCoeffFamily R a))⁻¹) :=
      mul_le_mul hmatRaw hinvBridge
        (inv_nonneg.mpr (multiscale_ellipticity_lambdaSq_finite_nonneg R
          (s.1 / 2) 2 A (by norm_num) (by linarith [s.2.1])))
        (mul_nonneg hd_nonneg hsigma0.le)
    calc
      matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹ ≤
          ((d : ℝ) * sigma0) * ((d : ℝ) *
            (Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
              (rootPointwiseCoeffFamily R a))⁻¹) := hprod
      _ = (d : ℝ) ^ 2 *
          (sigma0 * (Book.Ch02.lambdaSq R (s.1 / 2) (.finite 2)
            (rootPointwiseCoeffFamily R a))⁻¹) := by ring
      _ ≤ (d : ℝ) ^ 2 * (4 * (d : ℝ) * (H2 ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hpoincareEnvelope (sq_nonneg _)
      _ = 4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1) := by ring
  have henergy :
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
        coarseFluxResponseRHSEnergyBound R A a0 s.1 u.toCubeSet.grad ≤
      (2 * M * (d : ℝ)) * X := by
    unfold coarseFluxResponseRHSEnergyBound
    rw [hH1eq]
    change
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
          (s.1⁻¹ * Real.sqrt (matNorm a0) * H1 * E) ≤
        (2 * M * (d : ℝ)) * X
    calc
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
          (s.1⁻¹ * Real.sqrt (matNorm a0) * H1 * E) ≤
          (2 * M) * (s.1⁻¹ * ((d : ℝ) * Real.sqrt sigma0) *
            H1 * E) := by
            gcongr
      _ = (2 * M * (d : ℝ)) * X := by ring
  have hresponse :
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
        coarseFluxResponseRHSResponseCorrectionBound R A a0 s.1 (fun x => -g x) ≤
      (8 * M * (d : ℝ) ^ 3) * Y := by
    unfold coarseFluxResponseRHSResponseCorrectionBound
    rw [hBneg]
    rw [hH1eq]
    have hraw_nonneg : 0 ≤ Real.sqrt (matNorm a0) *
        Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1 :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hH1_nonneg
    calc
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
          (Real.rpow s.1 (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
            Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1 * B) =
          (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
            (Real.rpow s.1 (-(5 / 2 : ℝ)) *
              (Real.sqrt (matNorm a0) * Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1) * B) := by ring
      _ ≤
          (2 * M) * (Real.rpow s.1 (-(5 / 2 : ℝ)) *
            (Real.sqrt (matNorm a0) * Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1) * B) := by
            apply mul_le_mul_of_nonneg_right hC
            exact mul_nonneg (mul_nonneg hrpow52_nonneg hraw_nonneg) hB_nonneg
      _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
            (Real.sqrt (matNorm a0) * Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1) * B) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hpow52 hraw_nonneg) hB_nonneg)
              (mul_nonneg (by norm_num) hM_nonneg)
      _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
            (4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B) := by
            calc
              (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                  (Real.sqrt (matNorm a0) * Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1) * B) =
                  (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    ((Real.sqrt (matNorm a0) * Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * H1) * B)) := by ring
              _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    ((4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B)) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hresponseRaw hB_nonneg) hrpow9_nonneg)
                    (mul_nonneg (by norm_num) hM_nonneg)
              _ = (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    (4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B) := by ring
      _ = (8 * M * (d : ℝ) ^ 3) * Y := by dsimp [Y]; ring
  have hweak :
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
        coarseFluxResponseRHSWeakFluxCorrectionBound R A s.1 (fun x => -g x) ≤
      (8 * M * (d : ℝ) ^ 3) * Y := by
    unfold coarseFluxResponseRHSWeakFluxCorrectionBound
    rw [hBneg]
    have hraw_nonneg : 0 ≤ Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
        Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
          (Real.rpow s.1 (-(5 / 2 : ℝ)) *
            Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
            Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * B) =
          (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
            (Real.rpow s.1 (-(5 / 2 : ℝ)) *
              (Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
                Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹)) * B) := by ring
      _ ≤
          (2 * M) * (Real.rpow s.1 (-(5 / 2 : ℝ)) *
            (Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
              Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹)) * B) := by
            apply mul_le_mul_of_nonneg_right hC
            exact mul_nonneg (mul_nonneg hrpow52_nonneg hraw_nonneg) hB_nonneg
      _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
            (Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
              Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹)) * B) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hpow52 hraw_nonneg) hB_nonneg)
              (mul_nonneg (by norm_num) hM_nonneg)
      _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
            (4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B) := by
            calc
              (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                  (Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
                    Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹)) * B) =
                  (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    ((Real.sqrt (LambdaSq R (s.1 / 2) (.finite 2) A) *
                      Real.sqrt ((lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹)) * B)) := by ring
              _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    ((4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B)) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hweakRaw hB_nonneg) hrpow9_nonneg)
                    (mul_nonneg (by norm_num) hM_nonneg)
              _ = (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    (4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B) := by ring
      _ = (8 * M * (d : ℝ) ^ 3) * Y := by dsimp [Y]; ring
  have hpoincare :
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
        coarseFluxResponseRHSPoincareCorrectionBound R A a0 s.1 (fun x => -g x) ≤
      (8 * M * (d : ℝ) ^ 3) * Y := by
    unfold coarseFluxResponseRHSPoincareCorrectionBound
    rw [hBneg]
    have hraw_nonneg : 0 ≤ matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹ :=
      mul_nonneg (matNorm_nonneg _) (inv_nonneg.mpr
        (multiscale_ellipticity_lambdaSq_finite_nonneg R (s.1 / 2) 2 A
          (by norm_num) (by linarith [s.2.1])))
    calc
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
          (Real.rpow s.1 (-3 : ℝ) * matNorm a0 *
            (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹ * B) =
          (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
            (Real.rpow s.1 (-3 : ℝ) *
              (matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * B) := by ring
      _ ≤
          (2 * M) * (Real.rpow s.1 (-3 : ℝ) *
            (matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * B) := by
            apply mul_le_mul_of_nonneg_right hC
            exact mul_nonneg (mul_nonneg hrpow3_nonneg hraw_nonneg) hB_nonneg
      _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
            (matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * B) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hpow3 hraw_nonneg) hB_nonneg)
              (mul_nonneg (by norm_num) hM_nonneg)
      _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
            (4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B) := by
            calc
              (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                  (matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * B) =
                  (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    ((matNorm a0 * (lambdaSq R (s.1 / 2) (.finite 2) A)⁻¹) * B)) := by ring
              _ ≤ (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    ((4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B)) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hpoincareRaw hB_nonneg) hrpow9_nonneg)
                    (mul_nonneg (by norm_num) hM_nonneg)
              _ = (2 * M) * (Real.rpow s.1 (-(9 / 2 : ℝ)) *
                    (4 * (d : ℝ) ^ 3 * (H2 ^ 2 + 1)) * B) := by ring
      _ = (8 * M * (d : ℝ) ^ 3) * Y := by dsimp [Y]; ring
  have hreal :
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
        coarseFluxResponseRHSBound R A a0 s.1 u.toCubeSet.grad (fun x => -g x) ≤
      localCoarseGrainingOneCubeConstant d * (X + Y) := by
    rw [coarseFluxResponseRHSBound_eq_component_sum]
    calc
      (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
          (coarseFluxResponseRHSEnergyBound R A a0 s.1 u.toCubeSet.grad +
            coarseFluxResponseRHSResponseCorrectionBound R A a0 s.1 (fun x => -g x) +
            coarseFluxResponseRHSWeakFluxCorrectionBound R A s.1 (fun x => -g x) +
            coarseFluxResponseRHSPoincareCorrectionBound R A a0 s.1 (fun x => -g x)) =
          (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
            coarseFluxResponseRHSEnergyBound R A a0 s.1 u.toCubeSet.grad +
          (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
            coarseFluxResponseRHSResponseCorrectionBound R A a0 s.1 (fun x => -g x) +
          (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
            coarseFluxResponseRHSWeakFluxCorrectionBound R A s.1 (fun x => -g x) +
          (2 * _root_.Homogenization.ZeroTraceDirichletCorrectorData.zeroTraceDirichletCorrectedWeakFluxApexConstant d s.1) *
            coarseFluxResponseRHSPoincareCorrectionBound R A a0 s.1 (fun x => -g x) := by ring
      _ ≤ (2 * M * (d : ℝ)) * X + (8 * M * (d : ℝ) ^ 3) * Y +
          (8 * M * (d : ℝ) ^ 3) * Y + (8 * M * (d : ℝ) ^ 3) * Y := by
        gcongr
      _ = (2 * M * (d : ℝ)) * X +
          (24 * M * (d : ℝ) ^ 3) * Y := by ring
      _ ≤ localCoarseGrainingOneCubeConstant d * (X + Y) :=
        localCoarseGrainingOneCubeConstant_dominates_forcing X Y hX_nonneg hY_nonneg
  have hapex := ENNReal_ofReal_norm_cubeAverageVec_source_fluxDefect_le_legacyApex_of_memCubeEuclideanFullWsp
    sigma0 hsigma0 s s2 p hp hss2 hg h
  have hmain : ENNReal.ofReal ‖cubeAverageVec R
      (fluxDefect a.toCoeffField (scalarMatrix (d := d) sigma0) u.toCubeSet.grad)‖ ≤
      ENNReal.ofReal (localCoarseGrainingOneCubeConstant d * (X + Y)) :=
    hapex.trans (ENNReal.ofReal_le_ofReal (by simpa only [A, a0] using hreal))
  have henergyENN : ENNReal.ofReal E = localSymmetricEnergyENorm R a u := by
    dsimp [E, A]
    exact ENNReal_ofReal_sqrt_cubeAverage_public_energy_eq_localSymmetricEnergy R a u
  have hXENN : ENNReal.ofReal X =
      ENNReal.ofReal (s.1⁻¹) * ENNReal.ofReal (Real.sqrt sigma0) *
        ENNReal.ofReal H1 * localSymmetricEnergyENorm R a u := by
    rw [show X = s.1⁻¹ * Real.sqrt sigma0 * H1 * E by rfl]
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hs_inv_nonneg (Real.sqrt_nonneg _)) hH1_nonneg),
      ENNReal.ofReal_mul (mul_nonneg hs_inv_nonneg (Real.sqrt_nonneg _)),
      ENNReal.ofReal_mul hs_inv_nonneg, henergyENN]
  have hYENN : ENNReal.ofReal Y =
      ENNReal.ofReal (Real.rpow s.1 (-(9 / 2 : ℝ))) *
        (1 + ENNReal.ofReal H2 ^ 2) * ENNReal.ofReal B := by
    rw [show Y = Real.rpow s.1 (-(9 / 2 : ℝ)) * (H2 ^ 2 + 1) * B by rfl]
    rw [ENNReal.ofReal_mul (mul_nonneg hrpow9_nonneg (add_nonneg (sq_nonneg H2) zero_le_one)),
      ENNReal.ofReal_mul hrpow9_nonneg, ENNReal.ofReal_add (sq_nonneg H2) zero_le_one,
      ENNReal.ofReal_pow]
    · simp only [ENNReal.ofReal_one, add_comm]
    · exact hH2_nonneg
  rw [show ENNReal.ofReal (localCoarseGrainingOneCubeConstant d * (X + Y)) =
      ENNReal.ofReal (localCoarseGrainingOneCubeConstant d) * ENNReal.ofReal (X + Y) by
        rw [ENNReal.ofReal_mul (localCoarseGrainingOneCubeConstant_nonneg d)]] at hmain
  rw [ENNReal.ofReal_add hX_nonneg hY_nonneg, hXENN, hYENN] at hmain
  simpa only [H1, H2] using hmain

end

end ABK26
end Ch03
end Book
end Homogenization
