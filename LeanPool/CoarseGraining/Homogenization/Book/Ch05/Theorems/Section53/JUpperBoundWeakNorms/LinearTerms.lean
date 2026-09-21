/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.CutoffOscillation

/-! # Linear Terms -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# LinearTerms

Linear gradient and flux term bounds.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- A constant-vector dot product against a cube average is bounded
componentwise. -/
theorem abs_vecDot_const_cubeAverageVec_le_sum_abs_mul_norm_cubeAverage
    {d : ℕ} (Q : TriadicCube d) (c : Vec d) (field : Vec d → Vec d) :
    |vecDot c (cubeAverageVec Q field)| ≤
      ∑ i : Fin d, |c i| * ‖cubeAverage Q (fun x => field x i)‖ := by
  calc
    |vecDot c (cubeAverageVec Q field)|
        = |∑ i : Fin d, c i * cubeAverage Q (fun x => field x i)| := by
            simp [vecDot, cubeAverageVec]
    _ ≤ ∑ i : Fin d, |c i * cubeAverage Q (fun x => field x i)| := by
          exact Finset.abs_sum_le_sum_abs (s := Finset.univ)
            (f := fun i : Fin d => c i * cubeAverage Q (fun x => field x i))
    _ = ∑ i : Fin d, |c i| * ‖cubeAverage Q (fun x => field x i)‖ := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [abs_mul, Real.norm_eq_abs]

/-- A constant-vector dot product commutes with `cubeAverageVec`. -/
theorem cubeAverage_vecDot_const_left_eq_vecDot_cubeAverageVec
    {d : ℕ} (Q : TriadicCube d) (c : Vec d) (field : Vec d → Vec d)
    (hField :
      ∀ i : Fin d,
        IntegrableOn (fun x => field x i) (cubeSet Q) volume) :
    cubeAverage Q (fun x => vecDot c (field x)) =
      vecDot c (cubeAverageVec Q field) := by
  have hterm :
      ∀ i ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun x => c i * field x i)
          (volume.restrict (cubeSet Q)) := by
    intro i _hi
    simpa [IntegrableOn] using
      (hField i).integrable.const_mul (c i)
  unfold cubeAverage vecDot cubeAverageVec
  rw [integral_finsetSum Finset.univ hterm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [integral_const_mul]
  unfold cubeAverage
  ring_nf

/-- Single half-linear term from per-component average estimates. -/
theorem abs_half_vecDot_const_cubeAverageVec_le_const_mul_size_weak_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (c : Vec d) (field : Vec d → Vec d)
    (componentBound : Fin d → ℝ) {C cSize fieldWeak : ℝ}
    (hhalfC : (1 / 2 : ℝ) ≤ C)
    (hcSize_nonneg : 0 ≤ cSize) (hfieldWeak_nonneg : 0 ≤ fieldWeak)
    (hComponentBound :
      ∀ i : Fin d, ‖cubeAverage Q (fun x => field x i)‖ ≤ componentBound i)
    (hComponentSum :
      (∑ i : Fin d, |c i| * componentBound i) ≤ cSize * fieldWeak) :
    |(1 / 2 : ℝ) * vecDot c (cubeAverageVec Q field)| ≤
      C * cSize * fieldWeak := by
  have hComponent :
      (∑ i : Fin d, |c i| * ‖cubeAverage Q (fun x => field x i)‖) ≤
        cSize * fieldWeak := by
    refine (Finset.sum_le_sum ?_).trans hComponentSum
    intro i _hi
    exact mul_le_mul_of_nonneg_left (hComponentBound i) (abs_nonneg (c i))
  have hbase :
      |vecDot c (cubeAverageVec Q field)| ≤ cSize * fieldWeak :=
    (abs_vecDot_const_cubeAverageVec_le_sum_abs_mul_norm_cubeAverage Q c field).trans
      hComponent
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hprod_nonneg : 0 ≤ cSize * fieldWeak :=
    mul_nonneg hcSize_nonneg hfieldWeak_nonneg
  calc
    |(1 / 2 : ℝ) * vecDot c (cubeAverageVec Q field)|
        = (1 / 2 : ℝ) * |vecDot c (cubeAverageVec Q field)| := by
            rw [abs_mul, abs_of_nonneg hhalf_nonneg]
    _ ≤ (1 / 2 : ℝ) * (cSize * fieldWeak) := by
          exact mul_le_mul_of_nonneg_left hbase hhalf_nonneg
    _ ≤ C * (cSize * fieldWeak) := by
          exact mul_le_mul_of_nonneg_right hhalfC hprod_nonneg
    _ = C * cSize * fieldWeak := by ring

/-- The two manuscript linear terms after componentwise average/Besov bounds
have been supplied. -/
theorem abs_half_linear_pair_cubeAverageVec_le_const_mul_sizes_weaks_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (q0 p0 : Vec d)
    (gradField fluxField : Vec d → Vec d)
    (gradComponentBound fluxComponentBound : Fin d → ℝ)
    {C q0Size p0Size gradWeak fluxWeak : ℝ}
    (hhalfC : (1 / 2 : ℝ) ≤ C)
    (hq0Size_nonneg : 0 ≤ q0Size) (hp0Size_nonneg : 0 ≤ p0Size)
    (hgradWeak_nonneg : 0 ≤ gradWeak) (hfluxWeak_nonneg : 0 ≤ fluxWeak)
    (hGradComponentBound :
      ∀ i : Fin d, ‖cubeAverage Q (fun x => gradField x i)‖ ≤ gradComponentBound i)
    (hFluxComponentBound :
      ∀ i : Fin d, ‖cubeAverage Q (fun x => fluxField x i)‖ ≤ fluxComponentBound i)
    (hGradComponentSum :
      (∑ i : Fin d, |q0 i| * gradComponentBound i) ≤ q0Size * gradWeak)
    (hFluxComponentSum :
      (∑ i : Fin d, |p0 i| * fluxComponentBound i) ≤ p0Size * fluxWeak) :
    |(1 / 2 : ℝ) * vecDot q0 (cubeAverageVec Q gradField) +
        (1 / 2 : ℝ) * vecDot p0 (cubeAverageVec Q fluxField)| ≤
      C * q0Size * gradWeak + C * p0Size * fluxWeak := by
  have hGrad :
      |(1 / 2 : ℝ) * vecDot q0 (cubeAverageVec Q gradField)| ≤
        C * q0Size * gradWeak :=
    abs_half_vecDot_const_cubeAverageVec_le_const_mul_size_weak_of_component_bounds
      Q q0 gradField gradComponentBound hhalfC hq0Size_nonneg hgradWeak_nonneg
      hGradComponentBound hGradComponentSum
  have hFlux :
      |(1 / 2 : ℝ) * vecDot p0 (cubeAverageVec Q fluxField)| ≤
        C * p0Size * fluxWeak :=
    abs_half_vecDot_const_cubeAverageVec_le_const_mul_size_weak_of_component_bounds
      Q p0 fluxField fluxComponentBound hhalfC hp0Size_nonneg hfluxWeak_nonneg
      hFluxComponentBound hFluxComponentSum
  exact (abs_add_le _ _).trans (add_le_add hGrad hFlux)

/-- The cutoff `q0` linear term as a half dot-product of a vector cube
average. -/
theorem cutoffGradientLinearTermOnCube_eq_half_vecDot_cubeAverageVec
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (hField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x => (φ x • canonicalMaximizerGradientDefectOnCube Q a p q p0 x) i)
          (cubeSet Q) volume) :
    cutoffGradientLinearTermOnCube Q a φ p q p0 q0 =
      (1 / 2 : ℝ) * vecDot q0
        (cubeAverageVec Q
          (fun x => φ x • canonicalMaximizerGradientDefectOnCube Q a p q p0 x)) := by
  let field : Vec d → Vec d :=
    fun x => φ x • canonicalMaximizerGradientDefectOnCube Q a p q p0 x
  have hAvg :
      cubeAverage Q (fun x => vecDot q0 (field x)) =
        vecDot q0 (cubeAverageVec Q field) :=
    cubeAverage_vecDot_const_left_eq_vecDot_cubeAverageVec Q q0 field
      (by simpa [field] using hField)
  have hpoint :
      (fun x => φ x * centeredGradientLinearDensityOnCube Q a p q p0 q0 x) =
        fun x => (1 / 2 : ℝ) * vecDot q0 (field x) := by
    funext x
    change
      φ x * ((1 / 2 : ℝ) *
          vecDot q0 (canonicalMaximizerGradientOnCube Q a p q x - p0)) =
        (1 / 2 : ℝ) *
          vecDot q0 (φ x • canonicalMaximizerGradientDefectOnCube Q a p q p0 x)
    rw [vecDot_smul_right]
    simp [canonicalMaximizerGradientDefectOnCube]
    ring
  calc
    cutoffGradientLinearTermOnCube Q a φ p q p0 q0 =
        cubeAverage Q (fun x => φ x *
          centeredGradientLinearDensityOnCube Q a p q p0 q0 x) := by
          simp [cutoffGradientLinearTermOnCube]
    _ = cubeAverage Q (fun x => (1 / 2 : ℝ) * vecDot q0 (field x)) := by
          rw [hpoint]
    _ = (1 / 2 : ℝ) * vecDot q0 (cubeAverageVec Q field) := by
          rw [cubeAverage_const_mul, hAvg]

/-- The cutoff `p0` linear term as a half dot-product of a vector cube
average. -/
theorem cutoffFluxLinearTermOnCube_eq_half_vecDot_cubeAverageVec
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (φ : Vec d → ℝ) (p q p0 q0 : Vec d)
    (hField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x => (φ x • canonicalMaximizerFluxDefectOnCube Q a p q q0 x) i)
          (cubeSet Q) volume) :
    cutoffFluxLinearTermOnCube Q a φ p q p0 q0 =
      (1 / 2 : ℝ) * vecDot p0
        (cubeAverageVec Q
          (fun x => φ x • canonicalMaximizerFluxDefectOnCube Q a p q q0 x)) := by
  let field : Vec d → Vec d :=
    fun x => φ x • canonicalMaximizerFluxDefectOnCube Q a p q q0 x
  have hAvg :
      cubeAverage Q (fun x => vecDot p0 (field x)) =
        vecDot p0 (cubeAverageVec Q field) :=
    cubeAverage_vecDot_const_left_eq_vecDot_cubeAverageVec Q p0 field
      (by simpa [field] using hField)
  have hpoint :
      (fun x => φ x * centeredFluxLinearDensityOnCube Q a p q p0 q0 x) =
        fun x => (1 / 2 : ℝ) * vecDot p0 (field x) := by
    funext x
    change
      φ x * ((1 / 2 : ℝ) *
          vecDot p0 (canonicalMaximizerFluxOnCube Q a p q x - q0)) =
        (1 / 2 : ℝ) *
          vecDot p0 (φ x • canonicalMaximizerFluxDefectOnCube Q a p q q0 x)
    rw [vecDot_smul_right]
    simp [canonicalMaximizerFluxDefectOnCube]
    ring
  calc
    cutoffFluxLinearTermOnCube Q a φ p q p0 q0 =
        cubeAverage Q (fun x => φ x *
          centeredFluxLinearDensityOnCube Q a p q p0 q0 x) := by
          simp [cutoffFluxLinearTermOnCube]
    _ = cubeAverage Q (fun x => (1 / 2 : ℝ) * vecDot p0 (field x)) := by
          rw [hpoint]
    _ = (1 / 2 : ℝ) * vecDot p0 (cubeAverageVec Q field) := by
          rw [cubeAverage_const_mul, hAvg]

/-- The deterministic linear-pair term is controlled by the current Ch4
scalar-response gradient and flux weak norms.  The only cutoff inputs are the
ordinary Besov dual-test bounds for the scalar cutoff `φ`. -/
theorem abs_cutoffLinearPairTermOnDependentFamily_le_ch04WeakNorms_of_cutoffDualBounds
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (s t : ℝ) (φ : Vec d → ℝ)
    (p q p0 q0 : Vec d) {BφS BφT : ℝ}
    (hGradField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerGradientDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q p0 x) i)
          (cubeSet Q) volume)
    (hFluxField :
      ∀ i : Fin d,
        IntegrableOn
          (fun x =>
            (φ x • canonicalMaximizerFluxDefectOnCube Q
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q q0 x) i)
          (cubeSet Q) volume)
    (hs : 0 < s) (ht : 0 < t)
    (hBφS : 0 ≤ BφS) (hBφT : 0 ≤ BφT)
    (hφDualS :
      ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφS)
    (hφDualT :
      ∀ N : ℕ, cubeBesovDualTestNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N φ ≤ BφT)
    (hφMem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) φ) :
    let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    let gradWeak := Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
    let fluxWeak := Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
    let gradCoeff :=
      (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
    let fluxCoeff :=
      (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
    |cutoffLinearPairTermOnCube Q (F.coeffOn Q) φ p q p0 q0| ≤
      (1 / 2 : ℝ) * ‖q0‖ *
          (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) +
        (1 / 2 : ℝ) * ‖p0‖ *
          (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak) := by
  intro F gradWeak fluxWeak gradCoeff fluxCoeff
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  let gradField : Vec d → Vec d :=
    fun x => φ x • canonicalMaximizerGradientDefectOnCube Q aQ p q p0 x
  let fluxField : Vec d → Vec d :=
    fun x => φ x • canonicalMaximizerFluxDefectOnCube Q aQ p q q0 x
  have hgradWeak_nonneg : 0 ≤ gradWeak := by
    have hpartial_nonneg :
        0 ≤ cubeBesovNegativeVectorPartialSeminorm Q s 0
          (canonicalMaximizerGradientDefectOnCube Q aQ p q p0) :=
      cubeBesovNegativeVectorPartialSeminorm_nonneg Q s 0
        (canonicalMaximizerGradientDefectOnCube Q aQ p q p0)
    have hpartial_le :
        cubeBesovNegativeVectorPartialSeminorm Q s 0
            (canonicalMaximizerGradientDefectOnCube Q aQ p q p0) ≤ gradWeak := by
      simpa [F, aQ, gradWeak] using
        cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_le_ch04WeakNorm
          a ha Q hs 0 p q p0
    exact hpartial_nonneg.trans hpartial_le
  have hfluxWeak_nonneg : 0 ≤ fluxWeak := by
    have hpartial_nonneg :
        0 ≤ cubeBesovNegativeVectorPartialSeminorm Q t 0
          (canonicalMaximizerFluxDefectOnCube Q aQ p q q0) :=
      cubeBesovNegativeVectorPartialSeminorm_nonneg Q t 0
        (canonicalMaximizerFluxDefectOnCube Q aQ p q q0)
    have hpartial_le :
        cubeBesovNegativeVectorPartialSeminorm Q t 0
            (canonicalMaximizerFluxDefectOnCube Q aQ p q q0) ≤ fluxWeak := by
      simpa [F, aQ, fluxWeak] using
        cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
          a ha Q ht 0 p q q0
    exact hpartial_nonneg.trans hpartial_le
  have hgradCoeff_nonneg : 0 ≤ gradCoeff := by
    dsimp [gradCoeff]
    exact mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (cubeBesovScaleWeight_nonneg (-s) Q))
      hBφS
  have hfluxCoeff_nonneg : 0 ≤ fluxCoeff := by
    dsimp [fluxCoeff]
    exact mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (cubeBesovScaleWeight_nonneg (-t) Q))
      hBφT
  have hGradComponentBound :
      ∀ i : Fin d,
        ‖cubeAverage Q (fun x => gradField x i)‖ ≤ gradCoeff * gradWeak := by
    intro i
    have hcomp :
        MemLp (fun x => canonicalMaximizerGradientDefectOnCube Q aQ p q p0 x i)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      memLp_component_of_memLp
        (canonicalMaximizerGradientDefectOnCube Q aQ p q p0) i
        (canonicalMaximizerGradientDefectOnCube_memLp Q aQ p q p0)
    have hpartial :
        ∀ N : ℕ,
          cubeBesovNegativeVectorPartialSeminorm Q s N
              (canonicalMaximizerGradientDefectOnCube Q aQ p q p0) ≤ gradWeak := by
      intro N
      simpa [F, aQ, gradWeak] using
        cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_le_ch04WeakNorm
          a ha Q hs N p q p0
    simpa [F, aQ, gradField, gradCoeff] using
      norm_cubeAverage_smul_component_le_cutoffDualCoeff_mul_negativeVectorPartialBound
        Q s (canonicalMaximizerGradientDefectOnCube Q aQ p q p0) φ i
        hs hcomp hBφS hφDualS hφMem hpartial
  have hFluxComponentBound :
      ∀ i : Fin d,
        ‖cubeAverage Q (fun x => fluxField x i)‖ ≤ fluxCoeff * fluxWeak := by
    intro i
    have hcomp :
        MemLp (fun x => canonicalMaximizerFluxDefectOnCube Q aQ p q q0 x i)
          (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
      memLp_component_of_memLp
        (canonicalMaximizerFluxDefectOnCube Q aQ p q q0) i
        (canonicalMaximizerFluxDefectOnCube_memLp Q aQ p q q0)
    have hpartial :
        ∀ N : ℕ,
          cubeBesovNegativeVectorPartialSeminorm Q t N
              (canonicalMaximizerFluxDefectOnCube Q aQ p q q0) ≤ fluxWeak := by
      intro N
      simpa [F, aQ, fluxWeak] using
        cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_le_ch04WeakNorm
          a ha Q ht N p q q0
    simpa [F, aQ, fluxField, fluxCoeff] using
      norm_cubeAverage_smul_component_le_cutoffDualCoeff_mul_negativeVectorPartialBound
        Q t (canonicalMaximizerFluxDefectOnCube Q aQ p q q0) φ i
        ht hcomp hBφT hφDualT hφMem hpartial
  have hGradComponentSum :
      (∑ i : Fin d, |q0 i| * (gradCoeff * gradWeak)) ≤
        ‖q0‖ * (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) := by
    have hsum :=
      sum_abs_mul_const_mul_le_card_mul_norm_mul_const_mul_of_nonneg
        q0 hgradCoeff_nonneg hgradWeak_nonneg
    calc
      (∑ i : Fin d, |q0 i| * (gradCoeff * gradWeak))
          ≤ ((Fintype.card (Fin d) : ℝ) * gradCoeff) * ‖q0‖ * gradWeak := hsum
      _ = ‖q0‖ * (((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak) := by
            ring
  have hFluxComponentSum :
      (∑ i : Fin d, |p0 i| * (fluxCoeff * fluxWeak)) ≤
        ‖p0‖ * (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak) := by
    have hsum :=
      sum_abs_mul_const_mul_le_card_mul_norm_mul_const_mul_of_nonneg
        p0 hfluxCoeff_nonneg hfluxWeak_nonneg
    calc
      (∑ i : Fin d, |p0 i| * (fluxCoeff * fluxWeak))
          ≤ ((Fintype.card (Fin d) : ℝ) * fluxCoeff) * ‖p0‖ * fluxWeak := hsum
      _ = ‖p0‖ * (((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak) := by
            ring
  have hGradEq :=
    cutoffGradientLinearTermOnCube_eq_half_vecDot_cubeAverageVec
      Q aQ φ p q p0 q0 (by simpa [F, aQ, gradField] using hGradField)
  have hFluxEq :=
    cutoffFluxLinearTermOnCube_eq_half_vecDot_cubeAverageVec
      Q aQ φ p q p0 q0 (by simpa [F, aQ, fluxField] using hFluxField)
  have hPair :
      cutoffLinearPairTermOnCube Q aQ φ p q p0 q0 =
        (1 / 2 : ℝ) * vecDot q0 (cubeAverageVec Q gradField) +
          (1 / 2 : ℝ) * vecDot p0 (cubeAverageVec Q fluxField) := by
    simp [cutoffLinearPairTermOnCube, gradField, fluxField, hGradEq, hFluxEq]
  rw [show (F.coeffOn Q) = aQ by rfl, hPair]
  simpa using
    abs_half_linear_pair_cubeAverageVec_le_const_mul_sizes_weaks_of_component_bounds
      Q q0 p0 gradField fluxField (fun _ => gradCoeff * gradWeak)
      (fun _ => fluxCoeff * fluxWeak)
      (C := (1 / 2 : ℝ)) (q0Size := ‖q0‖) (p0Size := ‖p0‖)
      (gradWeak := ((Fintype.card (Fin d) : ℝ) * gradCoeff) * gradWeak)
      (fluxWeak := ((Fintype.card (Fin d) : ℝ) * fluxCoeff) * fluxWeak)
      le_rfl (norm_nonneg q0) (norm_nonneg p0)
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hgradCoeff_nonneg)
        hgradWeak_nonneg)
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hfluxCoeff_nonneg)
        hfluxWeak_nonneg)
      hGradComponentBound hFluxComponentBound hGradComponentSum hFluxComponentSum

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
