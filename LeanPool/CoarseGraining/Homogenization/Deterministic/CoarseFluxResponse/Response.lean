/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.EnergyForm
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.HarmonicAndData

/-! # Response -/

namespace Homogenization

noncomputable section

open scoped BigOperators MatrixOrder Pointwise

/-- For a symmetric elliptic matrix `a0`, the actual-defect energy form
controls the Euclidean square of the averaged defect up to `matNorm a0`. -/
private theorem vecNormSq_le_matNorm_mul_vecDot_inv_of_isEllipticMatrix_of_isSymm {d : ℕ}
    {a0 : Mat d} {lam Lam : ℝ} (ha0 : IsEllipticMatrix lam Lam a0) (ha0symm : a0.IsSymm)
    (ξ : Vec d) :
    vecNormSq ξ ≤ matNorm a0 * vecDot ξ (matVecMul a0⁻¹ ξ) := by
  have ha0psd : a0.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · simpa [Matrix.IsHermitian, Matrix.IsSymm] using ha0symm
    · intro x
      have hlam_pos : 0 < lam := ha0.1
      have hbase : 0 ≤ lam * vecNormSq x := by
        exact mul_nonneg (le_of_lt hlam_pos) (vecNormSq_nonneg x)
      have hlower := lowerBound_symmPart_of_isEllipticMatrix ha0 x
      rw [vecDot_matVecMul_symmPart] at hlower
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using le_trans hbase hlower
  have hleftInv : ∀ x : Vec d, matVecMul a0 (matVecMul a0⁻¹ x) = x := by
    intro x
    rw [matVecMul_mul, Matrix.mul_nonsing_inv a0 (isUnit_det_of_isEllipticMatrix ha0)]
    funext i
    simp [matVecMul, Matrix.one_apply]
  exact
    vecNormSq_le_matNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := a0⁻¹) (B := a0) ha0psd hleftInv ξ

/-- Descendant cube-average control for a flux-defect field by the local
normalized block response and a scalar energy density. -/
def CubeAverageFluxResponseControl {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) (defect : Vec d → Vec d)
    (energy : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    vecNormSq (cubeAverageVec R defect) ≤
      (((4 : ℝ) * matNorm a0 * normalizedBlockResponseMax R a a0) *
        cubeAverage R energy)

theorem cubeAverageFluxResponseControl_of_descendantScalarCanonicalFluxDefectData {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (defect : Vec d → Vec d) (energy : Vec d → ℝ)
    {lam0 Lam0 : ℝ} (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hdesc : DescendantScalarCanonicalFluxDefectData Q a a0 defect energy) :
    CubeAverageFluxResponseControl Q a a0 defect energy := by
  intro j R hR
  rcases hdesc j R hR with
    ⟨lam, Lam, w, hEll, hv, hdefect, henergy⟩
  rcases hv with ⟨v⟩
  let actualDefect : Vec d → Vec d :=
    fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x)
  have hdefectavg :
      cubeAverageVec R defect = cubeAverageVec R actualDefect :=
    cubeAverageVec_eq_of_eq_on_cubeSet hdefect
  have henergyavg :
      cubeAverage R energy = cubeAverage R (scalarVariationEnergyIntegrand a w) :=
    cubeAverage_eq_of_eq_on_cubeSet henergy
  have hv' :
      ScalarCanonicalMaximizer (cubeSet R)
        (-matVecMul ((symmPart a0)⁻¹) (cubeAverageVec R actualDefect))
        (-matVecMul (matTranspose a0)
          (matVecMul ((symmPart a0)⁻¹) (cubeAverageVec R actualDefect))) a := by
    simpa [actualDefect, hdefectavg] using v
  let D : Vec d := cubeAverageVec R actualDefect
  have hlocalEnergy :
      vecDot D (matVecMul a0⁻¹ D) ≤
        ((4 : ℝ) * normalizedBlockResponseMax R a a0) *
          cubeAverage R (scalarVariationEnergyIntegrand a w) := by
    simpa [D, actualDefect, symmPart_eq_of_isSymm ha0symm,
      matTranspose, Matrix.IsSymm] using
      (cubeAverageFluxDefect_energyForm_le_normalizedBlockResponseMax_mul_energyAverage_of_scalarCanonicalMaximizer
        (R := R) (a := a) (a0 := a0) hEll ha0 w hv')
  have hnorm :
      vecNormSq D ≤ matNorm a0 * vecDot D (matVecMul a0⁻¹ D) :=
    vecNormSq_le_matNorm_mul_vecDot_inv_of_isEllipticMatrix_of_isSymm ha0 ha0symm D
  calc
    vecNormSq (cubeAverageVec R defect) = vecNormSq D := by
      simpa [D] using congrArg vecNormSq hdefectavg
    _ ≤ matNorm a0 * vecDot D (matVecMul a0⁻¹ D) := hnorm
    _ ≤ matNorm a0 *
          (((4 : ℝ) * normalizedBlockResponseMax R a a0) *
            cubeAverage R (scalarVariationEnergyIntegrand a w)) := by
          exact mul_le_mul_of_nonneg_left hlocalEnergy (matNorm_nonneg a0)
    _ = (((4 : ℝ) * matNorm a0 * normalizedBlockResponseMax R a a0) *
          cubeAverage R (scalarVariationEnergyIntegrand a w)) := by
          ring
    _ = (((4 : ℝ) * matNorm a0 * normalizedBlockResponseMax R a a0) *
          cubeAverage R energy) := by rw [henergyavg]

/-- Direct descendant-average control for the actual flux defect of one
harmonic field on `cubeSet Q`. -/
theorem cubeAverageFluxResponseControl_of_aHarmonicFunction {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (u : AHarmonicFunction a (cubeSet Q)) :
    CubeAverageFluxResponseControl Q a a0
      (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))
      (scalarVariationEnergyIntegrand a u) := by
  exact
    cubeAverageFluxResponseControl_of_descendantScalarCanonicalFluxDefectData
      (Q := Q) (a := a) (a0 := a0)
      (defect := fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))
      (energy := scalarVariationEnergyIntegrand a u)
      ha0 ha0symm
      (descendantScalarCanonicalFluxDefectData_of_aHarmonicFunction
        (Q := Q) (a := a) (a0 := a0) hEll u)

theorem cubeBesovNegativeVectorDepthAverage_le_fluxResponseEnergy {d : ℕ}
    {Q : TriadicCube d} (a : CoeffField d) (a0 : Mat d)
    (defect : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hresp : CubeAverageFluxResponseControl Q a a0 defect energy)
    (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q defect j ≤
      ((4 : ℝ) * matNorm a0 *
        maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) *
          cubeAverage Q energy := by
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R defect) ≤
          (((4 : ℝ) * matNorm a0 *
              maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) *
            cubeAverage R energy) := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have havg_nonneg : 0 ≤ cubeAverage R energy := by
      apply cubeAverage_nonneg_of_nonneg_on
      intro x hx
      exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have hresp_le :
        ((4 : ℝ) * matNorm a0 * normalizedBlockResponseMax R a a0) ≤
          ((4 : ℝ) * matNorm a0 *
            maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) := by
      exact mul_le_mul_of_nonneg_left
        (normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale a a0 hRscale)
        (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) (matNorm_nonneg a0))
    exact le_trans (hresp j R hR) <|
      mul_le_mul_of_nonneg_right hresp_le havg_nonneg
  have hdesc :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have havg_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) =
        cubeAverage Q energy := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy henergy_int
  have hconst :
      descendantsAverage Q j (fun R =>
          (((4 : ℝ) * matNorm a0 *
              maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) *
            cubeAverage R energy)) =
        (((4 : ℝ) * matNorm a0 *
            maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) *
          descendantsAverage Q j (fun R => cubeAverage R energy)) := by
    let D := descendantsAtDepth Q j
    let M :=
      ((4 : ℝ) * matNorm a0 *
        maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0)
    unfold descendantsAverage
    calc
      ((D.card : ℝ)⁻¹) *
          Finset.sum D (fun R => M * cubeAverage R energy) =
            Finset.sum D (fun R => (((D.card : ℝ)⁻¹ * M) * cubeAverage R energy)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro R hR
              ring
      _ = (((D.card : ℝ)⁻¹ * M) *
            Finset.sum D (fun R => cubeAverage R energy)) := by
              simpa [mul_assoc] using
                (Finset.mul_sum (s := D) (f := fun R => cubeAverage R energy)
                  (((D.card : ℝ)⁻¹) * M)).symm
      _ = M * (((D.card : ℝ)⁻¹) * Finset.sum D (fun R => cubeAverage R energy)) := by
              ring
  rw [hconst, havg_eq] at hdesc
  simpa [cubeBesovNegativeVectorDepthAverage] using hdesc

/-- Finite-depth `q = 1` deterministic coarse flux-response bound under an
explicit descendant-local one-cube response bound. -/
theorem coarseFluxResponse_qone_partialSeminorm_le_of_cubeAverageFluxResponseControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (hs : 0 < s) (defect : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hresp : CubeAverageFluxResponseControl Q a a0 defect energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0))
    (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm Q s N defect ≤
      (geometricDiscount s 1)⁻¹ *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
        (Real.sqrt (((4 : ℝ) * matNorm a0)) * Real.sqrt (cubeAverage Q energy)) := by
  have hs1 : 0 < s * (1 : ℝ) := by
    simpa using hs
  have hdisc_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos hs1
  have hconst_nonneg : 0 ≤ ((4 : ℝ) * matNorm a0) := by
    exact mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) (matNorm_nonneg a0)
  let coeff : ℕ → ℝ := fun n =>
    Real.rpow (3 : ℝ) (-s * (n : ℝ)) *
      scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0
  let C : ℝ := Real.sqrt (((4 : ℝ) * matNorm a0)) * Real.sqrt (cubeAverage Q energy)
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovNegativeVectorDepthSeminorm Q s defect j ≤ coeff j * C := by
    intro j hj
    have havg :=
      cubeBesovNegativeVectorDepthAverage_le_fluxResponseEnergy
        (Q := Q) a a0 defect energy henergy_nonneg henergy_int hresp j
    have hmax_nonneg :
        0 ≤ maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0 := by
      exact maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le j)) a a0
    have hsqrt :
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q defect j) ≤
        Real.sqrt
            ((((4 : ℝ) * matNorm a0 *
                maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) *
              cubeAverage Q energy)) := by
      exact Real.sqrt_le_sqrt havg
    calc
      cubeBesovNegativeVectorDepthSeminorm Q s defect j =
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt (cubeBesovNegativeVectorDepthAverage Q defect j) := by
              rfl
      _ ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.sqrt
              ((((4 : ℝ) * matNorm a0 *
                  maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) *
                cubeAverage Q energy)) := by
              exact mul_le_mul_of_nonneg_left hsqrt
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      _ = coeff j * C := by
            unfold coeff C
            have hrewrite :
                (((4 : ℝ) * matNorm a0 *
                    maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0) *
                  cubeAverage Q energy) =
                  maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (j : ℤ)) a a0 *
                    ((((4 : ℝ) * matNorm a0)) * cubeAverage Q energy) := by
              ring
            rw [hrewrite]
            rw [mul_sqrt_mul_eq_mul_rpow_half_mul_sqrt hmax_nonneg]
            rw [← scaleResponseAtScale_infinity_eq]
            rw [Real.sqrt_mul hconst_nonneg]
  have hsum_partial :
      cubeBesovNegativeVectorPartialSeminorm Q s N defect ≤
        Finset.sum (Finset.range (N + 1)) coeff * C := by
    unfold cubeBesovNegativeVectorPartialSeminorm
    calc
      Finset.sum (Finset.range (N + 1)) (fun j =>
          cubeBesovNegativeVectorDepthSeminorm Q s defect j)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j =>
            coeff j * C) := by
              exact Finset.sum_le_sum hdepth
      _ = Finset.sum (Finset.range (N + 1)) coeff * C := by
            rw [Finset.sum_mul]
  have hcoeff_nonneg :
      ∀ n : ℕ, 0 ≤ geometricWeight s 1 n *
        scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0 := by
    intro n
    refine mul_nonneg (geometricWeight_nonneg n (by simpa using hs.le)) ?_
    exact scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  have hcoeff_eq :
      Finset.sum (Finset.range (N + 1)) coeff =
        (geometricDiscount s 1)⁻¹ *
          Finset.sum (Finset.range (N + 1)) (fun j =>
            geometricWeight s 1 j *
              scaleResponseAtScale Q (Q.scale - (j : ℤ)) .infinity a a0) := by
    unfold coeff
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [rpow_neg_s_nat_eq_inv_geometricDiscount_mul_geometricWeight hs j]
    ring
  have hfinite_le_tsum :
      Finset.sum (Finset.range (N + 1)) (fun j =>
          geometricWeight s 1 j *
            scaleResponseAtScale Q (Q.scale - (j : ℤ)) .infinity a a0)
        ≤ ∑' n : ℕ,
          geometricWeight s 1 n *
            scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0 := by
    exact hsum.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hcoeff_nonneg n)
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    cubeBesovNegativeVectorPartialSeminorm Q s N defect ≤
        Finset.sum (Finset.range (N + 1)) coeff * C :=
          hsum_partial
    _ = ((geometricDiscount s 1)⁻¹ *
          Finset.sum (Finset.range (N + 1)) (fun j =>
            geometricWeight s 1 j *
              scaleResponseAtScale Q (Q.scale - (j : ℤ)) .infinity a a0)) * C := by
            rw [hcoeff_eq]
    _ ≤ ((geometricDiscount s 1)⁻¹ *
          (∑' n : ℕ,
            geometricWeight s 1 n *
              scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) * C := by
            have hscaled :
                (geometricDiscount s 1)⁻¹ *
                    Finset.sum (Finset.range (N + 1)) (fun j =>
                      geometricWeight s 1 j *
                        scaleResponseAtScale Q (Q.scale - (j : ℤ)) .infinity a a0)
                  ≤
                (geometricDiscount s 1)⁻¹ *
                    (∑' n : ℕ,
                      geometricWeight s 1 n *
                        scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0) := by
              exact mul_le_mul_of_nonneg_left hfinite_le_tsum
                (inv_nonneg.mpr hdisc_pos.le)
            exact mul_le_mul_of_nonneg_right hscaled hC_nonneg
    _ = (geometricDiscount s 1)⁻¹ *
          HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
          C := by
            rw [homogenizationErrorOnCube_infinity_one_eq_tsum]

/-- Note-normalized `q = 1` deterministic coarse flux-response inequality under
an explicit descendant-local one-cube response bound. -/
theorem coarseFluxResponse_qone_of_cubeAverageFluxResponseControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (hs : 0 < s) (defect : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hresp : CubeAverageFluxResponseControl Q a a0 defect energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminorm Q s defect ≤
      (geometricDiscount s 1)⁻¹ *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
        (Real.sqrt (((4 : ℝ) * matNorm a0)) * Real.sqrt (cubeAverage Q energy)) := by
  exact
    cubeBesovNegativeVectorSeminorm_le_of_partialBound Q s defect fun N =>
      coarseFluxResponse_qone_partialSeminorm_le_of_cubeAverageFluxResponseControl
        (Q := Q) (a := a) (a0 := a0) (s := s) hs
        (defect := defect) (energy := energy)
        henergy_nonneg henergy_int hresp hsum N

/-- Note-facing `q = 1` deterministic coarse flux-response inequality for the
actual defect field, packaged directly from descendant scalar canonical
maximizer data. -/
theorem coarseFluxResponse_qone_of_descendantScalarCanonicalFluxDefectData {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (hs : 0 < s) (defect : Vec d → Vec d) (energy : Vec d → ℝ)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    {lam0 Lam0 : ℝ} (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hdesc : DescendantScalarCanonicalFluxDefectData Q a a0 defect energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminorm Q s defect ≤
      (geometricDiscount s 1)⁻¹ *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
        (Real.sqrt (((4 : ℝ) * matNorm a0)) * Real.sqrt (cubeAverage Q energy)) := by
  exact
    coarseFluxResponse_qone_of_cubeAverageFluxResponseControl
      (Q := Q) (a := a) (a0 := a0) (s := s) hs (defect := defect) (energy := energy)
      henergy_nonneg henergy_int
      (cubeAverageFluxResponseControl_of_descendantScalarCanonicalFluxDefectData
        (Q := Q) (a := a) (a0 := a0) (defect := defect) (energy := energy)
        ha0 ha0symm hdesc)
      hsum

/-- Note-facing `q = 1` deterministic coarse flux-response inequality for the
actual defect field of one harmonic function on `cubeSet Q`. -/
theorem coarseFluxResponse_qone_of_descendantScalarCanonicalFluxDefectAHarmonicData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (hs : 0 < s) {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (u : AHarmonicFunction a (cubeSet Q))
    (hdesc : DescendantScalarCanonicalFluxDefectAHarmonicData Q a a0 u)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminorm Q s
        (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x)) ≤
      (geometricDiscount s 1)⁻¹ *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
        (Real.sqrt (((4 : ℝ) * matNorm a0)) *
          Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a u))) := by
  let := isFiniteMeasureVolumeMeasureOnCubeSet Q
  have henergy_nonneg :
      ∀ x ∈ cubeSet Q, 0 ≤ scalarVariationEnergyIntegrand a u x :=
    scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) a hEll u
  have henergy_int :
      MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) (cubeSet Q)
        MeasureTheory.volume := by
    exact ResponseLinearIntegrabilityData.energy
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u
  exact
    coarseFluxResponse_qone_of_descendantScalarCanonicalFluxDefectData
      (Q := Q) (a := a) (a0 := a0) (s := s) hs
      (defect := fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))
      (energy := scalarVariationEnergyIntegrand a u)
      henergy_nonneg henergy_int ha0 ha0symm
      (descendantScalarCanonicalFluxDefectData_of_aHarmonicData
        (Q := Q) (a := a) (a0 := a0) (u := u) hdesc)
      hsum

/-- Finite-depth `q = 1` deterministic coarse flux-response bound for the
actual defect field of one harmonic function on `cubeSet Q`, with no separate
descendant witness package. -/
theorem coarseFluxResponse_qone_partialSeminorm_le_of_aHarmonicFunction
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (hs : 0 < s) {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (u : AHarmonicFunction a (cubeSet Q))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0))
    (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm Q s N
        (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x)) ≤
      (geometricDiscount s 1)⁻¹ *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
        (Real.sqrt (((4 : ℝ) * matNorm a0)) *
          Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a u))) := by
  let := isFiniteMeasureVolumeMeasureOnCubeSet Q
  have henergy_nonneg :
      ∀ x ∈ cubeSet Q, 0 ≤ scalarVariationEnergyIntegrand a u x :=
    scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) a hEll u
  have henergy_int :
      MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) (cubeSet Q)
        MeasureTheory.volume := by
    exact ResponseLinearIntegrabilityData.energy
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u
  exact
    coarseFluxResponse_qone_partialSeminorm_le_of_cubeAverageFluxResponseControl
      (Q := Q) (a := a) (a0 := a0) (s := s) hs
      (defect := fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))
      (energy := scalarVariationEnergyIntegrand a u)
      henergy_nonneg henergy_int
      (cubeAverageFluxResponseControl_of_aHarmonicFunction
        (Q := Q) (a := a) (a0 := a0) hEll ha0 ha0symm u)
      hsum N

/-- Note-facing `q = 1` deterministic coarse flux-response inequality for the
actual defect field of one harmonic function on `cubeSet Q`, with no separate
descendant witness package. -/
theorem coarseFluxResponse_qone_of_aHarmonicFunction
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (hs : 0 < s) {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (u : AHarmonicFunction a (cubeSet Q))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminorm Q s
        (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x)) ≤
      (geometricDiscount s 1)⁻¹ *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
        (Real.sqrt (((4 : ℝ) * matNorm a0)) *
          Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a u))) := by
  let := isFiniteMeasureVolumeMeasureOnCubeSet Q
  have henergy_nonneg :
      ∀ x ∈ cubeSet Q, 0 ≤ scalarVariationEnergyIntegrand a u x :=
    scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) a hEll u
  have henergy_int :
      MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) (cubeSet Q)
        MeasureTheory.volume := by
    exact ResponseLinearIntegrabilityData.energy
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u
  exact
    coarseFluxResponse_qone_of_cubeAverageFluxResponseControl
      (Q := Q) (a := a) (a0 := a0) (s := s) hs
      (defect := fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))
      (energy := scalarVariationEnergyIntegrand a u)
      henergy_nonneg henergy_int
      (cubeAverageFluxResponseControl_of_aHarmonicFunction
        (Q := Q) (a := a) (a0 := a0) hEll ha0 ha0symm u)
      hsum


end

end Homogenization
