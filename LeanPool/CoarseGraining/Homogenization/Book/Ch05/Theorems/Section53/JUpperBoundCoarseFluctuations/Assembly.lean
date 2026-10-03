/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.FluctuationIntegrability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.HighScaleAverages

/-! # Assembly -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators

/-!
# Assembly for the coarse-fluctuation lemma

This file is the intended owner of the final proof of
`JUpperBoundCoarseFluctuations_homogenizationScale`.  The deterministic
high-scale bridge is available from `CoarseAverages.lean`; the remaining
assembly step needs a law-facing stationarity/integrability theorem for the
normalized full-block operator-norm-square fluctuation observable.
-/

noncomputable section

/-- The RHS obtained by applying the first Section 5.3 lemma to the
coarse-fluctuation special vectors, before the second and third Section 5.3
lemmas are used to rewrite it into manuscript coarse-fluctuation quantities. -/
noncomputable def specialWeakNormManuscriptRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale
    P (m : ℤ) (k : ℤ) s t
    (1 + JUpperBoundWeakNorms.section53CutoffBound (originCube d (m : ℤ)))
    (JUpperBoundWeakNorms.section53CutoffOscillationConstant (originCube d (m : ℤ)))
    (JUpperBoundWeakNorms.section53CutoffScaleSep
      (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - (k : ℤ))))
    (JUpperBoundWeakNorms.section53CutoffDualBound (originCube d (m : ℤ)) s)
    (JUpperBoundWeakNorms.section53CutoffDualBound (originCube d (m : ℤ)) t)
    (JUpperBoundWeakNorms.section53CutoffProductCoeff (originCube d (m : ℤ)) s t)
    p_e q_e p0_e q0_e

/-- Scalar weight multiplying the tau and low-scale tail terms in the final
coarse-fluctuation RHS. -/
noncomputable def coarseFluctuationScalarWeightAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℕ) : ℝ :=
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  σ * (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
    σ⁻¹ * hP.barSigmaAtScale hStruct 0

/-- Weighted sum of normalized full-block operator-norm-square fluctuation
expectations appearing in the final coarse-fluctuation RHS. -/
noncomputable def coarseFluctuationFullBlockSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
    Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (originCube d n) a ∂P

/-- Weighted tau sum appearing in the final coarse-fluctuation RHS. -/
noncomputable def coarseFluctuationTauSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
    Real.rpow (3 : ℝ) (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
      tauAtScale P (m : ℤ) n p_e q_e

/-- Unit-scale moment weight appearing in the final coarse-fluctuation RHS. -/
noncomputable def coarseFluctuationUnitMomentWeightAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) : ℝ :=
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  σ * Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi +
    σ⁻¹ * Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi

/-- Response moment appearing in the positive-excess contribution of the final
coarse-fluctuation RHS. -/
noncomputable def coarseFluctuationResponseMomentAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) : ℝ :=
  let ζ := section53CoarseFluctuationZeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  Real.rpow
    (∫ a,
      Real.rpow
        (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ ∂P)
    ζ⁻¹

/-- The six-term manuscript RHS from
`e.J.upper.bound.coarse.fluctuations.homogenization.scale`.

This is the target RHS for the final third Section 5.3 lemma.  The matrix
fluctuation term uses the Euclidean operator norm via
`fullBlockNormalizedFluctuationOperatorNormSqAtScale`. -/
noncomputable def coarseFluctuationManuscriptRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C ε : ℝ) (k m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let scalarWeight := coarseFluctuationScalarWeightAtScale hP hStruct m
  let fluctuationSum := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let tauSum := coarseFluctuationTauSumAtScale hP hStruct hP4 k m e
  let unitMomentWeight := coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m
  let responseMoment := coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  C * Real.sqrt (tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) *
      Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e) +
    C * ε * (Real.sqrt θ - 1) ^ 2 +
      C * ε⁻¹ * β⁻¹ * θ * fluctuationSum +
        C * ε⁻¹ * (β ^ 2)⁻¹ * scalarWeight * tauSum +
          C * (hP4.xi : ℝ) * ε⁻¹ * (β ^ 3)⁻¹ *
              Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              unitMomentWeight * responseMoment +
            C * ε⁻¹ * (β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ) (-2 * β * ((m - k : ℕ) : ℝ)) *
              scalarWeight * (θ - 1)

/-- The first Section 5.3 lemma instantiated at the special vectors used in
the coarse-fluctuation lemma.  The two integrability hypotheses are exactly
the finite-RHS side conditions intentionally left on
`JUpperBoundWeakNorms_homogenizationScale`; this theorem does not introduce a
new proof package. -/
theorem expectedCenteredResponseJAtScale_le_specialWeakNormManuscriptRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d)
    (hGradSq :
      let β := section53CoarseFluctuationBeta hP4
      let s := hP4.sLower + 2 * β
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
              (originCube d (m : ℤ)) s p_e q_e p0_e a.toFun) ^ 2) P)
    (hFluxSq :
      let β := section53CoarseFluctuationBeta hP4
      let t := hP4.sUpper + 2 * β
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (originCube d (m : ℤ)) t p_e q_e q0_e a.toFun) ^ 2) P) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e ≤
      specialWeakNormManuscriptRHSAtScale hP hStruct hP4 k m e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  have hk_nonneg : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hs_pos : 0 < s := by
    dsimp [s, β]
    linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
  have ht_pos : 0 < t := by
    dsimp [t, β]
    linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
  have hs_lt_one : s < 1 := by
    dsimp [s, β]
    have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
    have hupper := hP4.sUpper_pos
    have hbeta := section53CoarseFluctuationBeta_pos hP4
    nlinarith
  have hst : s + t ≤ 1 := by
    dsimp [s, t, β]
    have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
    nlinarith
  have hWeak :=
    JUpperBoundWeakNorms_homogenizationScale
      hP hstat hStruct hP4 hk_nonneg hkm_int
      (s := s) (t := t) hs_pos hs_lt_one ht_pos hst
      p_e q_e p0_e q0_e
      (by simpa [s, p_e, q_e, p0_e, β] using hGradSq)
      (by simpa [t, p_e, q_e, q0_e, β] using hFluxSq)
  have hCenter :=
    expectedResponseJCubeSet_sub_half_vecDot_specialCentering_eq_expectedCenteredResponseJAtScale
      hP hStruct hP4 m e
  calc
    expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e =
        Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e -
          (1 / 2 : ℝ) * vecDot p0_e q0_e := by
          rw [← hCenter]
    _ ≤
        specialWeakNormManuscriptRHSAtScale hP hStruct hP4 k m e := by
          simpa [specialWeakNormManuscriptRHSAtScale, s, t, p_e, q_e, p0_e, q0_e, β]
            using hWeak

/-- Proof-internal bridge from the Section 5.3 fluctuation notation to the
Ch4 law-facing stationarity theorem.  The observable is the Ch4 normalized
full-block operator-norm-square fluctuation; this theorem only rewrites the
proof-folder alias and applies stationarity. -/
private theorem integral_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) ∂P =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n) a ∂P := by
  simpa [fullBlockNormalizedFluctuationOperatorNormSqAtScale] using
    hP.integral_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
      hstat hStruct center hn hnm
      (by simpa [fullBlockNormalizedFluctuationOperatorNormSqAtScale] using! hOrigin)

/-- Constant multiples of the normalized full-block fluctuation descendant
average also stationarize to the origin cube.  This is the form used after the
deterministic coarse-average bridge, whose right side carries the deterministic
factor `2 * thetaAtScale`. -/
private theorem integral_descendantsAverage_const_mul_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) (C : ℝ)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            C *
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center R a) ∂P =
      C *
        ∫ a,
          fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct center (originCube d n) a ∂P := by
  have hbase :=
    integral_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
      hP hstat hStruct center hn hnm hOrigin
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            C *
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center R a) ∂P
        =
      ∫ a,
        C *
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (fun R =>
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center R a) ∂P := by
          congr 1
          ext a
          rw [descendantsAverage_mul_left]
    _ =
      C *
        ∫ a,
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (fun R =>
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center R a) ∂P := by
          rw [integral_const_mul]
    _ =
      C *
        ∫ a,
          fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct center (originCube d n) a ∂P := by
          rw [hbase]

/-- Expectation-level stationarity conversion for the weighted full-block
fluctuation sum generated by the deterministic high-scale bridge. -/
theorem integral_weighted_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) :
    let β := section53CoarseFluctuationBeta hP4
    let θ := thetaAtScale hP hStruct (m : ℤ)
    let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
    let w : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    ∫ a,
        ∑ n ∈ S, w n *
          descendantsAverage (originCube d (m : ℤ))
            (Int.toNat ((m : ℤ) - n))
            (fun R =>
              2 * θ *
                fullBlockNormalizedFluctuationOperatorNormSqAtScale
                  hP hStruct (m : ℤ) R a) ∂P =
      ∑ n ∈ S, w n *
        (2 * θ *
          ∫ a,
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (originCube d n) a ∂P) := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  have htermInt :
      ∀ n ∈ S,
        Integrable
          (fun a : RegCoeffField d =>
            w n *
              descendantsAverage (originCube d (m : ℤ))
                (Int.toNat ((m : ℤ) - n))
                (fun R =>
                  2 * θ *
                    fullBlockNormalizedFluctuationOperatorNormSqAtScale
                      hP hStruct (m : ℤ) R a)) P := by
    intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by
      have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
      linarith
    have hnm : n ≤ (m : ℤ) := hn_bounds.2
    have hOrigin :
        Integrable
          (fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (m : ℤ) (originCube d n)) P := by
      have hnat :=
        Section52.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_originCube_from_P4
          hP hStruct hP4 (m : ℤ) (Int.toNat n)
      simpa [Int.toNat_of_nonneg hn_nonneg] using! hnat
    have hdesc :
        Integrable
          (fun a : RegCoeffField d =>
            descendantsAverage (originCube d (m : ℤ))
              (Int.toNat ((m : ℤ) - n))
              (fun R =>
                2 * θ *
                  fullBlockNormalizedFluctuationOperatorNormSqAtScale
                    hP hStruct (m : ℤ) R a)) P := by
      refine Ch04.integrable_descendantsAverage ?_
      intro R hR
      have hRscale : R ∈ descendantsAtScale (originCube d (m : ℤ)) n := by
        simpa [descendantsAtScale_eq_descendantsAtDepth
          (originCube d (m : ℤ)) hnm] using! hR
      exact
        (hP.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_mem_descendantsAtScale_originCube
          hstat hStruct (m : ℤ) hn_nonneg hnm hRscale hOrigin).const_mul (2 * θ)
    exact hdesc.const_mul (w n)
  calc
    ∫ a,
        ∑ n ∈ S, w n *
          descendantsAverage (originCube d (m : ℤ))
            (Int.toNat ((m : ℤ) - n))
            (fun R =>
              2 * θ *
                fullBlockNormalizedFluctuationOperatorNormSqAtScale
                  hP hStruct (m : ℤ) R a) ∂P
        =
      ∑ n ∈ S,
        ∫ a,
          w n *
            descendantsAverage (originCube d (m : ℤ))
              (Int.toNat ((m : ℤ) - n))
              (fun R =>
                2 * θ *
                  fullBlockNormalizedFluctuationOperatorNormSqAtScale
                    hP hStruct (m : ℤ) R a) ∂P := by
          rw [integral_finsetSum S htermInt]
    _ =
      ∑ n ∈ S, w n *
        (2 * θ *
          ∫ a,
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (originCube d n) a ∂P) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hn_bounds := Finset.mem_Icc.mp hn
          have hn_nonneg : 0 ≤ n := by
            have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
            linarith
          have hnm : n ≤ (m : ℤ) := hn_bounds.2
          have hOrigin :
              Integrable
                (fullBlockNormalizedFluctuationOperatorNormSqAtScale
                  hP hStruct (m : ℤ) (originCube d n)) P := by
            have hnat :=
              Section52.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_originCube_from_P4
                hP hStruct hP4 (m : ℤ) (Int.toNat n)
            simpa [Int.toNat_of_nonneg hn_nonneg] using! hnat
          have hstatn :=
            integral_descendantsAverage_const_mul_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
              hP hstat hStruct (m : ℤ) hn_nonneg hnm (2 * θ) hOrigin
          calc
            ∫ a,
                w n *
                  descendantsAverage (originCube d (m : ℤ))
                    (Int.toNat ((m : ℤ) - n))
                    (fun R =>
                      2 * θ *
                        fullBlockNormalizedFluctuationOperatorNormSqAtScale
                          hP hStruct (m : ℤ) R a) ∂P
                =
              w n *
                ∫ a,
                  descendantsAverage (originCube d (m : ℤ))
                    (Int.toNat ((m : ℤ) - n))
                    (fun R =>
                      2 * θ *
                        fullBlockNormalizedFluctuationOperatorNormSqAtScale
                          hP hStruct (m : ℤ) R a) ∂P := by
                  rw [integral_const_mul]
            _ =
              w n *
                (2 * θ *
                  ∫ a,
                    fullBlockNormalizedFluctuationOperatorNormSqAtScale
                      hP hStruct (m : ℤ) (originCube d n) a ∂P) := by
                  rw [hstatn]

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
