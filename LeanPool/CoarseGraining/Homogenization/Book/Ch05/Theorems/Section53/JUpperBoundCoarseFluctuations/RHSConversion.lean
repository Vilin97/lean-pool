/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Assembly
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.EllipticityMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PositiveExcessDefectSquare
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.AdditivityDefects
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.LinearProductAbsorption

/-! # RHSConversion -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# RHS conversion for the coarse-fluctuation lemma

This file is proof-internal to the third Section 5.3 lemma.  It owns the
scalar/nonnegativity bookkeeping and the expectation-level conversion from the
first-lemma weak-norm RHS to the manuscript coarse-fluctuation RHS.
-/

noncomputable section

private theorem barSigmaStarAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaStarAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hInv : 0 < hP.barSigmaStarInvAtScale hStruct (m : ℤ) := by
    simpa [Ch04.RestrictionLawCarrier.barSigmaStarInvAtScale] using
      Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
        hP
        (Ch04.Internal.annealedPrimitiveScalarizationData_of_structuralLaw
          hP hStruct (m : ℤ))
        hBlock
  rw [hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct (m : ℤ)]
  exact inv_pos.mpr hInv

private theorem barSigmaAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < hP.barSigmaAtScale hStruct (m : ℤ) := by
  have hBlock :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have htheta :=
    Section52.one_le_thetaAtScale_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct (m : ℤ) hBlock
  have hstar_pos := barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hprod_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := by
    exact lt_of_lt_of_le zero_lt_one (by
      simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale] using htheta)
  exact pos_of_mul_pos_left hprod_pos (inv_pos.mpr hstar_pos).le

private theorem sigmaHatAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) :
    0 ≤ sigmaHatAtScale hP hStruct m := by
  exact Real.sqrt_nonneg _

private theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (m : ℤ) (R : TriadicCube d) (a : RegCoeffField d) :
    0 ≤ fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m R a := by
  simp [fullBlockNormalizedFluctuationOperatorNormSqAtScale,
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
    Ch04.fullBlockNormalizedFluctuationOperatorNormSq]

private theorem aemeasurable_vecNormSq_sub_const
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {F : α → Vec d} (hF : AEMeasurable F μ) (v : Vec d) :
    AEMeasurable (fun a : α => vecNormSq (F a - v)) μ := by
  have hcoord : ∀ i : Fin d, AEMeasurable (fun a : α => F a i - v i) μ := by
    intro i
    exact ((aemeasurable_pi_iff.mp hF) i).sub aemeasurable_const
  simpa [vecNormSq, vecDot] using
    (Finset.univ.aemeasurable_fun_sum
      (μ := μ)
      (f := fun i a => (F a i - v i) * (F a i - v i))
      (fun i _hi => (hcoord i).mul (hcoord i)))

/-- Nonnegativity of the scalar ellipticity weight in the final RHS. -/
theorem coarseFluctuationScalarWeightAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 ≤ coarseFluctuationScalarWeightAtScale hP hStruct m := by
  dsimp [coarseFluctuationScalarWeightAtScale]
  have hσ : 0 ≤ sigmaHatAtScale hP hStruct (m : ℤ) :=
    sigmaHatAtScale_nonneg hP hStruct (m : ℤ)
  have hσ_inv : 0 ≤ (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ :=
    inv_nonneg.mpr hσ
  have hstar_inv :
      0 ≤ (hP.barSigmaStarAtScale hStruct 0)⁻¹ :=
    (inv_pos.mpr (by
      simpa using barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0)).le
  have hbar :
      0 ≤ hP.barSigmaAtScale hStruct 0 :=
    (barSigmaAtScale_pos_of_P4 hP hStruct hP4 0).le
  exact add_nonneg (mul_nonneg hσ hstar_inv) (mul_nonneg hσ_inv hbar)

private theorem sigmaHatAtScale_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 < sigmaHatAtScale hP hStruct (m : ℤ) := by
  dsimp [sigmaHatAtScale]
  exact Real.sqrt_pos_of_pos
    (mul_pos (barSigmaAtScale_pos_of_P4 hP hStruct hP4 m)
      (barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m))

/-- The scalar weight in the coarse-fluctuation RHS is uniformly bounded
below.  This is just AM-GM applied to
`\widehat\sigma_m \bar\sigma_{*,0}^{-1}` and
`\widehat\sigma_m^{-1} \bar\sigma_0`, whose product is `Theta_0 ≥ 1`. -/
theorem one_le_coarseFluctuationScalarWeightAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    1 ≤ coarseFluctuationScalarWeightAtScale hP hStruct m := by
  dsimp [coarseFluctuationScalarWeightAtScale]
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let b0 := hP.barSigmaAtScale hStruct 0
  let c0 := hP.barSigmaStarAtScale hStruct 0
  let θ0 := thetaAtScale hP hStruct (0 : ℤ)
  let x := σ * c0⁻¹
  let y := σ⁻¹ * b0
  have hσ : 0 < σ := by
    simpa [σ] using sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hb0 : 0 < b0 := by
    simpa [b0] using barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
  have hc0 : 0 < c0 := by
    simpa [c0] using barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hσ.le (inv_pos.mpr hc0).le
  have hy : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg (inv_pos.mpr hσ).le hb0.le
  have hθ0_one : 1 ≤ θ0 := by
    simpa [θ0] using one_le_thetaAtScale_of_P4 hP hStruct hP4 0
  have hθ0_nonneg : 0 ≤ θ0 := le_trans zero_le_one hθ0_one
  have hxy : x * y = θ0 := by
    dsimp [x, y, θ0, thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale,
      b0, c0]
    field_simp [hσ.ne', hc0.ne']
  have hAM : 2 * Real.sqrt θ0 ≤ x + y :=
    two_mul_le_add_of_sq_le_mul hx hy (by
      rw [Real.sq_sqrt hθ0_nonneg, hxy])
  have hsqrt_one : 1 ≤ Real.sqrt θ0 := by
    simpa [θ0] using (Real.one_le_sqrt.mpr hθ0_one)
  have hone : 1 ≤ x + y := by nlinarith
  simpa [x, y, σ, b0, c0] using hone

/-- Nonnegativity of the full-block fluctuation sum.  The fluctuation term is
the squared Euclidean operator norm (`Matrix.toEuclideanCLM`), not a Frobenius
norm. -/
theorem coarseFluctuationFullBlockSumAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (k m : ℕ) :
    0 ≤ coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := by
  dsimp [coarseFluctuationFullBlockSumAtScale]
  refine Finset.sum_nonneg ?_
  intro n _hn
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (integral_nonneg fun a =>
      fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
        hP hStruct (m : ℤ) (originCube d n) a)

/-- Nonnegativity of the tau sum in the final RHS. -/
theorem coarseFluctuationTauSumAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) :
    0 ≤ coarseFluctuationTauSumAtScale hP hStruct hP4 k m e := by
  dsimp [coarseFluctuationTauSumAtScale]
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  refine Finset.sum_nonneg ?_
  intro n hn
  have hn_bounds := Finset.mem_Icc.mp hn
  have hn_nonneg : 0 ≤ n := by
    have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    linarith
  have hnm : n ≤ (m : ℤ) := hn_bounds.2
  have hOrigin :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (Int.toNat n : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 (Int.toNat n)
  have hOrigin' :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P := by
    simpa [Int.toNat_of_nonneg hn_nonneg] using hOrigin
  have hParent :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hDesc :
      ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) n →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hStruct.stationary hn_nonneg hnm hR hOrigin'
  have htau :
      0 ≤ tauAtScale P (m : ℤ) n p_e q_e :=
    Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hstat hn_nonneg hnm p_e q_e hParent hDesc
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) htau

/-- Nonnegativity of the unit-scale ellipticity moment weight. -/
theorem coarseFluctuationUnitMomentWeightAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    0 ≤ coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m := by
  dsimp [coarseFluctuationUnitMomentWeightAtScale]
  have hσ : 0 ≤ sigmaHatAtScale hP hStruct (m : ℤ) :=
    sigmaHatAtScale_nonneg hP hStruct (m : ℤ)
  have hσ_inv : 0 ≤ (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ :=
    inv_nonneg.mpr hσ
  have hLower :
      0 ≤ Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi :=
    Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos
  have hUpper :
      0 ≤ Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi :=
    Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos
  exact add_nonneg (mul_nonneg hσ hLower) (mul_nonneg hσ_inv hUpper)

/-- Nonnegativity of the response moment term. -/
theorem coarseFluctuationResponseMomentAtScale_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) :
    0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  dsimp [coarseFluctuationResponseMomentAtScale]
  let ζ := section53CoarseFluctuationZeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hJpow_nonneg :
      ∀ a : RegCoeffField d,
        0 ≤ Real.rpow
          (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p_e q_e a) ζ := by
    intro a
    exact Real.rpow_nonneg
      (Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p_e q_e a) _
  exact Real.rpow_nonneg (integral_nonneg hJpow_nonneg) _

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
  · intro j _hj
    have harg : Int.toNat (m - (m - (j : ℤ))) = j := by
      have hsub : m - (m - (j : ℤ)) = (j : ℤ) := by ring
      simp [hsub]
    exact congrArg F harg.symm

private theorem sum_Icc_betaWeight_le_five_beta_inv
    {k m : ℤ} (hkm : k ≤ m) {β : ℝ} (hβ : 0 < β) (hβ_le : β ≤ 1) :
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) ≤
      5 * β⁻¹ := by
  let L : ℕ := Int.toNat (m - k)
  have hsum_eq :
      (∑ n ∈ Finset.Icc (k + 1) m,
          Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ))) =
        ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    simpa [L] using
      (sum_range_to_Icc_descending (k := k) (m := m) hkm
        (fun j => Real.rpow (3 : ℝ) (-β * (j : ℝ)))).symm
  have hrange_le :
      (∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ))) ≤
        ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
          Real.rpow (3 : ℝ) (-β * (j : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      simpa only [Finset.mem_filter, and_true] using
        Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
    · intro j _hj _hj_not
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hgeom :=
    Homogenization.sum_filter_triadicDepthWeight_le_geometric_inv
      β L (fun _j => True) hβ
  have hgeom_five :
      (1 - Real.rpow (3 : ℝ) (-β))⁻¹ ≤ 5 * β⁻¹ :=
    Homogenization.Book.Ch02.inv_one_sub_rpow_three_neg_le_five_inv hβ hβ_le
  calc
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-β * (Int.toNat (m - n) : ℝ)))
        =
      ∑ j ∈ Finset.range L, Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hsum_eq
    _ ≤
      ∑ j ∈ (Finset.range (L + 1)).filter (fun _j => True),
        Real.rpow (3 : ℝ) (-β * (j : ℝ)) := hrange_le
    _ ≤ (1 - Real.rpow (3 : ℝ) (-β))⁻¹ := hgeom
    _ ≤ 5 * β⁻¹ := hgeom_five

/-- Expectation-level conversion for the paired high-scale average terms in the
weak-norm maximizer RHS.  This is the full-block fluctuation part of the
paired square estimate; the fluctuation observable is the squared Euclidean
operator norm (`Matrix.toEuclideanCLM`), not a Frobenius norm. -/
theorem integral_paired_highScaleAverageTerms_special_le_fullBlockSumAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (_hkm : k < m) (e : Vec d) (he : vecNormSq e = 1) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let t := hP4.sUpper + 2 * β
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let σ := sigmaHatAtScale hP hStruct (m : ℤ)
    let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
    let w : ℤ → ℝ :=
      fun n => Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
    Integrable
        (fun a : RegCoeffField d =>
          σ *
              (WeakNormsMaximizer.gradientAverageTermAtScale
                (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxAverageTermAtScale
                (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) P ∧
      ∫ a,
          (σ *
              (WeakNormsMaximizer.gradientAverageTermAtScale
                (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
            σ⁻¹ *
              (WeakNormsMaximizer.fluxAverageTermAtScale
                (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
        ≤
          (∑ n ∈ S, w n) *
            (2 * thetaAtScale hP hStruct (m : ℤ) *
              coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let X : RegCoeffField d → ℝ :=
    fun a =>
      σ *
          (WeakNormsMaximizer.gradientAverageTermAtScale
            (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
        σ⁻¹ *
          (WeakNormsMaximizer.fluxAverageTermAtScale
            (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2
  let Y : RegCoeffField d → ℝ :=
    fun a =>
      (∑ n ∈ S, w n) *
        ∑ n ∈ S, w n *
          descendantsAverage (originCube d (m : ℤ))
            (Int.toNat ((m : ℤ) - n))
            (fun R =>
              2 * θ *
                fullBlockNormalizedFluctuationOperatorNormSqAtScale
                  hP hStruct (m : ℤ) R a)
  have hβs : β ≤ s := by
    dsimp [s]
    linarith [hP4.sLower_pos, section53CoarseFluctuationBeta_pos hP4]
  have hβt : β ≤ t := by
    dsimp [t]
    linarith [hP4.sUpper_pos, section53CoarseFluctuationBeta_pos hP4]
  have hb : 0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hX_nonneg : 0 ≤ᵐ[P] X := by
    filter_upwards with a
    have hσ : 0 ≤ σ := by
      exact sigmaHatAtScale_nonneg hP hStruct (m : ℤ)
    exact add_nonneg
      (mul_nonneg hσ (sq_nonneg _))
      (mul_nonneg (inv_nonneg.mpr hσ) (sq_nonneg _))
  have hPoint : X ≤ᵐ[P] Y := by
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    have h :=
      paired_highScaleAverageTerms_special_le_weighted_fullBlockNormalized_fluctuation
        hP hStruct a ha (k := k) (m := m) β s t hβs hβt e hb hc he
    simpa [X, Y, S, w, σ, θ, p_e, q_e, p0_e, q0_e, s, t, β] using h
  have hTermInt :
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
  have hY_int : Integrable Y P := by
    have hsum :
        Integrable
          (fun a : RegCoeffField d =>
            ∑ n ∈ S, w n *
              descendantsAverage (originCube d (m : ℤ))
                (Int.toNat ((m : ℤ) - n))
                (fun R =>
                  2 * θ *
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
                      hP hStruct (m : ℤ) R a)) P :=
      MeasureTheory.integrable_finsetSum S hTermInt
    simpa [Y] using hsum.const_mul (∑ n ∈ S, w n)
  have hGradAvgAE :
      AEMeasurable
        (fun a : RegCoeffField d =>
          WeakNormsMaximizer.gradientAverageTermAtScale
            (m : ℤ) (k : ℤ) s p_e q_e p0_e a) P := by
    dsimp [WeakNormsMaximizer.gradientAverageTermAtScale]
    change AEMeasurable
      (fun a : RegCoeffField d =>
        ∑ n ∈ S,
          Real.rpow (3 : ℝ) (-s * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (descendantsAverage (originCube d (m : ℤ))
                (Int.toNat ((m : ℤ) - n))
                (fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseGradientAverageCubeSet
                      R R p_e q_e a.toFun - p0_e)))) P
    refine S.aemeasurable_fun_sum (μ := P) ?_
    intro n _hn
    exact
      aemeasurable_const.mul
        ((Ch04.aemeasurable_descendantsAverage
          (P := P) (Q := originCube d (m : ℤ))
          (j := Int.toNat ((m : ℤ) - n))
          (F := fun R a =>
            vecNormSq
              (Ch04.canonicalScalarResponseGradientAverageCubeSet
                R R p_e q_e a.toFun - p0_e))
          (fun R _hR =>
            aemeasurable_vecNormSq_sub_const
              (hP.aemeasurable_canonicalScalarResponseGradientAverage_cubeSet
                R R p_e q_e) p0_e)).sqrt)
  have hFluxAvgAE :
      AEMeasurable
        (fun a : RegCoeffField d =>
          WeakNormsMaximizer.fluxAverageTermAtScale
            (m : ℤ) (k : ℤ) t p_e q_e q0_e a) P := by
    dsimp [WeakNormsMaximizer.fluxAverageTermAtScale]
    change AEMeasurable
      (fun a : RegCoeffField d =>
        ∑ n ∈ S,
          Real.rpow (3 : ℝ) (-t * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (descendantsAverage (originCube d (m : ℤ))
                (Int.toNat ((m : ℤ) - n))
                (fun R =>
                  vecNormSq
                    (Ch04.canonicalScalarResponseFluxAverageCubeSet
                      R R p_e q_e a.toFun - q0_e)))) P
    refine S.aemeasurable_fun_sum (μ := P) ?_
    intro n _hn
    exact
      aemeasurable_const.mul
        ((Ch04.aemeasurable_descendantsAverage
          (P := P) (Q := originCube d (m : ℤ))
          (j := Int.toNat ((m : ℤ) - n))
          (F := fun R a =>
            vecNormSq
              (Ch04.canonicalScalarResponseFluxAverageCubeSet
                R R p_e q_e a.toFun - q0_e))
          (fun R _hR =>
            aemeasurable_vecNormSq_sub_const
              (hP.aemeasurable_canonicalScalarResponseFluxAverage_cubeSet
                R R p_e q_e) q0_e)).sqrt)
  have hXAE : AEMeasurable X P := by
    simpa [X, pow_two] using!
      (aemeasurable_const.mul (hGradAvgAE.mul hGradAvgAE)).add
        (aemeasurable_const.mul (hFluxAvgAE.mul hFluxAvgAE))
  have hX_int : Integrable X P := by
    refine Integrable.mono' hY_int hXAE.aestronglyMeasurable ?_
    filter_upwards [hPoint, hX_nonneg] with a hle hnonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hmono : ∫ a, X a ∂P ≤ ∫ a, Y a ∂P :=
    integral_mono_ae hX_int hY_int hPoint
  have hstationary :=
    integral_weighted_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq
      hP hstat hStruct hP4 k m
  have hY_eq :
      ∫ a, Y a ∂P =
        (∑ n ∈ S, w n) *
          (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) := by
    calc
      ∫ a, Y a ∂P =
          (∑ n ∈ S, w n) *
            ∫ a,
              ∑ n ∈ S, w n *
                descendantsAverage (originCube d (m : ℤ))
                  (Int.toNat ((m : ℤ) - n))
                  (fun R =>
                    2 * θ *
                      fullBlockNormalizedFluctuationOperatorNormSqAtScale
                        hP hStruct (m : ℤ) R a) ∂P := by
            rw [integral_const_mul]
      _ =
          (∑ n ∈ S, w n) *
            (∑ n ∈ S, w n *
              (2 * θ *
                ∫ a,
                  fullBlockNormalizedFluctuationOperatorNormSqAtScale
                    hP hStruct (m : ℤ) (originCube d n) a ∂P)) := by
            rw [hstationary]
      _ =
          (∑ n ∈ S, w n) *
            (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) := by
            congr 1
            simp [coarseFluctuationFullBlockSumAtScale, S, w, β, θ,
              Finset.mul_sum, mul_assoc, mul_comm]
  have hmain :
      ∫ a, X a ∂P ≤
        (∑ n ∈ S, w n) *
          (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) := by
    calc
      ∫ a, X a ∂P ≤ ∫ a, Y a ∂P := hmono
      _ =
          (∑ n ∈ S, w n) *
            (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) := hY_eq
  refine ⟨by simpa [X, S, w, σ, θ, s, t, p_e, q_e, p0_e, q0_e, β] using hX_int, ?_⟩
  simpa [X, S, w, σ, θ, s, t, p_e, q_e, p0_e, q0_e, β] using hmain

/-- The paired high-scale average part of the weak-norm maximizer RHS has the
manuscript `beta^{-1} * theta * full-block fluctuation` form.  The fluctuation
observable is the squared Euclidean operator norm (`Matrix.toEuclideanCLM`),
not a Frobenius norm. -/
theorem integral_paired_highScaleAverageTerms_special_le_beta_inv_fullBlockSumAtScale
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P)
        {k m : ℕ}, k < m → ∀ e : Vec d, vecNormSq e = 1 →
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let t := hP4.sUpper + 2 * β
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
        let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
        let σ := sigmaHatAtScale hP hStruct (m : ℤ)
        ∫ a,
            (σ *
                (WeakNormsMaximizer.gradientAverageTermAtScale
                  (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
              σ⁻¹ *
                (WeakNormsMaximizer.fluxAverageTermAtScale
                  (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
          ≤
            C * β⁻¹ * thetaAtScale hP hStruct (m : ℤ) *
              coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := by
  refine ⟨10, by norm_num, ?_⟩
  intro P hP hstat hStruct hP4 k m hkm e he
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let S := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  have hbase :=
    integral_paired_highScaleAverageTerms_special_le_fullBlockSumAtScale
      hP hstat hStruct hP4 hkm e he
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_le_one : β ≤ 1 := by
    have hle := sLower_add_beta_le_one hP4
    dsimp [β] at hle ⊢
    linarith [hP4.sLower_pos]
  have hsum_le :
      (∑ n ∈ S, w n) ≤ 5 * β⁻¹ := by
    simpa [S, w, β] using
      sum_Icc_betaWeight_le_five_beta_inv
        (k := (k : ℤ)) (m := (m : ℤ))
        (by exact_mod_cast hkm.le) hβ_pos hβ_le_one
  have hθ_nonneg : 0 ≤ θ := by
    have hθ_one : 1 ≤ θ := by
      simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
    linarith
  have hFull_nonneg :
      0 ≤ coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m :=
    coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4 k m
  have hβ_inv_nonneg : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ_pos.le
  have htail_nonneg :
      0 ≤ 2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := by
    exact mul_nonneg (mul_nonneg (by norm_num) hθ_nonneg) hFull_nonneg
  have hfactor :
      (∑ n ∈ S, w n) *
          (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m)
        ≤
      (5 * β⁻¹) *
          (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) :=
    mul_le_mul_of_nonneg_right hsum_le htail_nonneg
  have hrewrite :
      (5 * β⁻¹) *
          (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m)
        =
      10 * β⁻¹ * θ *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := by ring
  calc
    ∫ a,
        (σ *
            (WeakNormsMaximizer.gradientAverageTermAtScale
              (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
          σ⁻¹ *
            (WeakNormsMaximizer.fluxAverageTermAtScale
              (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
        ≤
      (∑ n ∈ S, w n) *
        (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) := by
          simpa [β, s, t, p_e, q_e, p0_e, q0_e, σ, θ, S, w] using hbase.2
    _ ≤
      (5 * β⁻¹) *
        (2 * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m) := hfactor
    _ =
      10 * β⁻¹ * θ *
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := hrewrite

/-- The beta-weighted response-defect square-root sum at the Section 5.3
special vectors is controlled by the manuscript weighted tau sum.  All
response integrability inputs are discharged from `(P4)` and the Ch4
law-facing integrability surface. -/
theorem integral_sq_beta_weighted_sqrt_responseDefectAverageAtScale_special_le_tauSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    ∫ a,
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ)
              (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (WeakNormsMaximizer.responseDefectAverageAtScale
                (m : ℤ) n p_e q_e a)) ^ 2 ∂P
      ≤
        (5 * β⁻¹) *
          coarseFluctuationTauSumAtScale hP hStruct hP4 k m e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hk_nonneg : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_le_one : β ≤ 1 := by
    have hle := sLower_add_beta_le_one hP4
    dsimp [β] at hle ⊢
    linarith [hP4.sLower_pos]
  have hBlockM :
      Integrable
        (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hParent :
      Integrable
        (Ch04.restrictionResponseJObservableCubeSet (originCube d (m : ℤ)) p_e q_e) P :=
    hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (originCube d (m : ℤ)) p_e q_e hBlockM
  have hDesc :
      ∀ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) n →
          Integrable (Ch04.restrictionResponseJObservableCubeSet R p_e q_e) P := by
    intro n hn R hR
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
      linarith
    have hnm : n ≤ (m : ℤ) := hn_bounds.2
    have hOrigin_nat :
        Integrable
          (Ch04.coarseFullBlockMatrixAtCube
            (originCube d ((Int.toNat n : ℕ) : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 (Int.toNat n)
    have hOrigin :
        Integrable
          (Ch04.coarseFullBlockMatrixAtCube (originCube d n)) P := by
      simpa [Int.toNat_of_nonneg hn_nonneg] using hOrigin_nat
    have hBlockR :
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P :=
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hn_nonneg hnm hR hOrigin
    exact
      hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p_e q_e hBlockR
  have hbase :=
    integral_sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_beta_inv_tauSum
      hP hstat hk_nonneg hkm_int hβ_pos hβ_le_one p_e q_e hParent hDesc
  simpa [coarseFluctuationTauSumAtScale, β, p_e, q_e] using hbase

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
