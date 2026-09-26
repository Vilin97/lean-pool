/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.FinalRHS
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarPreliminaries

/-! # Young RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

/-!
# YoungRHS

The standard coarse-fluctuation estimate contains the initial term
`sqrt(tau_{m,k}) * sqrt(E[J_k])`.  For the flatness-rules route we need the
same theorem with this term treated by Young, yielding
`eta * E[J_k] + eta^{-1} * tau_{m,k}`.  This file derives that theorem from the
already proved Section 5.3 coarse-fluctuation estimate by a scalar comparison
of right-hand sides.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

/-- The coarse-fluctuation manuscript RHS with the initial square-root term
replaced by its Young envelope. -/
noncomputable def coarseFluctuationYoungManuscriptRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C ε η : ℝ) (k m : ℕ) (e : Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let scalarWeight := coarseFluctuationScalarWeightAtScale hP hStruct m
  let fluctuationSum := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let tauSum := coarseFluctuationTauSumAtScale hP hStruct hP4 k m e
  let unitMomentWeight := coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m
  let responseMoment := coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  C *
      (η * Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e +
        η⁻¹ * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) +
    C * ε * (Real.sqrt θ - 1) ^ 2 +
      C * ε⁻¹ * β⁻¹ * θ * fluctuationSum +
        C * ε⁻¹ * (β ^ 2)⁻¹ * scalarWeight * tauSum +
          C * (hP4.xi : ℝ) * ε⁻¹ * (β ^ 3)⁻¹ *
              Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              unitMomentWeight * responseMoment +
            C * ε⁻¹ * (β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ) (-2 * β * ((m - k : ℕ) : ℝ)) *
              scalarWeight * (θ - 1)

private theorem sqrt_mul_sqrt_le_young
    {x y η : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hη : 0 < η) :
    Real.sqrt x * Real.sqrt y ≤
      (η * y + η⁻¹ * x) / 2 := by
  have hyoung :=
    two_mul_le_add_mul_sq (a := Real.sqrt y) (b := Real.sqrt x) hη
  have hx_sq : (Real.sqrt x) ^ (2 : ℕ) = x := by
    simpa [pow_two] using Real.sq_sqrt hx
  have hy_sq : (Real.sqrt y) ^ (2 : ℕ) = y := by
    simpa [pow_two] using Real.sq_sqrt hy
  have htwice :
      2 * (Real.sqrt x * Real.sqrt y) ≤ η * y + η⁻¹ * x := by
    simpa [mul_assoc, mul_left_comm, mul_comm, hx_sq, hy_sq] using hyoung
  linarith

private theorem expectedResponseJCubeSet_nonneg
    {d : ℕ} (P : Ch04.RestrictionCoeffLaw d) (Q : TriadicCube d) (p q : Vec d) :
    0 ≤ Ch04.expectedResponseJCubeSet P Q p q := by
  dsimp [Ch04.expectedResponseJCubeSet]
  exact integral_nonneg fun a => Ch04.restrictionResponseJObservableCubeSet_nonneg Q p q a

/-- Scalar comparison of the standard Section 5.3 coarse-fluctuation RHS with
the Young-envelope RHS. -/
theorem coarseFluctuationManuscriptRHSAtScale_le_youngManuscriptRHSAtScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {C ε η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) :
    coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C ε k m e ≤
      coarseFluctuationYoungManuscriptRHSAtScale hP hStruct hP4 C ε η k m e := by
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hk_nonneg : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
  have hBlockM :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
  have hBlockK :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
  have hDescBlock :
      ∀ R, R ∈ descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hk_nonneg hkm_int hR hBlockK
  have htau :
      0 ≤ tauAtScale P (m : ℤ) (k : ℤ) p_e q_e :=
    Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hstat hk_nonneg hkm_int p_e q_e hBlockM hDescBlock
  have hresponse :
      0 ≤ Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e :=
    expectedResponseJCubeSet_nonneg P (originCube d (k : ℤ)) p_e q_e
  let T :=
    Real.sqrt (tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) *
      Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e)
  let Y :=
    η * Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e +
      η⁻¹ * tauAtScale P (m : ℤ) (k : ℤ) p_e q_e
  have hTY : 2 * T ≤ Y := by
    have h :=
      sqrt_mul_sqrt_le_young
        (x := tauAtScale P (m : ℤ) (k : ℤ) p_e q_e)
        (y := Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e)
        htau hresponse hη
    have hmul := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * T ≤ 2 * (Y / 2) := by
        simpa [T, Y, mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = Y := by ring
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfirst :
      C * T ≤ C * Y := by
    exact mul_le_mul_of_nonneg_left (by nlinarith [hTY, hT_nonneg]) hC
  unfold coarseFluctuationManuscriptRHSAtScale
  unfold coarseFluctuationYoungManuscriptRHSAtScale
  dsimp only
  nlinarith [hfirst]

/-- Section 5.3 coarse-fluctuation bound with the initial square-root term
replaced by the Young envelope. -/
theorem JUpperBoundCoarseFluctuations_young_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ε η : ℝ}, 0 < ε → ε ≤ 1 → 0 < η →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e ≤
          coarseFluctuationYoungManuscriptRHSAtScale
            hP hStruct hP4 C ε η k m e := by
  rcases JUpperBoundCoarseFluctuations_homogenizationScale params with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e he ε η hε hε_le hη
  have hstandard :=
    hC hP hstat hStruct hP4 hparams hkm e he hε hε_le
  have hcompare :=
    coarseFluctuationManuscriptRHSAtScale_le_youngManuscriptRHSAtScale
      hP hstat hStruct hP4 (C := C) (ε := ε) (η := η)
      hC_nonneg hη (k := k) (m := m) hkm.le e
  exact hstandard.trans hcompare

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
