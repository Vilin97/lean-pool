/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.PairedWeakNormSquares
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.LinearProductAbsorption
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.CutoffOscillationUniform
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.RHSConversion
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.WeakNormSquareIntegrability

/-! # Final RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

/-!
# Final RHS conversion for the coarse-fluctuation lemma

This proof-internal file collects the already proved expectation estimates into
the manuscript coarse-fluctuation RHS.
-/

noncomputable section

attribute [local irreducible] specialWeakNormManuscriptRHSAtScale
  coarseFluctuationManuscriptRHSAtScale

private theorem firstTermCoeff_le_dimensional
    {d : ℕ} (Q : TriadicCube d) :
    2 * (1 + JUpperBoundWeakNorms.section53CutoffBound Q) ≤
      2 * (1 + (2 : ℝ) ^ d) := by
  have hB := JUpperBoundWeakNorms.section53CutoffBound_le_two_pow_card Q
  nlinarith

private theorem firstTermCoeff_dimensional_nonneg (d : ℕ) :
    0 ≤ 2 * (1 + (2 : ℝ) ^ d) := by
  positivity

private theorem finalRHS_linear_pair
    {LinProd Center Pairs Ssum CLin CPair ε : ℝ}
    (hCLin_nonneg : 0 ≤ CLin) (hε_inv_nonneg : 0 ≤ ε⁻¹)
    (hLin : LinProd ≤ CLin * ε * Center + CLin * ε⁻¹ * Pairs)
    (hPair : Pairs ≤ CPair * Ssum) :
    LinProd ≤ CLin * ε * Center + (CLin * CPair) * ε⁻¹ * Ssum := by
  have hpair_term :
      CLin * ε⁻¹ * Pairs ≤ (CLin * CPair) * ε⁻¹ * Ssum := by
    calc
      CLin * ε⁻¹ * Pairs ≤ CLin * ε⁻¹ * (CPair * Ssum) := by
        exact mul_le_mul_of_nonneg_left hPair
          (mul_nonneg hCLin_nonneg hε_inv_nonneg)
      _ = (CLin * CPair) * ε⁻¹ * Ssum := by ring
  calc
    LinProd ≤ CLin * ε * Center + CLin * ε⁻¹ * Pairs := hLin
    _ ≤ CLin * ε * Center + (CLin * CPair) * ε⁻¹ * Ssum :=
        by nlinarith [hpair_term]

private theorem finalRHS_osc_pair
    {D Ssum COsc CLin CPair C ε : ℝ}
    (hε_inv_nonneg : 0 ≤ ε⁻¹) (hS_nonneg : 0 ≤ Ssum)
    (hD_le_Ssum : D ≤ Ssum) (hCOsc_nonneg : 0 ≤ COsc)
    (hCOscPair_le : COsc + CLin * CPair ≤ C) :
    COsc * ε⁻¹ * D + (CLin * CPair) * ε⁻¹ * Ssum ≤
      C * ε⁻¹ * Ssum := by
  have hleft :
      COsc * ε⁻¹ * D ≤ COsc * ε⁻¹ * Ssum := by
    exact mul_le_mul_of_nonneg_left hD_le_Ssum
      (mul_nonneg hCOsc_nonneg hε_inv_nonneg)
  have hsum :
      COsc * ε⁻¹ * Ssum + (CLin * CPair) * ε⁻¹ * Ssum ≤
        C * ε⁻¹ * Ssum := by
    have hcoeff :
        (COsc + CLin * CPair) * (ε⁻¹ * Ssum) ≤
          C * (ε⁻¹ * Ssum) := by
      exact mul_le_mul_of_nonneg_right hCOscPair_le
        (mul_nonneg hε_inv_nonneg hS_nonneg)
    calc
      COsc * ε⁻¹ * Ssum + (CLin * CPair) * ε⁻¹ * Ssum =
          (COsc + CLin * CPair) * (ε⁻¹ * Ssum) := by ring
      _ ≤ C * (ε⁻¹ * Ssum) := hcoeff
      _ = C * ε⁻¹ * Ssum := by ring
  have hleftsum :
      COsc * ε⁻¹ * D + (CLin * CPair) * ε⁻¹ * Ssum ≤
        COsc * ε⁻¹ * Ssum + (CLin * CPair) * ε⁻¹ * Ssum :=
    by nlinarith [hleft]
  exact hleftsum.trans hsum

private theorem finalRHS_first_center
    {first T Center CLin C ε : ℝ}
    (hT_nonneg : 0 ≤ T) (hCenter_nonneg : 0 ≤ Center)
    (hε_nonneg : 0 ≤ ε) (hfirst_le : first ≤ C)
    (hCLin_le : CLin ≤ C) :
    first * T + CLin * ε * Center ≤ C * T + C * ε * Center := by
  have hfirst : first * T ≤ C * T :=
    mul_le_mul_of_nonneg_right hfirst_le hT_nonneg
  have hcenter : CLin * ε * Center ≤ C * ε * Center := by
    calc
      CLin * ε * Center = CLin * (ε * Center) := by ring
      _ ≤ C * (ε * Center) :=
          mul_le_mul_of_nonneg_right hCLin_le
            (mul_nonneg hε_nonneg hCenter_nonneg)
      _ = C * ε * Center := by ring
  exact add_le_add hfirst hcenter

private theorem finalRHS_combine_three
    {A B C D E Y Z : ℝ}
    (hB : B ≤ D + (C + E)) (hA : A + C ≤ Y) (hD : D + E ≤ Z) :
    A + B ≤ Y + Z := by
  calc
    A + B ≤ A + (D + (C + E)) := add_le_add (le_refl A) hB
    _ = (A + C) + (D + E) := by
      rw [add_comm D (C + E)]
      rw [add_assoc C E D]
      rw [add_comm E D]
      rw [← add_assoc A C (D + E)]
    _ ≤ Y + Z := add_le_add hA hD

private theorem finalRHS_bound
    {first T Osc LinProd COsc ε D CLin Center CPair Pairs Ssum C : ℝ}
    (hCLin_nonneg : 0 ≤ CLin) (hε_inv_nonneg : 0 ≤ ε⁻¹)
    (hLin' : LinProd ≤ CLin * ε * Center + CLin * ε⁻¹ * Pairs)
    (hPair' : Pairs ≤ CPair * Ssum)
    (hS_nonneg : 0 ≤ Ssum) (hD_le_Ssum : D ≤ Ssum)
    (hCOsc_nonneg : 0 ≤ COsc) (hCOscPair_le : COsc + CLin * CPair ≤ C)
    (hOsc' : Osc ≤ COsc * ε⁻¹ * D)
    (hT_nonneg : 0 ≤ T) (hCenter_nonneg : 0 ≤ Center)
    (hε_nonneg : 0 ≤ ε) (hFirstCoeff_le : first ≤ C) (hCLin_le : CLin ≤ C) :
    first * T + Osc + LinProd ≤ C * T + C * ε * Center + C * ε⁻¹ * Ssum := by
  have hLinPair :=
    finalRHS_linear_pair hCLin_nonneg hε_inv_nonneg hLin' hPair'
  have hOscPair :=
    finalRHS_osc_pair hε_inv_nonneg hS_nonneg hD_le_Ssum hCOsc_nonneg
      hCOscPair_le
  have hosc_lin :
      Osc + LinProd ≤
      COsc * ε⁻¹ * D +
        (CLin * ε * Center + (CLin * CPair) * ε⁻¹ * Ssum) :=
    add_le_add hOsc' hLinPair
  have hfirst_center :=
    finalRHS_first_center hT_nonneg hCenter_nonneg hε_nonneg hFirstCoeff_le hCLin_le
  have hcombine :
      first * T +
          (Osc + LinProd) ≤
        (C * T + C * ε * Center) + C * ε⁻¹ * Ssum :=
    finalRHS_combine_three hosc_lin hfirst_center hOscPair
  simpa [add_assoc] using hcombine

private theorem finalRHS_sum_four_nonneg
    {A B R D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    0 ≤ A + B + R + D := by
  nlinarith

private theorem finalRHS_fourth_le_sum_four
    {A B R D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    D ≤ A + B + R + D := by
  nlinarith

private theorem finalRHS_constant_nonneg
    {CFirst COsc CLin CPair : ℝ}
    (hCFirst : 0 ≤ CFirst) (hCOsc : 0 ≤ COsc) (hCLin : 0 ≤ CLin)
    (hCPair : 0 ≤ CPair) :
    0 ≤ CFirst + COsc + CLin + CLin * CPair + 1 := by
  have hprod : 0 ≤ CLin * CPair := mul_nonneg hCLin hCPair
  nlinarith

private theorem finalRHS_firstCoeff_le_constant
    {first CFirst COsc CLin CPair : ℝ}
    (hfirst : first ≤ CFirst) (hCOsc : 0 ≤ COsc) (hCLin : 0 ≤ CLin)
    (hCPair : 0 ≤ CPair) :
    first ≤ CFirst + COsc + CLin + CLin * CPair + 1 := by
  have hprod : 0 ≤ CLin * CPair := mul_nonneg hCLin hCPair
  nlinarith

private theorem finalRHS_oscPairCoeff_le_constant
    {CFirst COsc CLin CPair : ℝ}
    (hCFirst : 0 ≤ CFirst) (hCLin : 0 ≤ CLin) :
    COsc + CLin * CPair ≤ CFirst + COsc + CLin + CLin * CPair + 1 := by
  nlinarith

private theorem finalRHS_linearCoeff_le_constant
    {CFirst COsc CLin CPair : ℝ}
    (hCFirst : 0 ≤ CFirst) (hCOsc : 0 ≤ COsc) (hCLin : 0 ≤ CLin)
    (hCPair : 0 ≤ CPair) :
    CLin ≤ CFirst + COsc + CLin + CLin * CPair + 1 := by
  have hprod : 0 ≤ CLin * CPair := mul_nonneg hCLin hCPair
  nlinarith

private theorem specialWeakNormManuscriptRHSAtScale_eq_decomp
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Vec d) :
    specialWeakNormManuscriptRHSAtScale hP hStruct hP4 k m e =
      let β := section53CoarseFluctuationBeta hP4
      let s := hP4.sLower + 2 * β
      let t := hP4.sUpper + 2 * β
      let Q : TriadicCube d := originCube d (m : ℤ)
      let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
      let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
      let gradWeak :=
        Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
      let fluxWeak :=
        Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
      let G := ∫ a, (gradWeak a) ^ 2 ∂P
      let F := ∫ a, (fluxWeak a) ^ 2 ∂P
      let T :=
        Real.sqrt (tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) *
          Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e)
      let Osc :=
        JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
          JUpperBoundWeakNorms.section53CutoffScaleSep Q j *
            Ch04.expectedResponseJCubeSet P Q p_e q_e
      let LinProd :=
        (1 / 2 : ℝ) * ‖q0_e‖ *
            (((Fintype.card (Fin d) : ℝ) *
              ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q *
                JUpperBoundWeakNorms.section53CutoffDualBound Q s)) *
              ∫ a, gradWeak a ∂P) +
          (1 / 2 : ℝ) * ‖p0_e‖ *
            (((Fintype.card (Fin d) : ℝ) *
              ((3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q *
                JUpperBoundWeakNorms.section53CutoffDualBound Q t)) *
              ∫ a, fluxWeak a ∂P) +
            JUpperBoundWeakNorms.section53CutoffProductCoeff Q s t *
              (Real.sqrt G * Real.sqrt F)
      (2 * (1 + JUpperBoundWeakNorms.section53CutoffBound Q)) * T + Osc + LinProd := by
  unfold specialWeakNormManuscriptRHSAtScale
  simp [JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale]
  ring

private theorem coarseFluctuationManuscriptRHSAtScale_eq_decomp
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (C ε : ℝ) (k m : ℕ) (e : Vec d) :
    coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C ε k m e =
      let β := section53CoarseFluctuationBeta hP4
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let θ := thetaAtScale hP hStruct (m : ℤ)
      let T :=
        Real.sqrt (tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) *
          Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e)
      let Center := (Real.sqrt θ - 1) ^ 2
      let A :=
        β⁻¹ * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
      let B :=
        (β ^ 2)⁻¹ * coarseFluctuationScalarWeightAtScale hP hStruct m *
          coarseFluctuationTauSumAtScale hP hStruct hP4 k m e
      let R :=
        (hP4.xi : ℝ) * (β ^ 3)⁻¹ * Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
          coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
      let D :=
        (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
            coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)
      let Ssum := A + B + R + D
      C * T + C * ε * Center + C * ε⁻¹ * Ssum := by
  unfold coarseFluctuationManuscriptRHSAtScale
  simp [mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The first-lemma special-vector RHS is bounded by the final manuscript
coarse-fluctuation RHS. -/
theorem specialWeakNormManuscriptRHSAtScale_le_coarseFluctuationManuscriptRHSAtScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        specialWeakNormManuscriptRHSAtScale hP hStruct hP4 k m e ≤
          coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C ε k m e := by
  classical
  rcases cutoffOscillation_special_expectedResponse_le_lowScaleTail_uniform
      (d := d) with ⟨COsc, hCOsc_nonneg, hOsc_all⟩
  rcases linearProductTerms_special_le_centering_add_pairedWeakNormSquares
      (d := d) with ⟨CLin, hCLin_nonneg, hLin_all⟩
  rcases paired_weakNormSquares_special_le_coarseFluctuationTerms
      params with ⟨CPair, hCPair_nonneg, hPair_all⟩
  let CFirst : ℝ := 2 * (1 + (2 : ℝ) ^ d)
  let C : ℝ := CFirst + COsc + CLin + CLin * CPair + 1
  have hCFirst_nonneg : 0 ≤ CFirst := by
    simpa [CFirst] using firstTermCoeff_dimensional_nonneg d
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using
      finalRHS_constant_nonneg hCFirst_nonneg hCOsc_nonneg hCLin_nonneg hCPair_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e he ε hε hε_le
  subst params
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := thetaAtScale hP hStruct (m : ℤ)
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  let G := ∫ a, (gradWeak a) ^ 2 ∂P
  let F := ∫ a, (fluxWeak a) ^ 2 ∂P
  let T :=
    Real.sqrt (tauAtScale P (m : ℤ) (k : ℤ) p_e q_e) *
      Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d (k : ℤ)) p_e q_e)
  let Center := (Real.sqrt θ - 1) ^ 2
  let A :=
    β⁻¹ * θ * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let B :=
    (β ^ 2)⁻¹ * coarseFluctuationScalarWeightAtScale hP hStruct m *
      coarseFluctuationTauSumAtScale hP hStruct hP4 k m e
  let R :=
    (hP4.xi : ℝ) * (β ^ 3)⁻¹ * Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
      coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let D :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
        coarseFluctuationScalarWeightAtScale hP hStruct m * (θ - 1)
  let Ssum := A + B + R + D
  let Osc :=
    JUpperBoundWeakNorms.section53CutoffOscillationConstant Q *
      JUpperBoundWeakNorms.section53CutoffScaleSep Q j *
        Ch04.expectedResponseJCubeSet P Q p_e q_e
  let LinProd :=
    (1 / 2 : ℝ) * ‖q0_e‖ *
        (((Fintype.card (Fin d) : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q *
            JUpperBoundWeakNorms.section53CutoffDualBound Q s)) *
          ∫ a, gradWeak a ∂P) +
      (1 / 2 : ℝ) * ‖p0_e‖ *
        (((Fintype.card (Fin d) : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q *
            JUpperBoundWeakNorms.section53CutoffDualBound Q t)) *
          ∫ a, fluxWeak a ∂P) +
        JUpperBoundWeakNorms.section53CutoffProductCoeff Q s t *
          (Real.sqrt G * Real.sqrt F)
  let Pairs := σ * G + σ⁻¹ * F
  have hGradSq :
      Integrable (fun a : RegCoeffField d => (gradWeak a) ^ 2) P := by
    have h :=
      integrable_specialGradientWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialGradientWeakNormSquare at h
    simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using h
  have hFluxSq :
      Integrable (fun a : RegCoeffField d => (fluxWeak a) ^ 2) P := by
    have h :=
      integrable_specialFluxWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialFluxWeakNormSquare at h
    simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using h
  have hOsc := hOsc_all hP hStruct hP4 hkm e he hε hε_le
  have hLin := hLin_all hP hStruct hP4 hkm e he hε hε_le
      (by simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using hGradSq)
      (by simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using hFluxSq)
  have hPair := hPair_all hP hstat hStruct hP4 rfl hkm e he
      (by simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using hGradSq)
      (by simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using hFluxSq)
  have hOsc' : Osc ≤ COsc * ε⁻¹ * D := by
    have hOsc0 :
        Osc ≤
          COsc * ε⁻¹ * (β ^ 2)⁻¹ *
            Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
              coarseFluctuationScalarWeightAtScale hP hStruct m *
                (θ - 1) := by
      simpa [Osc, β, Q, j, p_e, q_e, θ] using hOsc
    calc
      Osc ≤
          COsc * ε⁻¹ * (β ^ 2)⁻¹ *
            Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
              coarseFluctuationScalarWeightAtScale hP hStruct m *
                (θ - 1) := hOsc0
      _ = COsc * ε⁻¹ * D := by
          simp [D]
          ring
  have hLin' :
      LinProd ≤ CLin * ε * Center + CLin * ε⁻¹ * Pairs := by
    simpa [LinProd, Pairs, Center, β, s, t, Q, p_e, q_e, p0_e, q0_e,
      σ, θ, gradWeak, fluxWeak, G, F] using hLin
  have hPair' : Pairs ≤ CPair * Ssum := by
    simpa [Pairs, Ssum, A, B, R, D, β, s, t, Q, p_e, q_e, p0_e, q0_e,
      σ, θ, gradWeak, fluxWeak, G, F] using hPair
  obtain ⟨hA_nonneg, hB_nonneg, hR_nonneg, hD_nonneg⟩ :=
    coarseFluctuationTerms_nonneg hP hstat hStruct hP4 k m e
  have hS_nonneg : 0 ≤ Ssum := by
    simpa [Ssum] using
      finalRHS_sum_four_nonneg hA_nonneg hB_nonneg hR_nonneg hD_nonneg
  have hD_le_Ssum : D ≤ Ssum := by
    simpa [Ssum] using
      finalRHS_fourth_le_sum_four (D := D) hA_nonneg hB_nonneg hR_nonneg
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hCenter_nonneg : 0 ≤ Center := by
    exact sq_nonneg _
  have hε_nonneg : 0 ≤ ε := hε.le
  have hε_inv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε_nonneg
  have hFirstCoeff_le : 2 * (1 + JUpperBoundWeakNorms.section53CutoffBound Q) ≤ C := by
    have hdim := firstTermCoeff_le_dimensional Q
    simpa [C, CFirst] using
      finalRHS_firstCoeff_le_constant hdim hCOsc_nonneg hCLin_nonneg hCPair_nonneg
  have hCOscPair_le : COsc + CLin * CPair ≤ C := by
    simpa [C] using
      finalRHS_oscPairCoeff_le_constant (CPair := CPair) hCFirst_nonneg hCLin_nonneg
  have hCLin_le : CLin ≤ C := by
    simpa [C] using
      finalRHS_linearCoeff_le_constant hCFirst_nonneg hCOsc_nonneg hCLin_nonneg
        hCPair_nonneg
  have hSpecial_eq :
      specialWeakNormManuscriptRHSAtScale hP hStruct hP4 k m e =
        (2 * (1 + JUpperBoundWeakNorms.section53CutoffBound Q)) * T +
          Osc + LinProd := by
    simpa [β, s, t, Q, j, p_e, q_e, p0_e, q0_e, T, Osc, LinProd, G, F,
      gradWeak, fluxWeak] using
      specialWeakNormManuscriptRHSAtScale_eq_decomp hP hStruct hP4 k m e
  have hCoarse_eq :
      coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C ε k m e =
        C * T + C * ε * Center + C * ε⁻¹ * Ssum := by
    simpa [T, Center, Ssum, A, B, R, D, β, p_e, q_e, θ, C] using
      coarseFluctuationManuscriptRHSAtScale_eq_decomp hP hStruct hP4 C ε k m e
  have hBound :
      specialWeakNormManuscriptRHSAtScale hP hStruct hP4 k m e ≤
        C * T + C * ε * Center + C * ε⁻¹ * Ssum := by
    rw [hSpecial_eq]
    exact finalRHS_bound hCLin_nonneg hε_inv_nonneg hLin' hPair' hS_nonneg
      hD_le_Ssum hCOsc_nonneg hCOscPair_le hOsc' hT_nonneg hCenter_nonneg
      hε_nonneg hFirstCoeff_le hCLin_le
  rw [hCoarse_eq]
  exact hBound

/-- The third Section 5.3 coarse-fluctuation lemma, assembled from the
first-lemma special-vector estimate and the final RHS conversion. -/
theorem JUpperBoundCoarseFluctuations_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (_hstat : Ch04.RestrictionStationaryLaw P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e ≤
          coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C ε k m e := by
  classical
  rcases
    specialWeakNormManuscriptRHSAtScale_le_coarseFluctuationManuscriptRHSAtScale
      params with
    ⟨C, hC_nonneg, hRHS_all⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e he ε hε hε_le
  subst params
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : TriadicCube d := originCube d (m : ℤ)
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let gradWeak :=
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p_e q_e p0_e
  let fluxWeak :=
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p_e q_e q0_e
  have hGradSq :
      Integrable (fun a : RegCoeffField d => (gradWeak a) ^ 2) P := by
    have h :=
      integrable_specialGradientWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialGradientWeakNormSquare at h
    simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using h
  have hFluxSq :
      Integrable (fun a : RegCoeffField d => (fluxWeak a) ^ 2) P := by
    have h :=
      integrable_specialFluxWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialFluxWeakNormSquare at h
    simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using h
  have hRHS := hRHS_all hP hstat hStruct hP4 rfl hkm e he hε hε_le
  dsimp only
  exact
    (expectedCenteredResponseJAtScale_le_specialWeakNormManuscriptRHSAtScale
      hP hstat hStruct hP4 hkm e
      (by simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using hGradSq)
      (by simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using hFluxSq)).trans hRHS

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
