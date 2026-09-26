/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.NormalizedCutoff
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarPreliminaries

/-! # Young RHS -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# YoungRHS

An alternative expectation surface for the first Section 5.3 lemma.  The
standard manuscript RHS collapses the additivity term by Cauchy in probability,
giving `sqrt tau * sqrt E[J_k]`.  For the flatness-rules route we keep the
estimate base-free by applying Young to that scalar product, producing
`eta * E[J_k] + eta^{-1} * tau` instead.
-/

open MeasureTheory
open scoped BigOperators
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- Manuscript expected RHS with the first square-root additivity term replaced
by its Young envelope. -/
noncomputable def jUpperWeakNormYoungManuscriptExpectedRHSAtScale {d : ℕ}
    (P : Ch04.RestrictionCoeffLaw d) (m k : ℤ) (s t : ℝ)
    (C Cosc scaleSep BφS BφT Cprod η : ℝ)
    (p q p0 q0 : Vec d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let gradWeak : RegCoeffField d → ℝ := fun a =>
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a.toFun
  let fluxWeak : RegCoeffField d → ℝ := fun a =>
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a.toFun
  let gradCoeff := (3 : ℝ) ^ ((d : ℝ) + s) * cubeBesovScaleWeight (-s) Q * BφS
  let fluxCoeff := (3 : ℝ) ^ ((d : ℝ) + t) * cubeBesovScaleWeight (-t) Q * BφT
  let scaledGrad : RegCoeffField d → ℝ := gradWeak
  let scaledFlux : RegCoeffField d → ℝ := fluxWeak
  C *
      (η * Ch04.expectedResponseJCubeSet P (originCube d k) p q +
        η⁻¹ * tauAtScale P m k p q) +
    Cosc * scaleSep * Ch04.expectedResponseJCubeSet P Q p q +
      ((1 / 2 : ℝ) * ‖q0‖ *
          (((Fintype.card (Fin d) : ℝ) * gradCoeff) *
            ∫ a, gradWeak a ∂P) +
        (1 / 2 : ℝ) * ‖p0‖ *
          (((Fintype.card (Fin d) : ℝ) * fluxCoeff) *
            ∫ a, fluxWeak a ∂P)) +
        Cprod *
          (Real.sqrt (∫ a, (scaledGrad a) ^ 2 ∂P) *
            Real.sqrt (∫ a, (scaledFlux a) ^ 2 ∂P))

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

/-- The standard manuscript RHS is bounded by the Young-envelope RHS for the
first additivity term. -/
theorem jUpperWeakNormManuscriptExpectedRHSAtScale_le_youngManuscriptExpectedRHSAtScale
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {m k : ℤ} {s t : ℝ}
    {C Cosc scaleSep BφS BφT Cprod η : ℝ}
    (p q p0 q0 : Vec d)
    (hC : 0 ≤ C) (hη : 0 < η)
    (htau : 0 ≤ tauAtScale P m k p q)
    (hresponse : 0 ≤ Ch04.expectedResponseJCubeSet P (originCube d k) p q) :
    jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        C Cosc scaleSep BφS BφT Cprod p q p0 q0
      ≤
      jUpperWeakNormYoungManuscriptExpectedRHSAtScale P m k s t
        C Cosc scaleSep BφS BφT Cprod η p q p0 q0 := by
  let Q : TriadicCube d := originCube d m
  let T :=
    Real.sqrt (tauAtScale P m k p q) *
      Real.sqrt (Ch04.expectedResponseJCubeSet P (originCube d k) p q)
  let Y :=
    η * Ch04.expectedResponseJCubeSet P (originCube d k) p q +
      η⁻¹ * tauAtScale P m k p q
  have hTY : 2 * T ≤ Y := by
    have h :=
      sqrt_mul_sqrt_le_young
        (x := tauAtScale P m k p q)
        (y := Ch04.expectedResponseJCubeSet P (originCube d k) p q)
        htau hresponse hη
    have hmul := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * T ≤ 2 * (Y / 2) := by
        simpa [T, Y, mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = Y := by ring
  have hfirst :
      (2 * C) * T ≤ C * Y := by
    calc
      (2 * C) * T = C * (2 * T) := by ring
      _ ≤ C * Y := mul_le_mul_of_nonneg_left hTY hC
  unfold jUpperWeakNormManuscriptExpectedRHSAtScale
  unfold jUpperWeakNormYoungManuscriptExpectedRHSAtScale
  dsimp only
  nlinarith [hfirst]

/-- First Section 5.3 lemma with the Young-envelope additivity term, using the
same normalized cutoff and P4 integrability inputs as the standard public
surface. -/
theorem expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormYoungManuscriptExpectedRHSAtScale_of_normalizedCutoff_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (hs_lt_one : s < 1) (ht : 0 < t)
    (hst : s + t ≤ 1)
    (p q p0 q0 : Vec d) {η : ℝ} (hη : 0 < η)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P) :
    let Q : TriadicCube d := originCube d m
    let j : ℕ := Int.toNat (m - k)
    Ch04.expectedResponseJCubeSet P Q p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      jUpperWeakNormYoungManuscriptExpectedRHSAtScale P m k s t
        (1 + section53CutoffBound Q)
        (section53CutoffOscillationConstant Q)
        (section53CutoffScaleSep Q j)
        (section53CutoffDualBound Q s)
        (section53CutoffDualBound Q t)
        (section53CutoffProductCoeff Q s t)
        η p q p0 q0 := by
  dsimp only
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - k)
  let C := 1 + section53CutoffBound Q
  let Cosc := section53CutoffOscillationConstant Q
  let scaleSep := section53CutoffScaleSep Q j
  let BφS := section53CutoffDualBound Q s
  let BφT := section53CutoffDualBound Q t
  let Cprod := section53CutoffProductCoeff Q s t
  have hstandard :
      Ch04.expectedResponseJCubeSet P Q p q -
          (1 / 2 : ℝ) * vecDot p0 q0 ≤
        jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0 := by
    simpa [Q, j, C, Cosc, scaleSep, BφS, BφT, Cprod] using
      expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_normalizedCutoff_of_P4
        hP hstat hStruct hP4 hk_nonneg hkm hs hs_lt_one ht hst p q p0 q0
        hGradSq hFluxSq
  have hm_nonneg : 0 ≤ m := le_trans hk_nonneg hkm
  have hBlockM_nat :
      Integrable
        (Ch04.coarseFullBlockMatrixAtCube
          (originCube d ((Int.toNat m : ℕ) : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 (Int.toNat m)
  have hBlockM :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d m)) P := by
    simpa [Int.toNat_of_nonneg hm_nonneg] using hBlockM_nat
  have hBlockK_nat :
      Integrable
        (Ch04.coarseFullBlockMatrixAtCube
          (originCube d ((Int.toNat k : ℕ) : ℤ))) P :=
    Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 (Int.toNat k)
  have hBlockK :
      Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d k)) P := by
    simpa [Int.toNat_of_nonneg hk_nonneg] using hBlockK_nat
  have hDescBlock :
      ∀ R, R ∈ descendantsAtScale (originCube d m) k →
        Integrable (Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hk_nonneg hkm hR hBlockK
  have htau :
      0 ≤ tauAtScale P m k p q :=
    Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hstat hk_nonneg hkm p q hBlockM hDescBlock
  have hresponse :
      0 ≤ Ch04.expectedResponseJCubeSet P (originCube d k) p q :=
    expectedResponseJCubeSet_nonneg P (originCube d k) p q
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [section53CutoffBound_nonneg Q]
  have hcompare :
      jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
          C Cosc scaleSep BφS BφT Cprod p q p0 q0
        ≤
        jUpperWeakNormYoungManuscriptExpectedRHSAtScale P m k s t
          C Cosc scaleSep BφS BφT Cprod η p q p0 q0 :=
    jUpperWeakNormManuscriptExpectedRHSAtScale_le_youngManuscriptExpectedRHSAtScale
      p q p0 q0 hC_nonneg hη htau hresponse
  exact hstandard.trans hcompare

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
