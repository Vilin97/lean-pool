/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexComponent

/-! # RHSConstant Apex Energy -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Energy-envelope one-cube RHS coarse-flux response apex

This leaf keeps the component-budget apex available with one shared
coefficient-energy envelope.  It is the formal socket that the
zero-Dirichlet energy estimate from the notes should eventually feed.
-/

open scoped BigOperators ENNReal

/--
Component-budget one-cube apex where the weak-flux and Poincare energy
components are both derived from a single parent cube-energy envelope.

The remaining tail and force component budgets stay explicit: those are
different analytic estimates in the notes.  The common energy envelope is the
piece supplied by the zero-Dirichlet RHS energy estimate.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_component_budgets_of_energy_envelope_of_descendant_depth_zero_inputs
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (v : H1Function (cubeSet Q))
    (w : AHarmonicFunction a (cubeSet Q))
    (C : ℝ) {lam Lam lam0 Lam0 : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = w.toH1.grad x + v.grad x)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        Summable (fun m : ℕ =>
          geometricWeight s 2 m *
            maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (a x) (v.grad x))))
    (huBdd_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N v.grad))
    (hgBdd_centered_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    {BU BV BEnergy BweakEnergy BUtail BVtail BweakForce
      BPoincareEnergy BPoincareForce : ℝ}
    (hweakBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s v.grad n))
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a v.grad)
        (cubeSet Q) MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hBU_nonneg : 0 ≤ BU)
    (hBV_nonneg : 0 ≤ BV)
    (hu_tail :
      ∀ k : ℕ, coarsePoincareRHSSn Q s v.grad k ≤ BU)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w0 : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              v.grad x = w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w0.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w0.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV)
    (hdefectW_partialBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s N
          (fluxDefect a a0 w.toH1.grad)))
    (hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0))
    (hhomogeneous :
      coarseFluxResponseQOneBound Q a a0 s w ≤
        C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g)
    (henergyEnvelope :
      cubeAverage Q (coefficientEnergyDensity a v.grad) ≤ BEnergy)
    (hweakEnergyBudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a * BEnergy ≤
        BweakEnergy)
    (hBU : (5 * s⁻¹) * BU ≤ BUtail)
    (hBV : (5 * s⁻¹) * BV ≤ BVtail)
    (hweakForce :
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        BweakForce)
    (hweakBudget :
      BweakEnergy + BUtail + BVtail + BweakForce ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2)
    (hPoincareEnergyBudget :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            BEnergy) ≤
        BPoincareEnergy)
    (hPoincareForce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        BPoincareForce)
    (hPoincareBudget :
      BPoincareEnergy + BPoincareForce ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  have hLambda_nonneg :
      0 ≤ LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hweakCoeff_nonneg :
      0 ≤ 50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (50 : ℝ)) (sq_nonneg (s⁻¹)))
        hLambda_nonneg
  have hweakEnergy :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) ≤
        BweakEnergy := by
    exact
      (mul_le_mul_of_nonneg_left henergyEnvelope hweakCoeff_nonneg).trans
        hweakEnergyBudget
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambdaInv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have hPoincareCoeff_nonneg :
      0 ≤ (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
    exact
      mul_nonneg (sq_nonneg (matNorm a0))
        (mul_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
          hlambdaInv_nonneg)
  have hPoincareEnergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) ≤
        BPoincareEnergy := by
    calc
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad))
          =
          ((matNorm a0) ^ 2 *
            (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            cubeAverage Q (coefficientEnergyDensity a v.grad) := by
            ring
      _ ≤
          ((matNorm a0) ^ 2 *
            (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            BEnergy := by
            exact mul_le_mul_of_nonneg_left henergyEnvelope hPoincareCoeff_nonneg
      _ =
          (matNorm a0) ^ 2 *
            (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
              BEnergy) := by
            ring
      _ ≤ BPoincareEnergy := hPoincareEnergyBudget
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_component_budgets_of_descendant_depth_zero_inputs
      Q a a0 s gradU g v w C hC_nonneg hs hs_le hEll_open
      ha0 ha0symm hweak hgrad hEll_desc hC_desc hData hsum_desc
      hchildBdd huBdd_desc hgBdd_centered_desc hweakBdd hsum_half
      hint hmem hLocalBdd hBU_nonneg hBV_nonneg hu_tail hvConstructed
      hdefectW_partialBdd hresponseSum hhomogeneous hweakEnergy hBU hBV
      hweakForce hweakBudget hPoincareEnergy hPoincareForce hPoincareBudget

end

end Homogenization
