/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantAbsorption
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantEnvelope

/-! # RHSConstant Apex -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Constant-envelope one-cube RHS coarse-flux response apex

This leaf composes the `C`-scaled correction wrappers with the split
recomposition theorem.  The remaining mathematical inputs are the analytic
component budgets: the homogeneous energy correction and the zero-Dirichlet
RHS weak-flux/Poincare budgets.
-/

open scoped BigOperators ENNReal

/--
One-cube §3.2.4 RHS flux-response recomposition with a single nonnegative
constant multiplying each compact component.

The theorem is intentionally still component-budget-facing: it records the
formal route from the H¹ weak-solution estimates to the manuscript-shaped
`C(d)` one-cube bound, while leaving the analytic energy/tail/forcing budget
estimates as explicit hypotheses.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_component_budgets
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (v : H1Function (cubeSet Q))
    (w : AHarmonicFunction a (cubeSet Q))
    (C : ℝ) {lam Lam lam0 Lam0 : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = w.toH1.grad x + v.grad x)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) v.grad)
    (hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
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
    {BU BV BweakEnergy BUtail BVtail BweakForce BPoincareEnergy BPoincareForce : ℝ}
    (hweakBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s v.grad n))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a v.grad))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a v.grad)
        (cubeSet Q) MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (v.grad x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (v.grad x))))
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad))
    (hweakEnergy :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) ≤
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
    (hPoincareEnergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) ≤
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
  have hfluxW_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
  have ha0Field :
      IsEllipticFieldOn lam0 Lam0 (cubeSet Q) (constantCoeffField a0) :=
    isEllipticFieldOn_constantCoeffField (measurableSet_cubeSet Q) ha0
  have ha0W_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (w.toH1.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn ha0Field w.toH1.grad_memVectorL2
  have hdefectW_mem :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 w.toH1.grad) := by
    unfold fluxDefect
    exact hfluxW_mem.sub ha0W_mem
  have hfluxV_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (v.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.grad_memVectorL2
  have ha0V_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn ha0Field v.grad_memVectorL2
  have hdefectW_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 w.toH1.grad)) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_partialSeminorm_bddAbove
      Q s (fluxDefect a a0 w.toH1.grad) hdefectW_partialBdd
  have hdefectW :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 w.toH1.grad) ≤
        C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g :=
    (cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseQOneBound_of_aHarmonicFunction
      Q a a0 s hs hEll ha0 ha0symm w hresponseSum).trans
      hhomogeneous
  have hfluxV :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (a x) (v.grad x)) ≤
        C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g :=
    cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
      Q a s g v C hC_nonneg hs hs_le hweak hEll_desc hu_mem_desc
      hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc hweakBdd hEll_open hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed hfluxV_bdd
      hweakEnergy hBU hBV hweakForce hweakBudget
  have ha0V :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (v.grad x)) ≤
        C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g :=
    have hgrad_mem_desc :
        ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
          MemVectorL2 (cubeSet R) v.grad := by
      intro j R hR
      exact hu_mem_desc R ⟨j, hR⟩
    cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_const_mul_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
      Q a a0 s g v C hC_nonneg hs hs_le hEll hweak hg hGlobalBdd
      hgrad_mem_desc hgrad_bdd hPoincareEnergy hPoincareForce hPoincareBudget
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_const_mul_split_component_bounds
      Q a a0 gradU w.toH1.grad v.grad g hC_nonneg hs hGlobalBdd
      hgrad hdefectW_mem hfluxV_mem ha0V_mem
      hdefectW_bdd hfluxV_bdd ha0V_bdd hdefectW hfluxV ha0V

/--
Same one-cube apex with the weak-flux and Poincare scalar sides stated as the
exact expanded budget inequalities, rather than through auxiliary budget
variables.  This is the cleanest current note-facing surface: the remaining
analytic work is precisely the two displayed scalar budget bounds plus the
homogeneous energy-correction estimate.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_exact_budgets
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (v : H1Function (cubeSet Q))
    (w : AHarmonicFunction a (cubeSet Q))
    (C : ℝ) {lam Lam lam0 Lam0 : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = w.toH1.grad x + v.grad x)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) v.grad)
    (hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
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
    {BU BV : ℝ}
    (hweakBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s v.grad n))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a v.grad))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a v.grad)
        (cubeSet Q) MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (v.grad x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (v.grad x))))
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad))
    (hweakBudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2)
    (hPoincareBudget :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) +
        (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_component_budgets
      (Q := Q) (a := a) (a0 := a0) (s := s) (gradU := gradU)
      (g := g) (v := v) (w := w) (C := C)
      (lam := lam) (Lam := Lam) (lam0 := lam0) (Lam0 := Lam0)
      (BU := BU) (BV := BV)
      (BweakEnergy :=
        50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad))
      (BUtail := (5 * s⁻¹) * BU)
      (BVtail := (5 * s⁻¹) * BV)
      (BweakForce :=
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
      (BPoincareEnergy :=
        (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)))
      (BPoincareForce :=
        (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
      hC_nonneg hs hs_le hEll hEll_open ha0 ha0symm hweak hgrad
      hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc
      hchildBdd huBdd_desc hgBdd_centered_desc hweakBdd hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hg hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed hdefectW_partialBdd
      hresponseSum hhomogeneous hfluxV_bdd ha0V_bdd hgrad_bdd
      (by rfl) (by rfl) (by rfl) (by rfl) hweakBudget
      (by rfl) (by rfl) hPoincareBudget

/--
Exact-budget one-cube apex with coefficient-energy average nonnegativity
derived from the ellipticity hypotheses.

This is the cleaner note-facing surface after the average-nonnegativity
bookkeeping has been moved into the RHS layer.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_exact_budgets_of_descendant_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (v : H1Function (cubeSet Q))
    (w : AHarmonicFunction a (cubeSet Q))
    (C : ℝ) {lam Lam lam0 Lam0 : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = w.toH1.grad x + v.grad x)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) v.grad)
    (hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
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
    {BU BV : ℝ}
    (hweakBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s v.grad n))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
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
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (v.grad x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (v.grad x))))
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad))
    (hweakBudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2)
    (hPoincareBudget :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) +
        (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  have havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q a v.grad hEll
  have havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a v.grad) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_descendant_isEllipticFieldOn
      Q a v.grad hEll_desc
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_exact_budgets
      Q a a0 s gradU g v w C hC_nonneg hs hs_le hEll hEll_open
      ha0 ha0symm hweak hgrad hEll_desc hu_mem_desc hg_mem_desc
      hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc hweakBdd hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hg hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed hdefectW_partialBdd
      hresponseSum hhomogeneous hfluxV_bdd ha0V_bdd hgrad_bdd
      hweakBudget hPoincareBudget

/--
Exact-budget one-cube apex with the parent-cube ellipticity hypothesis derived
from descendant ellipticity at depth zero.

This removes the redundant standalone `IsEllipticFieldOn ... (cubeSet Q) a`
input when the caller already supplies ellipticity on all descendants of `Q`.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_exact_budgets_of_descendant_isEllipticFieldOn_self
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
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) v.grad)
    (hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
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
    {BU BV : ℝ}
    (hweakBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s v.grad n))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
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
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (v.grad x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (v.grad x))))
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad))
    (hweakBudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2)
    (hPoincareBudget :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) +
        (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  have hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a :=
    isEllipticFieldOn_self_of_descendant_isEllipticFieldOn Q a hEll_desc
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_exact_budgets_of_descendant_isEllipticFieldOn
      Q a a0 s gradU g v w C hC_nonneg hs hs_le hEll hEll_open
      ha0 ha0symm hweak hgrad hEll_desc hu_mem_desc hg_mem_desc
      hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc hweakBdd hData hsum_half hint hmem hg
      hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg hu_tail hvConstructed
      hdefectW_partialBdd hresponseSum hhomogeneous hfluxV_bdd ha0V_bdd
      hgrad_bdd hweakBudget hPoincareBudget

/--
Exact-budget one-cube apex with all parent depth-zero inputs derived from the
corresponding descendant/global hypotheses.

Besides deriving self-cube ellipticity from descendant ellipticity, this
wrapper also derives the descendant deterministic-data family from the
single parent descendant-data hypothesis, the descendant `MemVectorL2 v.grad`
family from the H¹ input, the parent `a∇v` partial boundedness from ellipticity
and H¹ data, the parent `v.grad` and `a₀∇v` partial boundedness inputs from the
descendant `v.grad` boundedness family, the parent `MemLp g`, the descendant
`MemVectorL2 g` family, and the parent positive-Besov boundedness hypothesis
from their descendant/global versions.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_exact_budgets_of_descendant_depth_zero_inputs
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
    {BU BV : ℝ}
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
    (hweakBudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2)
    (hPoincareBudget :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) +
        (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * C * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  have hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a := by
    intro R hR
    rcases hR with ⟨n, hRn⟩
    have hRn_scale : R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hRn
    have hn_scale : Q.scale - (n : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    exact OpenCubeDescendantDeterministicCoarseData.of_mem_descendantsAtScale
      hData hn_scale hRn_scale
  have hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) v.grad := by
    intro R hR
    rcases hR with ⟨n, hRn⟩
    simpa [MemVectorL2, volumeMeasureOn] using
      v.grad_memVectorL2.mono_measure
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
          (cubeSet_subset_of_mem_descendantsAtDepth hRn))
  have hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g := by
    intro R hR
    rcases hR with ⟨n, hRn⟩
    exact memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
      (hmem n R hRn)
  have hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q) :=
    hmem 0 Q (by simp)
  have hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g) :=
    hLocalBdd 0 Q (by simp)
  have hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad) :=
    huBdd_desc Q ⟨0, by simp⟩
  have hEll :
      IsEllipticFieldOn lam Lam (cubeSet Q) a :=
    isEllipticFieldOn_self_of_descendant_isEllipticFieldOn Q a hEll_desc
  have hfluxV_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (v.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.grad_memVectorL2
  have hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (v.grad x))) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
      (fun x => matVecMul (a x) (v.grad x))
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hfluxV_mem)
  have ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (v.grad x))) := by
    rcases hgrad_bdd with ⟨M, hM⟩
    refine ⟨matNorm a0 * M, ?_⟩
    rintro y ⟨N, rfl⟩
    calc
      cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (v.grad x))
          ≤ matNorm a0 * cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad := by
            exact cubeBesovNegativeVectorPartialSeminormTwo_constMatMul_le
              Q s a0 v.grad N
              (fun j _ R hR => hu_mem_desc R ⟨j, hR⟩)
      _ ≤ matNorm a0 * M := by
            exact mul_le_mul_of_nonneg_left (hM ⟨N, rfl⟩) (matNorm_nonneg a0)
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_exact_budgets_of_descendant_isEllipticFieldOn_self
      Q a a0 s gradU g v w C hC_nonneg hs hs_le hEll_open ha0 ha0symm
      hweak hgrad hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc
      hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc hweakBdd hData
      hsum_half hint hmem hg hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg
      hu_tail hvConstructed hdefectW_partialBdd hresponseSum hhomogeneous
      hfluxV_bdd ha0V_bdd hgrad_bdd hweakBudget hPoincareBudget

end

end Homogenization
