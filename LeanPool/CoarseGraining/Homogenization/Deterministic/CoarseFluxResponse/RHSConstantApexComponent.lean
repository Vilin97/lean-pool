/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApex

/-! # RHSConstant Apex Component -/

namespace Homogenization

noncomputable section

/-!
# Component-budget one-cube RHS coarse-flux response apex

This leaf keeps `RHSConstantApex` below the file-size guardrail while exposing
the clean depth-zero-input surface for the component-budget version of the
one-cube RHS flux-response theorem.
-/

open scoped BigOperators ENNReal

/--
Component-budget one-cube apex with all parent depth-zero bookkeeping inputs
derived from descendant/global hypotheses.

Compared with the exact-budget wrapper in `RHSConstantApex`, this surface keeps
the weak-flux and Poincare scalar sides split into energy, tail, and forcing
component budgets.  These are the inputs that the remaining analytic
energy-to-force estimates are meant to discharge separately.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_component_budgets_of_descendant_depth_zero_inputs
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
    {BU BV BweakEnergy BUtail BVtail BweakForce BPoincareEnergy BPoincareForce : ℝ}
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
  have havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q a v.grad hEll
  have havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a v.grad) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_descendant_isEllipticFieldOn
      Q a v.grad hEll_desc
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
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_aHarmonicFunction_h1DirichletRhsWeakSolutionOn_component_budgets
      Q a a0 s gradU g v w C hC_nonneg hs hs_le hEll hEll_open
      ha0 ha0symm hweak hgrad hEll_desc hu_mem_desc hg_mem_desc
      hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc hweakBdd hData hsum_half havg_parent_nonneg
      havg_nonneg hint hmem hg hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg
      hu_tail hvConstructed hdefectW_partialBdd hresponseSum hhomogeneous
      hfluxV_bdd ha0V_bdd hgrad_bdd hweakEnergy hBU hBV hweakForce
      hweakBudget hPoincareEnergy hPoincareForce hPoincareBudget

end

end Homogenization
