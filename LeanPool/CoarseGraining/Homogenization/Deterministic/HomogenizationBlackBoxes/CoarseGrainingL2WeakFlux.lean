/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2Response
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedNoteApex

/-! # Coarse Graining L2Weak Flux -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/--
The expanded note-facing Section 3.2.3 weak-flux RHS, named so the Section
3.3.B composition layer can state its scalar handoff without repeating the
large square-root expression.
-/
noncomputable def weakFluxNoteEnergySeminormsForceBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradU : Vec d → Vec d) (m : ℕ) (BU BV : ℝ) : ℝ :=
  Real.sqrt
    ((coarsePoincareRHSDepthWeight s m)⁻¹ *
      (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a gradU) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))

/--
Named black-box handoff from the Section 3.2.3 H¹ weak-solution apex to the
compressed RHS name used by the Section 3.3.B wrapper.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_weakFluxNoteEnergySeminormsForceBound_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) (u : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) u.grad)
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
              (fun x => matVecMul (a x) (u.grad x))))
    (huBdd_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u.grad))
    (hgBdd_centered_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    (m : ℕ) {BU BV : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u.grad n))
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a u.grad))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u.grad))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u.grad) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
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
      ∀ k : ℕ, coarsePoincareRHSSn Q s u.grad (m + k) ≤ BU)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u.grad x)) m ≤
      weakFluxNoteEnergySeminormsForceBound Q a s g u.grad m BU BV := by
  simpa [weakFluxNoteEnergySeminormsForceBound] using
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (g := g) (u := u) (lam := lam)
      (Lam := Lam) hs hs_le hweak hEll_desc hu_mem_desc hg_mem_desc
      hC_desc hData_desc hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc
      (m := m) (BU := BU) (BV := BV) hBdd hEll_open hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed

/--
Bridge-explicit Section 3.3.B composition surface routed through the Section
3.2.3 H¹ weak-flux RHS apex.

This theorem is intentionally not given the final Step-B name: the remaining
bridge hypotheses are genuine interface obligations.  The Section 3.2.3 H¹
apex controls the weak-flux field `a∇u`, whereas Section 3.3.A consumes the
coarse flux-defect `(a-a₀)∇u`.  The first bridge supplies that negative-Besov
field conversion; the second compares the expanded weak-flux RHS with the
manuscript coarse-graining RHS.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds_of_weakFluxBridges
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) u.grad)
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
              (fun x => matVecMul (a x) (u.grad x))))
    (huBdd_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u.grad))
    (hgBdd_centered_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    {BU BV : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u.grad n))
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a u.grad))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u.grad))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u.grad) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
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
      ∀ k : ℕ, coarsePoincareRHSSn Q s u.grad (j + k) ≤ BU)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV)
    (hweakFluxControlsDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.grad) j ≤
        localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u.grad x)) j)
    (hweakFluxRhs_le :
      weakFluxNoteEnergySeminormsForceBound Q a s g u.grad j BU BV ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g) :
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j u.grad g := by
  have _ : IsEllipticMatrix lam0 Lam0 a0 := ha0
  have _ : a0.IsSymm := ha0symm
  have hweakFlux :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u.grad x)) j ≤
        weakFluxNoteEnergySeminormsForceBound Q a s g u.grad j BU BV :=
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_weakFluxNoteEnergySeminormsForceBound_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (g := g) (u := u) (lam := lam)
      (Lam := Lam) hs_pos hs_lt_one.le hweak hEll_desc hu_mem_desc hg_mem_desc
      hC_desc hData_desc hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc
      (m := j) (BU := BU) (BV := BV) hBdd hEll_open hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed
  have hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.grad) j ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g :=
    (hweakFluxControlsDefect.trans hweakFlux).trans hweakFluxRhs_le
  exact
    solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_of_coarseFluxDefect_le
      hdual Q a a0 sigma0 u v g j hsigma0 ha0eq hs_pos hs_lt_one hEll
      hweak hv hzeroTrace hcoarseFluxDefect

end

end Homogenization
