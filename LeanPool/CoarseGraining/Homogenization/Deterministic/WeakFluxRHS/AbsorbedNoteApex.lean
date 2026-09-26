/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedNoteConstants
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity

/-! # Absorbed Note Apex -/

@[expose] public section

namespace Homogenization

noncomputable section

/-- Square-root bridge from the note-base weak-flux apex to the expanded
note-constant energy/seminorm forcing RHS. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_noteBase
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u g : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) (m : ℕ) {BU BV : ℝ}
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hmain :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            (weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹))) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
              cubeAverage Q (coefficientEnergyDensity a u) +
            (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
            2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  have hbase :
      weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
        50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
            cubeAverage Q (coefficientEnergyDensity a u) +
          (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
          2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 :=
    weakFluxRHSAbsorbedLocalizedNoteBase_mul_inv_one_sub_step_le_noteEnergySeminormsForce
      Q a u g hs hs_le m havg_nonneg hBU_nonneg hBV_nonneg
  have hweight_nonneg : 0 ≤ (coarsePoincareRHSDepthWeight s m)⁻¹ := by
    refine inv_nonneg.mpr ?_
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  exact
    hmain.trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hbase hweight_nonneg))

/--
Parent potential/solenoidal note-facing weak-flux RHS apex with the absorbed
base expanded into the manuscript energy/seminorm forcing RHS.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_parent_potential_solenoidal_of_constructed_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (u g : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) u)
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
              (fun x => matVecMul (a x) (u x))))
    (huBdd_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N u))
    (hgBdd_centered_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    (m : ℕ) {BU BV : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
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
    (hu :
      ∀ k : ℕ, coarsePoincareRHSSn Q s u (m + k) ≤ BU)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
              cubeAverage Q (coefficientEnergyDensity a u) +
            (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
            2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  have hmain :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            (weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) :=
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedNoteBase_of_parent_potential_solenoidal_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (u := u) (g := g) (lam := lam)
      (Lam := Lam) hs hu_potential hu_residual hEll_desc hu_mem_desc
      hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc (m := m) hBdd hEll_open hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu hvConstructed
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_noteBase
      Q a u g hs hs_le m havg_parent_nonneg hBU_nonneg hBV_nonneg hmain

/--
H¹ weak-solution note-facing weak-flux RHS apex with the absorbed base expanded
into the manuscript energy/seminorm forcing RHS.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
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
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
              cubeAverage Q (coefficientEnergyDensity a u.grad) +
            (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
            2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  have hmain :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u.grad x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            (weakFluxRHSAbsorbedLocalizedNoteBase Q a u.grad g s m BU BV *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) :=
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedNoteBase_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (g := g) (u := u) (lam := lam)
      (Lam := Lam) hs hweak hEll_desc hu_mem_desc hg_mem_desc hC_desc
      hData_desc hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc (m := m)
      hBdd hEll_open hData hsum_half havg_parent_nonneg havg_nonneg hint
      hmem hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg hu_tail hvConstructed
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_noteBase
      Q a u.grad g hs hs_le m havg_parent_nonneg hBU_nonneg hBV_nonneg hmain

/--
H¹ weak-solution note-facing weak-flux RHS apex with the RHS `H^s` regularity
data compressed to the manuscript-facing package.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds_of_cubeVectorBesovHRegularity
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
    (hg : CubeVectorBesovHRegularity Q s g)
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
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
              cubeAverage Q (coefficientEnergyDensity a u.grad) +
            (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
            2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  have hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S) := by
    intro j S hS
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hS hg.memLp
  have hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro n R hR
    exact cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
      s g hR hg.partialSeminorms_bddAbove
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
      Q a s g u hs hs_le hweak hEll_desc hu_mem_desc hg_mem_desc hC_desc
      hData_desc hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc m hBdd
      hEll_open hData hsum_half havg_parent_nonneg havg_nonneg hint hmem
      hg.partialSeminorms_bddAbove hLocalBdd hBU_nonneg hBV_nonneg hu_tail
      hvConstructed

end

end Homogenization
