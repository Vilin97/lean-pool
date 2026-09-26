/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.WeakFluxRHS.Selection.CorrectorEnergy

/-! # Constructed -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Weak flux RHS selection: constructed harmonic-remainder bridge
-/

noncomputable section

/-- Depth-zero expanded RHS obtained after closing the `u`-tail by public
coarse Poincare and closing the harmonic-remainder `BV` tail by the selected
Neumann-corrector tail `Bω`. -/
noncomputable def forcedSolutionWeakFluxSelectedNeumannTailExpandedRHS
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (Bω : ℝ) : ℝ :=
  Real.sqrt
    (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
        (publicCoeffField Q a) *
        cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (forcedSolutionGradientField u)) +
      (5 * s⁻¹) * forcedSolutionWeakFluxPoincareTailBudget Q a s u +
      (5 * s⁻¹) *
        (4 * (forcedSolutionWeakFluxPoincareTailBudget Q a s u + Bω)) +
      2500 * (s⁻¹) ^ 4 *
        (LambdaSq Q (s / 2) (.finite 2) (publicCoeffField Q a)) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)

theorem forcedSolutionGradientField_coarsePoincareRHSSn_le_weakFluxPoincareTailBudget_publicCoeffField
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} {s : ℝ}
    (u : ForcedCubeSolution Q a g) (hs : 0 < s) (hs_le : s ≤ 1)
    (hg : ForceBesovRegularity Q s g) (m : ℕ) :
    coarsePoincareRHSSn Q s (forcedSolutionGradientField u) m ≤
      forcedSolutionWeakFluxPoincareTailBudget Q a s u := by
  simpa [forcedSolutionWeakFluxPoincareTailBudget] using
    forcedSolutionGradientField_coarsePoincareRHSSn_le_expanded_publicCoeffField
      (Q := Q) (a := a) (g := g) (s := s) u hs hs_le hg m

/-- Public forced-solution specialization of the deterministic weak-flux
localized apex, with the harmonic-remainder tail inputs still explicit. -/
theorem localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_constructed_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (m : ℕ) {BU BV : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hu_tail :
      ∀ k : ℕ, coarsePoincareRHSSn Q s (forcedSolutionGradientField u) (m + k) ≤ BU)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction (publicCoeffField Q a) (cubeSet R),
            (∀ x ∈ cubeSet R,
              forcedSolutionGradientField u x =
                w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a) *
              cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q a)
                  (forcedSolutionGradientField u)) +
            (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
            2500 * (s⁻¹) ^ 4 *
              (LambdaSq Q (s / 2) (.finite 2)
                (publicCoeffField Q a)) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  have hs_le : s ≤ 1 := hs_lt.le
  have hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
          (cubeSet R) (publicCoeffField Q a) := by
    intro R hR
    rcases hR with ⟨j, hR⟩
    exact publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR
  have hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) (publicH1ToCubeSet u.toH1).grad := by
    intro R hR
    rcases hR with ⟨j, hR⟩
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
      forcedSolutionGradientField_memVectorL2_descendant_cubeSet u hR
  have hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g := by
    intro R hR
    rcases hR with ⟨j, hR⟩
    exact memVectorL2_descendant_cubeSet_of_forceBesovRegularity hg hR
  have hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R) := by
    intro R _hR
    exact h1CoerciveEstimateCubeSet R
  have hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R (publicCoeffField Q a) := by
    intro R hR
    rcases hR with ⟨j, hR⟩
    exact publicCoeffField_openCubeDescendantDeterministicCoarseData_descendant Q a hR
  have hsum_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        Summable (fun n : ℕ =>
          geometricWeight s 2 n *
            maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ))
              (publicCoeffField Q a)) := by
    intro R hR
    rcases hR with ⟨j, hR⟩
    exact publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale_descendant
      (Q := Q) (a := a) hR hs
  have hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (publicCoeffField Q a x)
                ((publicH1ToCubeSet u.toH1).grad x))) := by
    intro R hR S hS
    rcases hR with ⟨j, hR⟩
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
      forcedSolutionPublicFlux_negativeBesovPartialSeminormTwo_bddAbove_child
        (Q := Q) (R := R) (S := S) (a := a) (g := g) u hR hS hs
  have huBdd_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (publicH1ToCubeSet u.toH1).grad) := by
    intro R hR
    rcases hR with ⟨j, hR⟩
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
      forcedSolutionGradientField_descendant_negativeBesovPartialSeminormTwo_bddAbove
        (Q := Q) (R := R) (a := a) (g := g) u hR hs
  have hgBdd_centered_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)) := by
    intro R hR
    rcases hR with ⟨j, hR⟩
    exact forceBesovRegularity_descendant_centered_partialSeminorms_bddAbove hg hR
  have hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q (publicCoeffField Q a) s
          (publicH1ToCubeSet u.toH1).grad n) := by
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
      weakFluxRHSScaledAveragedSeminormSq_bddAbove_publicCoeffField_forcedSolution
        u hs
  have hsum_half :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow
            (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ))
              (publicCoeffField Q a)) 1) :=
    publicCoeffField_summable_qtwo_maxDescendantBBlockNormAtScale_rpow_one
      (Q := Q) (a := a) (s := s / 2) (by nlinarith)
  have havg_parent_nonneg :
      0 ≤ cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (publicH1ToCubeSet u.toH1).grad) :=
    cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (publicH1ToCubeSet u.toH1).grad)
  have havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R
          (coefficientEnergyDensity (publicCoeffField Q a)
            (publicH1ToCubeSet u.toH1).grad) := by
    intro j R hR
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_descendant_cubeSet Q a hR)
        (publicH1ToCubeSet u.toH1).grad)
  have hint :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity (publicCoeffField Q a)
          (publicH1ToCubeSet u.toH1).grad)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      (publicH1ToCubeSet u.toH1).grad_memVectorL2
  have hweak :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q)
        (publicH1ToCubeSet u.toH1) g :=
    isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
      (Q := Q) (a := a) (u := u.toH1) (g := g) u.weakSolution
  have hu_tail' :
      ∀ k : ℕ, coarsePoincareRHSSn Q s (publicH1ToCubeSet u.toH1).grad (m + k) ≤ BU := by
    intro k
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using hu_tail k
  have hvConstructed' :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction (publicCoeffField Q a) (cubeSet R),
            (∀ x ∈ cubeSet R,
              (publicH1ToCubeSet u.toH1).grad x =
                w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV := by
    intro j R hR ω w hw
    exact hvConstructed j R hR ω w
      (by simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using hw)
  simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
    _root_.Homogenization.localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds_of_cubeVectorBesovHRegularity
      (Q := Q) (a := publicCoeffField Q a) (s := s) (g := g)
      (u := publicH1ToCubeSet u.toH1)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      hs hs_le hweak hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc
      hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc m hBdd
      (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)
      (publicCoeffField_openCubeDescendantDeterministicCoarseData Q a)
      hsum_half havg_parent_nonneg havg_nonneg hint hg
      hBU_nonneg hBV_nonneg hu_tail' hvConstructed'

/-- Public forced-solution weak-flux bridge with the coarse-Poincare tail
closed by the RHS Poincare theorem.  The harmonic-remainder tail remains the
only theorem-specific input. -/
theorem localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_constructed_harmonicRemainder_bounds_of_public_poincare_tail
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (m : ℕ) {BV : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBV_nonneg : 0 ≤ BV)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction (publicCoeffField Q a) (cubeSet R),
            (∀ x ∈ cubeSet R,
              forcedSolutionGradientField u x =
                w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (publicCoeffField Q a x)
          (forcedSolutionGradientField u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2)
              (publicCoeffField Q a) *
              cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q a)
                  (forcedSolutionGradientField u)) +
            (5 * s⁻¹) * forcedSolutionWeakFluxPoincareTailBudget Q a s u +
            (5 * s⁻¹) * BV +
            2500 * (s⁻¹) ^ 4 *
              (LambdaSq Q (s / 2) (.finite 2)
                (publicCoeffField Q a)) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)) := by
  exact
    localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (g := g) u m
      (BU := forcedSolutionWeakFluxPoincareTailBudget Q a s u) (BV := BV)
      hs hs_lt hg (forcedSolutionWeakFluxPoincareTailBudget_nonneg u hs)
      hBV_nonneg
      (fun k =>
        forcedSolutionGradientField_coarsePoincareRHSSn_le_weakFluxPoincareTailBudget_publicCoeffField
          (Q := Q) (a := a) (g := g) (s := s) u hs hs_lt.le hg (m + k))
      hvConstructed

end

end Ch03
end Book
end Homogenization
