/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.WeakFluxRHS.Selection.Constructed

/-! # Averaged Tail -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Weak flux RHS selection: averaged tail selector
-/

noncomputable section

/-- Public weak-flux bridge with the harmonic-remainder selector produced by
the deterministic Neumann-corrector construction.  The selector's local
boundedness is discharged from harmonicity; the only remaining remainder input
is the averaged scalar `BV` tail for this selected field. -/
theorem exists_harmonicRemainderSelector_localizedForcedSolutionPublicFlux_le_weakFluxExpandedRHS_of_averaged_tail
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (m : ℕ) {BV : ℝ}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hBV_nonneg : 0 ≤ BV) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∃ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          ∃ w : AHarmonicFunction (publicCoeffField Q a) (cubeSet R),
            v R = (fun x => w.toH1.grad x) ∧
            ∀ x ∈ cubeSet R,
              forcedSolutionGradientField u x =
                w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
      ((∀ k : ℕ,
        weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + k) ≤ BV) →
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
                  (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))) := by
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
  have hQdesc : ∃ n : ℕ, Q ∈ descendantsAtDepth Q n := ⟨0, by simp⟩
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
  have hu_tail :
      ∀ k : ℕ,
        coarsePoincareRHSSn Q s (publicH1ToCubeSet u.toH1).grad (m + k) ≤
          forcedSolutionWeakFluxPoincareTailBudget Q a s u := by
    intro k
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
      forcedSolutionGradientField_coarsePoincareRHSSn_le_weakFluxPoincareTailBudget_publicCoeffField
        (Q := Q) (a := a) (g := g) (s := s) u hs hs_le hg (m + k)
  have hη : 0 < coarsePoincareRHSNoteEta s :=
    coarsePoincareRHSNoteEta_pos hs
  rcases
      _root_.Homogenization.exists_harmonicRemainderSelector_fluxSeminormStepAbsorbedLocalError_with_decomposition_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (Q := Q) (a := publicCoeffField Q a) (s := s)
        (η := coarsePoincareRHSNoteEta s)
        (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
        (u := (publicH1ToCubeSet u.toH1).grad) (g := g)
        hs hη (publicH1ToCubeSet u.toH1).isPotentialOn
        (hweak.residual_solenoidal (hEll_desc Q hQdesc) (hg_mem_desc Q hQdesc))
        hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc
        hchildBdd huBdd_desc hgBdd_centered_desc with
    ⟨v, hselected, hlocal_of_bdd⟩
  have hvBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R)) := by
    intro R hRdesc
    rcases hselected R hRdesc with ⟨ω, w, hv_eq, _hdecomp⟩
    simpa [hv_eq] using
      AHarmonicFunction.grad_negativeBesovPartialSeminormTwo_bddAbove
        (Q := R) (a := publicCoeffField Q a) w hs
  refine ⟨v, ?_, ?_⟩
  · intro R hRdesc
    rcases hselected R hRdesc with ⟨ω, w, hv_eq, hdecomp⟩
    refine ⟨ω, w, hv_eq, ?_⟩
    intro x hx
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
      hdecomp x hx
  · intro hv_tail
    have hmain :
        localizedFluxDefectNegativeBesovAverageTwo Q s
            (fun x => matVecMul (publicCoeffField Q a x)
              ((publicH1ToCubeSet u.toH1).grad x)) m ≤
          Real.sqrt
            ((coarsePoincareRHSDepthWeight s m)⁻¹ *
              (weakFluxRHSAbsorbedLocalizedNoteBase Q (publicCoeffField Q a)
                (publicH1ToCubeSet u.toH1).grad g s m
                (forcedSolutionWeakFluxPoincareTailBudget Q a s u) BV *
                (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
      have hraw :=
        _root_.Homogenization.localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_bddAbove
          (Q := Q) (a := publicCoeffField Q a) (s := s)
          (η := coarsePoincareRHSNoteEta s)
          (u := (publicH1ToCubeSet u.toH1).grad) (g := g) (v := v)
          (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
          hs hη (hlocal_of_bdd hvBdd) (m := m) hBdd
          (publicCoeffField_isEllipticFieldOn_openCubeSet Q a)
          (publicCoeffField_openCubeDescendantDeterministicCoarseData Q a)
          hsum_half havg_parent_nonneg havg_nonneg hint hmem
          hg.partialSeminorms_bddAbove hLocalBdd
          (forcedSolutionWeakFluxPoincareTailBudget_nonneg u hs) hBV_nonneg
          hu_tail hv_tail
      simpa [weakFluxRHSAbsorbedLocalizedNoteBase] using hraw
    have hexpanded :=
      _root_.Homogenization.localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_noteBase
        Q (publicCoeffField Q a) (publicH1ToCubeSet u.toH1).grad g
        hs hs_le m havg_parent_nonneg
        (forcedSolutionWeakFluxPoincareTailBudget_nonneg u hs) hBV_nonneg hmain
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using hexpanded

/-- Public forced-solution selector for the corrected weak-flux recurrence.
On each descendant cube it chooses the centered Neumann corrector supplied by
the deterministic local step and exposes its gradient as the selector used by
the public corrected-energy bridge. -/
theorem exists_neumannCorrectorSelector_fluxSeminormStepCorrectorEnergyLocalError_forcedSolution
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {s : ℝ} {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (hs : 0 < s) (hg : ForceBesovRegularity Q s g) :
    ∃ z : TriadicCube d → Vec d → Vec d,
      (∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        ∃ ω : MeanZeroNeumannCorrectorData R (publicCoeffField Q a)
            (fun x => g x - cubeAverageVec R g),
          z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) ∧
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (publicCoeffField Q a x)
            (forcedSolutionGradientField u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (publicCoeffField Q a x)
                    (forcedSolutionGradientField u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R (publicCoeffField Q a)
            (forcedSolutionGradientField u) (z R) s := by
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
  have hweak :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q)
        (publicH1ToCubeSet u.toH1) g :=
    isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
      (Q := Q) (a := a) (u := u.toH1) (g := g) u.weakSolution
  have hQdesc : ∃ n : ℕ, Q ∈ descendantsAtDepth Q n := ⟨0, by simp⟩
  rcases
      _root_.Homogenization.exists_correctorGradientSelector_fluxSeminormStepCorrectorEnergyLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (Q := Q) (a := publicCoeffField Q a) (s := s)
        (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
        (u := (publicH1ToCubeSet u.toH1).grad) (g := g)
        hs (publicH1ToCubeSet u.toH1).isPotentialOn
        (hweak.residual_solenoidal (hEll_desc Q hQdesc) (hg_mem_desc Q hQdesc))
        hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc
        hchildBdd with
    ⟨z, hz, hlocal⟩
  refine ⟨z, ?_, ?_⟩
  · intro n R hR
    exact hz R ⟨n, hR⟩
  · intro j R hR
    simpa [forcedSolutionGradientField, publicH1ToCubeSet_grad] using
      hlocal j R hR

end

end Ch03
end Book
end Homogenization
