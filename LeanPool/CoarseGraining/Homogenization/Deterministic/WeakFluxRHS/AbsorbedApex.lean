/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedGlobalIteration

/-! # Absorbed Apex -/

namespace Homogenization

noncomputable section

/--
Global localized weak-flux estimate with the local absorbed recurrence derived
from parent potential/solenoidal data on descendant cubes.

This removes the anonymous `hlocal` recurrence hypothesis from
`localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_bddAbove`.
The selected harmonic remainders still expose their local boundedness and
global tail bound, which are the next closure obligations for the
note-facing weak-flux RHS apex.
-/
theorem exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (u g : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
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
      ∀ k : ℕ, coarsePoincareRHSSn Q s u (m + k) ≤ BU) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R))) →
      (∀ k : ℕ,
        weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + k) ≤ BV) →
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            ((weakFluxRHSWeightedCoefficientEnergyBase Q a u s +
                η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  rcases
      exists_harmonicRemainderSelector_fluxSeminormStepAbsorbedLocalError_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (Q := Q) (a := a) (s := s) (η := η) (lam := lam) (Lam := Lam)
        (u := u) (g := g) hs hη hu_potential hu_residual hEll_desc
        hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd
        huBdd_desc hgBdd_centered_desc with
    ⟨v, hlocal_of_bdd⟩
  refine ⟨v, ?_⟩
  intro hvBdd hv
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_bddAbove
      (Q := Q) (a := a) (s := s) (η := η) (u := u) (g := g) (v := v)
      (lam := lam) (Lam := Lam) hs hη (hlocal_of_bdd hvBdd) (m := m)
      hBdd hEll_open hData hsum_half havg_parent_nonneg havg_nonneg hint
      hmem hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg hu hv

/--
Global localized weak-flux estimate with the selected harmonic-remainder tail
derived from descendantwise squared control.

This is the same parent potential/solenoidal wrapper as
`exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal`,
but it asks for pointwise descendant control of the selected remainders at the
reciprocal depth-weight scale instead of an already-averaged tail bound.
-/
theorem exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal_of_descendant_scaled_harmonicRemainder_sq_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (u g : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
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
      ∀ k : ℕ, coarsePoincareRHSSn Q s u (m + k) ≤ BU) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R))) →
      (∀ k : ℕ, ∀ R ∈ descendantsAtDepth Q (m + k),
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s (m + k))⁻¹ * BV) →
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            ((weakFluxRHSWeightedCoefficientEnergyBase Q a u s +
                η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  rcases
      exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal
        (Q := Q) (a := a) (s := s) (η := η) (u := u) (g := g)
        (lam := lam) (Lam := Lam) hs hη hu_potential hu_residual hEll_desc
        hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd
        huBdd_desc hgBdd_centered_desc (m := m) hBdd hEll_open hData
        hsum_half havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd
        hLocalBdd hBU_nonneg hBV_nonneg hu with
    ⟨v, hconclusion⟩
  refine ⟨v, ?_⟩
  intro hvBdd hvSq
  exact hconclusion hvBdd
    (weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_tail_le_of_descendant_scaled_sq_bound
      Q s v m hvSq)

/--
Global localized weak-flux estimate with the selected harmonic-remainder
boundedness and square tail both discharged from bounds on every local
harmonic remainder produced by the centered Neumann-corrector construction.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal_of_constructed_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (u g : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
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
          ((weakFluxRHSWeightedCoefficientEnergyBase Q a u s +
              η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  rcases
      exists_harmonicRemainderSelector_fluxSeminormStepAbsorbedLocalError_with_decomposition_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
        (Q := Q) (a := a) (s := s) (η := η) (lam := lam) (Lam := Lam)
        (u := u) (g := g) hs hη hu_potential hu_residual hEll_desc
        hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd
        huBdd_desc hgBdd_centered_desc with
    ⟨v, hselected, hlocal_of_bdd⟩
  have hvBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R)) := by
    intro R hRdesc
    rcases hRdesc with ⟨j, hR⟩
    rcases hselected R ⟨j, hR⟩ with ⟨ω, w, hv_eq, hdecomp⟩
    have hbdd := (hvConstructed j R hR ω w hdecomp).1
    simpa [hv_eq] using hbdd
  have hvSq :
      ∀ k : ℕ, ∀ R ∈ descendantsAtDepth Q (m + k),
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s (m + k))⁻¹ * BV := by
    intro k R hR
    rcases hselected R ⟨m + k, hR⟩ with ⟨ω, w, hv_eq, hdecomp⟩
    have hsq := (hvConstructed (m + k) R hR ω w hdecomp).2
    simpa [hv_eq] using hsq
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_bddAbove
      (Q := Q) (a := a) (s := s) (η := η) (u := u) (g := g) (v := v)
      (lam := lam) (Lam := Lam) hs hη (hlocal_of_bdd hvBdd) (m := m)
      hBdd hEll_open hData hsum_half havg_parent_nonneg havg_nonneg hint
      hmem hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg hu
      (weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_tail_le_of_descendant_scaled_sq_bound
        Q s v m hvSq)

/--
Note-eta form of the constructed harmonic-remainder parent wrapper.

This fixes the absorption parameter to the manuscript choice
`coarsePoincareRHSNoteEta s` and packages the component base as
`weakFluxRHSAbsorbedLocalizedNoteBase`.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedNoteBase_of_parent_potential_solenoidal_of_constructed_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (u g : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s)
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
          (weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  have hη : 0 < coarsePoincareRHSNoteEta s :=
    coarsePoincareRHSNoteEta_pos hs
  simpa [weakFluxRHSAbsorbedLocalizedNoteBase] using
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (η := coarsePoincareRHSNoteEta s)
      (u := u) (g := g) (lam := lam) (Lam := Lam) hs hη hu_potential
      hu_residual hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc
      hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc (m := m) hBdd
      hEll_open hData hsum_half havg_parent_nonneg havg_nonneg hint hmem
      hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg hu hvConstructed

/--
H¹ weak-solution wrapper for the global localized weak-flux estimate.

The PDE hypothesis `-div(a grad u) = div g` supplies the parent potential field
and residual solenoidal flux required by
`exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal`.
-/
theorem exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_h1DirichletRhsWeakSolutionOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (g : Vec d → Vec d) (u : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
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
      ∀ k : ℕ, coarsePoincareRHSSn Q s u.grad (m + k) ≤ BU) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R))) →
      (∀ k : ℕ,
        weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + k) ≤ BV) →
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u.grad x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            ((weakFluxRHSWeightedCoefficientEnergyBase Q a u.grad s +
                η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  have hQdesc : ∃ n : ℕ, Q ∈ descendantsAtDepth Q n := ⟨0, by simp⟩
  exact
    exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal
      (Q := Q) (a := a) (s := s) (η := η) (u := u.grad) (g := g)
      (lam := lam) (Lam := Lam) hs hη u.isPotentialOn
      (hweak.residual_solenoidal (hEll_desc Q hQdesc) (hg_mem_desc Q hQdesc))
      hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc
      hchildBdd huBdd_desc hgBdd_centered_desc (m := m) hBdd hEll_open
      hData hsum_half havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hBU_nonneg hBV_nonneg hu_tail

/--
H¹ weak-solution wrapper whose selected harmonic-remainder tail is supplied by
descendantwise squared bounds rather than an averaged tail hypothesis.
-/
theorem exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_h1DirichletRhsWeakSolutionOn_of_descendant_scaled_harmonicRemainder_sq_bound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (g : Vec d → Vec d) (u : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
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
      ∀ k : ℕ, coarsePoincareRHSSn Q s u.grad (m + k) ≤ BU) :
    ∃ v : TriadicCube d → Vec d → Vec d,
      (∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N (v R))) →
      (∀ k : ℕ, ∀ R ∈ descendantsAtDepth Q (m + k),
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s (m + k))⁻¹ * BV) →
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (u.grad x)) m ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s m)⁻¹ *
            ((weakFluxRHSWeightedCoefficientEnergyBase Q a u.grad s +
                η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
              (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  rcases
      exists_localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (s := s) (η := η) (g := g) (u := u)
        (lam := lam) (Lam := Lam) hs hη hweak hEll_desc hu_mem_desc
        hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
        hgBdd_centered_desc (m := m) hBdd hEll_open hData hsum_half
        havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
        hBU_nonneg hBV_nonneg hu_tail with
    ⟨v, hconclusion⟩
  refine ⟨v, ?_⟩
  intro hvBdd hvSq
  exact hconclusion hvBdd
    (weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_tail_le_of_descendant_scaled_sq_bound
      Q s v m hvSq)

/--
H¹ weak-solution form of the constructed harmonic-remainder bound wrapper.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (g : Vec d → Vec d) (u : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
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
          ((weakFluxRHSWeightedCoefficientEnergyBase Q a u.grad s +
              η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  have hQdesc : ∃ n : ℕ, Q ∈ descendantsAtDepth Q n := ⟨0, by simp⟩
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_parent_potential_solenoidal_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (η := η) (u := u.grad) (g := g)
      (lam := lam) (Lam := Lam) hs hη u.isPotentialOn
      (hweak.residual_solenoidal (hEll_desc Q hQdesc) (hg_mem_desc Q hQdesc))
      hEll_desc hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc
      hchildBdd huBdd_desc hgBdd_centered_desc (m := m) hBdd hEll_open
      hData hsum_half havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hBU_nonneg hBV_nonneg hu_tail hvConstructed

/--
H¹ weak-solution note-eta form of the constructed harmonic-remainder wrapper.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedNoteBase_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) (u : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s)
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
          (weakFluxRHSAbsorbedLocalizedNoteBase Q a u.grad g s m BU BV *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  have hη : 0 < coarsePoincareRHSNoteEta s :=
    coarsePoincareRHSNoteEta_pos hs
  simpa [weakFluxRHSAbsorbedLocalizedNoteBase] using
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
      (Q := Q) (a := a) (s := s) (η := coarsePoincareRHSNoteEta s)
      (g := g) (u := u) (lam := lam) (Lam := Lam) hs hη hweak hEll_desc
      hu_mem_desc hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd
      huBdd_desc hgBdd_centered_desc (m := m) hBdd hEll_open hData
      hsum_half havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hBU_nonneg hBV_nonneg hu_tail hvConstructed


end

end Homogenization
