/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.GlobalIteration

/-! # Note Step And Constants -/

namespace Homogenization

noncomputable section

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q))
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
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s)) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤
      coarsePoincareRHSSIntrinsicGlobalEnergyBase Q a u s 5 0 * (5 * s⁻¹) +
        coarsePoincareRHSSIntrinsicGlobalForceBase Q a g s (120 * s⁻¹) 0 *
          (5 * s⁻¹) := by
  simpa using
    coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hData hsum_half hu havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hlocal 0

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q))
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
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s)) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a u) +
        15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hmain :=
    sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hData hsum_half hu havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hlocal
  have hE :=
    coarsePoincareRHSSIntrinsicGlobalEnergyBase_zero_noteConstants_le
      (Q := Q) (a := a) (u := u) hs hs_le (havg_nonneg 0 Q (by simp))
  have hF :=
    coarsePoincareRHSSIntrinsicGlobalForceBase_zero_noteConstants_le
      (Q := Q) (a := a) (g := g) (s := s) hs hs_le
  exact hmain.trans (add_le_add hE hF)

theorem coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants_expanded
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q))
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
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s))
    (m : ℕ) :
    coarsePoincareRHSSn Q s u m ≤
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a u) +
        15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hmain :=
    coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hData hsum_half hu havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hlocal m
  have hE :=
    coarsePoincareRHSSIntrinsicGlobalEnergyBase_noteConstants_le
      (Q := Q) (a := a) (u := u) hs hs_le (havg_nonneg 0 Q (by simp)) m
  have hF :=
    coarsePoincareRHSSIntrinsicGlobalForceBase_noteConstants_le
      (Q := Q) (a := a) (g := g) (s := s) hs hs_le m
  exact hmain.trans (add_le_add hE hF)


end

end Homogenization
