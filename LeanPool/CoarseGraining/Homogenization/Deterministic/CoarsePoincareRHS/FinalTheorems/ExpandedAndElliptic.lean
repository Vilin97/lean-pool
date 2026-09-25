/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.FinalTheorems.NoteStepAndConstants
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.LocalNoteTerms.Intrinsic

/-! # Expanded And Elliptic -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)
  have hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1) := by
    have hs_half : 0 < s / 2 := by nlinarith
    simpa using
      summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) (s / 2) hs_half hEll hOrigin
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have huMem : MemVectorL2 (cubeSet Q) u :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hu
  have hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll huMem
  have havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u) := by
    intro n R hR
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (hEll.mono (measurableSet_cubeSet R)
          (cubeSet_subset_of_mem_descendantsAtDepth hR)) u)
  have hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S) := by
    intro j S hS
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hS hg
  have hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro n R hR
    exact cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
      s g hR hGlobalBdd
  exact
    sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEllOpen hData hsum_half hu havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hlocal

theorem coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)
  have hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1) := by
    have hs_half : 0 < s / 2 := by nlinarith
    simpa using
      summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) (s / 2) hs_half hEll hOrigin
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have huMem : MemVectorL2 (cubeSet Q) u :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hu
  have hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll huMem
  have havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u) := by
    intro n R hR
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (hEll.mono (measurableSet_cubeSet R)
          (cubeSet_subset_of_mem_descendantsAtDepth hR)) u)
  have hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S) := by
    intro j S hS
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hS hg
  have hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro n R hR
    exact cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
      s g hR hGlobalBdd
  exact
    coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants_expanded
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEllOpen hData hsum_half hu havg_nonneg hint hmem hGlobalBdd
      hLocalBdd hlocal m

theorem cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s)) :
    cubeBesovNegativeVectorSeminormTwo Q s u ≤
      Real.sqrt
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a u) +
          15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  have hsq :=
    sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_isEllipticFieldOn
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hu hg hGlobalBdd hlocal
  have hnonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s u :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp Q hs u hu
  calc
    cubeBesovNegativeVectorSeminormTwo Q s u
        = Real.sqrt ((cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
    _ ≤
        Real.sqrt
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
              cubeAverage Q (coefficientEnergyDensity a u) +
            15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) :=
            Real.sqrt_le_sqrt hsq

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a u) +
        15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have huMem : MemVectorL2 (cubeSet Q) u := by
    rcases hu_potential with ⟨v, hv⟩
    simpa [← hv] using v.grad_memVectorL2
  have hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q huMem
  have hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s) := by
    intro n R hR
    have hLocalBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) :=
      cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
        s g hR hGlobalBdd
    exact
      ZeroTraceDirichletCorrectorData.sq_cubeBesovNegativeVectorSeminormTwo_le_discount_next_add_intrinsicAbsorbedLocalError_noteEta_of_parent_potential_solenoidal
        (Q := Q) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam) (s := s)
        hs hu_potential hu_residual hR hEll hg hLocalBdd
  exact
    sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_isEllipticFieldOn
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hu hg hGlobalBdd hlocal

theorem cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    cubeBesovNegativeVectorSeminormTwo Q s u ≤
      Real.sqrt
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a u) +
          15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  have huMem : MemVectorL2 (cubeSet Q) u := by
    rcases hu_potential with ⟨v, hv⟩
    simpa [← hv] using v.grad_memVectorL2
  have hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q huMem
  have hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s) := by
    intro n R hR
    have hLocalBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) :=
      cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
        s g hR hGlobalBdd
    exact
      ZeroTraceDirichletCorrectorData.sq_cubeBesovNegativeVectorSeminormTwo_le_discount_next_add_intrinsicAbsorbedLocalError_noteEta_of_parent_potential_solenoidal
        (Q := Q) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam) (s := s)
        hs hu_potential hu_residual hR hEll hg hLocalBdd
  exact
    cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_isEllipticFieldOn
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hu hg hGlobalBdd hlocal

theorem coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_potential : IsPotentialOn (cubeSet Q) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet Q) (fun x => matVecMul (a x) (u x) - g x))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (m : ℕ) :
    coarsePoincareRHSSn Q s u m ≤
      250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a u) +
        15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have huMem : MemVectorL2 (cubeSet Q) u := by
    rcases hu_potential with ⟨v, hv⟩
    simpa [← hv] using v.grad_memVectorL2
  have hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q huMem
  have hlocal :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 ≤
          coarsePoincareRHSDiscount s * coarsePoincareRHSRn R s u 1 +
          coarsePoincareRHSIntrinsicAbsorbedLocalError R a g u s
            (coarsePoincareRHSNoteEta s) := by
    intro n R hR
    have hLocalBdd :
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) :=
      cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
        s g hR hGlobalBdd
    exact
      ZeroTraceDirichletCorrectorData.sq_cubeBesovNegativeVectorSeminormTwo_le_discount_next_add_intrinsicAbsorbedLocalError_noteEta_of_parent_potential_solenoidal
        (Q := Q) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam) (s := s)
        hs hu_potential hu_residual hR hEll hg hLocalBdd
  exact
    coarsePoincareRHSSn_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_isEllipticFieldOn
      (Q := Q) (a := a) (g := g) (u := u)
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hu hg hGlobalBdd hlocal m

end

end Homogenization
