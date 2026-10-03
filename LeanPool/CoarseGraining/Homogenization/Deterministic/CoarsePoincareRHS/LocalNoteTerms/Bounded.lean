/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.LocalNoteTerms.Stepping

/-! # Bounded -/

@[expose] public section

namespace Homogenization

noncomputable section

namespace ZeroTraceDirichletCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_eta_uSq_eta_wSq_invEta_gSq_two_two_of_bddAbove
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) {η : ℝ}
    (hs : 0 < s) (hη : 0 < η) (N : ℕ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
      η * (cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)) ^ 2 +
      2 * η⁻¹ *
        (((((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g)) ^ 2) := by
  let Child : ℝ :=
    Real.rpow (3 : ℝ) (-2 * s) *
      descendantsAverage Q 1
        (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2)
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  let W : ℝ := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)
  let C : ℝ := (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹
  let A : ℝ := 2 * C * cubeAverage Q (coefficientEnergyDensity a u)
  let K : ℝ := C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))
  let D : ℝ := 2 * K
  have hnegρ :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x) ≤
          Real.sqrt 2 * (U + W) := by
    dsimp [U, W]
    exact
      ρ.cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bddAbove
        (u := u) w huw hu s huBdd hwBdd
  have hposg :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g) ≤ G := by
    intro N
    dsimp [G]
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s (fun x => g x - cubeAverageVec Q g) hgBdd N
  have hmain :=
    ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_centeredCollapsedNoteTerm_two_two
      (u := u) w s hs N hEll hu hgrad hsum huw hmem hg hgradρ hBg hnegρ hposg
  have hmain' :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
        Child + A + D * (U + W) * G := by
    dsimp [Child, U, W, G, C, A, K, D] at hmain ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib] using hmain
  have hcross :
      D * (U + W) * G ≤ η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2) := by
    have hraw := add_bilinear_term_le_add_eta_sq_add_invEta_sq
      (D := D) (U := U) (W := W) (G := G) hη
    have hhalf : (D / 2) * G = K * G := by
      dsimp [D]
      ring
    calc
      D * (U + W) * G ≤
          η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * (((D / 2) * G) ^ 2) := hraw
      _ = η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2) := by
            rw [hhalf]
  have hfinal :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
        Child + A + η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2) := by
    linarith
  simpa [Child, U, W, G, C, A, K] using hfinal

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_harmonic_le_uCoeffEnergy_add_correctorShortTerm_two_two_of_bddAbove
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) (hs : 0 < s) (N : ℕ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => w.toH1.grad x)) ^ 2 ≤
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
            (Real.sqrt 2 *
              (cubeBesovNegativeVectorSeminormTwo Q s u +
                cubeBesovNegativeVectorSeminormTwo Q s
                  (fun x => w.toH1.grad x))) *
            cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g))) := by
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  let W : ℝ := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)
  let Short : ℝ :=
    (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * (Real.sqrt 2 * (U + W)) * G)
  have hharmonic :=
    sq_coarsePoincare_gradient_qtwo_partial_of_cubeAverageEnergyControl
      Q a s hs (fun x => w.toH1.grad x)
      (coefficientEnergyDensity a (fun x => w.toH1.grad x)) N
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll
        (fun x => w.toH1.grad x))
      (integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
        w.toH1.grad_memVectorL2)
      hgrad hsum
  have hnegρ :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x) ≤
          Real.sqrt 2 * (U + W) := by
    dsimp [U, W]
    exact
      ρ.cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bddAbove
        (u := u) w huw hu s huBdd hwBdd
  have hposg :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g) ≤ G := by
    intro N
    dsimp [G]
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s (fun x => g x - cubeAverageVec Q g) hgBdd N
  have hρenergy :
      cubeAverage Q
          (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x)) ≤
        Short := by
    dsimp [Short, U, W, G]
    exact
      ρ.coefficientEnergy_average_le_collapsed_note_term_centered_two_two
        s hs hmem hg hgradρ hBg hnegρ hposg
  have hwavg :=
    ρ.cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
      (u := u) w hEll huw hu
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hlambda_nonneg : 0 ≤ lambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  let C : ℝ := (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
      (inv_nonneg.mpr hlambda_nonneg)
  calc
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => w.toH1.grad x)) ^ 2
        ≤ C * cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) := by
            simpa [C] using hharmonic
    _ ≤ C *
        (2 * cubeAverage Q (coefficientEnergyDensity a u) +
          2 * cubeAverage Q
            (coefficientEnergyDensity a (fun x => ρ.toH10.toH1Function.grad x))) := by
            exact mul_le_mul_of_nonneg_left hwavg hC_nonneg
    _ ≤ C *
        (2 * cubeAverage Q (coefficientEnergyDensity a u) + 2 * Short) := by
            exact mul_le_mul_of_nonneg_left (by gcongr) hC_nonneg
    _ = 2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
          2 * C * Short := by
            ring
    _ =
        2 *
          ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
            cubeAverage Q (coefficientEnergyDensity a u) +
        2 *
          ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
              (Real.sqrt 2 *
                (cubeBesovNegativeVectorSeminormTwo Q s u +
                  cubeBesovNegativeVectorSeminormTwo Q s
                    (fun x => w.toH1.grad x))) *
              cubeBesovPositiveVectorSeminormTwo Q s
                (fun x => g x - cubeAverageVec Q g))) := by
            simp [C, Short, U, W, G]

theorem sq_cubeBesovNegativeVectorSeminormTwo_harmonic_le_uCoeffEnergy_add_correctorShortTerm_two_two_of_bddAbove
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ)
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)) ^ 2 ≤
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
            (Real.sqrt 2 *
              (cubeBesovNegativeVectorSeminormTwo Q s u +
                cubeBesovNegativeVectorSeminormTwo Q s
                  (fun x => w.toH1.grad x))) *
            cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g))) := by
  let B : ℝ :=
    2 *
      ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
        cubeAverage Q (coefficientEnergyDensity a u) +
    2 *
      ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
          (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s
                (fun x => w.toH1.grad x))) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g)))
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hlambda_nonneg : 0 ≤ lambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  have huSem_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s u :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s u huBdd
  have hwSem_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x) :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s
      (fun x => w.toH1.grad x) hwBdd
  have hgSem_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove
      Q s (fun x => g x - cubeAverageVec Q g) hgBdd
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine add_nonneg ?_ ?_
    · refine mul_nonneg ?_ ?_
      · refine mul_nonneg (by norm_num) ?_
        exact mul_nonneg
          (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
          (inv_nonneg.mpr hlambda_nonneg)
      · exact cubeAverage_nonneg_of_nonneg_on
          (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u)
    · refine mul_nonneg ?_ ?_
      · refine mul_nonneg (by norm_num) ?_
        exact mul_nonneg
          (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
          (inv_nonneg.mpr hlambda_nonneg)
      · refine mul_nonneg (by positivity) ?_
        refine mul_nonneg ?_ hgSem_nonneg
        refine mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) ?_
        exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg huSem_nonneg hwSem_nonneg)
  have hpartial :
      ∀ N : ℕ,
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)) ^ 2 ≤ B := by
    intro N
    dsimp [B]
    exact
      ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_harmonic_le_uCoeffEnergy_add_correctorShortTerm_two_two_of_bddAbove
        (u := u) w s hs N hEll hu hgrad hsum huw
        hmem hg hgradρ hBg huBdd hwBdd hgBdd
  simpa [B] using
    sq_cubeBesovNegativeVectorSeminormTwo_le_of_partialSqBound
      (Q := Q) (s := s) (u := fun x => w.toH1.grad x) hB_nonneg hpartial

theorem sq_cubeBesovNegativeVectorSeminormTwo_harmonic_le_uCoeffEnergy_add_eta_uSq_add_invEta_gSq_two_two_of_bddAbove
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) {η : ℝ}
    (hs : 0 < s) (hη : 0 < η) (hη_lt : η < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)) ^ 2 ≤
      (1 - η)⁻¹ *
        (2 *
            ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
            cubeAverage Q (coefficientEnergyDensity a u) +
          η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
          2 * η⁻¹ *
            (((((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
              cubeBesovPositiveVectorSeminormTwo Q s
                (fun x => g x - cubeAverageVec Q g)) ^ 2)) := by
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  let W : ℝ := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)
  let C : ℝ := (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹
  let A : ℝ := 2 * C * cubeAverage Q (coefficientEnergyDensity a u)
  let K : ℝ := C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))
  let D : ℝ := 2 * K
  have hmain :=
    ρ.sq_cubeBesovNegativeVectorSeminormTwo_harmonic_le_uCoeffEnergy_add_correctorShortTerm_two_two_of_bddAbove
      (u := u) w s hs hEll hu hgrad hsum huw
      hmem hg hgradρ hBg huBdd hwBdd hgBdd
  have hmain' : W ^ 2 ≤ A + D * (U + W) * G := by
    dsimp [U, W, G, C, A, K, D] at hmain ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib] using hmain
  have habsorb :=
    sq_le_inv_one_sub_mul_add_of_sq_le_add_bilinear_term
      (A := A) (D := D) (U := U) (W := W) (G := G) hη hη_lt hmain'
  have hhalf : (D / 2) * G = K * G := by
    dsimp [D]
    ring
  have hfinal :
      W ^ 2 ≤ (1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2)) := by
    calc
      W ^ 2 ≤
          (1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * (((D / 2) * G) ^ 2)) :=
            habsorb
      _ = (1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2)) := by
            rw [hhalf]
  simpa [U, W, G, C, A, K] using hfinal

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_absorbed_uSq_gSq_two_two_of_bddAbove
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) {η : ℝ}
    (hs : 0 < s) (hη : 0 < η) (hη_lt : η < 1) (N : ℕ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
      η *
        ((1 - η)⁻¹ *
          (2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
              cubeAverage Q (coefficientEnergyDensity a u) +
            η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
            2 * η⁻¹ *
              (((((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                  ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
                cubeBesovPositiveVectorSeminormTwo Q s
                  (fun x => g x - cubeAverageVec Q g)) ^ 2))) +
      2 * η⁻¹ *
        (((((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g)) ^ 2) := by
  let Child : ℝ :=
    Real.rpow (3 : ℝ) (-2 * s) *
      descendantsAverage Q 1
        (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2)
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  let W : ℝ := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)
  let C : ℝ := (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹
  let A : ℝ := 2 * C * cubeAverage Q (coefficientEnergyDensity a u)
  let K : ℝ := C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))
  let H : ℝ := (1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2))
  have hrec :=
    ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_eta_uSq_eta_wSq_invEta_gSq_two_two_of_bddAbove
      (u := u) w s hs hη N hEll hu hgrad hsum huw
      hmem hg hgradρ hBg huBdd hwBdd hgBdd
  have hrec' :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
        Child + A + η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2) := by
    simpa [Child, U, W, G, C, A, K] using hrec
  have hharm :=
    ρ.sq_cubeBesovNegativeVectorSeminormTwo_harmonic_le_uCoeffEnergy_add_eta_uSq_add_invEta_gSq_two_two_of_bddAbove
      (u := u) w s hs hη hη_lt hEll hu hgrad hsum huw
      hmem hg hgradρ hBg huBdd hwBdd hgBdd
  have hharm' : W ^ 2 ≤ H := by
    simpa [W, G, C, A, K, H, U] using hharm
  have hηW : η * W ^ 2 ≤ η * H :=
    mul_le_mul_of_nonneg_left hharm' hη.le
  have hfinal :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
        Child + A + η * U ^ 2 + η * H + 2 * η⁻¹ * ((K * G) ^ 2) := by
    linarith
  simpa [Child, U, G, C, A, K, H] using hfinal

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_descendantsAverage_add_uCoeffEnergy_add_absorbed_uSq_gSq_two_two_of_partialChildBounds
    (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} (s : ℝ) {η : ℝ} (Bchild : TriadicCube d → ℝ)
    (hs : 0 < s) (hη : 0 < η) (hη_lt : η < 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : MemVectorL2 (cubeSet Q) u)
    (hgrad :
      CubeAverageGradientEnergyControl Q a (fun x => w.toH1.grad x)
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q, u x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hmem : MemVectorL2 (cubeSet Q) g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hgradρ : MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
      (2 : ENNReal) (normalizedCubeMeasure Q))
    (hBg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g)))
    (hchild :
      ∀ R ∈ descendantsAtDepth Q 1, ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo R s N u ≤ Bchild R) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) +
      2 *
        ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
          cubeAverage Q (coefficientEnergyDensity a u) +
      η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
      η *
        ((1 - η)⁻¹ *
          (2 *
              ((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
              cubeAverage Q (coefficientEnergyDensity a u) +
            η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
            2 * η⁻¹ *
              (((((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
                  ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
                cubeBesovPositiveVectorSeminormTwo Q s
                  (fun x => g x - cubeAverageVec Q g)) ^ 2))) +
      2 * η⁻¹ *
        (((((geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹) *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g)) ^ 2) := by
  let Echild : ℝ :=
    Real.rpow (3 : ℝ) (-2 * s) *
      descendantsAverage Q 1 (fun R => (Bchild R) ^ 2)
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)
  let C : ℝ := (geometricDiscount s 2)⁻¹ * (lambdaSq Q s (.finite 2) a)⁻¹
  let A : ℝ := 2 * C * cubeAverage Q (coefficientEnergyDensity a u)
  let K : ℝ := C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))
  let H : ℝ := (1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2))
  let F : ℝ := A + η * U ^ 2 + η * H + 2 * η⁻¹ * ((K * G) ^ 2)
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hlambda_nonneg : 0 ≤ lambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s 2 a (by norm_num)
      (by nlinarith [hs])
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
      (inv_nonneg.mpr hlambda_nonneg)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hC_nonneg)
      (cubeAverage_nonneg_of_nonneg_on
        (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u))
  have hone_sub : 0 < 1 - η := by linarith
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    refine mul_nonneg (inv_nonneg.mpr hone_sub.le) ?_
    refine add_nonneg (add_nonneg hA_nonneg ?_) ?_
    · exact mul_nonneg hη.le (sq_nonneg U)
    · exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hη.le)) (sq_nonneg (K * G))
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    refine add_nonneg (add_nonneg (add_nonneg hA_nonneg ?_) ?_) ?_
    · exact mul_nonneg hη.le (sq_nonneg U)
    · exact mul_nonneg hη.le hH_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hη.le)) (sq_nonneg (K * G))
  have hEchild_nonneg : 0 ≤ Echild := by
    dsimp [Echild]
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (descendantsAverage_nonneg Q 1 _ fun R hR => sq_nonneg (Bchild R))
  have hB_nonneg : 0 ≤ Echild + F := add_nonneg hEchild_nonneg hF_nonneg
  have hlocal :
      ∀ N : ℕ,
        (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
          F := by
    intro N
    have hN :=
      ρ.sq_cubeBesovNegativeVectorPartialSeminormTwo_succ_le_descendantsAverage_add_uCoeffEnergy_add_absorbed_uSq_gSq_two_two_of_bddAbove
        (u := u) w s hs hη hη_lt N hEll hu hgrad hsum huw
        hmem hg hgradρ hBg huBdd hwBdd hgBdd
    simpa [U, G, C, A, K, H, F, add_assoc] using hN
  have hfull :=
    sq_cubeBesovNegativeVectorSeminormTwo_le_descendantsAverage_add_of_succ_partialBound
      (Q := Q) (s := s) (u := u) Bchild hB_nonneg hlocal hchild
  simpa [Echild, U, G, C, A, K, H, F, add_assoc] using hfull


end ZeroTraceDirichletCorrectorData

end

end Homogenization
