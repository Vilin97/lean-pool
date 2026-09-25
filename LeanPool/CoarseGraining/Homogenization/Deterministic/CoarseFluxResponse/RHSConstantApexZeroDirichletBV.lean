/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletEstimates
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletScalarAdequacy

/-! # RHSConstant Apex Zero Dirichlet BV -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Averaged `BV` tail for the zero-Dirichlet RHS apex

This leaf proves the averaged harmonic-remainder tail estimate actually
consumed by the weak-flux iteration.  The pointwise `BVEstimate` package in
`RHSConstantApexZeroDirichletEstimates` remains available, but this theorem
targets the weaker averaged quantity appearing in the recurrence.
-/

open scoped BigOperators ENNReal

namespace ZeroTraceDirichletCorrectorData

theorem zeroTraceDirichletHarmonicRemainderSq_le_corrector_energy_and_neumann_young_terms
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hgR : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N
          (fun x => g x - cubeAverageVec R g)))
    (ω : MeanZeroNeumannCorrectorData R a
      (fun x => g x - cubeAverageVec R g))
    (w0 : AHarmonicFunction a (cubeSet R))
    (hdecomp :
      ∀ x ∈ cubeSet R,
        ρ.toH10.toH1Function.grad x =
          w0.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) :
    (cubeBesovNegativeVectorSeminormTwo R s
      (fun x => w0.toH1.grad x)) ^ 2 ≤
      500 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage R
            (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x)) +
        (250 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => ω.toH1MeanZero.toH1Function.grad x)) ^ 2 +
          250 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
              cubeBesovPositiveVectorSeminormTwo R s
                (fun x => g x - cubeAverageVec R g))) ^ 2) := by
  let W : ℝ :=
    cubeBesovNegativeVectorSeminormTwo R s
      (fun x => ω.toH1MeanZero.toH1Function.grad x)
  let G : ℝ :=
    cubeBesovPositiveVectorSeminormTwo R s
      (fun x => g x - cubeAverageVec R g)
  let M : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
  let K : ℝ :=
    250 * (s⁻¹) ^ 2 * (lambdaSq R (s / 2) (.finite 2) a)⁻¹
  have hzeroMem :
      MeasureTheory.MemLp (0 : Vec d → Vec d) (2 : ENNReal)
        (normalizedCubeMeasure R) := by
    simp
  have hsol :
      IsSolenoidalOn (cubeSet R)
        (fun x => matVecMul (a x) (w0.toH1.grad x) -
          (0 : Vec d → Vec d) x) := by
    simpa using w0.isHarmonic.2
  have hsq :
      (cubeBesovNegativeVectorSeminormTwo R s
        (fun x => w0.toH1.grad x)) ^ 2 ≤
        250 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => w0.toH1.grad x)) := by
    simpa using
      sq_cubeBesovNegativeVectorSeminormTwo_le_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
        (Q := R) (a := a) (g := (0 : Vec d → Vec d))
        (u := fun x => w0.toH1.grad x)
        (s := s) (lam := lam) (Lam := Lam)
        hs hs_le hEllR w0.isHarmonic.1 hsol hzeroMem
        (cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove R s)
  have hρMemQ :
      MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      ρ.toH10.toH1Function.grad_memVectorL2
  have hρMemR :
      MemVectorL2 (cubeSet R)
        (fun x => ρ.toH10.toH1Function.grad x) :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
      (memLp_on_descendant_of_memLp_generic (E := Vec d) hR hρMemQ)
  have hsplit :
      cubeAverage R
          (coefficientEnergyDensity a
            (fun x => w0.toH1.grad x)) ≤
        2 * cubeAverage R
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) +
        2 * cubeAverage R
          (coefficientEnergyDensity a
            (fun x => ω.toH1MeanZero.toH1Function.grad x)) :=
    ω.cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
      (u := fun x => ρ.toH10.toH1Function.grad x) w0 hEllR hdecomp
      hρMemR
  have hlambda_nonneg :
      0 ≤ lambdaSq R (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg R (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hcoeff250_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have hsplit_weighted :
      250 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage R
            (coefficientEnergyDensity a
              (fun x => w0.toH1.grad x)) ≤
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) +
          500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
    nlinarith [mul_le_mul_of_nonneg_left hsplit hcoeff250_nonneg]
  have hgMemR : MemVectorL2 (cubeSet R) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R hgR
  have hωgrad :
      MeasureTheory.MemLp (fun x => ω.toH1MeanZero.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet R
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hωBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp R hs
      (fun x => ω.toH1MeanZero.toH1Function.grad x) hωgrad
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact
      cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove R s
        (fun x => g x - cubeAverageVec R g) hgBdd
  have hωEnergy :=
    ω.coefficientEnergy_average_le_collapsed_note_term_centered_two_two
      (s := s) (Bω := W) (Bg := G)
      hs hgMemR hgR hωgrad hG_nonneg
      (fun N =>
        cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          R s (fun x => ω.toH1MeanZero.toH1Function.grad x) hωBdd N)
      (fun N =>
        cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
          R s (fun x => g x - cubeAverageVec R g) hgBdd N)
  have hcoeff500_nonneg :
      0 ≤ 500 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (500 : ℝ)) (sq_nonneg (s⁻¹)))
        (inv_nonneg.mpr hlambda_nonneg)
  have hωWeighted :
      500 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage R
            (coefficientEnergyDensity a
              (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
        500 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * W * G)) :=
    mul_le_mul_of_nonneg_left hωEnergy hcoeff500_nonneg
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact hcoeff250_nonneg
  have hYoung :
      500 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * W * G)) ≤
        K * W ^ 2 + K * (M * G) ^ 2 := by
    have hbase : 2 * W * (M * G) ≤ W ^ 2 + (M * G) ^ 2 := by
      nlinarith [sq_nonneg (W - M * G)]
    have hscaled := mul_le_mul_of_nonneg_left hbase hK_nonneg
    calc
      500 * (s⁻¹) ^ 2 *
          (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * W * G))
          =
        K * (2 * W * (M * G)) := by
          dsimp [K, M]
          ring
      _ ≤ K * (W ^ 2 + (M * G) ^ 2) := hscaled
      _ = K * W ^ 2 + K * (M * G) ^ 2 := by ring
  calc
    (cubeBesovNegativeVectorSeminormTwo R s
      (fun x => w0.toH1.grad x)) ^ 2
        ≤ 250 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => w0.toH1.grad x)) := hsq
    _ ≤
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) +
          500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) :=
        hsplit_weighted
    _ ≤
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) +
          (K * W ^ 2 + K * (M * G) ^ 2) := by
        exact add_le_add_right (hωWeighted.trans hYoung) _
    _ =
        500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) +
          (250 * (s⁻¹) ^ 2 *
              (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
              (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) ^ 2 +
            250 * (s⁻¹) ^ 2 *
              (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
                cubeBesovPositiveVectorSeminormTwo R s
                  (fun x => g x - cubeAverageVec R g))) ^ 2) := by
        dsimp [K, W, G, M]
        ring

/--
Raw averaged control of the zero-trace corrector-energy part of the harmonic
remainder `BV` budget.

This is the analytic `rho` component before converting the natural
`lambda^{-2}` scale produced by the energy envelope into the corrected
weak-flux compact `Lambda * lambda^{-1}` scale.
-/
theorem zeroTraceDirichletHarmonicRemainderRhoEnergyAverage_le_raw_lambdaInv_sq
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    ∀ j : ℕ,
      coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j
            (fun R =>
              500 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage R
                    (coefficientEnergyDensity a
                      (fun x => ρ.toH10.toH1Function.grad x))) ≤
        325000 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          ((s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  intro j
  let u : Vec d → Vec d := fun x => ρ.toH10.toH1Function.grad x
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let E : ℝ := cubeAverage Q (coefficientEnergyDensity a u)
  let W : ℝ := coarsePoincareRHSDepthWeight s j
  let T : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  have hs_half : 0 < s / 2 := by nlinarith
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)
  have hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a)
            (2 / 2)) := by
    have hsum :
        Summable (fun m : ℕ =>
          geometricWeight (s / 2) 2 m *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) :=
      summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) (s := s / 2) hs_half hEll hData
    simpa using hsum
  have hlocal_lambda :
      ∀ R ∈ descendantsAtDepth Q j,
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤ T * L := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hloc :
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
          Real.rpow (3 : ℝ)
              (2 * (s / 2) *
                (Int.toNat (Q.scale - (Q.scale - (j : ℤ))) : ℝ)) *
            L := by
      simpa [L] using
        multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a (s / 2) 2
          (by nlinarith : 0 ≤ s / 2) (by norm_num) hRscale hsum_half
    have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
      have hdiff : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by
        omega
      rw [hdiff]
      simp
    have hloc' :
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
          Real.rpow (3 : ℝ) (2 * (s / 2) * (j : ℝ)) * L := by
      simpa [htoNat] using hloc
    simpa [T, show 2 * (s / 2) * (j : ℝ) = s * (j : ℝ) by ring] using hloc'
  have havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u) := by
    intro R hR
    exact
      cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        R a u
        (hEll.mono (measurableSet_cubeSet R)
          (cubeSet_subset_of_mem_descendantsAtDepth hR))
  have hlocal_bound :
      descendantsAverage Q j
          (fun R =>
            500 * (s⁻¹) ^ 2 *
                (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage R (coefficientEnergyDensity a u)) ≤
        500 * (s⁻¹) ^ 2 * (T * L) *
          descendantsAverage Q j
            (fun R => cubeAverage R (coefficientEnergyDensity a u)) := by
    calc
      descendantsAverage Q j
          (fun R =>
            500 * (s⁻¹) ^ 2 *
                (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage R (coefficientEnergyDensity a u))
          ≤
        descendantsAverage Q j
          (fun R =>
            (500 * (s⁻¹) ^ 2 * (T * L)) *
                cubeAverage R (coefficientEnergyDensity a u)) := by
          refine descendantsAverage_le_descendantsAverage Q j ?_
          intro R hR
          have hscaled :=
            mul_le_mul_of_nonneg_right (hlocal_lambda R hR) (havg_nonneg R hR)
          have hcoeff_nonneg : 0 ≤ 500 * (s⁻¹) ^ 2 := by
            exact mul_nonneg (by norm_num : 0 ≤ (500 : ℝ)) (sq_nonneg (s⁻¹))
          nlinarith [mul_le_mul_of_nonneg_left hscaled hcoeff_nonneg]
      _ =
        500 * (s⁻¹) ^ 2 * (T * L) *
          descendantsAverage Q j
            (fun R => cubeAverage R (coefficientEnergyDensity a u)) := by
          rw [descendantsAverage_smul Q j (500 * (s⁻¹) ^ 2 * (T * L))
            (fun R => cubeAverage R (coefficientEnergyDensity a u))]
  have hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume := by
    dsimp [u]
    exact integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  have hpartition :
      descendantsAverage Q j
          (fun R => cubeAverage R (coefficientEnergyDensity a u)) = E := by
    dsimp [E]
    exact (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j (coefficientEnergyDensity a u) hint).symm
  have hweight_nonneg : 0 ≤ W := by
    dsimp [W]
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hweighted :
      W *
          descendantsAverage Q j
            (fun R =>
              500 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage R (coefficientEnergyDensity a u)) ≤
        500 * (s⁻¹) ^ 2 * L * E := by
    have hmul := mul_le_mul_of_nonneg_left hlocal_bound hweight_nonneg
    have hcancel : W * T = 1 := by
      dsimp [W, T]
      unfold coarsePoincareRHSDepthWeight
      calc
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            Real.rpow (3 : ℝ) (s * (j : ℝ))
            = Real.rpow (3 : ℝ) ((-s * (j : ℝ)) + s * (j : ℝ)) := by
              exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
                (-s * (j : ℝ)) (s * (j : ℝ))).symm
        _ = 1 := by
              have hsum : (-s * (j : ℝ)) + s * (j : ℝ) = 0 := by ring
              rw [hsum]
              simp
    calc
      W *
          descendantsAverage Q j
            (fun R =>
              500 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage R (coefficientEnergyDensity a u))
          ≤
        W *
          (500 * (s⁻¹) ^ 2 * (T * L) *
            descendantsAverage Q j
              (fun R => cubeAverage R (coefficientEnergyDensity a u))) := hmul
      _ = (W * T) * (500 * (s⁻¹) ^ 2 * L * E) := by
            rw [hpartition]
            ring
      _ = 500 * (s⁻¹) ^ 2 * L * E := by
            rw [hcancel]
            ring
  have henergyEnvelope :
      E ≤ zeroTraceDirichletEnergyEnvelope Q a s g := by
    dsimp [E, u]
    exact
      ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded
        (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hcoeff_nonneg : 0 ≤ 500 * (s⁻¹) ^ 2 * L := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (500 : ℝ)) (sq_nonneg (s⁻¹)))
        hL_nonneg
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  have henv_display :
      zeroTraceDirichletEnergyEnvelope Q a s g ≤
        650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
    simpa [L, N, G, mul_assoc, mul_left_comm, mul_comm] using
      zeroTraceDirichletEnergyEnvelope_le_poincareDisplayedScale_noteConstants
        Q a g hs hG_nonneg
  calc
    coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j
            (fun R =>
              500 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage R
                    (coefficientEnergyDensity a
                      (fun x => ρ.toH10.toH1Function.grad x)))
        =
      W *
          descendantsAverage Q j
            (fun R =>
              500 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage R (coefficientEnergyDensity a u)) := by
          dsimp [W, u]
    _ ≤ 500 * (s⁻¹) ^ 2 * L * E := hweighted
    _ ≤ 500 * (s⁻¹) ^ 2 * L *
          zeroTraceDirichletEnergyEnvelope Q a s g := by
          exact mul_le_mul_of_nonneg_left henergyEnvelope hcoeff_nonneg
    _ ≤ 500 * (s⁻¹) ^ 2 * L *
          (650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2) := by
          exact mul_le_mul_of_nonneg_left henv_display hcoeff_nonneg
    _ =
        325000 * N ^ 2 * ((s⁻¹) ^ 4 * L ^ 2 * G ^ 2) := by ring
    _ =
        325000 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          ((s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
          dsimp [N, L, G]

theorem zeroTraceDirichletHarmonicRemainderScaledAveragedTail_le_of_selectors_corrector_energy_and_neumann_young_average_bounds
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s : ℝ) {BV Bρ BωNeg BωForce lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hg_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R))
    (hgBdd_centered_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    (v : TriadicCube d → Vec d → Vec d)
    (ω : (R : TriadicCube d) →
      MeanZeroNeumannCorrectorData R a
        (fun x => g x - cubeAverageVec R g))
    (w0 : (R : TriadicCube d) → AHarmonicFunction a (cubeSet R))
    (hv_eq :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        v R = (fun x => (w0 R).toH1.grad x))
    (hdecomp :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ x ∈ cubeSet R,
          ρ.toH10.toH1Function.grad x =
            (w0 R).toH1.grad x +
              (ω R).toH1MeanZero.toH1Function.grad x)
    (hρEnergyAvg :
      ∀ j : ℕ,
        coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j
            (fun R =>
              500 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage R
                    (coefficientEnergyDensity a
                      (fun x => ρ.toH10.toH1Function.grad x))) ≤ Bρ)
    (hωNegSqAvg :
      ∀ j : ℕ,
        coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j
            (fun R =>
              250 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => (ω R).toH1MeanZero.toH1Function.grad x)) ^ 2) ≤
          BωNeg)
    (hcenteredForceSqAvg :
      ∀ j : ℕ,
        coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j
            (fun R =>
              250 * (s⁻¹) ^ 2 *
                  (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
                  ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
                    cubeBesovPositiveVectorSeminormTwo R s
                      (fun x => g x - cubeAverageVec R g))) ^ 2) ≤
          BωForce)
    (hbudget : Bρ + (BωNeg + BωForce) ≤ BV) :
    ∀ j : ℕ,
      weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v j ≤ BV := by
  intro j
  let Aρ : TriadicCube d → ℝ := fun R =>
    500 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
        cubeAverage R
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x))
  let Aω : TriadicCube d → ℝ := fun R =>
    250 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => (ω R).toH1MeanZero.toH1Function.grad x)) ^ 2
  let Ag : TriadicCube d → ℝ := fun R =>
    250 * (s⁻¹) ^ 2 *
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovPositiveVectorSeminormTwo R s
            (fun x => g x - cubeAverageVec R g))) ^ 2
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤
          Aρ R + (Aω R + Ag R) := by
    intro R hR
    have hlocal :=
      zeroTraceDirichletHarmonicRemainderSq_le_corrector_energy_and_neumann_young_terms
        (Q := Q) (R := R) ρ hR hs hs_le
        (hEll_desc R ⟨j, hR⟩) (hg_mem_desc j R hR)
        (hgBdd_centered_desc j R hR) (ω R) (w0 R)
        (hdecomp j R hR)
    simpa [hv_eq j R hR, Aρ, Aω, Ag] using hlocal
  have havg :
      weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v j ≤
        descendantsAverage Q j (fun R => Aρ R + (Aω R + Ag R)) := by
    unfold weakFluxRHSHarmonicRemainderAveragedSeminormSq
    exact descendantsAverage_le_descendantsAverage Q j hpoint
  have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s j := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hscaled :
      weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v j ≤
        coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j (fun R => Aρ R + (Aω R + Ag R)) := by
    unfold weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq
    exact mul_le_mul_of_nonneg_left havg hweight_nonneg
  have hsplit :
      coarsePoincareRHSDepthWeight s j *
          descendantsAverage Q j (fun R => Aρ R + (Aω R + Ag R)) =
        coarsePoincareRHSDepthWeight s j * descendantsAverage Q j Aρ +
          (coarsePoincareRHSDepthWeight s j * descendantsAverage Q j Aω +
            coarsePoincareRHSDepthWeight s j * descendantsAverage Q j Ag) := by
    rw [descendantsAverage_add Q j Aρ (fun R => Aω R + Ag R)]
    rw [descendantsAverage_add Q j Aω Ag]
    ring
  have hsum :
      coarsePoincareRHSDepthWeight s j * descendantsAverage Q j Aρ +
          (coarsePoincareRHSDepthWeight s j * descendantsAverage Q j Aω +
            coarsePoincareRHSDepthWeight s j * descendantsAverage Q j Ag) ≤
        Bρ + (BωNeg + BωForce) := by
    exact add_le_add (hρEnergyAvg j)
      (add_le_add (hωNegSqAvg j) (hcenteredForceSqAvg j))
  exact hscaled.trans (by rw [hsplit]; exact hsum.trans hbudget)

end ZeroTraceDirichletCorrectorData

end

end Homogenization
