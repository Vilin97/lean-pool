/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedComponentBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyPoincare

/-! # Corrector Energy Averaged -/

namespace Homogenization

noncomputable section

/-!
# Averaged corrector-energy input for the corrected weak-flux route

This leaf turns the local Neumann-corrector force-scale estimate into the
depth-weighted descendant average used by the corrected zero-Dirichlet
weak-flux recurrence.
-/

open scoped ENNReal

private theorem inv_geometricDiscount_two_mul_inv_one_sub_step_le_five_halves_inv_sq
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) :
    (geometricDiscount s 2)⁻¹ * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      (5 / 2) * (s⁻¹) ^ 2 := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s)
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.rpow (3 : ℝ) t) :=
    convexOn_rpow_left (by norm_num : 0 < (3 : ℝ))
  have hr_chord : r ≤ 1 - (2 / 3) * s := by
    have hconv_ineq := And.right hconv
    have h :=
      hconv_ineq (x := (0 : ℝ)) (y := (-1 : ℝ)) (a := 1 - s) (b := s)
        (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
        (by linarith) hs.le (by ring)
    have hpow_neg_one : Real.rpow (3 : ℝ) (-1 : ℝ) = (3 : ℝ)⁻¹ := by
      change (3 : ℝ) ^ (-1 : ℝ) = (3 : ℝ)⁻¹
      rw [Real.rpow_neg_one]
    dsimp [r] at h
    have h' : Real.rpow (3 : ℝ) (-s) ≤ 1 - s + s * (3 : ℝ)⁻¹ := by
      simpa [Real.rpow_neg_one] using h
    nlinarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hr_le_one : r ≤ 1 := hr_lt_one.le
  have hdenH_pos : 0 < 1 - r := by linarith
  have hdenD_pos : 0 < geometricDiscount s 2 :=
    geometricDiscount_pos (by nlinarith : 0 < s * 2)
  have htarget_den_pos : 0 < (2 / 3) * s := by positivity
  have hden_lower : (2 / 3) * s ≤ 1 - r := by
    linarith
  have hH_le :
      (1 - r)⁻¹ ≤ (3 / 2) * s⁻¹ := by
    have hraw := (inv_le_inv₀ hdenH_pos htarget_den_pos).2 hden_lower
    have hrewrite : ((2 / 3) * s)⁻¹ = (3 / 2) * s⁻¹ := by
      field_simp [hs.ne']
    simpa [hrewrite] using hraw
  have hr_sq_le : r ^ 2 ≤ r := by
    have hmul := mul_le_mul_of_nonneg_right hr_le_one hr_nonneg
    simpa [pow_two] using hmul
  have hr_sq_eq :
      r ^ 2 = Real.rpow (3 : ℝ) (-s * 2) := by
    dsimp [r]
    calc
      (Real.rpow (3 : ℝ) (-s)) ^ 2 =
          Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (-s) := by ring
      _ = Real.rpow (3 : ℝ) ((-s) + (-s)) := by
          exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) (-s) (-s)).symm
      _ = Real.rpow (3 : ℝ) (-s * 2) := by
          ring_nf
  have hden_order : 1 - r ≤ geometricDiscount s 2 := by
    unfold geometricDiscount
    rw [← hr_sq_eq]
    nlinarith
  have hD_le_H :
      (geometricDiscount s 2)⁻¹ ≤ (1 - r)⁻¹ :=
    (inv_le_inv₀ hdenD_pos hdenH_pos).2 hden_order
  have hH_nonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr hdenH_pos.le
  have hprod :
      (geometricDiscount s 2)⁻¹ * (1 - r)⁻¹ ≤
        ((1 - r)⁻¹) ^ 2 := by
    calc
      (geometricDiscount s 2)⁻¹ * (1 - r)⁻¹ ≤
          (1 - r)⁻¹ * (1 - r)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hD_le_H hH_nonneg
      _ = ((1 - r)⁻¹) ^ 2 := by ring
  have hHsq :
      ((1 - r)⁻¹) ^ 2 ≤ ((3 / 2) * s⁻¹) ^ 2 :=
    pow_le_pow_left₀ hH_nonneg hH_le 2
  have hconst :
      ((3 / 2) * s⁻¹) ^ 2 ≤ (5 / 2) * (s⁻¹) ^ 2 := by
    nlinarith [sq_nonneg (s⁻¹)]
  calc
    (geometricDiscount s 2)⁻¹ * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ =
        (geometricDiscount s 2)⁻¹ * (1 - r)⁻¹ := by rfl
    _ ≤ ((1 - r)⁻¹) ^ 2 := hprod
    _ ≤ ((3 / 2) * s⁻¹) ^ 2 := hHsq
    _ ≤ (5 / 2) * (s⁻¹) ^ 2 := hconst

/-- The force-scale corrector-energy base fits in the displayed corrector
allocation after summing the weak-flux geometric tail. -/
theorem weakFluxRHSCorrectorEnergyForceScale_mul_inv_one_sub_step_le_noteForceScale
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (1000 * (geometricDiscount s 2)⁻¹ * (s⁻¹) ^ 2 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      2500 * (s⁻¹) ^ 4 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let D : ℝ := (geometricDiscount s 2)⁻¹
  let H : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let LamQ : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let F : ℝ := 1000 * (s⁻¹) ^ 2 * LamQ * L * N ^ 2 * G ^ 2
  have hDH : D * H ≤ (5 / 2) * (s⁻¹) ^ 2 := by
    simpa [D, H] using
      inv_geometricDiscount_two_mul_inv_one_sub_step_le_five_halves_inv_sq
        hs hs_le
  have hLamQ_nonneg : 0 ≤ LamQ := by
    dsimp [LamQ]
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ)))
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    positivity
  have hscaled := mul_le_mul_of_nonneg_right hDH hF_nonneg
  calc
    (1000 * (geometricDiscount s 2)⁻¹ * (s⁻¹) ^ 2 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹
        =
      (D * H) * F := by
        dsimp [D, H, F, LamQ, L, N, G]
        ring
    _ ≤ ((5 / 2) * (s⁻¹) ^ 2) * F := hscaled
    _ =
      2500 * (s⁻¹) ^ 4 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
        dsimp [F, LamQ, L, N, G]
        ring

/--
Depth-weighted averaged control of the corrector-energy component in the
corrected weak-flux RHS recurrence.

The proof combines:
* half-scale localization of the weak-flux local coefficient,
* half-scale localization of the descendant `lambda^{-1}` factor,
* the local Neumann-corrector energy force-scale estimate for each selected
  descendant corrector, and
* the global positive-Besov descendant averaging bound.
-/
theorem weakFluxRHSDepthWeight_mul_correctorEnergyErrorAverage_le_forceScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) {s lam Lam : ℝ} (n : ℕ)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (z : TriadicCube d → Vec d → Vec d)
    (hz :
      ∀ R ∈ descendantsAtDepth Q n,
        ∃ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          z R = (fun x => ω.toH1MeanZero.toH1Function.grad x)) :
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n ≤
      1000 * (geometricDiscount s 2)⁻¹ * (s⁻¹) ^ 2 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let D : ℝ := (geometricDiscount s 2)⁻¹
  let T : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  let LamQ : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let A : TriadicCube d → ℝ := fun R =>
    weakFluxRHSLocalCorrectorEnergyError R a (z R) s
  let GR : TriadicCube d → ℝ := fun R => cubeBesovPositiveVectorSeminormTwo R s g
  let C : ℝ := 1000 * D * (s⁻¹) ^ 2 * LamQ * L * N ^ 2 * T ^ 2
  have hs_half : 0 < s / 2 := by nlinarith
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hsum_B_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1) := by
    have hsum :
        Summable (fun m : ℕ =>
          geometricWeight (s / 2) 2 m *
            maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) :=
      summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) (s := s / 2) hs_half hEll hData
    simpa [Real.rpow_one] using hsum
  have hsum_lambda_half :
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
      ∀ R ∈ descendantsAtDepth Q n,
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤ T * L := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) :=
      mem_descendantsAtScale_of_mem_descendantsAtDepth hR
    have hloc :
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
          Real.rpow (3 : ℝ)
              (2 * (s / 2) *
                (Int.toNat (Q.scale - (Q.scale - (n : ℤ))) : ℝ)) *
            L := by
      simpa [L] using
        multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := Q.scale - (n : ℤ)) a (s / 2) 2
          (by nlinarith : 0 ≤ s / 2) (by norm_num) hRscale hsum_lambda_half
    have htoNat : Int.toNat (Q.scale - (Q.scale - (n : ℤ))) = n := by
      have hdiff : Q.scale - (Q.scale - (n : ℤ)) = (n : ℤ) := by
        omega
      rw [hdiff]
      simp
    have hloc' :
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
          Real.rpow (3 : ℝ) (2 * (s / 2) * (n : ℝ)) * L := by
      simpa [htoNat] using hloc
    simpa [T, show 2 * (s / 2) * (n : ℝ) = s * (n : ℝ) by ring] using hloc'
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hLamQ_nonneg :
      0 ≤ LamQ := by
    dsimp [LamQ]
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact inv_nonneg.mpr (le_of_lt (geometricDiscount_pos (by nlinarith : 0 < s * 2)))
  have hT_pos : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hT_nonneg : 0 ≤ T := hT_pos.le
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le d)
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (Real.sqrt_nonneg 2))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hlocalBdd :
      ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g) := by
    intro R hR
    exact cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
      s g hR hGlobalBdd
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q n,
        A R ≤ C * (GR R) ^ 2 := by
    intro R hR
    rcases hz R hR with ⟨ωR, hzR⟩
    let ER : ℝ :=
      cubeAverage R
        (coefficientEnergyDensity a (z R))
    have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
      hEll.mono (measurableSet_cubeSet R)
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hgR : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg
    have hcoeff :
        weakFluxRHSLocalCoeff R a s ≤ D * (T * LamQ) := by
      simpa [D, T, LamQ, mul_assoc] using
        weakFluxRHSLocalCoeff_le_parentHalfLambda_of_mem_descendantsAtDepth
          (Q := Q) (R := R) a hs hR hEllOpen hData hsum_B_half
    have hER_nonneg : 0 ≤ ER := by
      dsimp [ER]
      exact cubeAverage_nonneg_of_nonneg_on
        (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEllR
          (z R))
    have henergy_raw :
        ER ≤
          500 * (s⁻¹) ^ 2 *
            (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
            N ^ 2 * (GR R) ^ 2 := by
      dsimp [ER, N, GR]
      simpa [hzR, mul_assoc, mul_left_comm, mul_comm] using
        ωR.coefficientEnergy_average_le_force_scale_noteConstants_expanded
          (s := s) (lam := lam) (Lam := Lam)
          hs hs_le hEllR hgR (hlocalBdd R hR)
    have hforce_factor_nonneg :
        0 ≤ 500 * (s⁻¹) ^ 2 * N ^ 2 * (GR R) ^ 2 := by
      positivity
    have henergy :
        ER ≤
          500 * (s⁻¹) ^ 2 * (T * L) * N ^ 2 * (GR R) ^ 2 := by
      calc
        ER ≤
            500 * (s⁻¹) ^ 2 *
              (lambdaSq R (s / 2) (.finite 2) a)⁻¹ *
              N ^ 2 * (GR R) ^ 2 := henergy_raw
        _ =
            (500 * (s⁻¹) ^ 2 * N ^ 2 * (GR R) ^ 2) *
              (lambdaSq R (s / 2) (.finite 2) a)⁻¹ := by ring
        _ ≤
            (500 * (s⁻¹) ^ 2 * N ^ 2 * (GR R) ^ 2) * (T * L) := by
              exact mul_le_mul_of_nonneg_left (hlocal_lambda R hR)
                hforce_factor_nonneg
        _ =
            500 * (s⁻¹) ^ 2 * (T * L) * N ^ 2 * (GR R) ^ 2 := by ring
    have hcoeff_nonneg :
        0 ≤ 2 * (D * (T * LamQ)) := by positivity
    calc
      A R =
          2 * weakFluxRHSLocalCoeff R a s * ER := by
            dsimp [A, ER]
            rfl
      _ ≤
          2 * (D * (T * LamQ)) * ER := by
            have hscaled :=
              mul_le_mul_of_nonneg_right hcoeff hER_nonneg
            nlinarith
      _ ≤
          2 * (D * (T * LamQ)) *
            (500 * (s⁻¹) ^ 2 * (T * L) * N ^ 2 * (GR R) ^ 2) := by
            exact mul_le_mul_of_nonneg_left henergy hcoeff_nonneg
      _ = C * (GR R) ^ 2 := by
            dsimp [C]
            ring
  have hlocal_avg :
      weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n ≤
        C * descendantsAverage Q n (fun R => (GR R) ^ 2) := by
    calc
      weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n =
        descendantsAverage Q n A := by
          unfold weakFluxRHSLocalCorrectorEnergyErrorAverage
          rfl
      _ ≤ descendantsAverage Q n (fun R => C * (GR R) ^ 2) := by
          exact descendantsAverage_le_descendantsAverage Q n hpoint
      _ = C * descendantsAverage Q n (fun R => (GR R) ^ 2) := by
          exact descendantsAverage_smul Q n C _
  have hforce_avg :
      descendantsAverage Q n (fun R => (GR R) ^ 2) ≤
        coarsePoincareRHSGlobalForceBound Q g s n := by
    simpa [GR] using
      descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_global_scaled
        Q g s n hGlobalBdd hlocalBdd
  have hunweighted :
      weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n ≤
        1000 * D * (s⁻¹) ^ 2 * LamQ * L * N ^ 2 * G ^ 2 := by
    have hstep := hlocal_avg.trans
      (mul_le_mul_of_nonneg_left hforce_avg hC_nonneg)
    have hT_sq_ne : T ^ 2 ≠ 0 := by positivity
    have hcancel : T ^ 2 * (T ^ 2)⁻¹ = 1 := by
      exact mul_inv_cancel₀ hT_sq_ne
    calc
      weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n
          ≤ C * coarsePoincareRHSGlobalForceBound Q g s n := hstep
      _ =
          (1000 * D * (s⁻¹) ^ 2 * LamQ * L * N ^ 2) *
            (T ^ 2 * (T ^ 2)⁻¹) * G ^ 2 := by
            dsimp [C, G, T, coarsePoincareRHSGlobalForceBound]
            ring
      _ =
          1000 * D * (s⁻¹) ^ 2 * LamQ * L * N ^ 2 * G ^ 2 := by
            rw [hcancel]
            ring
  have herror_nonneg :
      0 ≤ weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n := by
    unfold weakFluxRHSLocalCorrectorEnergyErrorAverage
    exact descendantsAverage_nonneg Q n _ fun R hR => by
      unfold weakFluxRHSLocalCorrectorEnergyError
      have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
        hEll.mono (measurableSet_cubeSet R)
          (cubeSet_subset_of_mem_descendantsAtDepth hR)
      exact mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
          (weakFluxRHSLocalCoeff_nonneg R a hs))
        (cubeAverage_nonneg_of_nonneg_on
          (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEllR
            (z R)))
  have hW_le_one : coarsePoincareRHSDepthWeight s n ≤ 1 := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3)
      (by nlinarith [mul_nonneg hs.le (by positivity : 0 ≤ (n : ℝ))])
  calc
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n
        ≤
      1 *
        weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n := by
        exact mul_le_mul_of_nonneg_right hW_le_one herror_nonneg
    _ ≤ 1000 * D * (s⁻¹) ^ 2 * LamQ * L * N ^ 2 * G ^ 2 := by
        simpa using hunweighted
    _ =
      1000 * (geometricDiscount s 2)⁻¹ * (s⁻¹) ^ 2 *
        LambdaSq Q (s / 2) (.finite 2) a *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
        dsimp [D, LamQ, L, N, G]

end

end Homogenization
