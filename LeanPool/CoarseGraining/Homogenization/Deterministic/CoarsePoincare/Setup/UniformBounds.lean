/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.Conversions

/-! # Uniform Bounds -/

namespace Homogenization

noncomputable section

open scoped BigOperators


private theorem coarseBBlockNorm_le_uniform_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hData : OpenCubeDeterministicCoarseData R a) :
    coarseBBlockNorm R a ≤
      4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ 2 := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  let U := openCubeSet R
  let hOpenR : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet R
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hOpenR.isFiniteMeasure_restrict_volume
  have hvol : (MeasureTheory.volume U).toReal ≠ 0 := by
    simpa [U, volume_openCubeSet_toReal] using (cubeVolume_pos R).ne'
  have hlam_pos : 0 < lam := by
    exact (hEllOpen.2 (cubeCenter R) (by
      rw [← ball_cubeCenter_eq_openCubeSet]
      simpa [Metric.mem_ball] using cubeRadius_pos R)).1
  let B := bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)
  have hBpos : B.PosSemidef :=
    bCoarse_canonical_posSemidef_of_isSigmaCoarse (U := U) (a := a) hS hK hSigma hdet
  have hBquad :
      ∀ p : Vec d, vecDot p (matVecMul B p) ≤
        (2 * lam⁻¹ * Lam ^ 2) * vecNormSq p := by
    intro p
    have hresp :
        ResponseJ U p 0 a ≤ lam⁻¹ * Lam ^ 2 * vecNormSq p := by
      have hresp0 :=
        responseJ_le_plainUpperBound_of_isEllipticFieldOn
          (U := U) (a := a) hEllOpen hvol p (0 : Vec d)
      have hzero : vecNormSq (0 : Vec d) = 0 := by
        simp [vecNormSq, vecDot]
      simpa [hzero, mul_assoc] using hresp0
    have hformula :
        ResponseJ U p 0 a = (1 / 2 : ℝ) * vecDot p (matVecMul B p) := by
      simpa [B] using
        basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
          U a hS hK hSigma hdet p
    rw [hformula] at hresp
    nlinarith
  have hBnorm :
      matNorm B ≤ 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ 2 := by
    have hCnonneg : 0 ≤ 2 * lam⁻¹ * Lam ^ 2 := by
      positivity
    convert
      (matNorm_le_two_mul_card_mul_of_posSemidef_of_quadratic_le hBpos hCnonneg hBquad) using 1
    ring
  have hB_eq : B = bCoarse sigma sigmaStar kappa := by
    dsimp [B]
    rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
      eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
      eq_kappaCoarse_of_isKappaCoarse hS hK hdet]
  have hnorm_eq : coarseBBlockNorm R a = matNorm B := by
    unfold coarseBBlockNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a,
      coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix hA hS hK hSigma hdet,
      ← hB_eq]
  rw [hnorm_eq]
  exact hBnorm

private theorem coarseSigmaStarInvBlockNorm_le_uniform_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hData : OpenCubeDeterministicCoarseData R a) :
    coarseSigmaStarInvBlockNorm R a ≤
      4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  let U := openCubeSet R
  let hOpenR : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet R
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hOpenR.isFiniteMeasure_restrict_volume
  have hvol : (MeasureTheory.volume U).toReal ≠ 0 := by
    simpa [U, volume_openCubeSet_toReal] using (cubeVolume_pos R).ne'
  have hlam_pos : 0 < lam := by
    exact (hEllOpen.2 (cubeCenter R) (by
      rw [← ball_cubeCenter_eq_openCubeSet]
      simpa [Metric.mem_ball] using cubeRadius_pos R)).1
  let SInv := sigmaStarInvCoarse U a
  have hSInvPos : SInv.PosSemidef :=
    sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse (U := U) (a := a) hS
  have hSInvQuad :
      ∀ q : Vec d, vecDot q (matVecMul SInv q) ≤
        (2 * lam⁻¹) * vecNormSq q := by
    intro q
    have hresp :
        ResponseJ U 0 q a ≤ lam⁻¹ * vecNormSq q := by
      have hresp0 :=
        responseJ_le_plainUpperBound_of_isEllipticFieldOn
          (U := U) (a := a) hEllOpen hvol (0 : Vec d) q
      have hzero : vecNormSq (0 : Vec d) = 0 := by
        simp [vecNormSq, vecDot]
      simpa [hzero, mul_assoc] using hresp0
    have hformula :
        ResponseJ U 0 q a = (1 / 2 : ℝ) * vecDot q (matVecMul SInv q) := by
      have hInv :
          IsSigmaStarInvCoarse U a SInv := by
        exact isSigmaStarInvCoarse_sigmaStarInvCoarse
          ⟨sigmaStar⁻¹, isSigmaStarInvCoarse_of_isSigmaStarCoarse hS⟩
      simpa [SInv] using hInv.2 q
    rw [hformula] at hresp
    nlinarith
  have hSInvNorm :
      matNorm SInv ≤ 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ := by
    have hCnonneg : 0 ≤ 2 * lam⁻¹ := by
      positivity
    convert
      (matNorm_le_two_mul_card_mul_of_posSemidef_of_quadratic_le
        hSInvPos hCnonneg hSInvQuad) using 1
    ring
  have hcanonRsig : sigmaStar⁻¹ = SInv := by
    dsimp [SInv]
    symm
    rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
  have hnorm_eq : coarseSigmaStarInvBlockNorm R a = matNorm SInv := by
    unfold coarseSigmaStarInvBlockNorm SInv
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a,
      coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix hA hS hK hSigma hdet,
      hcanonRsig]
  rw [hnorm_eq]
  exact hSInvNorm

theorem maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (n : ℕ) :
    maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a ≤
      4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ 2 := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  unfold maxDescendantBBlockNormAtScale finsetSsup
  have hne :
      ((fun R => coarseBBlockNorm R a) ''
        (↑(descendantsAtScale Q (Q.scale - (n : ℤ))) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨coarseBBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtScale hk hR)
  have hEllOpenR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEllR.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  exact
    coarseBBlockNorm_le_uniform_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEllOpenR (hData _ hk R hR)

theorem maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (n : ℕ) :
    maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a ≤
      4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  have hne :
      ((fun R => coarseSigmaStarInvBlockNorm R a) ''
        (↑(descendantsAtScale Q (Q.scale - (n : ℤ))) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨coarseSigmaStarInvBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtScale hk hR)
  have hEllOpenR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEllR.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  exact
    coarseSigmaStarInvBlockNorm_le_uniform_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEllOpenR (hData _ hk R hR)

theorem maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (n : ℕ) :
    maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a ≤
      4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ 2 := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  unfold maxDescendantBBlockNormAtScale finsetSsup
  have hne :
      ((fun R => coarseBBlockNorm R a) ''
        (↑(descendantsAtScale Q (Q.scale - (n : ℤ))) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨coarseBBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  exact
    coarseBBlockNorm_le_uniform_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEllR (hData _ hk R hR)

theorem maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (n : ℕ) :
    maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a ≤
      4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  have hne :
      ((fun R => coarseSigmaStarInvBlockNorm R a) ''
        (↑(descendantsAtScale Q (Q.scale - (n : ℤ))) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨coarseSigmaStarInvBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  exact
    coarseSigmaStarInvBlockNorm_le_uniform_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEllR (hData _ hk R hR)

theorem summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ 2
  refine summable_geometricWeight_mul_of_nonneg_of_le
    (C := Real.rpow C (1 / 2 : ℝ)) (by simpa using hs) ?_ ?_
  · intro n
    exact Real.rpow_nonneg
      (maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a) _
  · intro n
    have hbound :
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a ≤ C :=
      maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) hEll hData n
    refine Real.rpow_le_rpow ?_ hbound ?_
    · exact maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
    · positivity

theorem summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹
  refine summable_geometricWeight_mul_of_nonneg_of_le
    (C := Real.rpow C (1 / 2 : ℝ)) (by simpa using hs) ?_ ?_
  · intro n
    exact Real.rpow_nonneg
      (maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a) _
  · intro n
    have hbound :
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a ≤ C :=
      maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) hEll hData n
    refine Real.rpow_le_rpow ?_ hbound ?_
    · exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
    · positivity

theorem
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ 2
  refine summable_geometricWeight_mul_of_nonneg_of_le
    (C := Real.rpow C (1 / 2 : ℝ)) (by simpa using hs) ?_ ?_
  · intro n
    exact Real.rpow_nonneg
      (maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a) _
  · intro n
    have hbound :
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a ≤ C :=
      maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) hEll hData n
    refine Real.rpow_le_rpow ?_ hbound ?_
    · exact maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
    · positivity

theorem
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹
  refine summable_geometricWeight_mul_of_nonneg_of_le
    (C := Real.rpow C (1 / 2 : ℝ)) (by simpa using hs) ?_ ?_
  · intro n
    exact Real.rpow_nonneg
      (maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a) _
  · intro n
    have hbound :
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a ≤ C :=
      maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) hEll hData n
    refine Real.rpow_le_rpow ?_ hbound ?_
    · exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
    · positivity

theorem summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ 2
  refine summable_geometricWeight_mul_of_nonneg_of_le (C := C) (by positivity) ?_ ?_
  · intro n
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  · intro n
    exact
      (maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) hEll hData n)

theorem summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  let C : ℝ := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹
  refine summable_geometricWeight_mul_of_nonneg_of_le (C := C) (by positivity) ?_ ?_
  · intro n
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  · intro n
    exact
      (maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) hEll hData n)

theorem
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)

theorem
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)

theorem
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)

theorem
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  exact
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)

theorem
    summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  exact
    summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem
    summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  exact
    summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)

theorem
    summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  exact
    summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem
    summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    Summable (fun n : ℕ =>
      geometricWeight s 2 n *
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  exact
    summable_qtwo_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) s hs hEll
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)

theorem cubeAverage_nonneg_of_nonneg_on {d : ℕ} {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : ∀ x ∈ cubeSet Q, 0 ≤ f x) :
    0 ≤ cubeAverage Q f := by
  unfold cubeAverage
  refine mul_nonneg ?_ ?_
  · exact inv_nonneg.mpr (le_of_lt (cubeVolume_pos Q))
  · apply MeasureTheory.integral_nonneg_of_ae
    exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
      Filter.Eventually.of_forall fun x hx => hf x hx

theorem volumeAverage_cubeSet_eq_cubeAverage {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = cubeAverage Q f := by
  calc
    volumeAverage (cubeSet Q) f
        = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume := by
            unfold volumeAverage
            rw [volume_cubeSet_toReal]
    _ = cubeAverage Q f := rfl

theorem cubeAverage_eq_of_eq_on_cubeSet {d : ℕ} {Q : TriadicCube d} {f g : Vec d → ℝ}
    (hfg : ∀ x ∈ cubeSet Q, f x = g x) :
    cubeAverage Q f = cubeAverage Q g := by
  unfold cubeAverage
  refine congrArg (fun t : ℝ => (cubeVolume Q)⁻¹ * t) ?_
  refine MeasureTheory.integral_congr_ae ?_
  exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
    Filter.Eventually.of_forall fun x hx => hfg x hx

theorem cubeAverageVec_eq_of_eq_on_cubeSet {d : ℕ} {Q : TriadicCube d}
    {f g : Vec d → Vec d} (hfg : ∀ x ∈ cubeSet Q, f x = g x) :
    cubeAverageVec Q f = cubeAverageVec Q g := by
  funext i
  exact cubeAverage_eq_of_eq_on_cubeSet fun x hx => congrArg (fun v => v i) (hfg x hx)


end

end Homogenization
