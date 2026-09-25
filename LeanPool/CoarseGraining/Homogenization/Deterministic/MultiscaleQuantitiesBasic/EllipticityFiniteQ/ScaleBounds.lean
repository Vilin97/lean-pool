/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.EllipticityFiniteQ.Descendants

/-! # Scale Bounds -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem multiscale_ellipticity_lambdaSq_two_inv_le_of_mem_descendantsAtScale_of_half_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : CoeffField d) {s : ℝ} {lam Lam : ℝ}
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) 1)) :
    (lambdaSq R s (.finite 2) a)⁻¹ ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
  have hhalf : 0 < s / 2 := by positivity
  have hlt : s / 2 < s := by linarith
  have hsum_half' :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (2 / 2)) := by
    simpa using hsum_half
  simpa using
    multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := Q) (R := R) (k := k) a (q := 2) (t := s / 2) (s := s)
      (lam := lam) (Lam := Lam) (by norm_num) hhalf hlt hR hEll hData hsum_half'

theorem multiscale_ellipticity_lambdaSq_two_inv_le_rpow_s_of_mem_descendantsAtScale_of_half_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : CoeffField d) {s : ℝ} {lam Lam : ℝ}
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) 1)) :
    (lambdaSq R s (.finite 2) a)⁻¹ ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
  have hhalf : 0 < s / 2 := by positivity
  have hlt : s / 2 < s := by linarith
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hEllR :
      IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    hData.of_mem_descendantsAtScale hk hR
  have hsum_half' :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)) := by
    simpa using hsum_half
  have hsumR_half :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale R (R.scale - (n : ℤ)) a)
            (2 / 2)) :=
    summable_geometricWeight_maxDescendantSigmaStarInvNormAtScale_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a (s / 2) 2 hhalf.le (by norm_num) hR hsum_half'
  have hmono :
      (lambdaSq R s (.finite 2) a)⁻¹ ≤ (lambdaSq R (s / 2) (.finite 2) a)⁻¹ :=
    multiscale_ellipticity_lambdaSq_finite_inv_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := R) a (q := 2) (t := s / 2) (s := s) (lam := lam) (Lam := Lam)
      (by norm_num) hhalf hlt hEllR hDataR hsumR_half
  have hloc :
      (lambdaSq R (s / 2) (.finite 2) a)⁻¹ ≤
        Real.rpow (3 : ℝ) (2 * (s / 2) * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a (s / 2) 2 hhalf.le (by norm_num) hR hsum_half'
  calc
    (lambdaSq R s (.finite 2) a)⁻¹ ≤
        (lambdaSq R (s / 2) (.finite 2) a)⁻¹ := hmono
    _ ≤ Real.rpow (3 : ℝ) (2 * (s / 2) * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := hloc
    _ = Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
        congr 2
        ring

/-- Half-scale upper-ellipticity localization for the finite-`q = 2`
multiscale coefficient. -/
theorem multiscale_ellipticity_LambdaSq_two_le_rpow_s_of_mem_descendantsAtScale_of_half_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : CoeffField d) {s : ℝ} {lam Lam : ℝ}
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) 1)) :
    LambdaSq R s (.finite 2) a ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        LambdaSq Q (s / 2) (.finite 2) a := by
  have hhalf : 0 < s / 2 := by positivity
  have hlt : s / 2 < s := by linarith
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hEllR :
      IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    IsEllipticFieldOn.mono hEll (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtScale hk hR)
  have hDataR : OpenCubeDescendantDeterministicCoarseData R a :=
    hData.of_mem_descendantsAtScale hk hR
  have hsum_half' :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (2 / 2)) := by
    simpa using hsum_half
  have hsumR_half :
      Summable (fun n : ℕ =>
        geometricWeight (s / 2) 2 n *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (2 / 2)) :=
    summable_geometricWeight_maxDescendantBBlockNormAtScale_rpow_q_div_two_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a (s / 2) 2 hhalf.le (by norm_num) hR hsum_half'
  have hmono :
      LambdaSq R s (.finite 2) a ≤ LambdaSq R (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := R) a (q := 2) (t := s / 2) (s := s) (lam := lam) (Lam := Lam)
      (by norm_num) hhalf hlt hEllR hDataR hsumR_half
  have hloc :
      LambdaSq R (s / 2) (.finite 2) a ≤
        Real.rpow (3 : ℝ) (2 * (s / 2) * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a (s / 2) 2 hhalf.le (by norm_num) hR hsum_half'
  calc
    LambdaSq R s (.finite 2) a ≤
        LambdaSq R (s / 2) (.finite 2) a := hmono
    _ ≤ Real.rpow (3 : ℝ) (2 * (s / 2) * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q (s / 2) (.finite 2) a := hloc
    _ = Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q (s / 2) (.finite 2) a := by
        congr 2
        ring

theorem multiscale_ellipticity_LambdaSq_finite_descendantsAtScale_le {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))) :
    finsetSsup (descendantsAtScale Q k) (fun R => LambdaSq R s (.finite q) a) ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        LambdaSq Q s (.finite q) a := by
  unfold finsetSsup
  have hne :
      ((fun R => LambdaSq R s (.finite q) a) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨LambdaSq R s (.finite q) a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact multiscale_ellipticity_LambdaSq_finite_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s q hs hq hR hsum

theorem multiscale_ellipticity_lambdaSq_finite_inv_descendantsAtScale_le {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    finsetSsup (descendantsAtScale Q k) (fun R => (lambdaSq R s (.finite q) a)⁻¹) ≤
      Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
        (lambdaSq Q s (.finite q) a)⁻¹ := by
  unfold finsetSsup
  have hne :
      ((fun R => (lambdaSq R s (.finite q) a)⁻¹) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨(lambdaSq R s (.finite q) a)⁻¹, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s q hs hq hR hsum

theorem multiscale_ellipticity_finite_scale_bounds {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s q : ℝ)
    (hs : 0 ≤ s) (hq : 0 < q)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    finsetSsup (descendantsAtScale Q k) (fun R => LambdaSq R s (.finite q) a) ≤
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q s (.finite q) a ∧
      finsetSsup (descendantsAtScale Q k) (fun R => (lambdaSq R s (.finite q) a)⁻¹) ≤
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q s (.finite q) a)⁻¹ := by
  refine ⟨?_, ?_⟩
  · exact multiscale_ellipticity_LambdaSq_finite_descendantsAtScale_le Q hk a s q hs hq hBsum
  · exact multiscale_ellipticity_lambdaSq_finite_inv_descendantsAtScale_le Q hk a s q hs hq hSigmaSum

theorem multiscale_ellipticity_finite_basic_properties_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s q : ℝ} {lam Lam : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hBsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2))) :
    ((lambdaSq Q s (.finite q) a)⁻¹ ≤ (lambdaSq Q t (.finite q) a)⁻¹) ∧
      (coarseSigmaStarInvBlockNorm Q a ≤ (lambdaSq Q s (.finite q) a)⁻¹) ∧
      (coarseBBlockNorm Q a ≤ LambdaSq Q s (.finite q) a) ∧
      (LambdaSq Q s (.finite q) a ≤ LambdaSq Q t (.finite q) a) ∧
      ∀ {k : ℤ}, k ≤ Q.scale →
        finsetSsup (descendantsAtScale Q k) (fun R => LambdaSq R s (.finite q) a) ≤
            Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
              LambdaSq Q s (.finite q) a ∧
          finsetSsup (descendantsAtScale Q k) (fun R => (lambdaSq R s (.finite q) a)⁻¹) ≤
            Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
              (lambdaSq Q s (.finite q) a)⁻¹ := by
  have hs : 0 < s := lt_trans ht hts
  have hBnonneg :
      ∀ n : ℕ,
        0 ≤ Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2) := by
    intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hSigmaNonneg :
      ∀ n : ℕ,
        0 ≤ Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2) := by
    intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)) :=
    summable_geometricWeight_of_lt hBnonneg hq ht hts hBsum_t
  have hSigmaSum_s :
      Summable (fun n : ℕ =>
        geometricWeight s q n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) :=
    summable_geometricWeight_of_lt hSigmaNonneg hq ht hts hSigmaSum_t
  refine ⟨?_, ?_, ?_, ?_, fun {k} hk => ?_⟩
  · exact multiscale_ellipticity_lambdaSq_finite_inv_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hq ht hts hEll hData hSigmaSum_t
  · exact coarseSigmaStarInvBlockNorm_le_lambdaSq_finite_inv_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hs hq hEll hData hSigmaSum_s
  · exact coarseBBlockNorm_le_LambdaSq_finite_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hs hq hEll hData hBsum_s
  · exact multiscale_ellipticity_LambdaSq_finite_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hq ht hts hEll hData hBsum_t
  exact multiscale_ellipticity_finite_scale_bounds Q hk a s q hs.le hq hBsum_s hSigmaSum_s

end

end Homogenization
