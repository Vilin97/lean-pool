/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.Descendants

/-! # Scale Bounds -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem coarseBBlockNorm_le_inv_geometricWeight_sq_mul_LambdaSq_one_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    coarseBBlockNorm R a ≤
      (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
        LambdaSq Q s (.finite 1) a := by
  let w : ℝ := geometricWeight s 1 (Int.toNat (Q.scale - k))
  have hw_pos : 0 < w := by
    dsimp [w]
    exact geometricWeight_pos _ (by simpa using hs)
  have hw_ne : w ≠ 0 := hw_pos.ne'
  have hw_sq_inv_nonneg : 0 ≤ (w ^ 2)⁻¹ := by
    positivity
  have hweighted :=
    weighted_sqrt_coarseBBlockNorm_le_LambdaSq_one_rpow_half
      (Q := Q) (R := R) (k := k) a s hs.le hR hsum
  have hleft_nonneg :
      0 ≤ w * Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ) := by
    refine mul_nonneg (le_of_lt hw_pos) ?_
    exact Real.rpow_nonneg (coarseBBlockNorm_nonneg R a) _
  have hsq := pow_le_pow_left₀ hleft_nonneg hweighted 2
  calc
    coarseBBlockNorm R a = (w ^ 2)⁻¹ * (w ^ 2 * coarseBBlockNorm R a) := by
      field_simp [hw_ne]
    _ = (w ^ 2)⁻¹ * (w * Real.rpow (coarseBBlockNorm R a) (1 / 2 : ℝ)) ^ 2 := by
      rw [pow_two]
      ring_nf
      rw [sq_rpow_half_eq_self_of_nonneg (coarseBBlockNorm_nonneg R a)]
    _ ≤ (w ^ 2)⁻¹ * (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq hw_sq_inv_nonneg
    _ = (w ^ 2)⁻¹ * LambdaSq Q s (.finite 1) a := by
      rw [sq_rpow_half_eq_self_of_nonneg
        (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le)]
    _ = (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
          LambdaSq Q s (.finite 1) a := by
      simp [w]

theorem coarseSigmaStarInvBlockNorm_le_inv_geometricWeight_sq_mul_lambdaSq_one_inv_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (s : ℝ)
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseSigmaStarInvBlockNorm R a ≤
      (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
        (lambdaSq Q s (.finite 1) a)⁻¹ := by
  let w : ℝ := geometricWeight s 1 (Int.toNat (Q.scale - k))
  have hw_pos : 0 < w := by
    dsimp [w]
    exact geometricWeight_pos _ (by simpa using hs)
  have hw_ne : w ≠ 0 := hw_pos.ne'
  have hw_sq_inv_nonneg : 0 ≤ (w ^ 2)⁻¹ := by
    positivity
  have hweighted :=
    weighted_sqrt_coarseSigmaStarInvBlockNorm_le_lambdaSq_one_rpow_neg_half
      (Q := Q) (R := R) (k := k) a s hs.le hR hsum
  have hleft_nonneg :
      0 ≤ w * Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ) := by
    refine mul_nonneg (le_of_lt hw_pos) ?_
    exact Real.rpow_nonneg (coarseSigmaStarInvBlockNorm_nonneg R a) _
  have hsq := pow_le_pow_left₀ hleft_nonneg hweighted 2
  calc
    coarseSigmaStarInvBlockNorm R a =
        (w ^ 2)⁻¹ * (w ^ 2 * coarseSigmaStarInvBlockNorm R a) := by
      field_simp [hw_ne]
    _ = (w ^ 2)⁻¹ * (w * Real.rpow (coarseSigmaStarInvBlockNorm R a) (1 / 2 : ℝ)) ^ 2 := by
      rw [pow_two]
      ring_nf
      rw [sq_rpow_half_eq_self_of_nonneg (coarseSigmaStarInvBlockNorm_nonneg R a)]
    _ ≤ (w ^ 2)⁻¹ * (Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq hw_sq_inv_nonneg
    _ = (w ^ 2)⁻¹ * (lambdaSq Q s (.finite 1) a)⁻¹ := by
      rw [sq_rpow_neg_half_eq_inv_of_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg Q s a hs.le)]
    _ = (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
          (lambdaSq Q s (.finite 1) a)⁻¹ := by
      simp [w]

theorem maxDescendantBBlockNormAtScale_le_inv_geometricWeight_sq_mul_LambdaSq_one {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ))) :
    maxDescendantBBlockNormAtScale Q k a ≤
      (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
        LambdaSq Q s (.finite 1) a := by
  unfold maxDescendantBBlockNormAtScale finsetSsup
  have hne :
      ((fun R => coarseBBlockNorm R a) '' (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨coarseBBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact coarseBBlockNorm_le_inv_geometricWeight_sq_mul_LambdaSq_one_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s hs hR hsum

theorem maxDescendantSigmaStarInvNormAtScale_le_inv_geometricWeight_sq_mul_lambdaSq_one_inv
    {d : ℕ} (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    maxDescendantSigmaStarInvNormAtScale Q k a ≤
      (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
        (lambdaSq Q s (.finite 1) a)⁻¹ := by
  unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
  have hne :
      ((fun R => coarseSigmaStarInvBlockNorm R a) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨coarseSigmaStarInvBlockNorm R a, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact coarseSigmaStarInvBlockNorm_le_inv_geometricWeight_sq_mul_lambdaSq_one_inv_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a s hs hR hsum

theorem multiscale_ellipticity_q1_normalized_scale_bounds {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (s : ℝ)
    (hs : 0 < s)
    (hBsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    maxDescendantBBlockNormAtScale Q k a ≤
        (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
          LambdaSq Q s (.finite 1) a ∧
      finsetSsup (descendantsAtScale Q k) (fun R => LambdaSq R s (.finite 1) a) ≤
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          LambdaSq Q s (.finite 1) a ∧
      maxDescendantSigmaStarInvNormAtScale Q k a ≤
        (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
          (lambdaSq Q s (.finite 1) a)⁻¹ ∧
      finsetSsup (descendantsAtScale Q k) (fun R => (lambdaSq R s (.finite 1) a)⁻¹) ≤
        Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
          (lambdaSq Q s (.finite 1) a)⁻¹ := by
  refine ⟨?_, ?_⟩
  · exact maxDescendantBBlockNormAtScale_le_inv_geometricWeight_sq_mul_LambdaSq_one
      Q hk a s hs hBsum
  · refine ⟨?_, ?_⟩
    · exact multiscale_ellipticity_LambdaSq_one_descendantsAtScale_le
        Q hk a s hs.le hBsum
    · refine ⟨?_, ?_⟩
      · exact maxDescendantSigmaStarInvNormAtScale_le_inv_geometricWeight_sq_mul_lambdaSq_one_inv
          Q hk a s hs hSigmaSum
      · exact multiscale_ellipticity_lambdaSq_one_inv_descendantsAtScale_le
          Q hk a s hs.le hSigmaSum

theorem multiscale_ellipticity_q1_normalized_basic_properties_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {t s : ℝ} {lam Lam : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hBsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    coarseSigmaStarInvBlockNorm Q a ≤
        (lambdaSq Q s (.finite 1) a)⁻¹ ∧
      (lambdaSq Q s (.finite 1) a)⁻¹ ≤ (lambdaSq Q t (.finite 1) a)⁻¹ ∧
      coarseBBlockNorm Q a ≤
        LambdaSq Q s (.finite 1) a ∧
      LambdaSq Q s (.finite 1) a ≤ LambdaSq Q t (.finite 1) a ∧
      ∀ {k : ℤ}, k ≤ Q.scale →
        maxDescendantBBlockNormAtScale Q k a ≤
            (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
              LambdaSq Q s (.finite 1) a ∧
          finsetSsup (descendantsAtScale Q k) (fun R => LambdaSq R s (.finite 1) a) ≤
            Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
              LambdaSq Q s (.finite 1) a ∧
          maxDescendantSigmaStarInvNormAtScale Q k a ≤
            (geometricWeight s 1 (Int.toNat (Q.scale - k)) ^ 2)⁻¹ *
              (lambdaSq Q s (.finite 1) a)⁻¹ ∧
          finsetSsup (descendantsAtScale Q k) (fun R => (lambdaSq R s (.finite 1) a)⁻¹) ≤
            Real.rpow (3 : ℝ) (2 * s * (Int.toNat (Q.scale - k) : ℝ)) *
              (lambdaSq Q s (.finite 1) a)⁻¹ := by
  have hs : 0 < s := lt_trans ht hts
  have hBnonneg :
      ∀ n : ℕ,
        0 ≤ Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ) := by
    intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantBBlockNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hSigmaNonneg :
      ∀ n : ℕ,
        0 ≤ Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ) := by
    intro n
    refine Real.rpow_nonneg ?_ _
    exact maxDescendantSigmaStarInvNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2 : ℝ)) :=
    summable_geometricWeight_one_of_lt hBnonneg ht hts hBsum_t
  have hSigmaSum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_one_of_lt hSigmaNonneg ht hts hSigmaSum_t
  have hsigma0 :
      coarseSigmaStarInvBlockNorm Q a ≤
        (lambdaSq Q s (.finite 1) a)⁻¹ := by
    exact coarseSigmaStarInvBlockNorm_le_lambdaSq_one_inv_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hs hEll hData hSigmaSum_s
  have hmonoSigma :
      (lambdaSq Q s (.finite 1) a)⁻¹ ≤ (lambdaSq Q t (.finite 1) a)⁻¹ :=
    multiscale_ellipticity_lambdaSq_one_inv_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a ht hts hEll hData hSigmaSum_t
  have hb0 :
      coarseBBlockNorm Q a ≤
        LambdaSq Q s (.finite 1) a := by
    exact coarseBBlockNorm_le_LambdaSq_one_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a hs hEll hData hBsum_s
  have hmonoB :
      LambdaSq Q s (.finite 1) a ≤ LambdaSq Q t (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a ht hts hEll hData hBsum_t
  refine ⟨hsigma0, hmonoSigma, hb0, hmonoB, ?_⟩
  intro k hk
  exact multiscale_ellipticity_q1_normalized_scale_bounds Q hk a s hs hBsum_s hSigmaSum_s


end

end Homogenization
