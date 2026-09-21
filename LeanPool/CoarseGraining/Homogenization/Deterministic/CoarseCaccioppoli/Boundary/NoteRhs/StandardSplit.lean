/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Boundary.NoteRhs.Basic
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.RadiusIteration

/-! # Standard Split -/

namespace Homogenization

noncomputable section

open scoped BigOperators

noncomputable def coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross : ℝ) : ℝ :=
  if LambdaSq Q s (.finite 1) a = 0 then
    0
  else
    let σ : ℝ := coarseCaccioppoliSigma s t
    let p : ℝ := 2 + 4 * s / σ
    let K : ℝ :=
      Real.rpow s (-2 * s / σ) *
        Real.rpow (ThetaRatio Q s t a) (s / σ) *
          LambdaSq Q s (.finite 1) a
    let A : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
        Q a s t Calpha Ccross
    σ * Real.rpow (max (A / K) 0 + 1) p⁻¹

theorem
    coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit_eq_zero_of_LambdaSq_eq_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross : ℝ)
    (hΛ : LambdaSq Q s (.finite 1) a = 0) :
    coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
      Q a s t Calpha Ccross = 0 := by
  unfold coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit
    coarseCaccioppoliBoundaryRecursionCoeffSplit
  simp [hΛ]

theorem
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_nonneg_of_thetaRatio_pos
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 0 < ThetaRatio Q s t a) :
    0 ≤ coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
      Q a s t Calpha Ccross := by
  unfold coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
  by_cases hΛ : LambdaSq Q s (.finite 1) a = 0
  · rw [if_pos hΛ]
  · rw [if_neg hΛ]
    let σ : ℝ := coarseCaccioppoliSigma s t
    let p : ℝ := 2 + 4 * s / σ
    let K : ℝ :=
      Real.rpow s (-2 * s / σ) *
        Real.rpow (ThetaRatio Q s t a) (s / σ) *
          LambdaSq Q s (.finite 1) a
    let A : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
        Q a s t Calpha Ccross
    have hΛ_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
      multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
    have hΛ_pos : 0 < LambdaSq Q s (.finite 1) a :=
      lt_of_le_of_ne' hΛ_nonneg hΛ
    have hσ_pos : 0 < σ := by
      dsimp [σ]
      exact coarseCaccioppoli_sigma_pos hst
    have hK_pos : 0 < K := by
      have hs_factor_pos :
          0 < Real.rpow s (-2 * s / σ) :=
        Real.rpow_pos_of_pos hs _
      have hTheta_factor_pos :
          0 < Real.rpow (ThetaRatio Q s t a) (s / σ) :=
        Real.rpow_pos_of_pos hTheta _
      dsimp [K]
      positivity
    have hX_nonneg : 0 ≤ max (A / K) 0 + 1 := by
      linarith [le_max_right (A / K) 0]
    simpa [σ, p, K, A] using
      mul_nonneg hσ_pos.le (Real.rpow_nonneg hX_nonneg p⁻¹)

private theorem coarseCaccioppoliBoundaryNoteKernelFactor_ge_one {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 1 ≤ ThetaRatio Q s t a) :
    1 ≤
      Real.rpow s (-2 * s / coarseCaccioppoliSigma s t) *
        Real.rpow (ThetaRatio Q s t a)
          (s / coarseCaccioppoliSigma s t) := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hs_le_one : s ≤ 1 := by
    linarith
  have hexp_s_nonpos : -2 * s / coarseCaccioppoliSigma s t ≤ 0 := by
    have hnum_nonpos : -2 * s ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hσ_pos.le
  have hs_factor :
      1 ≤ Real.rpow s (-2 * s / coarseCaccioppoliSigma s t) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs_le_one hexp_s_nonpos
  have hexp_theta_nonneg :
      0 ≤ s / coarseCaccioppoliSigma s t :=
    div_nonneg hs.le hσ_pos.le
  have htheta_factor :
      1 ≤ Real.rpow (ThetaRatio Q s t a)
        (s / coarseCaccioppoliSigma s t) :=
    Real.one_le_rpow hTheta hexp_theta_nonneg
  nlinarith [mul_le_mul hs_factor htheta_factor zero_le_one
    (le_trans zero_le_one hs_factor)]

private theorem coarseCaccioppoliBoundaryHeightFirstTerm_div_kernel_le {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 1 ≤ ThetaRatio Q s t a) :
    ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) * LambdaSq Q s (.finite 1) a) /
        (Real.rpow s (-2 * s / coarseCaccioppoliSigma s t) *
          Real.rpow (ThetaRatio Q s t a)
            (s / coarseCaccioppoliSigma s t) *
            LambdaSq Q s (.finite 1) a) ≤
      (6561 : ℝ) * 6561 * C ^ (2 : ℕ) := by
  let D : ℝ :=
    Real.rpow s (-2 * s / coarseCaccioppoliSigma s t) *
      Real.rpow (ThetaRatio Q s t a)
        (s / coarseCaccioppoliSigma s t)
  let Λ : ℝ := LambdaSq Q s (.finite 1) a
  have hD_ge_one : 1 ≤ D := by
    dsimp [D]
    exact coarseCaccioppoliBoundaryNoteKernelFactor_ge_one
      Q a s t hs ht hst hTheta
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD_ge_one
  have hconst_nonneg :
      0 ≤ (6561 : ℝ) * 6561 * C ^ (2 : ℕ) := by positivity
  by_cases hΛ_zero : Λ = 0
  · simp [Λ, hΛ_zero, hconst_nonneg]
  · have hΛ_nonneg : 0 ≤ Λ := by
      dsimp [Λ]
      exact multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
    have hΛ_pos : 0 < Λ := lt_of_le_of_ne' hΛ_nonneg hΛ_zero
    change
      ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) * Λ) / (D * Λ) ≤
        (6561 : ℝ) * 6561 * C ^ (2 : ℕ)
    calc
      ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) * Λ) / (D * Λ)
          = ((6561 : ℝ) * 6561 * C ^ (2 : ℕ)) / D := by
            field_simp [hD_pos.ne', hΛ_pos.ne']
      _ ≤ (6561 : ℝ) * 6561 * C ^ (2 : ℕ) := by
            rw [div_le_iff₀ hD_pos]
            nlinarith

private theorem coarseCaccioppoliBoundaryRecursionCoeffSplit_div_kernel_eq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t Calpha Ccross : ℝ)
    (hCalpha : 0 < Calpha) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 0 < ThetaRatio Q s t a)
    (hΛ : 0 < LambdaSq Q s (.finite 1) a) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let q : ℝ := coarseCaccioppoliPower s t
    coarseCaccioppoliBoundaryRecursionCoeffSplit Q a s t Calpha Ccross /
        (Real.rpow s (-2 * s / σ) *
          Real.rpow (ThetaRatio Q s t a) (s / σ) *
            LambdaSq Q s (.finite 1) a) =
      Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q) := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let q : ℝ := coarseCaccioppoliPower s t
  let Θ : ℝ := ThetaRatio Q s t a
  let Λ : ℝ := LambdaSq Q s (.finite 1) a
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact coarseCaccioppoli_sigma_pos hst
  have hs1_pos : 0 < 1 - s := by
    linarith
  have hden_pos : 0 < s * (1 - s) := mul_pos hs hs1_pos
  have hTheta_half_nonneg : 0 ≤ Real.rpow Θ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hTheta.le _
  have hCdiv_nonneg : 0 ≤ Calpha / (s * (1 - s)) :=
    div_nonneg hCalpha.le hden_pos.le
  have hhalf_q : (1 / 2 : ℝ) * q = s / σ := by
    dsimp [q, σ, coarseCaccioppoliPower]
    field_simp [hσ_pos.ne']
  have hneg_q : -2 * s / σ = -q := by
    dsimp [q, σ, coarseCaccioppoliPower]
    ring
  have htheta_pow :
      Real.rpow (Real.rpow Θ (1 / 2 : ℝ)) q =
        Real.rpow Θ (s / σ) := by
    calc
      Real.rpow (Real.rpow Θ (1 / 2 : ℝ)) q =
          Real.rpow Θ ((1 / 2 : ℝ) * q) :=
        (Real.rpow_mul hTheta.le (1 / 2 : ℝ) q).symm
      _ = Real.rpow Θ (s / σ) := by rw [hhalf_q]
  have hCdiv_pow :
      Real.rpow (Calpha / (s * (1 - s))) q =
        Real.rpow Calpha q / Real.rpow (s * (1 - s)) q :=
    Real.div_rpow hCalpha.le hden_pos.le q
  have hsden_pow :
      Real.rpow (s * (1 - s)) q =
        Real.rpow s q * Real.rpow (1 - s) q :=
    Real.mul_rpow hs.le hs1_pos.le
  have hspow_neg :
      Real.rpow s (-2 * s / σ) = (Real.rpow s q)⁻¹ := by
    rw [hneg_q]
    exact Real.rpow_neg hs.le q
  have hbase_pow :
      Real.rpow (Calpha / (s * (1 - s)) * Real.rpow Θ (1 / 2 : ℝ)) q =
        Real.rpow (Calpha / (s * (1 - s))) q *
          Real.rpow (Real.rpow Θ (1 / 2 : ℝ)) q :=
    Real.mul_rpow hCdiv_nonneg hTheta_half_nonneg
  have hs1pow_neg :
      Real.rpow (1 - s) (-q) = (Real.rpow (1 - s) q)⁻¹ :=
    Real.rpow_neg hs1_pos.le q
  change
    (Ccross *
        Real.rpow (Calpha / (s * (1 - s)) * Real.rpow Θ (1 / 2 : ℝ)) q * Λ) /
        (Real.rpow s (-2 * s / σ) * Real.rpow Θ (s / σ) * Λ) =
      Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
  rw [hbase_pow, hCdiv_pow,
    hsden_pow, htheta_pow, hspow_neg, hs1pow_neg]
  have hThetaPow_div_ne : Real.rpow Θ (s / σ) ≠ 0 :=
    (Real.rpow_pos_of_pos hTheta (s / σ)).ne'
  have hThetaPow_mul_ne : Real.rpow Θ (s * σ⁻¹) ≠ 0 :=
    (Real.rpow_pos_of_pos hTheta (s * σ⁻¹)).ne'
  have hΛ_ne : Λ ≠ 0 := by
    dsimp [Λ]
    exact hΛ.ne'
  field_simp [(Real.rpow_pos_of_pos hs q).ne',
    (Real.rpow_pos_of_pos hs1_pos q).ne',
    hThetaPow_div_ne, hThetaPow_mul_ne, hΛ_ne]

private theorem coarseCaccioppoliBoundaryHeightSecondTermSplit_div_kernel_le {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t Calpha Ccross : ℝ)
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 1 ≤ ThetaRatio Q s t a) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let q : ℝ := coarseCaccioppoliPower s t
    let K : ℝ :=
      Real.rpow s (-2 * s / σ) *
        Real.rpow (ThetaRatio Q s t a) (s / σ) *
          LambdaSq Q s (.finite 1) a
    ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
        Ccross * coarseCaccioppoliBoundaryRecursionCoeffSplit
          Q a s t Calpha Ccross / K ≤
      ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
        Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q) := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let q : ℝ := coarseCaccioppoliPower s t
  let K : ℝ :=
    Real.rpow s (-2 * s / σ) *
      Real.rpow (ThetaRatio Q s t a) (s / σ) *
        LambdaSq Q s (.finite 1) a
  let L : ℝ := (9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q
  have hTheta_pos : 0 < ThetaRatio Q s t a := lt_of_lt_of_le zero_lt_one hTheta
  have hs1_pos : 0 < 1 - s := by linarith
  have hRhs_nonneg :
      0 ≤ L * Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q) := by
    dsimp [L]
    positivity
  change
    L * Ccross * coarseCaccioppoliBoundaryRecursionCoeffSplit
        Q a s t Calpha Ccross / K ≤
      L * Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
  by_cases hCcross_zero : Ccross = 0
  · simp [coarseCaccioppoliBoundaryRecursionCoeffSplit, hCcross_zero]
  · by_cases hΛ_zero : LambdaSq Q s (.finite 1) a = 0
    · have hleft_zero :
          L * Ccross * coarseCaccioppoliBoundaryRecursionCoeffSplit
              Q a s t Calpha Ccross / K = 0 := by
        simp [K, L, coarseCaccioppoliBoundaryRecursionCoeffSplit, hΛ_zero]
      rw [hleft_zero]
      exact hRhs_nonneg
    · have hΛ_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
        multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
      have hΛ_pos : 0 < LambdaSq Q s (.finite 1) a :=
        lt_of_le_of_ne' hΛ_nonneg hΛ_zero
      have hK_pos : 0 < K := by
        dsimp [K]
        positivity
      have hrec :
          coarseCaccioppoliBoundaryRecursionCoeffSplit
              Q a s t Calpha Ccross / K =
            Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q) := by
        simpa [σ, q, K] using
          coarseCaccioppoliBoundaryRecursionCoeffSplit_div_kernel_eq
            Q a s t Calpha Ccross hCalpha hs ht hst hTheta_pos hΛ_pos
      have hleft_eq :
          L * Ccross * coarseCaccioppoliBoundaryRecursionCoeffSplit
              Q a s t Calpha Ccross / K =
            L * Ccross * Ccross * Real.rpow Calpha q *
              Real.rpow (1 - s) (-q) := by
        calc
          L * Ccross * coarseCaccioppoliBoundaryRecursionCoeffSplit
              Q a s t Calpha Ccross / K
              = L * Ccross *
                  (coarseCaccioppoliBoundaryRecursionCoeffSplit
                    Q a s t Calpha Ccross / K) := by
                field_simp [hK_pos.ne']
          _ = L * Ccross *
                (Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)) := by
                rw [hrec]
          _ = L * Ccross * Ccross * Real.rpow Calpha q *
                Real.rpow (1 - s) (-q) := by
                ring
      rw [hleft_eq]

theorem coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit_div_kernel_le_explicit
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross : ℝ)
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 1 ≤ ThetaRatio Q s t a) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let q : ℝ := coarseCaccioppoliPower s t
    let K : ℝ :=
      Real.rpow s (-2 * s / σ) *
        Real.rpow (ThetaRatio Q s t a) (s / σ) *
          LambdaSq Q s (.finite 1) a
    let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
    let B₁ : ℝ := (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)
    let B₂ : ℝ :=
      ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
        Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
    coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
        Q a s t Calpha Ccross / K ≤
      R * (B₁ + B₂) := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let q : ℝ := coarseCaccioppoliPower s t
  let Λ : ℝ := LambdaSq Q s (.finite 1) a
  let K : ℝ :=
    Real.rpow s (-2 * s / σ) *
      Real.rpow (ThetaRatio Q s t a) (s / σ) *
        Λ
  let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
  let L : ℝ := (9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q
  let first : ℝ := (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) * Λ
  let second : ℝ :=
    L * Ccross * coarseCaccioppoliBoundaryRecursionCoeffSplit
      Q a s t Calpha Ccross
  let B₁ : ℝ := (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)
  let B₂ : ℝ :=
    L * Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
  have hs1_pos : 0 < 1 - s := by linarith
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact
      coarseCaccioppoliStandardRadiusIterationConst_nonneg
        (coarseCaccioppoli_beta_nonneg hs hst)
  have hB_nonneg : 0 ≤ R * (B₁ + B₂) := by
    refine mul_nonneg hR_nonneg (add_nonneg ?_ ?_)
    · dsimp [B₁]
      positivity
    · dsimp [B₂, L]
      exact
        mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (by positivity : 0 ≤ (9 : ℝ))
                    (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
                  (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _))
                hCcross)
              hCcross)
            (Real.rpow_nonneg hCalpha.le _))
          (Real.rpow_nonneg hs1_pos.le _)
  unfold coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit
  change (R * (first + second)) / K ≤ R * (B₁ + B₂)
  by_cases hΛ_zero : Λ = 0
  · have hleft_zero : (R * (first + second)) / K = 0 := by
      simp [K, first, second, Λ, coarseCaccioppoliBoundaryRecursionCoeffSplit, hΛ_zero]
    rw [hleft_zero]
    exact hB_nonneg
  · have hΛ_nonneg : 0 ≤ Λ := by
      dsimp [Λ]
      exact multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
    have hΛ_pos : 0 < Λ := lt_of_le_of_ne' hΛ_nonneg hΛ_zero
    have hTheta_pos : 0 < ThetaRatio Q s t a := lt_of_lt_of_le zero_lt_one hTheta
    have hK_pos : 0 < K := by
      dsimp [K]
      positivity
    have hfirst :
        first / K ≤ B₁ := by
      simpa [σ, Λ, K, first, B₁] using
        coarseCaccioppoliBoundaryHeightFirstTerm_div_kernel_le
          Q a s t Ccross hs ht hst hTheta
    have hsecond :
        second / K ≤ B₂ := by
      simpa [σ, q, Λ, K, L, second, B₂] using
        coarseCaccioppoliBoundaryHeightSecondTermSplit_div_kernel_le
          Q a s t Calpha Ccross hCalpha hCcross hs ht hst hTheta
    calc
      (R * (first + second)) / K
          = R * (first / K + second / K) := by
            field_simp [hK_pos.ne']
      _ ≤ R * (B₁ + B₂) :=
            mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hR_nonneg

/--
Scalar extraction lemma for the exposed explicit note constant.

Once the height coefficient divided by the note kernel is bounded by a scalar
`B`, the explicit note constant is bounded by the displayed note-scale root.
This is the coefficient-cancellation step needed before choosing a uniform
dimension-only public constant.
-/
theorem coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_le_of_heightCoeff_div_kernel_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross B Ctarget : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hB : 0 ≤ B)
    (hdiv :
      let σ : ℝ := coarseCaccioppoliSigma s t
      let K : ℝ :=
        Real.rpow s (-2 * s / σ) *
          Real.rpow (ThetaRatio Q s t a) (s / σ) *
            LambdaSq Q s (.finite 1) a
      let A : ℝ :=
        coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
          Q a s t Calpha Ccross
      A / K ≤ B)
    (hCtarget :
      let σ : ℝ := coarseCaccioppoliSigma s t
      let p : ℝ := 2 + 4 * s / σ
      σ * Real.rpow (B + 1) p⁻¹ ≤ Ctarget) :
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
      Q a s t Calpha Ccross ≤ Ctarget := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let p : ℝ := 2 + 4 * s / σ
  let K : ℝ :=
    Real.rpow s (-2 * s / σ) *
      Real.rpow (ThetaRatio Q s t a) (s / σ) *
        LambdaSq Q s (.finite 1) a
  let A : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
      Q a s t Calpha Ccross
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact coarseCaccioppoli_sigma_pos hst
  have hp_pos : 0 < p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_pos hs hst
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_pos.le
  have hB1_nonneg : 0 ≤ B + 1 := by linarith
  have hCtarget_nonneg : 0 ≤ Ctarget := by
    exact
      (mul_nonneg hσ_pos.le (Real.rpow_nonneg hB1_nonneg p⁻¹)).trans
        (by simpa [σ, p] using hCtarget)
  unfold coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
  by_cases hΛ : LambdaSq Q s (.finite 1) a = 0
  · rw [if_pos hΛ]
    exact hCtarget_nonneg
  · rw [if_neg hΛ]
    have hdiv' : A / K ≤ B := by
      simpa [σ, K, A] using hdiv
    have hmax_le : max (A / K) 0 ≤ B := max_le hdiv' hB
    have hX_le : max (A / K) 0 + 1 ≤ B + 1 := by
      linarith
    have hX_nonneg : 0 ≤ max (A / K) 0 + 1 := by
      linarith [le_max_right (A / K) 0]
    have hrpow_le :
        Real.rpow (max (A / K) 0 + 1) p⁻¹ ≤ Real.rpow (B + 1) p⁻¹ :=
      Real.rpow_le_rpow hX_nonneg hX_le hp_inv_nonneg
    exact
      (mul_le_mul_of_nonneg_left hrpow_le hσ_pos.le).trans
        (by simpa [σ, p, K, A] using hCtarget)

theorem coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_le_explicitBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross : ℝ)
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 1 ≤ ThetaRatio Q s t a) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let p : ℝ := 2 + 4 * s / σ
    let q : ℝ := coarseCaccioppoliPower s t
    let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
    let B₁ : ℝ := (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)
    let B₂ : ℝ :=
      ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
        Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
    let B : ℝ := R * (B₁ + B₂)
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q a s t Calpha Ccross ≤
      σ * Real.rpow (B + 1) p⁻¹ := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let p : ℝ := 2 + 4 * s / σ
  let q : ℝ := coarseCaccioppoliPower s t
  let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
  let B₁ : ℝ := (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)
  let B₂ : ℝ :=
    ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
      Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
  let B : ℝ := R * (B₁ + B₂)
  have hs1_pos : 0 < 1 - s := by linarith
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact
      coarseCaccioppoliStandardRadiusIterationConst_nonneg
        (coarseCaccioppoli_beta_nonneg hs hst)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg hR_nonneg (add_nonneg ?_ ?_)
    · dsimp [B₁]
      positivity
    · dsimp [B₂]
      exact
        mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (by positivity : 0 ≤ (9 : ℝ))
                    (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
                  (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _))
                hCcross)
              hCcross)
            (Real.rpow_nonneg hCalpha.le _))
          (Real.rpow_nonneg hs1_pos.le _)
  have hdiv :
      let σ : ℝ := coarseCaccioppoliSigma s t
      let K : ℝ :=
        Real.rpow s (-2 * s / σ) *
          Real.rpow (ThetaRatio Q s t a) (s / σ) *
            LambdaSq Q s (.finite 1) a
      let A : ℝ :=
        coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
          Q a s t Calpha Ccross
      A / K ≤ B := by
    simpa [σ, q, R, B₁, B₂, B] using
      coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit_div_kernel_le_explicit
        Q a s t Calpha Ccross hCalpha hCcross hs ht hst hTheta
  have htarget :
      let σ : ℝ := coarseCaccioppoliSigma s t
      let p : ℝ := 2 + 4 * s / σ
      σ * Real.rpow (B + 1) p⁻¹ ≤ σ * Real.rpow (B + 1) p⁻¹ := by
    simp
  simpa [σ, p, q, R, B₁, B₂, B] using
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_le_of_heightCoeff_div_kernel_le
      Q a s t Calpha Ccross B (σ * Real.rpow (B + 1) p⁻¹)
      hs ht hst hB_nonneg hdiv htarget

theorem
    coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit_le_noteCoeff_standardExplicitNoteConstantSplit
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hTheta : 0 < ThetaRatio Q s t a) :
    coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
        Q a s t Calpha Ccross ≤
      coarseCaccioppoliBoundaryNoteCoeff Q a s t
        (coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
          Q a s t Calpha Ccross) := by
  have hΛ_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  unfold coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
  by_cases hΛ : LambdaSq Q s (.finite 1) a = 0
  · rw [if_pos hΛ]
    rw [coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit_eq_zero_of_LambdaSq_eq_zero
      Q a s t Calpha Ccross hΛ]
    exact coarseCaccioppoliBoundaryNoteCoeff_nonneg Q a s t 0
      (by norm_num) hs ht hst
  · rw [if_neg hΛ]
    let σ : ℝ := coarseCaccioppoliSigma s t
    let p : ℝ := 2 + 4 * s / σ
    let K : ℝ :=
      Real.rpow s (-2 * s / σ) *
        Real.rpow (ThetaRatio Q s t a) (s / σ) *
          LambdaSq Q s (.finite 1) a
    let A : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
        Q a s t Calpha Ccross
    have hΛ_pos : 0 < LambdaSq Q s (.finite 1) a :=
      lt_of_le_of_ne' hΛ_nonneg hΛ
    have hσ_pos : 0 < σ := by
      dsimp [σ]
      exact coarseCaccioppoli_sigma_pos hst
    have hp_pos : 0 < p := by
      have hdiv_nonneg : 0 ≤ 4 * s / σ := by positivity
      dsimp [p]
      linarith
    have hK_pos : 0 < K := by
      have hs_factor_pos :
          0 < Real.rpow s (-2 * s / σ) :=
        Real.rpow_pos_of_pos hs _
      have hTheta_factor_pos :
          0 < Real.rpow (ThetaRatio Q s t a) (s / σ) :=
        Real.rpow_pos_of_pos hTheta _
      dsimp [K]
      positivity
    let X : ℝ := max (A / K) 0 + 1
    let Cnote : ℝ := σ * Real.rpow X p⁻¹
    have hA_div_le_X : A / K ≤ X := by
      dsimp [X]
      linarith [le_max_left (A / K) 0]
    have hA_le_XK : A ≤ X * K := by
      have hmul := mul_le_mul_of_nonneg_right hA_div_le_X hK_pos.le
      have hdiv_mul : A / K * K = A := by
        field_simp [hK_pos.ne']
      simpa [hdiv_mul] using hmul
    have hX_pos : 0 < X := by
      dsimp [X]
      linarith [le_max_right (A / K) 0]
    have hCnote_div : Cnote / σ = Real.rpow X p⁻¹ := by
      dsimp [Cnote]
      field_simp [hσ_pos.ne']
    have hpow : Real.rpow (Cnote / σ) p = X := by
      rw [hCnote_div]
      simpa using (Real.rpow_inv_rpow hX_pos.le hp_pos.ne')
    have hnote :
        Real.rpow (Cnote / σ) p * K =
          coarseCaccioppoliBoundaryNoteCoeff Q a s t Cnote := by
      dsimp [K, p, σ]
      unfold coarseCaccioppoliBoundaryNoteCoeff
      simp [LambdaSq]
      ring_nf
    have hCnote_eq :
        σ * Real.rpow (max (A / K) 0 + 1) p⁻¹ = Cnote := by
      rfl
    have hmain :
        coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
            Q a s t Calpha Ccross ≤
          coarseCaccioppoliBoundaryNoteCoeff Q a s t Cnote := by
      calc
        coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
            Q a s t Calpha Ccross = A := rfl
        _ ≤ X * K := hA_le_XK
        _ = Real.rpow (Cnote / σ) p * K := by rw [hpow]
        _ = coarseCaccioppoliBoundaryNoteCoeff Q a s t Cnote := hnote
    change
      coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
          Q a s t Calpha Ccross ≤
        coarseCaccioppoliBoundaryNoteCoeff Q a s t
          (σ * Real.rpow (max (A / K) 0 + 1) p⁻¹)
    rw [hCnote_eq]
    exact hmain

/--
Standard split coefficient-level note-RHS comparison after the non-degenerate
multiscale factor `ThetaRatio` has been identified as positive.
-/
theorem
    coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit_le_noteRhs_standardExplicitNoteConstantSplit
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) (hTheta : 0 < ThetaRatio Q s t a) :
    coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit
        Q a s t Calpha Ccross uL2Sq ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t
        (coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
          Q a s t Calpha Ccross)
        uL2Sq := by
  rw [
    coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit_eq_coeff_mul_uL2Sq,
    coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq]
  exact mul_le_mul_of_nonneg_right
    (coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit_le_noteCoeff_standardExplicitNoteConstantSplit
      Q a s t Calpha Ccross hs ht hst hTheta)
    hu


end

end Homogenization
