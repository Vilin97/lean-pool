/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompressionFinal

/-! # Entry Scale Compression -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Entry-scale compression for the quenched theorem

The shifted minimal-scale theorem controls the random scale measured from the
annealed entry scale.  This file supplies the deterministic estimate needed to
put the absolute factor `3 ^ N0` back into the manuscript envelope
`exp(C log^2(2 + thetaHat))`.
-/

noncomputable section

open Section51

theorem log_two_add_le_const_mul_log_two_add_of_le_const_mul_sq
    {A T θ : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T) (hθ : 0 ≤ θ)
    (hT_le : T ≤ A * θ ^ (2 : ℕ)) :
    Real.log (2 + T) ≤
      (2 + 2 * max 0 (Real.log (2 + A))) * Real.log (2 + θ) := by
  have hargT_pos : 0 < 2 + T := by positivity
  have hargA_pos : 0 < 2 + A := by positivity
  have hargθ_pos : 0 < 2 + θ := by positivity
  have htarget_pos : 0 < (2 + A) * (2 + θ) ^ (2 : ℕ) := by positivity
  have harg_le : 2 + T ≤ (2 + A) * (2 + θ) ^ (2 : ℕ) := by
    have hslack_nonneg :
        0 ≤ 6 + 8 * θ + 2 * θ ^ (2 : ℕ) + 4 * A + 4 * A * θ := by
      positivity
    calc
      2 + T ≤ 2 + A * θ ^ (2 : ℕ) := by
        simpa [add_comm] using add_le_add_left hT_le 2
      _ ≤
          2 + A * θ ^ (2 : ℕ) +
            (6 + 8 * θ + 2 * θ ^ (2 : ℕ) + 4 * A + 4 * A * θ) :=
        le_add_of_nonneg_right hslack_nonneg
      _ = (2 + A) * (2 + θ) ^ (2 : ℕ) := by ring
  have hlog_le :
      Real.log (2 + T) ≤
        Real.log ((2 + A) * (2 + θ) ^ (2 : ℕ)) :=
    Real.log_le_log hargT_pos harg_le
  have hprod_log :
      Real.log ((2 + A) * (2 + θ) ^ (2 : ℕ)) =
        Real.log (2 + A) + 2 * Real.log (2 + θ) := by
    rw [Real.log_mul hargA_pos.ne' (pow_pos hargθ_pos 2).ne']
    rw [show (2 + θ) ^ (2 : ℕ) = (2 + θ) * (2 + θ) by ring]
    rw [Real.log_mul hargθ_pos.ne' hargθ_pos.ne']
    ring
  have hL_half : (1 / 2 : ℝ) ≤ Real.log (2 + θ) :=
    Section51.log_two_add_ge_half hθ
  have hmax_nonneg : 0 ≤ max 0 (Real.log (2 + A)) :=
    le_max_left 0 _
  have hlogA_bound :
      Real.log (2 + A) ≤
        2 * max 0 (Real.log (2 + A)) * Real.log (2 + θ) := by
    have hlogA_le_max :
        Real.log (2 + A) ≤ max 0 (Real.log (2 + A)) :=
      le_max_right 0 _
    have hscaled :
        max 0 (Real.log (2 + A)) ≤
          2 * max 0 (Real.log (2 + A)) * Real.log (2 + θ) := by
      have hone_le : (1 : ℝ) ≤ 2 * Real.log (2 + θ) := by
        calc
          (1 : ℝ) = 2 * (1 / 2 : ℝ) := by norm_num
          _ ≤ 2 * Real.log (2 + θ) :=
            mul_le_mul_of_nonneg_left hL_half (by norm_num : 0 ≤ (2 : ℝ))
      calc
        max 0 (Real.log (2 + A))
            = max 0 (Real.log (2 + A)) * 1 := by ring
        _ ≤ max 0 (Real.log (2 + A)) * (2 * Real.log (2 + θ)) :=
          mul_le_mul_of_nonneg_left hone_le hmax_nonneg
        _ = 2 * max 0 (Real.log (2 + A)) * Real.log (2 + θ) := by ring
    exact hlogA_le_max.trans hscaled
  calc
    Real.log (2 + T)
        ≤ Real.log ((2 + A) * (2 + θ) ^ (2 : ℕ)) := hlog_le
    _ = Real.log (2 + A) + 2 * Real.log (2 + θ) := hprod_log
    _ ≤ 2 * max 0 (Real.log (2 + A)) * Real.log (2 + θ) +
          2 * Real.log (2 + θ) := by
          exact add_le_add hlogA_bound le_rfl
    _ = (2 + 2 * max 0 (Real.log (2 + A))) *
          Real.log (2 + θ) := by ring

/-- The annealed algebraic entry scale is bounded by a single manuscript
`ceil(C log^2(2 + thetaHat))` scale.

The constant is selected before the law; it depends only on the finite
`sigma`, the parameter-only `(P4)` data, and the entry constant used to define
`N0`. -/
theorem exists_entryScale_le_natCeil_logSq
    {d : ℕ} [NeZero d] {σ Centry : ℝ}
    (hσ : 0 < σ) (hCentry : 0 < Centry)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ CentryScale : ℝ, 0 < CentryScale ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        N0 ≤
          Nat.ceil (CentryScale *
            (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
  classical
  let xi : ℝ := (params.xi : ℝ)
  let G : ℝ := Ch04.gammaMomentConst σ * xi ^ σ⁻¹
  let A : ℝ := G ^ (2 : ℕ)
  let Clog₁ : ℝ := 2 + 2 * max 0 (Real.log (2 + A))
  let A₂ : ℝ := Centry * xi * A
  let Clog₂ : ℝ := 2 + 2 * max 0 (Real.log (2 + A₂))
  let Mcoef : ℝ :=
    Centry * Clog₁ ^ (2 : ℕ) + 2 * Centry * xi * Clog₂
  let Ncoef : ℝ := Mcoef + 8
  let CentryScale : ℝ := Ncoef
  have hxi_pos_nat : 0 < params.xi := params.xi_pos
  have hxi_pos : 0 < xi := by
    dsimp [xi]
    exact_mod_cast hxi_pos_nat
  have hgamma_pos : 0 < Ch04.gammaMomentConst σ := by
    simpa [Ch04.gammaMomentConst] using
      IndependentSums.gammaMomentConst_pos hσ
  have hG_pos : 0 < G := by
    dsimp [G]
    positivity
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hA₂_nonneg : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hClog₁_pos : 0 < Clog₁ := by
    dsimp [Clog₁]
    have hmax_nonneg : 0 ≤ max 0 (Real.log (2 + A)) := le_max_left 0 _
    have htwo_le : (2 : ℝ) ≤ 2 + 2 * max 0 (Real.log (2 + A)) :=
      le_add_of_nonneg_right (mul_nonneg (by norm_num) hmax_nonneg)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) htwo_le
  have hClog₂_pos : 0 < Clog₂ := by
    dsimp [Clog₂]
    have hmax_nonneg : 0 ≤ max 0 (Real.log (2 + A₂)) := le_max_left 0 _
    have htwo_le : (2 : ℝ) ≤ 2 + 2 * max 0 (Real.log (2 + A₂)) :=
      le_add_of_nonneg_right (mul_nonneg (by norm_num) hmax_nonneg)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) htwo_le
  have hNcoef_pos : 0 < Ncoef := by
    dsimp [Ncoef, Mcoef]
    positivity
  have hCentryScale_pos : 0 < CentryScale := by
    dsimp [CentryScale]
    exact hNcoef_pos
  refine ⟨CentryScale, hCentryScale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let T : ℝ := widetildeThetaAtScale P (0 : ℤ) hP4
  let θ : ℝ := hΓ.thetaHat
  let Lθ : ℝ := Real.log (2 + θ)
  let LT : ℝ := Real.log (2 + T)
  let L₂ : ℝ := Real.log (2 + Centry * xi * T)
  let N0 : ℕ := annealedAlgebraicEntryScale P hP4 Centry
  have hP4_xi : hP4.xi = params.xi := by
    dsimp [hP4,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
      GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos]
    simp [hparams]
  have hθ_pos : 0 < θ := by simpa [θ] using hΓ.thetaHat_pos
  have hθ_nonneg : 0 ≤ θ := hθ_pos.le
  have hT_nonneg : 0 ≤ T := by
    simpa [T, hP4] using
      Section51.widetildeThetaAtScale_nonneg P hP4 (0 : ℤ)
  have hwide := hΓ.widetildeThetaAtScale_zero_le_gammaMomentScale_sq
  have hT_le_Aθ :
      T ≤ A * θ ^ (2 : ℕ) := by
    have hraw :
        T ≤ (G * θ) ^ (2 : ℕ) := by
      simpa [T, θ, G, xi, hσ_eq, hparams] using hwide
    calc
      T ≤ (G * θ) ^ (2 : ℕ) := hraw
      _ = A * θ ^ (2 : ℕ) := by
          dsimp [A]
          ring
  have hLT_bound : LT ≤ Clog₁ * Lθ := by
    simpa [LT, Lθ] using
      log_two_add_le_const_mul_log_two_add_of_le_const_mul_sq
        (A := A) (T := T) (θ := θ) hA_nonneg hT_nonneg hθ_nonneg
        hT_le_Aθ
  have hT₂_nonneg : 0 ≤ Centry * xi * T := by positivity
  have hT₂_le : Centry * xi * T ≤ A₂ * θ ^ (2 : ℕ) := by
    calc
      Centry * xi * T
          ≤ Centry * xi * (A * θ ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hT_le_Aθ
              (mul_nonneg hCentry.le hxi_pos.le)
      _ = A₂ * θ ^ (2 : ℕ) := by
          dsimp [A₂]
          ring
  have hL₂_bound : L₂ ≤ Clog₂ * Lθ := by
    simpa [L₂, Lθ] using
      log_two_add_le_const_mul_log_two_add_of_le_const_mul_sq
        (A := A₂) (T := Centry * xi * T) (θ := θ)
        hA₂_nonneg hT₂_nonneg hθ_nonneg hT₂_le
  have hLθ_half : (1 / 2 : ℝ) ≤ Lθ := by
    simpa [Lθ] using Section51.log_two_add_ge_half hθ_nonneg
  have hLθ_nonneg : 0 ≤ Lθ := by linarith
  have hLT_nonneg : 0 ≤ LT := by
    dsimp [LT]
    exact Section51.log_two_add_nonneg hT_nonneg
  have hL₂_nonneg : 0 ≤ L₂ := by
    dsimp [L₂]
    exact Section51.log_two_add_nonneg hT₂_nonneg
  have hLT_sq :
      LT ^ (2 : ℕ) ≤ Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ) := by
    calc
      LT ^ (2 : ℕ) ≤ (Clog₁ * Lθ) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hLT_nonneg hLT_bound 2
      _ = Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ) := by ring
  have hL₂_linear :
      L₂ ≤ 2 * Clog₂ * Lθ ^ (2 : ℕ) := by
    have hLθ_le : Lθ ≤ 2 * Lθ ^ (2 : ℕ) := by
      simpa [Lθ] using log_two_add_le_two_mul_sq hθ_nonneg
    calc
      L₂ ≤ Clog₂ * Lθ := hL₂_bound
      _ ≤ Clog₂ * (2 * Lθ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hLθ_le hClog₂_pos.le
      _ = 2 * Clog₂ * Lθ ^ (2 : ℕ) := by ring
  have hceil₁ :
      (Nat.ceil (Centry * LT ^ (2 : ℕ)) : ℝ) ≤
        Centry * Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ) + 1 := by
    have hx_nonneg : 0 ≤ Centry * LT ^ (2 : ℕ) := by positivity
    have hceil :=
      Section51.natCeil_le_add_one (x := Centry * LT ^ (2 : ℕ))
        hx_nonneg
    have hmain :
        Centry * LT ^ (2 : ℕ) ≤
          Centry * Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ) := by
      calc
        Centry * LT ^ (2 : ℕ)
            ≤ Centry * (Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ)) :=
              mul_le_mul_of_nonneg_left hLT_sq hCentry.le
        _ = Centry * Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ) := by ring
    exact hceil.trans (by linarith)
  have hceil₂ :
      (Nat.ceil (Centry * xi * L₂) : ℝ) ≤
        2 * Centry * xi * Clog₂ * Lθ ^ (2 : ℕ) + 1 := by
    have hy_nonneg : 0 ≤ Centry * xi * L₂ := by positivity
    have hceil :=
      Section51.natCeil_le_add_one (x := Centry * xi * L₂) hy_nonneg
    have hmain :
        Centry * xi * L₂ ≤
          2 * Centry * xi * Clog₂ * Lθ ^ (2 : ℕ) := by
      calc
        Centry * xi * L₂
            ≤ Centry * xi * (2 * Clog₂ * Lθ ^ (2 : ℕ)) :=
              mul_le_mul_of_nonneg_left hL₂_linear
                (mul_nonneg hCentry.le hxi_pos.le)
        _ = 2 * Centry * xi * Clog₂ * Lθ ^ (2 : ℕ) := by ring
    exact hceil.trans (by linarith)
  have htwo :
      (2 : ℝ) ≤ 8 * Lθ ^ (2 : ℕ) := by
    have hquarter : (1 / 4 : ℝ) ≤ Lθ ^ (2 : ℕ) := by
      simpa [Lθ] using log_two_add_sq_ge_quarter hθ_nonneg
    have hscaled :=
      mul_le_mul_of_nonneg_left hquarter (by norm_num : 0 ≤ (8 : ℝ))
    norm_num at hscaled
    exact hscaled
  have hN_real : (N0 : ℝ) ≤ Ncoef * Lθ ^ (2 : ℕ) := by
    have hN_eq :
        N0 =
          Nat.ceil (Centry * LT ^ (2 : ℕ)) +
            Nat.ceil (Centry * xi * L₂) := by
      dsimp [N0, annealedAlgebraicEntryScale, T, LT, L₂, hP4, xi]
      rw [hP4_xi]
    calc
      (N0 : ℝ)
          = (Nat.ceil (Centry * LT ^ (2 : ℕ)) : ℝ) +
              (Nat.ceil (Centry * xi * L₂) : ℝ) := by
              rw [hN_eq]
              norm_num
      _ ≤
          (Centry * Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ) + 1) +
            (2 * Centry * xi * Clog₂ * Lθ ^ (2 : ℕ) + 1) := by
              exact add_le_add hceil₁ hceil₂
      _ ≤ Ncoef * Lθ ^ (2 : ℕ) := by
          calc
            (Centry * Clog₁ ^ (2 : ℕ) * Lθ ^ (2 : ℕ) + 1) +
                (2 * Centry * xi * Clog₂ * Lθ ^ (2 : ℕ) + 1)
                =
              Mcoef * Lθ ^ (2 : ℕ) + 2 := by
                dsimp [Mcoef]
                ring
            _ ≤ Mcoef * Lθ ^ (2 : ℕ) + 8 * Lθ ^ (2 : ℕ) := by
                linarith
            _ = Ncoef * Lθ ^ (2 : ℕ) := by
                dsimp [Ncoef]
                ring
  have hceil :
      Ncoef * Lθ ^ (2 : ℕ) ≤
        (Nat.ceil (Ncoef * Lθ ^ (2 : ℕ)) : ℝ) :=
    Nat.le_ceil _
  have hN_real' :
      (N0 : ℝ) ≤ (Nat.ceil (Ncoef * Lθ ^ (2 : ℕ)) : ℝ) :=
    hN_real.trans hceil
  exact_mod_cast hN_real'

/-- The absolute annealed entry factor is absorbed by the manuscript
`exp(C log^2(2 + thetaHat))` envelope.

The constant is selected before the law; it depends only on the finite
`sigma`, the parameter-only `(P4)` data, and the entry constant used to define
`N0`. -/
theorem exists_entryScale_pow_three_le_exp_logSq
    {d : ℕ} [NeZero d] {σ Centry : ℝ}
    (hσ : 0 < σ) (hCentry : 0 < Centry)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ CentryScale : ℝ, 0 < CentryScale ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        (3 : ℝ) ^ N0 ≤
          Real.exp
            (CentryScale *
              (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
  obtain ⟨CentryScale, hCentryScale_pos, hentry⟩ :=
    exists_entryScale_le_natCeil_logSq (d := d) hσ hCentry params
  let Cpow : ℝ := Real.log (3 : ℝ) * (CentryScale + 4)
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hCpow_pos : 0 < Cpow := by
    dsimp [Cpow]
    positivity
  refine ⟨Cpow, hCpow_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Lθ : ℝ := Real.log (2 + hΓ.thetaHat)
  have hθ_nonneg : 0 ≤ hΓ.thetaHat := hΓ.thetaHat_pos.le
  have hL2_nonneg : 0 ≤ Lθ ^ (2 : ℕ) := by
    dsimp [Lθ]
    positivity
  have hceil_arg_nonneg : 0 ≤ CentryScale * Lθ ^ (2 : ℕ) := by
    positivity
  have hquarter : (1 / 4 : ℝ) ≤ Lθ ^ (2 : ℕ) := by
    simpa [Lθ] using log_two_add_sq_ge_quarter hθ_nonneg
  have hN_le :
      N0 ≤ Nat.ceil (CentryScale * Lθ ^ (2 : ℕ)) := by
    simpa [N0, Lθ] using hentry hP hStruct hΓ hσ_eq hparams
  have hpow_mono :
      (3 : ℝ) ^ N0 ≤
        (3 : ℝ) ^ Nat.ceil (CentryScale * Lθ ^ (2 : ℕ)) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hN_le
  have hceil_pow :
      (3 : ℝ) ^ Nat.ceil (CentryScale * Lθ ^ (2 : ℕ)) ≤
        3 * Real.exp (Real.log (3 : ℝ) *
          (CentryScale * Lθ ^ (2 : ℕ))) :=
    pow_three_natCeil_le_three_mul_exp hceil_arg_nonneg
  have hthree_exp :
      3 * Real.exp (Real.log (3 : ℝ) *
          (CentryScale * Lθ ^ (2 : ℕ))) =
        Real.exp (Real.log (3 : ℝ) +
          Real.log (3 : ℝ) * (CentryScale * Lθ ^ (2 : ℕ))) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hexp_le :
      Real.exp (Real.log (3 : ℝ) +
          Real.log (3 : ℝ) * (CentryScale * Lθ ^ (2 : ℕ))) ≤
        Real.exp (Cpow * Lθ ^ (2 : ℕ)) := by
    refine Real.exp_le_exp.mpr ?_
    have hlog3_le : Real.log (3 : ℝ) ≤
        Real.log (3 : ℝ) * (4 * Lθ ^ (2 : ℕ)) := by
      have hone_le : (1 : ℝ) ≤ 4 * Lθ ^ (2 : ℕ) := by
        have hscaled :=
          mul_le_mul_of_nonneg_left hquarter (by norm_num : 0 ≤ (4 : ℝ))
        norm_num at hscaled
        exact hscaled
      calc
        Real.log (3 : ℝ) = Real.log (3 : ℝ) * 1 := by ring
        _ ≤ Real.log (3 : ℝ) * (4 * Lθ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hone_le hlog3_pos.le
    calc
      Real.log (3 : ℝ) +
          Real.log (3 : ℝ) * (CentryScale * Lθ ^ (2 : ℕ))
          ≤ Real.log (3 : ℝ) * (4 * Lθ ^ (2 : ℕ)) +
              Real.log (3 : ℝ) * (CentryScale * Lθ ^ (2 : ℕ)) := by
            exact add_le_add hlog3_le le_rfl
      _ = Cpow * Lθ ^ (2 : ℕ) := by
            dsimp [Cpow]
            ring
  calc
    (3 : ℝ) ^ N0 ≤
        (3 : ℝ) ^ Nat.ceil (CentryScale * Lθ ^ (2 : ℕ)) := hpow_mono
    _ ≤ 3 * Real.exp (Real.log (3 : ℝ) *
          (CentryScale * Lθ ^ (2 : ℕ))) := hceil_pow
    _ = Real.exp (Real.log (3 : ℝ) +
          Real.log (3 : ℝ) * (CentryScale * Lθ ^ (2 : ℕ))) := hthree_exp
    _ ≤ Real.exp (Cpow * Lθ ^ (2 : ℕ)) := hexp_le

end

end Section57
end Ch05
end Book
end Homogenization
