/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.EnergySplit

/-! # Prefactors -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Coarse Caccioppoli with RHS Prefactors

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: convert homogeneous Caccioppoli prefactors into the with-RHS prefactor
normalization used by the public boundary estimate.

Downstream target: `CoarseCaccioppoliRHS/ZeroTraceValue.lean`.  This file
should stay scalar-prefactor algebra, not analytic bridge packaging.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Scalar identity converting the homogeneous Caccioppoli prefactor into the
first term of the forced Caccioppoli RHS. -/
theorem caccioppoliPrefactor_eq_caccioppoliWithRHSPrefactor_mul_lambdaS_scale
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    caccioppoliPrefactor C Q a s t =
      caccioppoliWithRHSPrefactor C Q a s t *
        (Ch02.lambdaS Q t a *
          Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) ) := by
  let σ : ℝ := 1 - s - t
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    linarith
  have hlambda_pos : 0 < Ch02.lambdaS Q t a := by
    unfold Ch02.lambdaS
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
  have hTheta_pos : 0 < Ch02.ThetaRatio Q s t a :=
    lt_of_lt_of_le zero_lt_one (Ch02.one_le_ThetaRatio_of_pos Q a hs ht)
  have hden : 1 - s - t ≠ 0 := by
    linarith
  have hexp :
      (1 - t) / (1 - s - t) = s / (1 - s - t) + 1 := by
    field_simp [hden]
    ring_nf
  have hThetaPow :
      Real.rpow (Ch02.ThetaRatio Q s t a) ((1 - t) / (1 - s - t)) =
        Real.rpow (Ch02.ThetaRatio Q s t a) (s / (1 - s - t)) *
          Ch02.ThetaRatio Q s t a := by
    simpa [hexp, Real.rpow_one] using
      Real.rpow_add hTheta_pos (s / (1 - s - t)) (1 : ℝ)
  have hThetaLambda :
      Ch02.ThetaRatio Q s t a * Ch02.lambdaS Q t a =
        Ch02.LambdaS Q s a := by
    unfold Ch02.ThetaRatio
    field_simp [hlambda_pos.ne']
  let front : ℝ :=
    Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
      Real.rpow s (-(2 * s / (1 - s - t)))
  let thetaPow : ℝ :=
    Real.rpow (Ch02.ThetaRatio Q s t a) (s / (1 - s - t))
  let scale : ℝ :=
    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))
  have hleft0 :
      caccioppoliPrefactor C Q a s t =
        front * thetaPow * Ch02.LambdaS Q s a * scale := by
    rfl
  have hleft :
      caccioppoliPrefactor C Q a s t =
        front * thetaPow * (Ch02.ThetaRatio Q s t a *
          Ch02.lambdaS Q t a) * scale := by
    calc
      caccioppoliPrefactor C Q a s t =
          front * thetaPow * Ch02.LambdaS Q s a * scale := hleft0
      _ =
          front * thetaPow * (Ch02.ThetaRatio Q s t a *
            Ch02.lambdaS Q t a) * scale := by
            rw [hThetaLambda]
  have hright0 :
      caccioppoliWithRHSPrefactor C Q a s t *
          (Ch02.lambdaS Q t a * scale) =
        front *
          Real.rpow (Ch02.ThetaRatio Q s t a)
            ((1 - t) / (1 - s - t)) *
          (Ch02.lambdaS Q t a * scale) := by
    rfl
  have hright :
      caccioppoliWithRHSPrefactor C Q a s t *
          (Ch02.lambdaS Q t a * scale) =
        front * thetaPow * (Ch02.ThetaRatio Q s t a *
          Ch02.lambdaS Q t a) * scale := by
    calc
      caccioppoliWithRHSPrefactor C Q a s t *
          (Ch02.lambdaS Q t a * scale) =
        front *
          Real.rpow (Ch02.ThetaRatio Q s t a)
            ((1 - t) / (1 - s - t)) *
          (Ch02.lambdaS Q t a * scale) := hright0
      _ =
        front * (thetaPow * Ch02.ThetaRatio Q s t a) *
          (Ch02.lambdaS Q t a * scale) := by
          rw [hThetaPow]
      _ =
        front * thetaPow * (Ch02.ThetaRatio Q s t a *
          Ch02.lambdaS Q t a) * scale := by
          ring
  rw [hleft, hright]

/-- The forced Caccioppoli scalar prefactor is nonnegative in the theorem
range. -/
theorem caccioppoliWithRHSPrefactor_nonneg
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ caccioppoliWithRHSPrefactor C Q a s t := by
  have hden_pos : 0 < 1 - s - t := by linarith
  have hCdiv_nonneg : 0 ≤ C / (1 - s - t) := by
    exact div_nonneg hC_nonneg hden_pos.le
  have htheta_nonneg : 0 ≤ Ch02.ThetaRatio Q s t a :=
    (le_trans zero_le_one (Ch02.one_le_ThetaRatio_of_pos Q a hs ht))
  have hfront_nonneg :
      0 ≤ Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) :=
    Real.rpow_nonneg hCdiv_nonneg _
  have hs_factor_nonneg :
      0 ≤ Real.rpow s (-(2 * s / (1 - s - t))) :=
    Real.rpow_nonneg hs.le _
  have htheta_factor_nonneg :
      0 ≤ Real.rpow (Ch02.ThetaRatio Q s t a) ((1 - t) / (1 - s - t)) :=
    Real.rpow_nonneg htheta_nonneg _
  simpa [caccioppoliWithRHSPrefactor] using
    mul_nonneg (mul_nonneg hfront_nonneg hs_factor_nonneg)
      htheta_factor_nonneg

/-- With the displayed constant at least `1`, the forced Caccioppoli
prefactor is at least `1` throughout the theorem range. -/
theorem one_le_caccioppoliWithRHSPrefactor
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} (hC : 1 ≤ C)
    (hs : 0 < s) (hs_lt : s < 1) (ht : 0 < t) (hst : s + t < 1) :
    1 ≤ caccioppoliWithRHSPrefactor C Q a s t := by
  let σ : ℝ := 1 - s - t
  let p : ℝ := 2 + 4 * s / σ
  let eθ : ℝ := (1 - t) / σ
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    linarith
  have hσ_le_one : σ ≤ 1 := by
    dsimp [σ]
    linarith
  have hp_nonneg : 0 ≤ p := by
    have hdiv_nonneg : 0 ≤ 4 * s / σ := by positivity
    dsimp [p]
    linarith
  have hbase_one : 1 ≤ C / σ := by
    have hCσ : σ ≤ C := hσ_le_one.trans hC
    exact (le_div_iff₀ hσ_pos).2 (by simpa using hCσ)
  have hfront :
      1 ≤ Real.rpow (C / σ) p := by
    have hone_pow : Real.rpow (C / σ) 0 = 1 := by
      simp
    calc
      1 = Real.rpow (C / σ) 0 := hone_pow.symm
      _ ≤ Real.rpow (C / σ) p :=
        Real.rpow_le_rpow_of_exponent_le hbase_one hp_nonneg
  have hs_exp_nonpos :
      -(2 * s / σ) ≤ 0 := by
    have hnonneg : 0 ≤ 2 * s / σ := by positivity
    linarith
  have hs_factor :
      1 ≤ Real.rpow s (-(2 * s / σ)) := by
    have hone_pow : Real.rpow (1 : ℝ) (-(2 * s / σ)) = 1 := by
      simp
    calc
      1 = Real.rpow (1 : ℝ) (-(2 * s / σ)) := hone_pow.symm
      _ ≤ Real.rpow s (-(2 * s / σ)) :=
        Real.rpow_le_rpow_of_nonpos hs hs_lt.le hs_exp_nonpos
  have htheta_one : 1 ≤ Ch02.ThetaRatio Q s t a :=
    Ch02.one_le_ThetaRatio_of_pos Q a hs ht
  have heθ_nonneg : 0 ≤ eθ := by
    dsimp [eθ, σ]
    have hnum : 0 ≤ 1 - t := by linarith
    exact div_nonneg hnum hσ_pos.le
  have htheta_factor :
      1 ≤ Real.rpow (Ch02.ThetaRatio Q s t a) eθ := by
    have hone_pow : Real.rpow (Ch02.ThetaRatio Q s t a) 0 = 1 := by
      simp
    calc
      1 = Real.rpow (Ch02.ThetaRatio Q s t a) 0 := hone_pow.symm
      _ ≤ Real.rpow (Ch02.ThetaRatio Q s t a) eθ :=
        Real.rpow_le_rpow_of_exponent_le htheta_one heθ_nonneg
  have hfront_nonneg :
      0 ≤ Real.rpow (C / σ) p := le_trans zero_le_one hfront
  have hs_factor_nonneg :
      0 ≤ Real.rpow s (-(2 * s / σ)) := le_trans zero_le_one hs_factor
  have hfirst :
      1 ≤ Real.rpow (C / σ) p *
          Real.rpow s (-(2 * s / σ)) := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ Real.rpow (C / σ) p *
          Real.rpow s (-(2 * s / σ)) :=
        mul_le_mul hfront hs_factor zero_le_one hfront_nonneg
  have hfirst_nonneg :
      0 ≤ Real.rpow (C / σ) p *
          Real.rpow s (-(2 * s / σ)) :=
    le_trans zero_le_one hfirst
  have hall :
      1 ≤
        (Real.rpow (C / σ) p *
          Real.rpow s (-(2 * s / σ))) *
          Real.rpow (Ch02.ThetaRatio Q s t a) eθ := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤
        (Real.rpow (C / σ) p *
          Real.rpow s (-(2 * s / σ))) *
          Real.rpow (Ch02.ThetaRatio Q s t a) eθ :=
        mul_le_mul hfirst htheta_factor zero_le_one hfirst_nonneg
  simpa [caccioppoliWithRHSPrefactor, σ, p, eθ] using hall

/-- A slightly stronger lower bound: the forced prefactor contains at least
`C^2` when `C >= 1`. This lets a large final dimension constant absorb
dimension-only multiples of the forcing summand. -/
theorem sq_le_caccioppoliWithRHSPrefactor
    {d : ℕ} [NeZero d] {C : ℝ} {Q : TriadicCube d} {a : CoeffFamily d}
    {s t : ℝ} (hC : 1 ≤ C)
    (hs : 0 < s) (hs_lt : s < 1) (ht : 0 < t) (hst : s + t < 1) :
    C ^ 2 ≤ caccioppoliWithRHSPrefactor C Q a s t := by
  let σ : ℝ := 1 - s - t
  let p : ℝ := 2 + 4 * s / σ
  let eθ : ℝ := (1 - t) / σ
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    linarith
  have hσ_le_one : σ ≤ 1 := by
    dsimp [σ]
    linarith
  have hp_ge_two : 2 ≤ p := by
    have hdiv_nonneg : 0 ≤ 4 * s / σ := by positivity
    dsimp [p]
    linarith
  have hC_nonneg : 0 ≤ C := le_trans zero_le_one hC
  have hbase_one : 1 ≤ C / σ := by
    have hCσ : σ ≤ C := hσ_le_one.trans hC
    exact (le_div_iff₀ hσ_pos).2 (by simpa using hCσ)
  have hC_le_base : C ≤ C / σ := by
    have hmul : C * σ ≤ C * 1 := by
      exact mul_le_mul_of_nonneg_left hσ_le_one hC_nonneg
    have hbase : C * σ ≤ C := by simpa using hmul
    exact (le_div_iff₀ hσ_pos).2 hbase
  have hfront_ge_C2 :
      C ^ 2 ≤ Real.rpow (C / σ) p := by
    calc
      C ^ 2 = Real.rpow C (2 : ℝ) := by
        exact (Real.rpow_two C).symm
      _ ≤ Real.rpow (C / σ) (2 : ℝ) :=
        Real.rpow_le_rpow hC_nonneg hC_le_base (by norm_num)
      _ ≤ Real.rpow (C / σ) p :=
        Real.rpow_le_rpow_of_exponent_le hbase_one hp_ge_two
  have hfront_nonneg :
      0 ≤ Real.rpow (C / σ) p :=
    le_trans (sq_nonneg C) hfront_ge_C2
  have hs_exp_nonpos :
      -(2 * s / σ) ≤ 0 := by
    have hnonneg : 0 ≤ 2 * s / σ := by positivity
    linarith
  have hs_factor :
      1 ≤ Real.rpow s (-(2 * s / σ)) := by
    have hone_pow : Real.rpow (1 : ℝ) (-(2 * s / σ)) = 1 := by
      simp
    calc
      1 = Real.rpow (1 : ℝ) (-(2 * s / σ)) := hone_pow.symm
      _ ≤ Real.rpow s (-(2 * s / σ)) :=
        Real.rpow_le_rpow_of_nonpos hs hs_lt.le hs_exp_nonpos
  have hs_factor_nonneg :
      0 ≤ Real.rpow s (-(2 * s / σ)) :=
    le_trans zero_le_one hs_factor
  have htheta_one : 1 ≤ Ch02.ThetaRatio Q s t a :=
    Ch02.one_le_ThetaRatio_of_pos Q a hs ht
  have heθ_nonneg : 0 ≤ eθ := by
    dsimp [eθ, σ]
    have hnum : 0 ≤ 1 - t := by linarith
    exact div_nonneg hnum hσ_pos.le
  have htheta_factor :
      1 ≤ Real.rpow (Ch02.ThetaRatio Q s t a) eθ := by
    have hone_pow : Real.rpow (Ch02.ThetaRatio Q s t a) 0 = 1 := by
      simp
    calc
      1 = Real.rpow (Ch02.ThetaRatio Q s t a) 0 := hone_pow.symm
      _ ≤ Real.rpow (Ch02.ThetaRatio Q s t a) eθ :=
        Real.rpow_le_rpow_of_exponent_le htheta_one heθ_nonneg
  have htheta_factor_nonneg :
      0 ≤ Real.rpow (Ch02.ThetaRatio Q s t a) eθ :=
    le_trans zero_le_one htheta_factor
  calc
    C ^ 2 ≤ Real.rpow (C / σ) p := hfront_ge_C2
    _ ≤ Real.rpow (C / σ) p *
          Real.rpow s (-(2 * s / σ)) := by
        calc
          Real.rpow (C / σ) p =
              Real.rpow (C / σ) p * 1 := by ring
          _ ≤ Real.rpow (C / σ) p *
              Real.rpow s (-(2 * s / σ)) :=
            mul_le_mul_of_nonneg_left hs_factor hfront_nonneg
    _ ≤
        (Real.rpow (C / σ) p *
          Real.rpow s (-(2 * s / σ))) *
          Real.rpow (Ch02.ThetaRatio Q s t a) eθ := by
        have hprod_nonneg :
            0 ≤ Real.rpow (C / σ) p *
                Real.rpow s (-(2 * s / σ)) :=
          mul_nonneg hfront_nonneg hs_factor_nonneg
        calc
          Real.rpow (C / σ) p *
              Real.rpow s (-(2 * s / σ)) =
              (Real.rpow (C / σ) p *
                Real.rpow s (-(2 * s / σ))) * 1 := by ring
          _ ≤
              (Real.rpow (C / σ) p *
                Real.rpow s (-(2 * s / σ))) *
                Real.rpow (Ch02.ThetaRatio Q s t a) eθ :=
            mul_le_mul_of_nonneg_left htheta_factor hprod_nonneg
    _ = caccioppoliWithRHSPrefactor C Q a s t := by
        rfl


end

end Ch03
end Book
end Homogenization
