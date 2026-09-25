/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


/-
  Genus-1 paired sum formula portion of the Li-criterion development.

  Extracted from `Lc/LiCriterion.lean` to keep files smaller and make editing
  the M-test + Cauchy inequality steps more manageable.
-/

public import LeanPool.LiCriterion.Lc.LiCriterion.Basic
public import LeanPool.LiCriterion.Lc.LiCriterion.ReverseDirection

/-! ## Genus‑1 paired sum formulation

For ξ the raw Li summand behaves like `(n+1)/ρ`,
so absolute convergence of the unpaired series fails.
The genus‑1 replacement is to sum the paired term `liPairedSummand n ρ`
and divide by `2`.

We prove the paired sum formula by passing to `ξ²`,
whose canonical factors are the quadratic terms
`xiPairedFactor ρ s = 1 - ((s - 1/2)/(ρ - 1/2))^2 = E₁(w)E₁(-w)`.
This removes the linear divergence and restores absolute convergence
under the genus‑1 hypothesis `∑ 1/‖ρ‖² < ∞`. -/

@[expose] public section

open Complex Real Set Function Filter
open scoped Topology

namespace LiCriterion

private theorem paired_factor_derivative_norm_le (ρ : NontrivialZero) (r : ℝ) (z : ℂ)
    (hρlarge : (1 : ℝ) ≤ ‖ρ.val‖) (hzsub : (1 : ℂ) - z ≠ 0)
    (hA : ‖(1 : ℂ) / (1 - z) - (1 / 2 : ℂ)‖ ≤ (1 : ℝ) / (1 - r) + 1 / 2)
    (h_inv_sq : ‖(1 : ℂ) / (1 - z) ^ 2‖ ≤ ((1 : ℝ) / (1 - r)) ^ 2) :
    ‖deriv (fun w => xiPairedFactor ρ (1 / (1 - w))) z‖ ≤
      8 * ((1 : ℝ) / (1 - r) + 1 / 2) * ((1 : ℝ) / (1 - r)) ^ 2 *
        ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  let fac : NontrivialZero → ℂ → ℂ := fun ρ z => xiPairedFactor ρ (1 / (1 - z))
  let A : ℝ := (1 : ℝ) / (1 - r) + (1 / 2 : ℝ)
  have hdf :
      deriv (fac ρ) z =
        deriv (xiPairedFactor ρ) ((1 : ℂ) / ((1 : ℂ) - z)) *
          deriv (fun w : ℂ => (1 : ℂ) / ((1 : ℂ) - w)) z := by
    have h_outer : DifferentiableAt ℂ (xiPairedFactor ρ) ((1 : ℂ) / ((1 : ℂ) - z)) :=
      (xiPairedFactor_differentiable ρ).differentiableAt
    have h_inner : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) / ((1 : ℂ) - w)) z := by
      apply DifferentiableAt.div
      · exact differentiableAt_const (c := (1 : ℂ))
      · exact
          (DifferentiableAt.sub
            (differentiableAt_const (c := (1 : ℂ))) differentiableAt_id)
      · exact hzsub
    -- `deriv_comp` is the chain rule.
    simpa [fac, Function.comp_def] using (deriv_comp z h_outer h_inner)
  have hderiv_inner :
      deriv (fun w : ℂ => (1 : ℂ) / ((1 : ℂ) - w)) z
        = (1 : ℂ) / ((1 : ℂ) - z) ^ 2 := by
    simpa [one_div] using (deriv_one_div_one_sub (z := z) hzsub)
  have hderiv_outer :
      deriv (xiPairedFactor ρ) ((1 : ℂ) / ((1 : ℂ) - z)) =
        -(2 : ℂ) *
          ((((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)) / ((ρ.val - (1 / 2 : ℂ)) ^ 2)) := by
    simpa using (deriv_xiPairedFactor ρ ((1 : ℂ) / ((1 : ℂ) - z)))
  have hderiv_bound :
      ‖deriv (fac ρ) z‖ ≤
        (8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    -- combine the explicit derivative formulas and the `‖ρ-1/2‖` estimate
    have hρhalf_le :
        (1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2
          ≤ (4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) :=
      inv_norm_sub_half_sq_le (ρ := ρ) hρlarge
    -- rewrite `‖((ρ - 1/2)^2)‖ = ‖ρ-1/2‖^2`
    have hρhalf' :
        ‖((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2‖ = ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
      simp [pow_two]
    -- `‖deriv fac‖ = ‖deriv outer * deriv inner‖`
    rw [hdf, hderiv_outer, hderiv_inner]
    -- bound by product of norms
    have := (norm_mul
      (-(2 : ℂ) * ((((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)) / ((ρ.val - (1 / 2 : ℂ)) ^ 2)))
      ((1 : ℂ) / ((1 : ℂ) - z) ^ 2))
    -- use `norm_mul` + crude bounds
    calc
      ‖(-(2 : ℂ) *
            ((((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)) /
              ((ρ.val - (1 / 2 : ℂ)) ^ 2))) *
          ((1 : ℂ) / ((1 : ℂ) - z) ^ 2)‖
          =
            ‖-(2 : ℂ) *
                ((((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)) /
                  ((ρ.val - (1 / 2 : ℂ)) ^ 2))‖ *
              ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ := by
        simp
      _ ≤ (2 : ℝ) *
            (‖((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)‖ / ‖((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2‖) *
            ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ := by
              -- `‖-2 * x‖ = 2 * ‖x‖` and `‖a/b‖ = ‖a‖/‖b‖`
              have :
                  ‖-(2 : ℂ) *
                      ((((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)) /
                        ((ρ.val - (1 / 2 : ℂ)) ^ 2))‖
                    =
                      (2 : ℝ) *
                        ‖(((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)) /
                          ((ρ.val - (1 / 2 : ℂ)) ^ 2)‖ := by
                simp
              rw [this]
              gcongr
              simp
      _ ≤ (2 : ℝ) *
            (A * ((4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2))) *
            ((1 : ℝ) / (1 - r)) ^ 2 := by
              -- Use `h_inv_sq`, `hA`, and the `‖ρ-1/2‖` reciprocal bound.
              have hden_ne : ‖((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2‖ ≠ 0 := by
                have : ((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2 ≠ 0 := by
                  apply pow_ne_zero 2
                  have hρne : (ρ.val : ℂ) ≠ (1 / 2 : ℂ) := by
                    intro hEq
                    have hnorm : (‖ρ.val‖ : ℝ) = (1 / 2 : ℝ) := by
                      simp [hEq]
                    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by simpa [hnorm] using hρlarge
                    nlinarith
                  exact sub_ne_zero.mpr hρne
                exact norm_ne_zero_iff.2 this
              have hdiv :
                  ‖((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)‖ /
                      ‖((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2‖
                    =
                      ‖((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)‖ *
                        ((1 : ℝ) / ‖((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2‖) := by
                simp [div_eq_mul_inv]
              rw [hdiv]
              have hρhalf'' :
                  (1 : ℝ) / ‖((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2‖
                    = (1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
                rw [hρhalf']
              -- Use the bounds (reassociate to apply `mul_le_mul_of_nonneg_left` cleanly).
              have h_inner :
                  (‖((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)‖ *
                      ((1 : ℝ) / ‖((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2‖)) *
                        ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖
                    ≤
                      (A * ((4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2))) *
                        ((1 : ℝ) / (1 - r)) ^ 2 := by
                have hA0 : 0 ≤ A :=
                  le_trans
                    (by positivity :
                      (0 : ℝ) ≤ ‖((1 : ℂ) / ((1 : ℂ) - z)) - (1 / 2 : ℂ)‖)
                    hA
                have hb0 : 0 ≤ A * ((4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2)) :=
                  mul_nonneg hA0 (by positivity)
                refine mul_le_mul ?_ h_inv_sq (by positivity) hb0
                · refine mul_le_mul hA ?_ (by positivity) hA0
                  -- `1/‖ρ-1/2‖² ≤ 4/‖ρ‖²`
                  simpa [hρhalf''] using hρhalf_le
              simpa [mul_assoc] using
                (mul_le_mul_of_nonneg_left h_inner (by positivity : (0 : ℝ) ≤ (2 : ℝ)))
      _ = (8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
            ring
  exact hderiv_bound

private theorem paired_log_deriv_cofinite_bound
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (r : ℝ) (hr_lt_one : r < 1)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    : ∀ᶠ ρ : NontrivialZero in Filter.cofinite, ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖logDeriv (fun w => xiPairedFactor ρ (1 / (1 - w))) z‖ ≤
        (16 * ((1 : ℝ) / (1 - r) + 1 / 2) * ((1 : ℝ) / (1 - r)) ^ 2) *
          ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let fac : NontrivialZero → ℂ → ℂ := fun ρ z => xiPairedFactor ρ (1 / (1 - z))
  let term : NontrivialZero → ℂ → ℂ := fun ρ z => logDeriv (fac ρ) z
  let A : ℝ := (1 : ℝ) / (1 - r) + (1 / 2 : ℝ)
  let Cfac : ℝ := 4 * A ^ 2
  let C : ℝ := 16 * A * ((1 : ℝ) / (1 - r)) ^ 2
  let u : NontrivialZero → ℝ := fun ρ => C * ((1 : ℝ) / ‖ρ.val‖ ^ 2)
  -- Eventual bound `‖ρ‖ ≥ 1` from genus-1 summability.
  have hlarge :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, (1 : ℝ) ≤ ‖ρ.val‖ :=
    eventually_le_norm_of_summable_inv_norm_sq hgenus (R := 1) (by norm_num)
  -- Eventual smallness of the crude `O(1/‖ρ‖²)` bound on `‖fac ρ z - 1‖`,
  -- used to control the denominator in `logDeriv`.
  have hsmallCfac :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite,
        Cfac * ((1 : ℝ) / ‖ρ.val‖ ^ 2) ≤ (1 / 2 : ℝ) := by
    have ht :
        Filter.Tendsto (fun ρ : NontrivialZero => Cfac * ((1 : ℝ) / ‖ρ.val‖ ^ 2))
          Filter.cofinite (𝓝 (0 : ℝ)) :=
      (hgenus.mul_left Cfac).tendsto_cofinite_zero
    exact ht.eventually_le_const (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
  -- Cofinite uniform bound on the logarithmic derivative (for the uniform M-test).
  have hbound :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, ∀ z ∈ K, ‖term ρ z‖ ≤ u ρ := by
    filter_upwards [hlarge, hsmallCfac] with ρ hρlarge hρsmall z hz
    have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
    have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
    -- `‖(1/(1-z))‖` is uniformly bounded on the ball by `1/(1-r)`.
    have h_inv_bound : ‖(1 : ℂ) / ((1 : ℂ) - z)‖ ≤ (1 : ℝ) / (1 - r) := by
      have hz_norm : ‖z‖ < r := by simpa [K, Metric.mem_ball, dist_eq_norm] using hz
      have h1 : (1 - r) ≤ ‖(1 : ℂ) - z‖ := by
        have htmp : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
          simpa using (norm_sub_norm_le (1 : ℂ) z)
        have hle : (1 : ℝ) - r ≤ (1 : ℝ) - ‖z‖ := by linarith [hz_norm.le]
        exact le_trans hle htmp
      have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
      have hrecip : (1 : ℝ) / ‖(1 : ℂ) - z‖ ≤ (1 : ℝ) / ((1 : ℝ) - r) :=
        one_div_le_one_div_of_le hpos h1
      simpa [div_eq_mul_inv] using hrecip
    have hA : ‖(1 : ℂ) / ((1 : ℂ) - z) - (1 / 2 : ℂ)‖ ≤ A := by
      have htri :
          ‖(1 : ℂ) / ((1 : ℂ) - z) - (1 / 2 : ℂ)‖ ≤
            ‖(1 : ℂ) / ((1 : ℂ) - z)‖ + ‖(1 / 2 : ℂ)‖ := by
        simpa [sub_eq_add_neg] using
          (norm_add_le ((1 : ℂ) / ((1 : ℂ) - z)) (-(1 / 2 : ℂ)))
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      dsimp [A]
      nlinarith [htri, h_inv_bound, hhalf]
    have h_inv_sq : ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ ≤ ((1 : ℝ) / (1 - r)) ^ 2 := by
      have : ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ = ‖(1 : ℂ) / ((1 : ℂ) - z)‖ ^ 2 := by
        -- `‖w^2‖ = ‖w‖^2`
        simp [pow_two]
      rw [this]
      have hnonneg : 0 ≤ ‖(1 : ℂ) / ((1 : ℂ) - z)‖ := by positivity
      have hnonneg' : 0 ≤ (1 : ℝ) / (1 - r) := by
        have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
        exact div_nonneg (by norm_num) hpos.le
      -- square the bound `h_inv_bound`
      simpa [pow_two] using mul_le_mul h_inv_bound h_inv_bound hnonneg hnonneg'
    -- Control the denominator `‖fac ρ z‖` away from `0`
    -- using the crude `O(1/‖ρ‖²)` bound.
    have hfac_sub :
        ‖fac ρ z - (1 : ℂ)‖ ≤ Cfac * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
      have hz' : z ∈ Metric.ball (0 : ℂ) r := hz
      have h :=
        xiPairedFactor_phi_norm_sub_one_le_of_one_le_norm_on_ball (r := r) hr_lt_one
          (ρ := ρ) hρlarge z hz'
      simpa [fac, Cfac, A] using h
    have hfac_sub' : ‖fac ρ z - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) := le_trans hfac_sub hρsmall
    have hfac_norm : (1 / 2 : ℝ) ≤ ‖fac ρ z‖ := by
      -- `‖fac‖ ≥ 1 - ‖fac - 1‖ ≥ 1/2`
      have htri : (1 : ℝ) - ‖fac ρ z‖ ≤ ‖(1 : ℂ) - fac ρ z‖ := by
        simpa [norm_one] using (norm_sub_norm_le (1 : ℂ) (fac ρ z))
      have htri' : (1 : ℝ) - ‖fac ρ z‖ ≤ ‖fac ρ z - (1 : ℂ)‖ := by
        simpa [norm_sub_rev] using htri
      have : (1 : ℝ) - ‖fac ρ z‖ ≤ (1 / 2 : ℝ) := le_trans htri' hfac_sub'
      linarith
    -- Bound the derivative of `fac ρ` by chain rule and crude norm estimates.
    have hderiv_bound :
        ‖deriv (fac ρ) z‖ ≤
          (8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) :=
      paired_factor_derivative_norm_le ρ r z hρlarge hzsub hA h_inv_sq
    -- Finally bound `logDeriv (fac ρ)` using `‖fac‖ ≥ 1/2`.
    have hinv_fac : ‖(fac ρ z)⁻¹‖ ≤ (2 : ℝ) := by
      have hpos_half : 0 < (1 / 2 : ℝ) := by norm_num
      have h := one_div_le_one_div_of_le hpos_half hfac_norm
      -- `‖x⁻¹‖ = 1/‖x‖`
      simpa [one_div] using (show (1 : ℝ) / ‖fac ρ z‖ ≤ (2 : ℝ) from by
        simpa using h)
    -- `‖logDeriv (fac ρ) z‖ = ‖deriv (fac ρ) z / fac ρ z‖ ≤ ‖deriv‖ * ‖(fac)⁻¹‖`
    have : ‖term ρ z‖ ≤ u ρ := by
      unfold term logDeriv
      have hmul :
          ‖deriv (fac ρ) z / fac ρ z‖ = ‖deriv (fac ρ) z‖ * ‖(fac ρ z)⁻¹‖ := by
        simp [div_eq_mul_inv]
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        have hr' : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
        have hdiv_nonneg : 0 ≤ (1 : ℝ) / ((1 : ℝ) - r) :=
          div_nonneg (by norm_num) hr'.le
        exact add_nonneg hdiv_nonneg (by norm_num)
      have hbound_nonneg :
          0 ≤ (8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
        have h8 : 0 ≤ (8 : ℝ) := by norm_num
        have hsq : 0 ≤ ((1 : ℝ) / (1 - r)) ^ 2 := by positivity
        have hρ : 0 ≤ (1 : ℝ) / ‖ρ.val‖ ^ 2 := by positivity
        have h1 : 0 ≤ (8 : ℝ) * A := mul_nonneg h8 hA_nonneg
        have h2 : 0 ≤ (8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 := mul_nonneg h1 hsq
        have h3 :
            0 ≤ (8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) :=
          mul_nonneg h2 hρ
        simpa [mul_assoc] using h3
      have hprod :
          ‖deriv (fac ρ) z‖ * ‖(fac ρ z)⁻¹‖ ≤
            ((8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2)) * (2 : ℝ) :=
        mul_le_mul hderiv_bound hinv_fac (by positivity) hbound_nonneg
      calc
        ‖deriv (fac ρ) z / fac ρ z‖
            = ‖deriv (fac ρ) z‖ * ‖(fac ρ z)⁻¹‖ := hmul
        _ ≤ ((8 : ℝ) * A * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2)) * (2 : ℝ) := hprod
        _ = u ρ := by
              simp [u, C]
              ring
    simpa using this
  exact hbound

private theorem paired_log_deriv_limit_eq
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s)
    (r : ℝ) (hr_lt_one : r < 1)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    : Set.EqOn (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
      (fun z => ∑' ρ : NontrivialZero, logDeriv (fun w => xiPairedFactor ρ (1 / (1 - w))) z)
      (Metric.ball (0 : ℂ) r) := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let fac : NontrivialZero → ℂ → ℂ := fun ρ z => xiPairedFactor ρ (1 / (1 - z))
  let term : NontrivialZero → ℂ → ℂ := fun ρ z => logDeriv (fac ρ) z
  let A : ℝ := (1 : ℝ) / (1 - r) + (1 / 2 : ℝ)
  let Cfac : ℝ := 4 * A ^ 2
  let C : ℝ := 16 * A * ((1 : ℝ) / (1 - r)) ^ 2
  let u : NontrivialZero → ℝ := fun ρ => C * ((1 : ℝ) / ‖ρ.val‖ ^ 2)
  have hu : Summable u := hgenus.mul_left C
  have hbound := paired_log_deriv_cofinite_bound hgenus r hr_lt_one havoid
  intro z hz
  have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
  have hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ) := (havoid z hz).2
  have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  -- Factor ξ² via the paired quadratic product.
  obtain ⟨a₂, hξ₂⟩ := xi_sq_factorization_paired_of_genus_one hgenus hhad
  have hφ :
      (fun w => (riemannXi (1 / (1 - w))) ^ 2)
        = fun w => Complex.exp a₂ * ∏' ρ : NontrivialZero, fac ρ w := by
    funext w
    simpa [fac] using (hξ₂ (1 / (1 - w)))
  -- Drop the constant prefactor.
  have h_drop :
      logDeriv (fun w => Complex.exp a₂ * (∏' ρ : NontrivialZero, fac ρ w)) z
        = logDeriv (fun w => ∏' ρ : NontrivialZero, fac ρ w) z := by
    -- Translate the mathlib lemma to our local `logDeriv` definition.
    simpa [logDeriv, _root_.logDeriv, _root_.logDeriv_apply] using
      (_root_.logDeriv_const_mul (x := z) (a := Complex.exp a₂)
        (f := fun w => ∏' ρ : NontrivialZero, fac ρ w) (ha := Complex.exp_ne_zero a₂))
  -- Summability of the log-derivative terms at this `z` from the cofinite M-test bound.
  have hm : Summable (fun ρ : NontrivialZero => logDeriv (fac ρ) z) := by
    have hbound_z :
        ∀ᶠ ρ : NontrivialZero in Filter.cofinite, ‖term ρ z‖ ≤ u ρ := by
      filter_upwards [hbound] with ρ hρ using hρ z hz
    exact Summable.of_norm_bounded_eventually hu hbound_z
  have hf_ne : ∀ ρ : NontrivialZero, fac ρ z ≠ 0 :=
    fun ρ => xiPairedFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid ρ
  have hd : ∀ ρ : NontrivialZero, DifferentiableOn ℂ (fac ρ) K := fun ρ =>
    xiPairedFactor_phi_differentiableOn_ball (r := r) hr_lt_one ρ
  have htend : MultipliableLocallyUniformlyOn fac K :=
    xiPairedFactor_phi_multipliableLocallyUniformlyOn_ball_of_genus_one
      (r := r) hr_lt_one hgenus
  have hnez : (∏' ρ : NontrivialZero, fac ρ z) ≠ 0 :=
    xiPairedFactor_phi_tprod_ne_zero_of_separation_of_genus_one
      (r := r) hr_lt_one hgenus (z := z) hz
      hzavoid
  have h_log :
      logDeriv (fun w => ∏' ρ : NontrivialZero, fac ρ w) z
        = ∑' ρ : NontrivialZero, logDeriv (fac ρ) z := by
    -- Apply `logDeriv_tprod_eq_tsum` pointwise at `z`.
    let s : Set ℂ := K
    have hs : IsOpen s := Metric.isOpen_ball
    simpa [s, logDeriv_eq_rootLogDeriv] using
      (logDeriv_tprod_eq_tsum (ι := NontrivialZero) (s := s) hs (x := z) (hx := hz)
        (f := fac)
        (hf := fun ρ => hf_ne ρ)
        (hd := fun ρ => hd ρ)
        (hm := by simpa [term, logDeriv_eq_rootLogDeriv] using hm)
        (htend := htend) (hnez := hnez))
  -- Combine everything.
  calc
    logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)) z
        = logDeriv (fun w => Complex.exp a₂ * (∏' ρ : NontrivialZero, fac ρ w)) z := by
            have hphi_def :
                phi (fun s : ℂ => (riemannXi s) ^ 2) =
                  fun w => (riemannXi (1 / (1 - w))) ^ 2 := by
              funext w
              rfl
            calc
              logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)) z
                  = logDeriv (fun w => (riemannXi (1 / (1 - w))) ^ 2) z := by
                      simp [hphi_def]
              _ = logDeriv (fun w => Complex.exp a₂ * (∏' ρ : NontrivialZero, fac ρ w)) z := by
                      have := congrArg (fun F : ℂ → ℂ => logDeriv F z) hφ
                      simpa [one_div] using this
    _ = logDeriv (fun w => ∏' ρ : NontrivialZero, fac ρ w) z := h_drop
    _ = ∑' ρ : NontrivialZero, term ρ z := by
          simpa [term] using h_log

private theorem paired_finite_coefficient [Fact xiFactorizationShiftedProd]
    (S : Finset NontrivialZero) (n : ℕ)
    (r : ℝ) (hrpos : 0 < r) (hr_lt_one : r < 1)
    (hpartial : Set.EqOn
      (fun z => logDeriv (fun w => ∏ ρ ∈ S, xiPairedFactor ρ (1 / (1 - w))) z)
      (fun z => ∑ ρ ∈ S, logDeriv (fun w => xiPairedFactor ρ (1 / (1 - w))) z)
      (Metric.ball (0 : ℂ) r)) :
    (deriv^[n] (fun z => logDeriv (fun w => ∏ ρ ∈ S, xiPairedFactor ρ (1 / (1 - w))) z)) 0 /
      n.factorial = ∑ ρ ∈ S, liPairedSummand n ρ := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let fac : NontrivialZero → ℂ → ℂ := fun ρ z => xiPairedFactor ρ (1 / (1 - z))
  let term : NontrivialZero → ℂ → ℂ := fun ρ z => logDeriv (fac ρ) z
  have h0K : (0 : ℂ) ∈ K := Metric.mem_ball_self hrpos
  -- On the ball, `logDeriv` of the product equals the finite sum of `logDeriv`s.
  have hEqOn :
      Set.EqOn
          (fun z => logDeriv (fun w => ∏ ρ ∈ S, fac ρ w) z)
          (fun z => ∑ ρ ∈ S, logDeriv (fac ρ) z) K := by
    intro z hz
    exact hpartial hz
  have hsopen : IsOpen K := Metric.isOpen_ball
  have hEqIter : iteratedDeriv n (fun z => logDeriv (fun w => ∏ ρ ∈ S, fac ρ w) z) 0
      = iteratedDeriv n (fun z => ∑ ρ ∈ S, logDeriv (fac ρ) z) 0 := by
    have hEqOn' :=
      Set.EqOn.iteratedDeriv_of_isOpen
        (f := fun z => logDeriv (fun w => ∏ ρ ∈ S, fac ρ w) z)
        (g := fun z => ∑ ρ ∈ S, logDeriv (fac ρ) z)
        (s := K) hEqOn hsopen n
    exact hEqOn' h0K
  have hEqIter' :
      (deriv^[n] (fun z => logDeriv (fun w => ∏ ρ ∈ S, fac ρ w) z)) 0
        =
      (deriv^[n] (fun z => ∑ ρ ∈ S, logDeriv (fac ρ) z)) 0 := by
    simpa [iteratedDeriv_eq_iterate] using hEqIter
  -- The iterated derivative of the finite sum is the finite sum of iterated derivatives.
  have hsum_iter :
      (deriv^[n] (fun z => ∑ ρ ∈ S, logDeriv (fac ρ) z)) 0
        =
      ∑ ρ ∈ S, (deriv^[n] (fun z => logDeriv (fac ρ) z)) 0 := by
    -- Use `iteratedDeriv_add` repeatedly via `Finset.induction_on`.
    have hsum_iter' :
        iteratedDeriv n (fun z => ∑ ρ ∈ S, logDeriv (fac ρ) z) 0
          =
        ∑ ρ ∈ S, iteratedDeriv n (fun z => logDeriv (fac ρ) z) 0 := by
      classical
      -- Each summand is analytic on `K`, hence `C^n` at `0`.
      have hterm_contDiff :
          ∀ ρ ∈ S, ContDiffAt ℂ n (fun z => logDeriv (fac ρ) z) 0 := by
        intro ρ hρ
        have hA : AnalyticAt ℂ (fun z => logDeriv (fac ρ) z) 0 := by
          -- `fac ρ` is differentiable on `K` and nonzero on `K`.
          have hfac_diff : DifferentiableOn ℂ (fac ρ) K :=
            xiPairedFactor_phi_differentiableOn_ball (r := r) hr_lt_one ρ
          have hfac_an : AnalyticAt ℂ (fac ρ) 0 :=
            (hfac_diff.analyticOnNhd Metric.isOpen_ball 0 h0K)
          have hfac_ne : fac ρ 0 ≠ 0 := by
            have hz1 : (0 : ℂ) ≠ (1 : ℂ) := by norm_num
            have hzavoid : ∀ ρ : NontrivialZero, (0 : ℂ) ≠ 1 - 1 / (ρ.val : ℂ) := by
              intro ρ h0eq
              -- `0 = 1 - 1/ρ` would force `ρ = 1`, impossible for nontrivial zeros.
              have : (ρ.val : ℂ) = 1 := by
                have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
                have h : (1 : ℂ) = (1 : ℂ) / ρ.val := sub_eq_zero.mp h0eq.symm
                have : (ρ.val : ℂ) = (1 : ℂ) := by
                  have : (1 : ℂ) * ρ.val = (1 : ℂ) := (eq_div_iff hρ0).1 h
                  simpa using this
                simpa using this
              exact (NontrivialZero.ne_one ρ) this
            exact xiPairedFactor_phi_ne_zero_of_separation (z := (0 : ℂ)) hz1 hzavoid ρ
          unfold logDeriv
          apply AnalyticAt.fun_div
          · exact hfac_an.deriv
          · exact hfac_an
          · exact hfac_ne
        -- Analytic ⇒ smooth.
        simpa [ContDiffAt] using hA.contDiffAt
      -- Now distribute `iteratedDeriv` over the Finset sum.
      simpa using
        (iteratedDeriv_finset_sum
          (T := S) (f := fun ρ z => logDeriv (fac ρ) z) (n := n) hterm_contDiff)
    -- Convert to `deriv^[n]`.
    simpa [iteratedDeriv_eq_iterate] using hsum_iter'
  -- Finish: rewrite each term with `taylorCoeff_xiPairedFactor`.
  have hterm_coeff :
      ∀ ρ, (deriv^[n] (fun z => logDeriv (fac ρ) z)) 0 / n.factorial = liPairedSummand n ρ := by
    intro ρ
    have h' :
        (deriv^[n] (logDeriv (phi (xiPairedFactor ρ)))) 0 / n.factorial =
          liPairedSummand n ρ := by
      simpa [taylorCoeff] using (taylorCoeff_xiPairedFactor (ρ := ρ) (n := n))
    have hphi_fac : phi (xiPairedFactor ρ) = fac ρ := by
      funext z
      rfl
    simpa [hphi_fac] using h'
  calc
    (deriv^[n] (fun z => logDeriv (fun w => ∏ ρ ∈ S, fac ρ w) z)) 0 / n.factorial
        = (deriv^[n] (fun z => ∑ ρ ∈ S, logDeriv (fac ρ) z)) 0 / n.factorial := by
            simp [hEqIter']
    _ = ∑ ρ ∈ S, (deriv^[n] (fun z => logDeriv (fac ρ) z)) 0 / n.factorial := by
          -- distribute division by `n!` and use `hsum_iter`
          simp [hsum_iter, Finset.sum_div]
    _ = ∑ ρ ∈ S, liPairedSummand n ρ := by
          classical
          simp [hterm_coeff]

/-- Paired sum formula via the `ξ²` paired-factor route (M-test + Cauchy). -/
theorem paired_sum_formula_of_mtest_and_cauchy
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hsep : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    (_hpair : ∀ ρ : NontrivialZero, ∃ ρ' : NontrivialZero, ρ'.val = 1 - ρ.val)
    (hhad : ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s) :
    ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero, liPairedSummand n ρ := by
  intro n
  classical
  -- Provide the shifted-product factorization as a typeclass instance for derived lemmas.
  have hhad' : xiFactorizationShiftedProd := by
    simpa [xiFactorizationShiftedProd] using hhad
  let : Fact xiFactorizationShiftedProd := ⟨hhad'⟩
  -- Choose an increasing exhaustion of the zero set by finite subsets.
  obtain ⟨T, monoT, coverT⟩ := exists_increasing_finite_cover_zeros
  -- Choose a separation radius (inside the unit disk) to avoid all points `1 - 1/ρ`.
  obtain ⟨r, hrpos, hr_lt_one, havoid⟩ := hsep
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  have h0K : (0 : ℂ) ∈ K := Metric.mem_ball_self hrpos
  -- The pulled-back paired factor and its logarithmic derivative.
  let fac : NontrivialZero → ℂ → ℂ := fun ρ z => xiPairedFactor ρ (1 / (1 - z))
  let term : NontrivialZero → ℂ → ℂ := fun ρ z => logDeriv (fac ρ) z
  -- A summable majorant for the M-test bounds on `logDeriv (fac ρ)`.
  let A : ℝ := (1 : ℝ) / (1 - r) + (1 / 2 : ℝ)
  let Cfac : ℝ := 4 * A ^ 2
  let C : ℝ := 16 * A * ((1 : ℝ) / (1 - r)) ^ 2
  let u : NontrivialZero → ℝ := fun ρ => C * ((1 : ℝ) / ‖ρ.val‖ ^ 2)
  have hu : Summable u := by
    simpa [u] using (hgenus.mul_left C)
  have hbound :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, ∀ z ∈ K, ‖term ρ z‖ ≤ u ρ :=
    paired_log_deriv_cofinite_bound hgenus r hr_lt_one havoid
  -- Uniform convergence of the partial sums of `term` to the `tsum` on the ball.
  have hsum_unif :
      TendstoUniformlyOn
        (fun t : Finset NontrivialZero => fun z => ∑ ρ ∈ t, term ρ z)
        (fun z => ∑' ρ : NontrivialZero, term ρ z)
        atTop K :=
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hbound
  -- Restrict uniform convergence to the chosen exhaustion `T`.
  have hT_atTop : Filter.Tendsto T atTop (atTop : Filter (Finset NontrivialZero)) := by
    apply Monotone.tendsto_atTop_finset monoT
    intro ρ
    have : ρ ∈ (⋃ n, (T n : Set NontrivialZero)) := by
      simp [coverT]
    simpa [Set.mem_iUnion] using this
  have hsum_unif_T :
      TendstoUniformlyOn
        (fun k : ℕ => fun z => ∑ ρ ∈ T k, term ρ z)
        (fun z => ∑' ρ : NontrivialZero, term ρ z)
        atTop K :=
    hsum_unif.seq_tendstoUniformlyOn T hT_atTop
  -- Identify each partial log-derivative with the corresponding finite sum.
  have h_partial_eq : ∀ k, Set.EqOn
      (fun z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z)
      (fun z => ∑ ρ ∈ T k, term ρ z) K := by
    intro k z hz
    have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
    have hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ) := (havoid z hz).2
    have hfac_ne : ∀ ρ ∈ T k, fac ρ z ≠ 0 := by
      intro ρ hρ
      exact xiPairedFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid ρ
    have hfac_diff : ∀ ρ ∈ T k, DifferentiableAt ℂ (fac ρ) z := by
      intro ρ hρ
      have hWithin : DifferentiableWithinAt ℂ (fac ρ) K z :=
        (xiPairedFactor_phi_differentiableOn_ball (r := r) hr_lt_one ρ) z hz
      exact hWithin.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    -- Use the (mathlib) finite-product log-derivative identity.
    simpa [term, fac, logDeriv_eq_rootLogDeriv] using
      (_root_.logDeriv_fun_prod (s := T k) (f := fac) (x := z) hfac_ne hfac_diff)
  -- The ξ² factorization identifies the limit log-derivative with the `tsum` of `term`.
  have h_limit_eq : Set.EqOn
      (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
      (fun z => ∑' ρ : NontrivialZero, term ρ z) K :=
    paired_log_deriv_limit_eq hgenus hhad r hr_lt_one havoid
  -- Uniform convergence of the partial log-derivatives to the ξ² log-derivative.
  have hunif :
      TendstoUniformlyOn
        (fun k z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z)
        (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
        atTop K := by
    have hunif_term :
        TendstoUniformlyOn (fun k : ℕ => fun z => ∑ ρ ∈ T k, term ρ z)
          (fun z => ∑' ρ : NontrivialZero, term ρ z) atTop K := hsum_unif_T
    have hunif' :
        TendstoUniformlyOn (fun k z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z)
          (fun z => ∑' ρ : NontrivialZero, term ρ z) atTop K := by
      refine hunif_term.congr (Filter.Eventually.of_forall ?_)
      intro k
      exact (h_partial_eq k).symm
    exact hunif'.congr_right h_limit_eq.symm
  -- Analyticity of the partial and limiting log-derivatives on the ball.
  have han_limit :
      AnalyticOnNhd ℂ (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2))) K := by
    intro z hz
    have hz' : ‖z‖ < 1 := by
      have : ‖z‖ < r := by
        -- unfold `K = ball 0 r`
        simpa [K, Metric.mem_ball, dist_eq_norm] using hz
      exact lt_of_lt_of_le this hr_lt_one.le
    have hf_entire : Differentiable ℂ (fun s : ℂ => (riemannXi s) ^ 2) := xi_entire.pow 2
    have hphi_an : AnalyticAt ℂ (phi (fun s : ℂ => (riemannXi s) ^ 2)) z :=
      phi_analytic hf_entire hz'
    have hphi_ne : phi (fun s : ℂ => (riemannXi s) ^ 2) z ≠ 0 := by
      -- If `riemannXi (1/(1-z)) = 0` then `1/(1-z)` equals a nontrivial zero, hence
      -- `z = 1 - 1/ρ`, contradicting separation.
      have hneq : ∀ ρ : NontrivialZero, (1 / (1 - z) : ℂ) ≠ ρ.val := by
        intro ρ hEq
        have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
        have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
        have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
        have : z = 1 - 1 / (ρ.val : ℂ) := by
          -- Solve `1/(1-z) = ρ` for `z`.
          have h1 : (ρ.val : ℂ) * ((1 : ℂ) - z) = 1 := by
            calc
              (ρ.val : ℂ) * ((1 : ℂ) - z) = (1 / (1 - z) : ℂ) * ((1 : ℂ) - z) := by
                    simp [hEq]
              _ = 1 := by field_simp [hzsub]
          have h2 : (1 : ℂ) - z = (1 : ℂ) / ρ.val := by
            apply (eq_div_iff hρ0).2
            simpa [mul_comm] using h1
          calc
            z = 1 - ((1 : ℂ) - z) := by ring
            _ = 1 - 1 / (ρ.val : ℂ) := by simp [h2]
        exact (havoid z hz).2 ρ this
      have hxi_ne : riemannXi (1 / (1 - z) : ℂ) ≠ 0 :=
        xi_nonzero_away_from_nontrivial_zeros (w := (1 / (1 - z) : ℂ)) hneq
      -- `phi f z = (riemannXi (1/(1-z)))^2`.
      simpa [phi] using pow_ne_zero 2 hxi_ne
    -- `logDeriv` is analytic as a quotient of analytic functions, away from zeros.
    have : AnalyticAt ℂ (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2))) z := by
      unfold logDeriv
      apply AnalyticAt.fun_div
      · exact hphi_an.deriv
      · exact hphi_an
      · exact hphi_ne
    exact this
  have han_partial :
      ∀ k, AnalyticOnNhd ℂ (fun z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z) K := by
    intro k z hz
    -- The finite product is complex differentiable on the ball.
    have hprod_diff :
        DifferentiableOn ℂ (fun w : ℂ => ∏ ρ ∈ T k, fac ρ w) K := by
      refine DifferentiableOn.fun_finsetProd (u := T k) ?_
      intro ρ hρ
      exact xiPairedFactor_phi_differentiableOn_ball (r := r) hr_lt_one ρ
    have hprod_an : AnalyticAt ℂ (fun w : ℂ => ∏ ρ ∈ T k, fac ρ w) z :=
      (hprod_diff.analyticOnNhd Metric.isOpen_ball z hz)
    have hprod_ne : (∏ ρ ∈ T k, fac ρ z) ≠ 0 := by
      have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
      have hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ) := (havoid z hz).2
      refine Finset.prod_ne_zero_iff.2 ?_
      intro ρ hρ
      exact xiPairedFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid ρ
    -- `logDeriv` is analytic as a quotient of analytic functions.
    unfold logDeriv
    apply AnalyticAt.fun_div
    · exact hprod_an.deriv
    · exact hprod_an
    · exact hprod_ne
  -- Apply Weierstrass (uniform convergence ⇒ convergence of Taylor coefficients).
  have hcoeff :
      Filter.Tendsto
          (fun k => (deriv^[n] (fun z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z)) 0 / n.factorial)
          atTop
          (𝓝 ((deriv^[n] (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))) 0 / n.factorial)) :=
    deriv_iterate_tendsto_of_uniform
      (f := fun k z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z)
      (g := logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
      (z₀ := (0 : ℂ)) (r := r) (n := n)
      hrpos han_partial han_limit hunif
  -- Identify the coefficient limits with `taylorCoeff` and rewrite the partial coefficients.
  have h_partial_coeff :
      ∀ k,
        (deriv^[n] (fun z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z)) 0 / n.factorial
          = ∑ ρ ∈ T k, liPairedSummand n ρ :=
    fun k => paired_finite_coefficient (T k) n r hrpos hr_lt_one (h_partial_eq k)
  -- The `tsum` limit of the finite sums over `T k`.
  have hsum_paired : Summable (fun ρ : NontrivialZero => liPairedSummand n ρ) :=
    summable_Li_paired_summand_of_genus_one hgenus n
  have hright :
      Filter.Tendsto (fun k => ∑ ρ ∈ T k, liPairedSummand n ρ) atTop
        (𝓝 (∑' ρ : NontrivialZero, liPairedSummand n ρ)) := by
    have h_hassum :
        HasSum (fun ρ : NontrivialZero => liPairedSummand n ρ)
          (∑' ρ : NontrivialZero, liPairedSummand n ρ) :=
      Summable.hasSum hsum_paired
    exact h_hassum.comp hT_atTop
  -- Conclude `taylorCoeff (ξ^2)` equals the paired `tsum` by uniqueness of limits.
  have hleft' :
      Filter.Tendsto (fun k => ∑ ρ ∈ T k, liPairedSummand n ρ) atTop
        (𝓝 (taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n)) := by
    -- Rewrite the sequence using `h_partial_coeff` and identify the limit as `taylorCoeff`.
    have hcoeff' :
        Filter.Tendsto
            (fun k =>
              (deriv^[n] (fun z => logDeriv (fun w => ∏ ρ ∈ T k, fac ρ w) z)) 0 / n.factorial)
            atTop
            (𝓝 (taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n)) := by
      -- `taylorCoeff` is definitional here.
      simpa [taylorCoeff] using hcoeff
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall h_partial_coeff) hcoeff'
  have h_xi_sq :
      taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n = ∑' ρ : NontrivialZero, liPairedSummand n ρ :=
    tendsto_nhds_unique hleft' hright
  -- Convert from ξ² back to ξ: `taylorCoeff (ξ^2) = 2 * taylorCoeff ξ`.
  have hsq := taylorCoeff_xi_sq (n := n)
  -- Solve for `taylorCoeff ξ`.
  calc
    taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * (taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n) := by
            -- multiply the identity `taylorCoeff (ξ^2) = 2 * taylorCoeff ξ` by `2⁻¹`
            have h' :
                (2 : ℂ) * taylorCoeff riemannXi n =
                  taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n := by
              simpa [mul_comm] using hsq.symm
            -- `a = 2⁻¹ * (2 * a)`
            calc
              taylorCoeff riemannXi n
                  = (2⁻¹ : ℂ) * ((2 : ℂ) * taylorCoeff riemannXi n) := by
                      simp
              _ = (2⁻¹ : ℂ) * taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n := by
                      simp [h']
    _ = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero, liPairedSummand n ρ := by
          simp [h_xi_sq]

private theorem weighted_paired_factor_cofinite_bound
    (hsigma_genus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2))
    (r : ℝ) (hr_lt_one : r < 1)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    : ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖xiPairedLinearFactor i.1 (1 / (1 - z)) - 1‖ ≤
        (2 * ((1 : ℝ) / (1 - r)) ^ 2) * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let fac : XiZeroWithMultiplicity → ℂ → ℂ :=
    fun i z => xiPairedLinearFactor i.1 (1 / (1 - z))
  let Cfac : ℝ := 2 * ((1 : ℝ) / (1 - r)) ^ 2
  have hlarge :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, (2 : ℝ) ≤ ‖i.1.val‖ :=
    eventually_le_norm_of_summable_inv_norm_sq_withMultiplicity hsigma_genus (R := 2) (by norm_num)
  have hfac_sub_bound :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ∀ z ∈ K,
        ‖fac i z - (1 : ℂ)‖ ≤ Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
    filter_upwards [hlarge] with i hi z hz
    have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
    have h_inv_bound : ‖(1 : ℂ) / ((1 : ℂ) - z)‖ ≤ (1 : ℝ) / (1 - r) := by
      have hz_norm : ‖z‖ < r := by simpa [K, Metric.mem_ball, dist_eq_norm] using hz
      have h1 : (1 - r) ≤ ‖(1 : ℂ) - z‖ := by
        have htmp : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
          simpa using (norm_sub_norm_le (1 : ℂ) z)
        have hle : (1 : ℝ) - r ≤ (1 : ℝ) - ‖z‖ := by linarith [hz_norm.le]
        exact le_trans hle htmp
      have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
      have hrecip : (1 : ℝ) / ‖(1 : ℂ) - z‖ ≤ (1 : ℝ) / ((1 : ℝ) - r) :=
        one_div_le_one_div_of_le hpos h1
      simpa [div_eq_mul_inv] using hrecip
    have h_inv_sq : ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ ≤ ((1 : ℝ) / (1 - r)) ^ 2 := by
      have : ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ = ‖(1 : ℂ) / ((1 : ℂ) - z)‖ ^ 2 := by
        simp [pow_two]
      rw [this]
      have hnonneg : 0 ≤ ‖(1 : ℂ) / ((1 : ℂ) - z)‖ := by positivity
      have hnonneg' : 0 ≤ (1 : ℝ) / (1 - r) := by
        have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
        exact div_nonneg (by norm_num) hpos.le
      simpa [pow_two] using mul_le_mul h_inv_bound h_inv_bound hnonneg hnonneg'
    have hz_norm_le_one : ‖z‖ ≤ (1 : ℝ) := by
      have hz_norm : ‖z‖ < r := by simpa [K, Metric.mem_ball, dist_eq_norm] using hz
      linarith [hr_lt_one]
    have hprod_bound := inv_norm_mul_pairedZero_le_of_two_le_norm i.1 hi
    calc
      ‖fac i z - (1 : ℂ)‖
          = ‖z / ((i.1.val * (pairedZero i.1).val) * ((1 : ℂ) - z) ^ 2)‖ := by
              rw [xiPairedLinearFactor_phi_sub_one hz1 i.1]
      _ = ‖z‖ * ((1 : ℝ) / ‖(i.1.val : ℂ) * (pairedZero i.1).val‖) *
            ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ := by
              rw [norm_div, norm_mul, norm_div]
              have hmul_ne : ‖(i.1.val : ℂ) * (pairedZero i.1).val‖ ≠ 0 := by
                refine norm_ne_zero_iff.2 ?_
                exact mul_ne_zero
                  (NontrivialZero.ne_zero i.1) (NontrivialZero.ne_zero (pairedZero i.1))
              have hpow_ne : ‖((1 : ℂ) - z) ^ 2‖ ≠ 0 := by
                refine norm_ne_zero_iff.2 ?_
                refine pow_ne_zero 2 ?_
                exact sub_ne_zero.mpr hz1.symm
              field_simp [hmul_ne, hpow_ne]
              simp
      _ ≤ ‖z‖ * ((2 : ℝ) * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) *
            ((1 : ℝ) / (1 - r)) ^ 2 := by
              gcongr
      _ ≤ (1 : ℝ) * ((2 : ℝ) * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) *
            ((1 : ℝ) / (1 - r)) ^ 2 := by
              gcongr
      _ = Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
            simp [Cfac]
            ring
  exact hfac_sub_bound

private theorem weighted_paired_log_deriv_cofinite_bound
    (hsigma_genus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2))
    (r : ℝ) (hr_lt_one : r < 1)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    : ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖logDeriv (fun w => xiPairedLinearFactor i.1 (1 / (1 - w))) z‖ ≤
        (4 * (2 * ((1 : ℝ) / (1 - r)) + 1) * ((1 : ℝ) / (1 - r)) ^ 2) *
          ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let fac : XiZeroWithMultiplicity → ℂ → ℂ :=
    fun i z => xiPairedLinearFactor i.1 (1 / (1 - z))
  let term : XiZeroWithMultiplicity → ℂ → ℂ := fun i z => logDeriv (fac i) z
  let B : ℝ := 2 * ((1 : ℝ) / (1 - r)) + 1
  let Cfac : ℝ := 2 * ((1 : ℝ) / (1 - r)) ^ 2
  let C : ℝ := 4 * B * ((1 : ℝ) / (1 - r)) ^ 2
  let u : XiZeroWithMultiplicity → ℝ := fun i => C * ((1 : ℝ) / ‖i.1.val‖ ^ 2)
  have hlarge :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, (2 : ℝ) ≤ ‖i.1.val‖ :=
    eventually_le_norm_of_summable_inv_norm_sq_withMultiplicity hsigma_genus (R := 2) (by norm_num)
  have hfac_sub_bound :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ∀ z ∈ K,
        ‖fac i z - (1 : ℂ)‖ ≤ Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2) :=
    weighted_paired_factor_cofinite_bound hsigma_genus r hr_lt_one havoid
  have hsmallCfac :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite,
        Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2) ≤ (1 / 2 : ℝ) := by
    have ht :
        Filter.Tendsto (fun i : XiZeroWithMultiplicity => Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2))
          Filter.cofinite (𝓝 (0 : ℝ)) :=
      (hsigma_genus.mul_left Cfac).tendsto_cofinite_zero
    exact ht.eventually_le_const (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
  have hbound :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ∀ z ∈ K, ‖term i z‖ ≤ u i := by
    filter_upwards [hlarge, hsmallCfac, hfac_sub_bound] with i hi hsmall hfac_sub z hz
    have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
    have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
    have h_inv_bound : ‖(1 : ℂ) / ((1 : ℂ) - z)‖ ≤ (1 : ℝ) / (1 - r) := by
      have hz_norm : ‖z‖ < r := by simpa [K, Metric.mem_ball, dist_eq_norm] using hz
      have h1 : (1 - r) ≤ ‖(1 : ℂ) - z‖ := by
        have htmp : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
          simpa using (norm_sub_norm_le (1 : ℂ) z)
        have hle : (1 : ℝ) - r ≤ (1 : ℝ) - ‖z‖ := by linarith [hz_norm.le]
        exact le_trans hle htmp
      have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
      have hrecip : (1 : ℝ) / ‖(1 : ℂ) - z‖ ≤ (1 : ℝ) / ((1 : ℝ) - r) :=
        one_div_le_one_div_of_le hpos h1
      simpa [div_eq_mul_inv] using hrecip
    have h_inv_sq : ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ ≤ ((1 : ℝ) / (1 - r)) ^ 2 := by
      have : ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ = ‖(1 : ℂ) / ((1 : ℂ) - z)‖ ^ 2 := by
        simp [pow_two]
      rw [this]
      have hnonneg : 0 ≤ ‖(1 : ℂ) / ((1 : ℂ) - z)‖ := by positivity
      have hnonneg' : 0 ≤ (1 : ℝ) / (1 - r) := by
        have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
        exact div_nonneg (by norm_num) hpos.le
      simpa [pow_two] using mul_le_mul h_inv_bound h_inv_bound hnonneg hnonneg'
    have hB :
        ‖(2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z)) - (1 : ℂ)‖ ≤ B := by
      have htri :
          ‖(2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z)) - (1 : ℂ)‖
            ≤ ‖(2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z))‖ + ‖(1 : ℂ)‖ := by
              simpa [sub_eq_add_neg] using
                (norm_add_le ((2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z))) (-(1 : ℂ)))
      have htwo : ‖(2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z))‖ =
          (2 : ℝ) * ‖(1 : ℂ) / ((1 : ℂ) - z)‖ := by
        simp
      have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by norm_num
      dsimp [B]
      rw [htwo, hone] at htri
      linarith
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
      positivity
    have hfac_sub' : ‖fac i z - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) := le_trans (hfac_sub z hz) hsmall
    have hfac_norm : (1 / 2 : ℝ) ≤ ‖fac i z‖ := by
      have htri : (1 : ℝ) - ‖fac i z‖ ≤ ‖(1 : ℂ) - fac i z‖ := by
        simpa [norm_one] using (norm_sub_norm_le (1 : ℂ) (fac i z))
      have htri' : (1 : ℝ) - ‖fac i z‖ ≤ ‖fac i z - (1 : ℂ)‖ := by
        simpa [norm_sub_rev] using htri
      have : (1 : ℝ) - ‖fac i z‖ ≤ (1 / 2 : ℝ) := le_trans htri' hfac_sub'
      linarith
    have hdf :
        deriv (fac i) z =
          (deriv (xiPairedLinearFactor i.1) ((1 : ℂ) / ((1 : ℂ) - z))) *
            deriv (fun w : ℂ => (1 : ℂ) / ((1 : ℂ) - w)) z := by
      have h_outer : DifferentiableAt ℂ (xiPairedLinearFactor i.1) ((1 : ℂ) / ((1 : ℂ) - z)) :=
        (xiPairedLinearFactor_differentiable i.1).differentiableAt
      have h_inner : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) / ((1 : ℂ) - w)) z := by
        apply DifferentiableAt.div
        · exact differentiableAt_const (c := (1 : ℂ))
        · exact (DifferentiableAt.sub (differentiableAt_const (c := (1 : ℂ))) differentiableAt_id)
        · exact hzsub
      simpa [fac, Function.comp_def] using (deriv_comp z h_outer h_inner)
    have hderiv_bound :
        ‖deriv (fac i) z‖ ≤
          (2 : ℝ) * B * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
      rw [hdf, deriv_xiPairedLinearFactor, deriv_one_div_one_sub hzsub]
      calc
        ‖(((2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z)) - 1) /
              (i.1.val * (pairedZero i.1).val)) *
            ((1 : ℂ) / ((1 : ℂ) - z) ^ 2)‖
            =
          ‖(((2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z)) - 1) /
              (i.1.val * (pairedZero i.1).val))‖ *
            ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ := by
              simp
        _ = (‖(2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z)) - 1‖ *
              ((1 : ℝ) / ‖(i.1.val : ℂ) * (pairedZero i.1).val‖)) *
            ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖ := by
              rw [norm_div]
              ring
        _ ≤ (B * ((2 : ℝ) * ((1 : ℝ) / ‖i.1.val‖ ^ 2))) * ((1 : ℝ) / (1 - r)) ^ 2 := by
              have hprod_nonneg : 0 ≤ B * ((2 : ℝ) * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) := by
                exact mul_nonneg hB_nonneg (by positivity)
              have h_inner :
                  (‖(2 : ℂ) * ((1 : ℂ) / ((1 : ℂ) - z)) - 1‖ *
                      ((1 : ℝ) / ‖(i.1.val : ℂ) * (pairedZero i.1).val‖)) *
                      ‖(1 : ℂ) / ((1 : ℂ) - z) ^ 2‖
                    ≤ (B * ((2 : ℝ) * ((1 : ℝ) / ‖i.1.val‖ ^ 2))) *
                        ((1 : ℝ) / (1 - r)) ^ 2 := by
                refine mul_le_mul ?_ h_inv_sq (by positivity) hprod_nonneg
                refine mul_le_mul hB (inv_norm_mul_pairedZero_le_of_two_le_norm i.1 hi)
                  (by positivity) hB_nonneg
              exact h_inner
        _ = (2 : ℝ) * B * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
              ring
    have hinv_fac : ‖(fac i z)⁻¹‖ ≤ (2 : ℝ) := by
      have hpos_half : 0 < (1 / 2 : ℝ) := by norm_num
      have h := one_div_le_one_div_of_le hpos_half hfac_norm
      simpa [one_div] using (show (1 : ℝ) / ‖fac i z‖ ≤ (2 : ℝ) from by simpa using h)
    have : ‖term i z‖ ≤ u i := by
      unfold term logDeriv
      have hmul :
          ‖deriv (fac i) z / fac i z‖ = ‖deriv (fac i) z‖ * ‖(fac i z)⁻¹‖ := by
        simp [div_eq_mul_inv]
      have hbound_nonneg :
          0 ≤ (2 : ℝ) * B * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
        dsimp [B]
        have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
        positivity
      have hprod :
          ‖deriv (fac i) z‖ * ‖(fac i z)⁻¹‖ ≤
            ((2 : ℝ) * B * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) * (2 : ℝ) :=
        mul_le_mul hderiv_bound hinv_fac (by positivity) hbound_nonneg
      calc
        ‖deriv (fac i) z / fac i z‖
            = ‖deriv (fac i) z‖ * ‖(fac i z)⁻¹‖ := hmul
        _ ≤ ((2 : ℝ) * B * ((1 : ℝ) / (1 - r)) ^ 2 * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) * (2 : ℝ) := hprod
        _ = u i := by
              simp [u, C]
              ring
    simpa using this
  exact hbound

private theorem weighted_paired_log_deriv_limit_eq
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : xiFactorizationProdWithMultiplicity) (r : ℝ) (hr_lt_one : r < 1)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    : Set.EqOn (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
      (fun z => ∑' i : XiZeroWithMultiplicity,
        logDeriv (fun w => xiPairedLinearFactor i.1 (1 / (1 - w))) z)
      (Metric.ball (0 : ℂ) r) := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let fac : XiZeroWithMultiplicity → ℂ → ℂ :=
    fun i z => xiPairedLinearFactor i.1 (1 / (1 - z))
  let term : XiZeroWithMultiplicity → ℂ → ℂ := fun i z => logDeriv (fac i) z
  let B : ℝ := 2 * ((1 : ℝ) / (1 - r)) + 1
  let Cfac : ℝ := 2 * ((1 : ℝ) / (1 - r)) ^ 2
  let C : ℝ := 4 * B * ((1 : ℝ) / (1 - r)) ^ 2
  let u : XiZeroWithMultiplicity → ℝ := fun i => C * ((1 : ℝ) / ‖i.1.val‖ ^ 2)
  have hsigma_genus := summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus hgenus
  have hu : Summable u := hsigma_genus.mul_left C
  have hbound := weighted_paired_log_deriv_cofinite_bound hsigma_genus r hr_lt_one havoid
  have hfac_sub_bound := weighted_paired_factor_cofinite_bound hsigma_genus r hr_lt_one havoid
  intro z hz
  have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
  have hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ) := (havoid z hz).2
  obtain ⟨b₂, hξ₂⟩ :=
    xi_sq_factorization_pairedLinear_withMultiplicity_of_weighted_genus hgenus hhad
  have hφ :
      (fun w => (riemannXi (1 / (1 - w))) ^ 2)
        = fun w => Complex.exp b₂ * ∏' i : XiZeroWithMultiplicity, fac i w := by
    funext w
    simpa [fac] using (hξ₂ (1 / (1 - w)))
  have h_drop :
      logDeriv (fun w => Complex.exp b₂ * (∏' i : XiZeroWithMultiplicity, fac i w)) z
        = logDeriv (fun w => ∏' i : XiZeroWithMultiplicity, fac i w) z := by
    simpa [logDeriv, _root_.logDeriv, _root_.logDeriv_apply] using
      (_root_.logDeriv_const_mul (x := z) (a := Complex.exp b₂)
        (f := fun w => ∏' i : XiZeroWithMultiplicity, fac i w) (ha := Complex.exp_ne_zero b₂))
  have hm : Summable (fun i : XiZeroWithMultiplicity => logDeriv (fac i) z) := by
    have hbound_z :
        ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ‖term i z‖ ≤ u i := by
      filter_upwards [hbound] with i hi using hi z hz
    exact Summable.of_norm_bounded_eventually hu hbound_z
  have hf_ne : ∀ i : XiZeroWithMultiplicity, fac i z ≠ 0 :=
    fun i => xiPairedLinearFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid i.1
  have hd : ∀ i : XiZeroWithMultiplicity, DifferentiableOn ℂ (fac i) K := fun i =>
    xiPairedLinearFactor_phi_differentiableOn_ball (r := r) hr_lt_one i.1
  have htend : MultipliableLocallyUniformlyOn fac K := by
    let g : XiZeroWithMultiplicity → ℂ → ℂ := fun i w => fac i w - 1
    have hu' : Summable (fun i : XiZeroWithMultiplicity => Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) := by
      simpa [Cfac] using (hsigma_genus.mul_left Cfac)
    have hbound_g :
        ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ∀ w ∈ K,
          ‖g i w‖ ≤ Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
      filter_upwards [hfac_sub_bound] with i hi w hw
      exact hi w hw
    have hcts : ∀ i : XiZeroWithMultiplicity, ContinuousOn (g i) K := by
      intro i
      have hdiff : DifferentiableOn ℂ (fac i) K :=
        xiPairedLinearFactor_phi_differentiableOn_ball (r := r) hr_lt_one i.1
      simpa [g, Pi.sub_def] using (hdiff.continuousOn.sub continuousOn_const)
    have ht : MultipliableLocallyUniformlyOn (fun i w ↦ (1 : ℂ) + g i w) K :=
      Summable.multipliableLocallyUniformlyOn_one_add
        (K := K) Metric.isOpen_ball hu' hbound_g hcts
    simpa [g, fac, sub_eq_add_neg] using ht
  have hnez : (∏' i : XiZeroWithMultiplicity, fac i z) ≠ 0 := by
    let g : XiZeroWithMultiplicity → ℂ := fun i => fac i z - 1
    have hdom :
        Summable (fun i : XiZeroWithMultiplicity => Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) := by
      simpa [Cfac] using (hsigma_genus.mul_left Cfac)
    have hsum_g : Summable g := by
      have hbound_z :
          ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite,
            ‖g i‖ ≤ Cfac * ((1 : ℝ) / ‖i.1.val‖ ^ 2) := by
        filter_upwards [hfac_sub_bound] with i hi
        exact hi z hz
      exact Summable.of_norm_bounded_eventually hdom hbound_z
    have hterm_ne : ∀ i : XiZeroWithMultiplicity, (1 : ℂ) + g i ≠ 0 := by
      intro i
      have hne : fac i z ≠ 0 := by
        simpa [fac] using
          xiPairedLinearFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid i.1
      simpa [g, sub_eq_add_neg] using hne
    have hprod_ne :
        (∏' i : XiZeroWithMultiplicity, ((1 : ℂ) + g i)) ≠ 0 :=
      _root_.tprod_one_add_ne_zero_of_summable (ι := XiZeroWithMultiplicity) (R := ℂ)
        (f := g) (hf := hterm_ne) (hu := hsum_g.norm)
    have hprod_eq :
        (∏' i : XiZeroWithMultiplicity, ((1 : ℂ) + g i))
          = ∏' i : XiZeroWithMultiplicity, fac i z := by
      refine tprod_congr ?_
      intro i
      simp [g, sub_eq_add_neg]
    simpa [hprod_eq] using hprod_ne
  have h_log :
      logDeriv (fun w => ∏' i : XiZeroWithMultiplicity, fac i w) z
        = ∑' i : XiZeroWithMultiplicity, logDeriv (fac i) z := by
    let s : Set ℂ := K
    have hs : IsOpen s := Metric.isOpen_ball
    simpa [s, logDeriv_eq_rootLogDeriv] using
      (logDeriv_tprod_eq_tsum
        (ι := XiZeroWithMultiplicity) (s := s) hs (x := z) (hx := hz) (f := fac)
        (hf := fun i => hf_ne i)
        (hd := fun i => hd i)
        (hm := hm) (htend := htend) (hnez := hnez))
  calc
    logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)) z
        =
          logDeriv
            (fun w => Complex.exp b₂ * (∏' i : XiZeroWithMultiplicity, fac i w)) z := by
            have hphi_def :
                phi (fun s : ℂ => (riemannXi s) ^ 2) =
                  fun w => (riemannXi (1 / (1 - w))) ^ 2 := by
              funext w
              rfl
            calc
              logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)) z
                  = logDeriv (fun w => (riemannXi (1 / (1 - w))) ^ 2) z := by
                      simp [hphi_def]
              _ =
                  logDeriv
                    (fun w => Complex.exp b₂ * (∏' i : XiZeroWithMultiplicity, fac i w)) z := by
                      have := congrArg (fun F : ℂ → ℂ => logDeriv F z) hφ
                      simpa [one_div] using this
    _ = logDeriv (fun w => ∏' i : XiZeroWithMultiplicity, fac i w) z := h_drop
    _ = ∑' i : XiZeroWithMultiplicity, term i z := by
          simpa [term] using h_log

private theorem xi_sq_log_deriv_analytic_on_separated_ball
    (r : ℝ) (hr_lt_one : r < 1)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    : AnalyticOnNhd ℂ (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
      (Metric.ball (0 : ℂ) r) := by
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  intro z hz
  have hz' : ‖z‖ < 1 := by
    have : ‖z‖ < r := by
      simpa [K, Metric.mem_ball, dist_eq_norm] using hz
    exact lt_of_lt_of_le this hr_lt_one.le
  have hf_entire : Differentiable ℂ (fun s : ℂ => (riemannXi s) ^ 2) := xi_entire.pow 2
  have hphi_an : AnalyticAt ℂ (phi (fun s : ℂ => (riemannXi s) ^ 2)) z :=
    phi_analytic hf_entire hz'
  have hphi_ne : phi (fun s : ℂ => (riemannXi s) ^ 2) z ≠ 0 := by
    have hneq : ∀ ρ : NontrivialZero, (1 / (1 - z) : ℂ) ≠ ρ.val := by
      intro ρ hEq
      have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
      have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
      have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
      have : z = 1 - 1 / (ρ.val : ℂ) := by
        have h1 : (ρ.val : ℂ) * ((1 : ℂ) - z) = 1 := by
          calc
            (ρ.val : ℂ) * ((1 : ℂ) - z) = (1 / (1 - z) : ℂ) * ((1 : ℂ) - z) := by
                  simp [hEq]
            _ = 1 := by field_simp [hzsub]
        have h2 : (1 : ℂ) - z = (1 : ℂ) / ρ.val := by
          apply (eq_div_iff hρ0).2
          simpa [mul_comm] using h1
        calc
          z = 1 - ((1 : ℂ) - z) := by ring
          _ = 1 - 1 / (ρ.val : ℂ) := by simp [h2]
      exact (havoid z hz).2 ρ this
    have hxi_ne : riemannXi (1 / (1 - z) : ℂ) ≠ 0 :=
      xi_nonzero_away_from_nontrivial_zeros (w := (1 / (1 - z) : ℂ)) hneq
    simpa [phi] using pow_ne_zero 2 hxi_ne
  have : AnalyticAt ℂ (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2))) z := by
    unfold logDeriv
    apply AnalyticAt.fun_div
    · exact hphi_an.deriv
    · exact hphi_an
    · exact hphi_ne
  exact this

private theorem weighted_paired_finite_coefficient
    (S : Finset XiZeroWithMultiplicity) (n : ℕ) (r : ℝ) (hrpos : 0 < r) (hr_lt_one : r < 1)
    (hpartial : Set.EqOn
      (fun z => logDeriv (fun w => ∏ i ∈ S, xiPairedLinearFactor i.1 (1 / (1 - w))) z)
      (fun z => ∑ i ∈ S, logDeriv (fun w => xiPairedLinearFactor i.1 (1 / (1 - w))) z)
      (Metric.ball (0 : ℂ) r)) :
    (deriv^[n] (fun z => logDeriv (fun w => ∏ i ∈ S, xiPairedLinearFactor i.1 (1 / (1 - w))) z)) 0 /
      n.factorial = ∑ i ∈ S, liPairedSummand n i.1 := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let fac : XiZeroWithMultiplicity → ℂ → ℂ :=
    fun i z => xiPairedLinearFactor i.1 (1 / (1 - z))
  let term : XiZeroWithMultiplicity → ℂ → ℂ := fun i z => logDeriv (fac i) z
  have h0K : (0 : ℂ) ∈ K := Metric.mem_ball_self hrpos
  have hEqOn :
      Set.EqOn
          (fun z => logDeriv (fun w => ∏ i ∈ S, fac i w) z)
          (fun z => ∑ i ∈ S, logDeriv (fac i) z) K := by
    intro z hz
    exact hpartial hz
  have hsopen : IsOpen K := Metric.isOpen_ball
  have hEqIter : iteratedDeriv n (fun z => logDeriv (fun w => ∏ i ∈ S, fac i w) z) 0
      = iteratedDeriv n (fun z => ∑ i ∈ S, logDeriv (fac i) z) 0 := by
    have hEqOn' :=
      Set.EqOn.iteratedDeriv_of_isOpen
        (f := fun z => logDeriv (fun w => ∏ i ∈ S, fac i w) z)
        (g := fun z => ∑ i ∈ S, logDeriv (fac i) z)
        (s := K) hEqOn hsopen n
    exact hEqOn' h0K
  have hEqIter' :
      (deriv^[n] (fun z => logDeriv (fun w => ∏ i ∈ S, fac i w) z)) 0
        =
      (deriv^[n] (fun z => ∑ i ∈ S, logDeriv (fac i) z)) 0 := by
    simpa [iteratedDeriv_eq_iterate] using hEqIter
  have hsum_iter :
      (deriv^[n] (fun z => ∑ i ∈ S, logDeriv (fac i) z)) 0
        =
      ∑ i ∈ S, (deriv^[n] (fun z => logDeriv (fac i) z)) 0 := by
    have hsum_iter' :
        iteratedDeriv n (fun z => ∑ i ∈ S, logDeriv (fac i) z) 0
          =
        ∑ i ∈ S, iteratedDeriv n (fun z => logDeriv (fac i) z) 0 := by
      classical
      have hterm_contDiff :
          ∀ i ∈ S, ContDiffAt ℂ n (fun z => logDeriv (fac i) z) 0 := by
        intro i hi
        have hA : AnalyticAt ℂ (fun z => logDeriv (fac i) z) 0 := by
          have hfac_diff : DifferentiableOn ℂ (fac i) K :=
            xiPairedLinearFactor_phi_differentiableOn_ball (r := r) hr_lt_one i.1
          have hfac_an : AnalyticAt ℂ (fac i) 0 :=
            (hfac_diff.analyticOnNhd Metric.isOpen_ball 0 h0K)
          have hfac_ne : fac i 0 ≠ 0 := by
            have hz1 : (0 : ℂ) ≠ (1 : ℂ) := by norm_num
            have hzavoid : ∀ ρ : NontrivialZero, (0 : ℂ) ≠ 1 - 1 / (ρ.val : ℂ) := by
              intro ρ h0eq
              have : (ρ.val : ℂ) = 1 := by
                have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
                have h : (1 : ℂ) = (1 : ℂ) / ρ.val := sub_eq_zero.mp h0eq.symm
                have : (ρ.val : ℂ) = (1 : ℂ) := by
                  have : (1 : ℂ) * ρ.val = (1 : ℂ) := (eq_div_iff hρ0).1 h
                  simpa using this
                simpa using this
              exact (NontrivialZero.ne_one ρ) this
            exact xiPairedLinearFactor_phi_ne_zero_of_separation (z := (0 : ℂ)) hz1 hzavoid i.1
          unfold logDeriv
          apply AnalyticAt.fun_div
          · exact hfac_an.deriv
          · exact hfac_an
          · exact hfac_ne
        simpa [ContDiffAt] using hA.contDiffAt
      simpa using
        (iteratedDeriv_finset_sum (T := S) (f := fun i z => logDeriv (fac i) z) (n := n)
          hterm_contDiff)
    simpa [iteratedDeriv_eq_iterate] using hsum_iter'
  have hterm_coeff :
      ∀ i : XiZeroWithMultiplicity,
        (deriv^[n] (fun z => logDeriv (fac i) z)) 0 / n.factorial = liPairedSummand n i.1 := by
    intro i
    have h' :
        (deriv^[n] (logDeriv (phi (xiPairedLinearFactor i.1)))) 0 / n.factorial
          = liPairedSummand n i.1 := by
      simpa [taylorCoeff] using (taylorCoeff_xiPairedLinearFactor (ρ := i.1) (n := n))
    have hphi_fac : phi (xiPairedLinearFactor i.1) = fac i := by
      funext z
      rfl
    simpa [hphi_fac] using h'
  calc
    (deriv^[n] (fun z => logDeriv (fun w => ∏ i ∈ S, fac i w) z)) 0 / n.factorial
        = (deriv^[n] (fun z => ∑ i ∈ S, logDeriv (fac i) z)) 0 / n.factorial := by
            simp [hEqIter']
    _ = ∑ i ∈ S, (deriv^[n] (fun z => logDeriv (fac i) z)) 0 / n.factorial := by
          simp [hsum_iter, Finset.sum_div]
    _ = ∑ i ∈ S, liPairedSummand n i.1 := by
          classical
          simp [hterm_coeff]

/-- Weighted paired sum formula via the multiplicity-aware paired-linear-factor route. -/
theorem weighted_paired_sum_formula_of_mtest_and_cauchy
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (hsep : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1 / ρ.val))
    (hhad : xiFactorizationProdWithMultiplicity) :
    ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
            (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ := by
  intro n
  classical
  have hsigma_genus := summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus hgenus
  obtain ⟨T, monoT, coverT⟩ := exists_increasing_finite_cover_zeros_with_multiplicity
  obtain ⟨r, hrpos, hr_lt_one, havoid⟩ := hsep
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  have h0K : (0 : ℂ) ∈ K := Metric.mem_ball_self hrpos
  let fac : XiZeroWithMultiplicity → ℂ → ℂ :=
    fun i z => xiPairedLinearFactor i.1 (1 / (1 - z))
  let term : XiZeroWithMultiplicity → ℂ → ℂ := fun i z => logDeriv (fac i) z
  let B : ℝ := 2 * ((1 : ℝ) / (1 - r)) + 1
  let Cfac : ℝ := 2 * ((1 : ℝ) / (1 - r)) ^ 2
  let C : ℝ := 4 * B * ((1 : ℝ) / (1 - r)) ^ 2
  let u : XiZeroWithMultiplicity → ℝ := fun i => C * ((1 : ℝ) / ‖i.1.val‖ ^ 2)
  have hu : Summable u := by
    simpa [u] using (hsigma_genus.mul_left C)
  have hbound :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, ∀ z ∈ K, ‖term i z‖ ≤ u i :=
    weighted_paired_log_deriv_cofinite_bound hsigma_genus r hr_lt_one havoid
  have hsum_unif :
      TendstoUniformlyOn
        (fun t : Finset XiZeroWithMultiplicity => fun z => ∑ i ∈ t, term i z)
        (fun z => ∑' i : XiZeroWithMultiplicity, term i z)
        atTop K :=
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hbound
  have hT_atTop :
      Filter.Tendsto T atTop (atTop : Filter (Finset XiZeroWithMultiplicity)) := by
    apply Monotone.tendsto_atTop_finset monoT
    intro i
    have : i ∈ (⋃ n, (T n : Set XiZeroWithMultiplicity)) := by
      simp [coverT]
    simpa [Set.mem_iUnion] using this
  have hsum_unif_T :
      TendstoUniformlyOn
        (fun k : ℕ => fun z => ∑ i ∈ T k, term i z)
        (fun z => ∑' i : XiZeroWithMultiplicity, term i z)
        atTop K :=
    hsum_unif.seq_tendstoUniformlyOn T hT_atTop
  have h_partial_eq : ∀ k, Set.EqOn
      (fun z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z)
      (fun z => ∑ i ∈ T k, term i z) K := by
    intro k z hz
    have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
    have hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ) := (havoid z hz).2
    have hfac_ne : ∀ i ∈ T k, fac i z ≠ 0 := by
      intro i hi
      exact xiPairedLinearFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid i.1
    have hfac_diff : ∀ i ∈ T k, DifferentiableAt ℂ (fac i) z := by
      intro i hi
      have hWithin : DifferentiableWithinAt ℂ (fac i) K z :=
        (xiPairedLinearFactor_phi_differentiableOn_ball (r := r) hr_lt_one i.1) z hz
      exact hWithin.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    simpa [term, fac, logDeriv_eq_rootLogDeriv] using
      (_root_.logDeriv_fun_prod (s := T k) (f := fac) (x := z) hfac_ne hfac_diff)
  have h_limit_eq : Set.EqOn
      (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
      (fun z => ∑' i : XiZeroWithMultiplicity, term i z) K :=
    weighted_paired_log_deriv_limit_eq hgenus hhad r hr_lt_one havoid
  have hunif :
      TendstoUniformlyOn
        (fun k z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z)
        (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
        atTop K := by
    have hunif_term :
        TendstoUniformlyOn (fun k : ℕ => fun z => ∑ i ∈ T k, term i z)
          (fun z => ∑' i : XiZeroWithMultiplicity, term i z) atTop K := hsum_unif_T
    have hunif' :
        TendstoUniformlyOn (fun k z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z)
          (fun z => ∑' i : XiZeroWithMultiplicity, term i z) atTop K := by
      refine hunif_term.congr (Filter.Eventually.of_forall ?_)
      intro k
      exact (h_partial_eq k).symm
    exact hunif'.congr_right h_limit_eq.symm
  have han_limit :
      AnalyticOnNhd ℂ (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2))) K :=
    xi_sq_log_deriv_analytic_on_separated_ball r hr_lt_one havoid
  have han_partial :
      ∀ k, AnalyticOnNhd ℂ (fun z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z) K := by
    intro k z hz
    have hprod_diff :
        DifferentiableOn ℂ (fun w : ℂ => ∏ i ∈ T k, fac i w) K := by
      refine DifferentiableOn.fun_finsetProd (u := T k) ?_
      intro i hi
      exact xiPairedLinearFactor_phi_differentiableOn_ball (r := r) hr_lt_one i.1
    have hprod_an : AnalyticAt ℂ (fun w : ℂ => ∏ i ∈ T k, fac i w) z :=
      (hprod_diff.analyticOnNhd Metric.isOpen_ball z hz)
    have hprod_ne : (∏ i ∈ T k, fac i z) ≠ 0 := by
      have hz1 : z ≠ (1 : ℂ) := (havoid z hz).1
      have hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ) := (havoid z hz).2
      refine Finset.prod_ne_zero_iff.2 ?_
      intro i hi
      exact xiPairedLinearFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid i.1
    unfold logDeriv
    apply AnalyticAt.fun_div
    · exact hprod_an.deriv
    · exact hprod_an
    · exact hprod_ne
  have hcoeff :
      Filter.Tendsto
          (fun k => (deriv^[n] (fun z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z)) 0 / n.factorial)
          atTop
          (𝓝 ((deriv^[n] (logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))) 0 / n.factorial)) :=
    deriv_iterate_tendsto_of_uniform
      (f := fun k z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z)
      (g := logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2)))
      (z₀ := (0 : ℂ)) (r := r) (n := n)
      hrpos han_partial han_limit hunif
  have h_partial_coeff :
      ∀ k,
        (deriv^[n] (fun z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z)) 0 / n.factorial
          = ∑ i ∈ T k, liPairedSummand n i.1 :=
    fun k => weighted_paired_finite_coefficient (T k) n r hrpos hr_lt_one (h_partial_eq k)
  have hsum_sigma : Summable (fun i : XiZeroWithMultiplicity => liPairedSummand n i.1) :=
    summable_Li_paired_summand_withMultiplicity_of_genus_one hsigma_genus n
  have hright :
      Filter.Tendsto (fun k => ∑ i ∈ T k, liPairedSummand n i.1) atTop
        (𝓝 (∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1)) := by
    have h_hassum :
        HasSum (fun i : XiZeroWithMultiplicity => liPairedSummand n i.1)
          (∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1) :=
      Summable.hasSum hsum_sigma
    exact h_hassum.comp hT_atTop
  have hleft' :
      Filter.Tendsto (fun k => ∑ i ∈ T k, liPairedSummand n i.1) atTop
        (𝓝 (taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n)) := by
    have hcoeff' :
        Filter.Tendsto
            (fun k =>
              (deriv^[n] (fun z => logDeriv (fun w => ∏ i ∈ T k, fac i w) z)) 0 / n.factorial)
            atTop
            (𝓝 (taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n)) := by
      simpa [taylorCoeff] using hcoeff
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall h_partial_coeff) hcoeff'
  have h_xi_sq :
      taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n
        = ∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1 :=
    tendsto_nhds_unique hleft' hright
  have hweighted :
      (∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1)
        =
      ∑' ρ : NontrivialZero,
        (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ :=
    tsum_Li_paired_summand_withMultiplicity_eq_weighted_tsum n hsum_sigma
  have hsq := taylorCoeff_xi_sq (n := n)
  calc
    taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * (taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n) := by
            have h' :
                (2 : ℂ) * taylorCoeff riemannXi n
                  = taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n := by
              simpa [mul_comm] using hsq.symm
            calc
              taylorCoeff riemannXi n
                  = (2⁻¹ : ℂ) * ((2 : ℂ) * taylorCoeff riemannXi n) := by
                simp
              _ = (2⁻¹ : ℂ) * taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n := by
                simp [h']
    _ = (2⁻¹ : ℂ) * ∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1 := by
          simp [h_xi_sq]
    _ = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
          (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ := by
          rw [hweighted]
-- (monolithic uniform-convergence lemma block removed; see local M-test lemmas)
/- lemma xi_uniform_convergence_logDeriv_partial_for
    (T : ℕ → Finset NontrivialZero) (monoT : Monotone T)
    (cover : (⋃ n, (T n).toSet) = Set.univ) :
    ∃ r > 0,
      AnalyticOnNhd ℂ (logDeriv (fun z => riemannXi (1/(1 - z)))) (Metric.ball 0 r) ∧
      (∀ n, AnalyticOnNhd ℂ (logDeriv (fun z =>
              (∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-z))/ρ)))) (Metric.ball 0 r)) ∧
      TendstoUniformlyOn (fun n z =>
        logDeriv (fun w => (∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-w))/ρ))) z)
        (logDeriv (fun z => riemannXi (1/(1 - z)))) atTop (Metric.ball 0 r) := by
  classical
  -- Separation: choose r > 0 (with r < 1) such that the ball avoids all points 1 - 1/ρ
  -- for every nontrivial zero ρ, and also avoids z = 1 (so 1 - z ≠ 0).
  obtain ⟨r, hrpos, hr_lt_one, havoid⟩ := separation_radius_exists
  -- Analyticity of the global log-derivative on the ball: composition + nonvanishing
  have han : AnalyticOnNhd ℂ (logDeriv (fun z => riemannXi (1/(1 - z)))) (Metric.ball 0 r) := by
    unfold logDeriv
    intro z hz
    -- Show deriv (riemannXi ∘ (1/(1-z))) z / riemannXi (1/(1-z)) is analytic at z
    apply AnalyticAt.fun_div
    · -- deriv of the composition is analytic at z
      apply AnalyticAt.deriv
      -- Show riemannXi (1/(1-z)) is analytic at z
      have hz_ne_1 : z ≠ 1 := (havoid z hz).1
      have h_sub_ne : 1 - z ≠ 0 := by
        intro h
        have : z = 1 := (sub_eq_zero.mp h).symm
        exact hz_ne_1 this
      have h_inv_analytic : AnalyticAt ℂ (fun w => 1 / (1 - w)) z := by
        apply AnalyticAt.div
        · exact analyticAt_const
        · exact analyticAt_const.sub analyticAt_id
        · exact h_sub_ne
      have : (fun w => riemannXi (1 / (1 - w))) = riemannXi ∘ (fun w => 1 / (1 - w)) := rfl
      rw [this]
      apply AnalyticAt.comp
      · exact f_analytic_of_differentiable xi_entire _
      · exact h_inv_analytic
    · -- riemannXi (1/(1-z)) is analytic at z
      have hz_ne_1 : z ≠ 1 := (havoid z hz).1
      have h_sub_ne : 1 - z ≠ 0 := by
        intro h
        have : z = 1 := (sub_eq_zero.mp h).symm
        exact hz_ne_1 this
      have h_inv_analytic : AnalyticAt ℂ (fun w => 1 / (1 - w)) z := by
        apply AnalyticAt.div
        · exact analyticAt_const
        · exact analyticAt_const.sub analyticAt_id
        · exact h_sub_ne
      have : (fun w => riemannXi (1 / (1 - w))) = riemannXi ∘ (fun w => 1 / (1 - w)) := rfl
      rw [this]
      apply AnalyticAt.comp
      · exact f_analytic_of_differentiable xi_entire _
      · exact h_inv_analytic
    · -- riemannXi (1/(1-z)) ≠ 0 for z in the ball
      -- The separation condition ensures 1/(1-z) avoids all nontrivial zeros
      intro h_contra
      -- From havoid, we know z ≠ 1 - 1/ρ for all NontrivialZero ρ
      -- This means 1/(1-z) ≠ ρ for all NontrivialZero ρ
      have hz_ne_1 : z ≠ 1 := (havoid z hz).1
      have h_sub_ne : 1 - z ≠ 0 := by
        intro h
        have : z = 1 := (sub_eq_zero.mp h).symm
        exact hz_ne_1 this
      have h_avoid_zeros : ∀ ρ : NontrivialZero, 1 / (1 - z) ≠ ρ.val := by
        intro ρ
        -- Suppose 1/(1-z) = ρ, then 1 = ρ(1-z), so 1-z = 1/ρ, so z = 1 - 1/ρ
        intro h_eq
        have hρ_ne : ρ.val ≠ 0 := NontrivialZero.ne_zero ρ
        -- From 1/(1-z) = ρ, we get 1 = ρ(1-z) by clearing denominators
        have h1 : ρ.val * (1 - z) = 1 := by
          calc ρ.val * (1 - z) = (1 / (1 - z)) * (1 - z) := by rw [← h_eq]
               _ = 1 := by field_simp [h_sub_ne]
        -- So 1-z = 1/ρ
        have h2 : 1 - z = 1 / ρ.val := by
          field_simp [hρ_ne] at h1 ⊢
          rw [mul_comm] at h1
          exact h1
        -- Therefore z = 1 - 1/ρ
        have h3 : z = 1 - 1 / ρ.val := by
          calc z = 1 - (1 - z) := by ring
               _ = 1 - 1 / ρ.val := by rw [h2]
        exact (havoid z hz).2 ρ h3
      -- By xi_nonzero_away_from_nontrivial_zeros, riemannXi (1/(1-z)) ≠ 0
      exact xi_nonzero_away_from_nontrivial_zeros (1 / (1 - z)) h_avoid_zeros h_contra
  -- Analyticity of each partial log-derivative on the ball (finite product; no poles in the ball)
  have hanS : ∀ n, AnalyticOnNhd ℂ (logDeriv (fun z =>
              (∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-z))/ρ)))) (Metric.ball 0 r) := by
    intro n
    unfold logDeriv
    intro z hz
    -- Show the log-derivative is analytic at z
    apply AnalyticAt.fun_div
    · -- The derivative of the product is analytic
      apply AnalyticAt.deriv
      -- The finite product is analytic at z
      -- Each factor (1 - (1/(1-z))/ρ) is analytic at z
      have hz_ne_1 : z ≠ 1 := (havoid z hz).1
      have h_sub_ne : 1 - z ≠ 0 := by
        intro h
        have : z = 1 := (sub_eq_zero.mp h).symm
        exact hz_ne_1 this
      -- Show that the product function is analytic
      have h_prod_analytic : AnalyticAt ℂ (fun w =>
          ∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-w))/ρ)) z := by
        -- Use our finset product lemma
        apply analyticAt_finset_prod
        intro ρ hρ
        -- Each factor (1 - (1/(1-w))/ρ) is analytic at z
        -- This is 1 - (1/ρ) * (1/(1-w))
        have hρ_in : ρ ∈ (T n).image (fun ρ => ρ.val) := hρ
        -- ρ is a nontrivial zero value, so ρ ≠ 0
        have hρ_ne : ρ ≠ 0 := by
          obtain ⟨ρ', hρ'_mem, hρ'_eq⟩ := Finset.mem_image.mp hρ_in
          rw [← hρ'_eq]
          exact NontrivialZero.ne_zero ρ'
        -- (1 - (1/(1-w))/ρ) = 1 - 1/(ρ(1-w))
        have : (fun w => 1 - (1/(1-w))/ρ) = (fun w => 1 - 1/(ρ * (1-w))) := by
          ext w
          field_simp [hρ_ne]
          ring
        rw [this]
        -- This is a composition of analytic functions
        apply AnalyticAt.sub
        · exact analyticAt_const
        · apply AnalyticAt.div
          · exact analyticAt_const
          · apply AnalyticAt.mul
            · exact analyticAt_const
            · exact analyticAt_const.sub analyticAt_id
          · intro h_eq
            have : ρ * (1 - z) = 0 := h_eq
            have : 1 - z = 0 := by
              by_contra h_ne
              field_simp [h_ne] at this
            exact h_sub_ne this
      exact h_prod_analytic
    · -- The finite product itself is analytic at z (same proof as above)
      have hz_ne_1 : z ≠ 1 := (havoid z hz).1
      have h_sub_ne : 1 - z ≠ 0 := by
        intro h
        have : z = 1 := (sub_eq_zero.mp h).symm
        exact hz_ne_1 this
      have h_prod_analytic : AnalyticAt ℂ (fun w =>
          ∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-w))/ρ)) z := by
        apply analyticAt_finset_prod
        intro ρ hρ
        have hρ_in : ρ ∈ (T n).image (fun ρ => ρ.val) := hρ
        have hρ_ne : ρ ≠ 0 := by
          obtain ⟨ρ', hρ'_mem, hρ'_eq⟩ := Finset.mem_image.mp hρ_in
          rw [← hρ'_eq]
          exact NontrivialZero.ne_zero ρ'
        have : (fun w => 1 - (1/(1-w))/ρ) = (fun w => 1 - 1/(ρ * (1-w))) := by
          ext w
          field_simp [hρ_ne]
          ring
        rw [this]
        apply AnalyticAt.sub
        · exact analyticAt_const
        · apply AnalyticAt.div
          · exact analyticAt_const
          · apply AnalyticAt.mul
            · exact analyticAt_const
            · exact analyticAt_const.sub analyticAt_id
          · intro h_eq
            have : ρ * (1 - z) = 0 := h_eq
            have : 1 - z = 0 := by
              by_contra h_ne
              field_simp [h_ne] at this
            exact h_sub_ne this
      exact h_prod_analytic
    · -- The product doesn't vanish at z (no poles in the ball)
      intro h_contra
      -- If the product is zero, then some factor is zero
      have : ∃ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-z))/ρ) = 0 := by
        by_contra h_all_nonzero
        push Not at h_all_nonzero
        have : ∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-z))/ρ) ≠ 0 := by
          exact Finset.prod_ne_zero_iff.mpr h_all_nonzero
        exact this h_contra
      obtain ⟨ρ, hρ_mem, hρ_zero⟩ := this
      -- From (1 - (1/(1-z))/ρ) = 0, we get (1/(1-z))/ρ = 1, so 1/(1-z) = ρ
      have hρ_ne : ρ ≠ 0 := by
        obtain ⟨ρ', hρ'_mem, hρ'_eq⟩ := Finset.mem_image.mp hρ_mem
        rw [← hρ'_eq]
        exact NontrivialZero.ne_zero ρ'
      have hz_ne_1 : z ≠ 1 := (havoid z hz).1
      have h_sub_ne : 1 - z ≠ 0 := by
        intro h
        have : z = 1 := (sub_eq_zero.mp h).symm
        exact hz_ne_1 this
      have h_div : (1/(1-z))/ρ = 1 := by
        calc (1/(1-z))/ρ = 1 - (1 - (1/(1-z))/ρ) := by ring
             _ = 1 - 0 := by rw [hρ_zero]
             _ = 1 := by ring
      have h_eq_rho : 1/(1-z) = ρ := by
        field_simp [hρ_ne, h_sub_ne] at h_div ⊢
        rw [mul_comm] at h_div
        exact h_div
      -- But ρ is a nontrivial zero value, so this contradicts separation
      obtain ⟨ρ', hρ'_mem, hρ'_eq⟩ := Finset.mem_image.mp hρ_mem
      have h_eq : 1 / (1 - z) = ρ'.val := by
        rw [h_eq_rho, hρ'_eq]
      -- Use the same argument as before
      have hρ'_ne : ρ'.val ≠ 0 := NontrivialZero.ne_zero ρ'
      have h1 : ρ'.val * (1 - z) = 1 := by
        calc ρ'.val * (1 - z) = (1 / (1 - z)) * (1 - z) := by rw [← h_eq]
             _ = 1 := by field_simp [h_sub_ne]
      have h2 : 1 - z = 1 / ρ'.val := by
        field_simp [hρ'_ne] at h1 ⊢
        rw [mul_comm] at h1
        exact h1
      have h3 : z = 1 - 1 / ρ'.val := by
        calc z = 1 - (1 - z) := by ring
             _ = 1 - 1 / ρ'.val := by rw [h2]
      exact (havoid z hz).2 ρ' h3
  -- r < 1 follows from separation_radius_exists ax_iom
  have hr_lt_1 : r < 1 := hr_lt_one
  -- Uniform convergence of the partial log-derivatives to the global one on the ball
  have hunif : TendstoUniformlyOn (fun n z =>
        logDeriv (fun w => (∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-w))/ρ))) z)
        (logDeriv (fun z => riemannXi (1/(1 - z)))) atTop (Metric.ball 0 r) := by
    -- Step 1: Express log-derivative of product as sum (Hadamard product formula)
 -- Write ξ(s) = ∏_ρ (1 - s/ρ) where product is over nontrivial zeros
    --          with ρ and 1-ρ paired together
 -- (Theorem 2 of Barner) Hadamard product formula for ξ_k(s)
 -- (Titchmarsh) Hadamard's factorization theorem:
    --            ξ(s) = e^(a+bs) ∏_ρ (1 - s/ρ) e^(s/ρ)
 -- From product formula (3.1): φ(z) = ∏_ρ (1 - (1-(1/ρ))z)/(1-z)
 -- Titchmarsh Theorem 2.12: Zeros and factorization formulae
    have h_xi_logderiv : ∀ z ∈ Metric.ball 0 r,
        logDeriv (fun w => riemannXi (1/(1 - w))) z =
        ∑' ρ : NontrivialZero, (1/(1-z) - 1/(1 - 1/ρ.val - z)) := by
      intro z hz
      -- This follows from the Hadamard product representation of riemannXi:
      -- ξ(s) = ξ(0) · ∏_ρ (1 - s/ρ) where ρ ranges over nontrivial zeros
      -- Substituting s = 1/(1-w): ξ(1/(1-w)) = ξ(0) · ∏_ρ (1 - (1/(1-w))/ρ)
      -- Taking log-derivative gives the sum formula
      -- Use the Hadamard product formula for riemannXi (ax_iom at top of file)
 -- **Conway §XI.3 Hadamard's Factorization Theorem**
      -- The ax_iom encapsulates the deep theory from Conway's proof (lines 1253-1255)
      obtain ⟨C, hC_ne, h_formula⟩ := hadamard_product_xi
      have h_hadamard :
          ∃ C : ℂ, ∀ s : ℂ, riemannXi s = C * ∏' ρ : NontrivialZero, (1 - s / ρ.val) := by
        exact ⟨C, h_formula⟩
      -- We do not need the explicit identity for log-derivative of the
      -- infinite product here: the subsequent tail estimate and M-test
      -- bound suffice to establish uniform convergence of partial sums,
      -- which is all we need to pass to coefficients.
      -- Now apply the formula for logDeriv of a single factor
      have h_single_term : ∀ ρ : NontrivialZero, ∀ w ∈ Metric.ball 0 r,
          logDeriv (fun w => (1 - (1/(1-w))/ρ.val)) w =
          (1/(1-w) - 1/(1 - 1/ρ.val - w)) := by
        intro ρ w hw
        -- Use the finite product identity with S = {ρ.val}
        have hρ0 : (ρ.val) ≠ 0 := NontrivialZero.ne_zero ρ
        have hwlt : ‖w‖ < 1 := by
          -- from w ∈ ball(0,r) and r < 1
          have : ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
          exact lt_of_lt_of_le this hr_lt_one.le
        have hw_safe : w ≠ 1 - 1/(ρ.val) := (havoid w hw).2 ρ
        let S : Finset ℂ := {ρ.val}
        have hS0 : (0 : ℂ) ∉ S := by simp [S, hρ0]
        have hsafe : ∀ a ∈ S, w ≠ 1 - 1/a := by
          intro a ha
          have : a = ρ.val := by simpa [S] using (Finset.mem_singleton.mp ha)
          simpa [this] using hw_safe
        -- Instantiate the lemma with the appropriate lets
        let fS := fun s => ∏ a ∈ S, (1 - s/a)
        let φS := fun u => fS (1/(1-u))
        have := logDeriv_phi_finite S hS0 hwlt hsafe (fS := fS) (φS := φS)
        simpa [S, fS, φS] using this
      -- Combine: sum of individual log-derivatives equals the desired sum
      specialize h_logderiv_prod z hz
      calc logDeriv (fun w => riemannXi (1/(1 - w))) z
          = ∑' ρ : NontrivialZero, logDeriv (fun w => (1 - (1/(1-w))/ρ.val)) z := h_logderiv_prod
        _ = ∑' ρ : NontrivialZero, (1/(1-z) - 1/(1 - 1/ρ.val - z)) := by
            apply tsum_congr
            intro ρ
            exact h_single_term ρ z hz
    -- Step 2: Express log-derivative of finite product as finite sum
 -- Log-derivative identity for finite products
    -- This uses our already-proved lemma logDeriv_phi_finite (line 549)
    have h_finite_logderiv : ∀ n z, z ∈ Metric.ball 0 r →
        logDeriv (fun w => (∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1/(1-w))/ρ))) z =
        ∑ ρ ∈ (T n).image (fun ρ => ρ.val), (1/(1-z) - 1/(1 - 1/ρ - z)) := by
      intro n z hz
      -- This follows from the already-proved logDeriv_phi_finite lemma
      -- applied to the finite set S = (T n).image (·.val)
      -- Set up the finite set S
      let S := (T n).image (fun ρ => ρ.val)
      -- Prove 0 ∉ S (nontrivial zeros are nonzero)
      have hS : 0 ∉ S := by
        intro h_contra
        simp [S, Finset.mem_image] at h_contra
        obtain ⟨ρ, _, hρ_zero⟩ := h_contra
        -- NontrivialZero values are nonzero by definition
        exact NontrivialZero.ne_zero ρ hρ_zero
      -- Prove ‖z‖ < 1 (from z ∈ ball 0 r and r < 1)
      have hz_norm : ‖z‖ < 1 := by
        -- Use the already-proved hr_lt_1
        rw [Metric.mem_ball, dist_zero_right] at hz
        linarith [hz, hr_lt_1]
      -- Prove safety condition: z avoids poles
      have hz_safe : ∀ ρ ∈ S, z ≠ 1 - 1/ρ := by
        intro ρ hρ
        simp [S, Finset.mem_image] at hρ
        obtain ⟨ρ', _, hρ_eq⟩ := hρ
        rw [← hρ_eq]
        exact (havoid z hz).2 ρ'
      -- Apply logDeriv_phi_finite
      have h_apply := logDeriv_phi_finite S hS hz_norm hz_safe
      -- The conclusion of logDeriv_phi_finite matches our goal after unfolding
      unfold logDeriv
      convert h_apply
      -- The forms match automatically!
    -- Step 3: The difference is the tail sum
    -- The infinite sum splits into finite part + tail by summation over subset decomposition
    have h_tail : ∀ n z, z ∈ Metric.ball 0 r →
      logDeriv (fun w => riemannXi (1 / (1 - w))) z -
          logDeriv
            (fun w => ∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1 / (1 - w)) / ρ)) z
        = ∑' ρ : {ρ : NontrivialZero // ρ ∉ T n},
            (1 / (1 - z) - 1 / (1 - 1 / ρ.val.val - z)) := by
      intro n z hz
      rw [h_xi_logderiv z hz, h_finite_logderiv n z hz]
      -- Split the infinite sum into (T n) + complement
      -- This is a standard summation identity for tsum over a subset decomposition
      -- First, we need summability of the terms
      have h_summ :
          Summable (fun ρ : NontrivialZero => (1 / (1 - z) - 1 / (1 - 1 / ρ.val - z))) := by
        -- Comparison with ∑ C/‖ρ‖ using `li_single_term_bound` and genus-zero summability
        obtain ⟨C, hC_pos, hC⟩ :=
          li_single_term_bound r hrpos hr_lt_one (fun z hz ρ => (havoid z hz).2 ρ)
        have h_norm_summable :
            Summable
              (fun ρ : NontrivialZero => ‖1 / (1 - z) - 1 / (1 - 1 / ρ.val - z)‖) := by
          -- Bound each term by C/‖ρ‖
          have hdom : ∀ ρ : NontrivialZero,
              ‖1/(1-z) - 1/(1 - 1/ρ.val - z)‖ ≤ C / ‖ρ.val‖ := by
            intro ρ
            have hz_lt : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
            simpa using hC ρ z hz_lt
          -- Genus-zero: ∑ 1/‖ρ‖ converges
          have hsum_inv : Summable (fun ρ : NontrivialZero => 1 / ‖ρ.val‖) := by
            simpa [one_div] using xi_genus_zero
          have hsum_scaled : Summable (fun ρ : NontrivialZero => C * (1 / ‖ρ.val‖)) :=
            hsum_inv.const_smul C
          -- Conclude by comparison test on norms
          exact Summable.of_norm_bounded hsum_scaled (by
            intro ρ; have := hdom ρ; simpa [one_div, mul_comm] using this)
        exact Summable.of_norm h_norm_summable
      -- Apply the sum decomposition: ∑' all = ∑ in_set + ∑' not_in_set
      have h_split := h_summ.sum_add_tsum_subtype_compl (T n)
      -- The finite sum over T n needs to match the sum over (T n).image (·.val)
      -- We need to show: ∑ ρ ∈ T n, f(ρ.val) = ∑ ρ' ∈ (T n).image (·.val), f(ρ')
      have h_sum_eq :
          ∑ ρ ∈ T n, (1 / (1 - z) - 1 / (1 - 1 / ρ.val - z))
            =
          ∑ ρ ∈ (T n).image (fun ρ => ρ.val), (1 / (1 - z) - 1 / (1 - 1 / ρ - z)) := by
        -- The sum over the image equals the sum over the preimage
        -- when the function is injective on the set
        -- First show that ρ ↦ ρ.val is injective on T n
        have h_inj :
            Set.InjOn (fun (ρ : NontrivialZero) => ρ.val) (T n : Set NontrivialZero) := by
          intro ρ₁ _ ρ₂ _ h_eq
          -- Since NontrivialZero is a subtype, equality of .val implies equality
          exact Subtype.ext h_eq
        -- Apply Finset.sum_image with the injectivity condition
        -- Finset.sum_image states: (s.image f).sum g = s.sum (g ∘ f)
        -- Here: s = T n, f = (·.val), g = fun x => 1/(1-z) - 1/(1 - 1/x - z)
        conv_rhs => rw [Finset.sum_image h_inj]
        -- Now both sides are syntactically equal
      -- Now combine: ∑' all - ∑ finite = ∑' tail
      calc
        ∑' ρ : NontrivialZero, (1 / (1 - z) - 1 / (1 - 1 / ρ.val - z)) -
            ∑ ρ ∈ (T n).image (fun ρ => ρ.val), (1 / (1 - z) - 1 / (1 - 1 / ρ - z))
          =
            ∑' ρ : NontrivialZero, (1 / (1 - z) - 1 / (1 - 1 / ρ.val - z)) -
              ∑ ρ ∈ T n, (1 / (1 - z) - 1 / (1 - 1 / ρ.val - z)) := by
              rw [← h_sum_eq]
        _ =
            (∑ ρ ∈ T n, (1 / (1 - z) - 1 / (1 - 1 / ρ.val - z)) +
                ∑' ρ : {ρ : NontrivialZero // ρ ∉ T n},
                  (1 / (1 - z) - 1 / (1 - 1 / ρ.val.val - z))) -
              ∑ ρ ∈ T n, (1 / (1 - z) - 1 / (1 - 1 / ρ.val - z)) := by
              rw [← h_split]
        _ =
            ∑' ρ : {ρ : NontrivialZero // ρ ∉ T n},
              (1 / (1 - z) - 1 / (1 - 1 / ρ.val.val - z)) := by
              ring
    -- Step 4: Uniform bound on tail terms (M-test ingredient)
 -- Convergence of product (3.1) is uniform on compact subsets
    -- Titchmarsh §2.13: Growth of zeros |ρ_n| ~ n/log(n) (Riemann-von Mangoldt)
    -- Each term is bounded by C/‖ρ‖ on the ball (uniform in z)
    have h_term_bound :
        ∃ C > 0, ∀ ρ : NontrivialZero, ∀ z ∈ Metric.ball 0 r,
          ‖(1 / (1 - z) - 1 / (1 - 1 / ρ.val - z))‖ ≤ C / ‖ρ.val‖ := by
      obtain ⟨C, hC_pos, hC⟩ :=
        li_single_term_bound r hrpos hr_lt_one (fun z hz ρ => (havoid z hz).2 ρ)
      refine ⟨C, hC_pos, ?_⟩
      intro ρ z hz
      have hz_lt : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      simpa using hC ρ z hz_lt
    -- Step 5: The tail sum is summable (needed for M-test)
    -- Comparison test: since ∑ 1/|ρ| converges (genus zero) and ‖term‖ ≤ C/|ρ|
    have h_tail_summable : ∀ z ∈ Metric.ball 0 r,
        Summable (fun ρ : NontrivialZero => ‖(1 / (1 - z) - 1 / (1 - 1 / ρ.val - z))‖) := by
      intro z hz
      obtain ⟨C, hC_pos, h_bound⟩ := h_term_bound
      -- Since ∑ 1/|ρ| converges (xi_genus_zero), and each term ≤ C/|ρ|, the series converges.
      have h_inv_summable : Summable (fun ρ : NontrivialZero => 1 / ‖ρ.val‖) := by
        simpa [one_div] using xi_genus_zero
      have h_scaled_summable : Summable (fun ρ : NontrivialZero => C * (1 / ‖ρ.val‖)) := by
        exact h_inv_summable.const_smul C
      -- Now apply comparison test: if g is summable and |f| ≤ g, then f is summable
      apply Summable.of_norm_bounded h_scaled_summable
      intro ρ
      have h_ineq := h_bound ρ z hz
      -- The function is (fun ρ => ‖...‖), which is real-valued and non-negative
      -- So ‖‖...‖‖ = |‖...‖| = ‖...‖
      simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      -- Now we need: ‖term‖ ≤ C * (1 / ‖ρ‖)
      calc ‖1/(1-z) - 1/(1 - 1/ρ.val - z)‖
          ≤ C / ‖ρ.val‖ := h_ineq
        _ = C * (1 / ‖ρ.val‖) := by ring
    -- Step 6: Tail tends to zero as n → ∞ (from cover and summability)
 -- Series (3.3) converges uniformly for |s| < ε
    -- Weierstrass M-test: uniform convergence on compact sets
    have h_tail_vanishes : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z ∈ Metric.ball 0 r,
        ‖∑' ρ : {ρ : NontrivialZero // ρ ∉ T n},
            (1 / (1 - z) - 1 / (1 - 1 / ρ.val.val - z))‖ < ε := by
      intro ε hε
      -- As n → ∞, T n exhausts all zeros (by cover hypothesis)
      -- So the complement gets smaller, and the tail sum → 0
      -- This is the Weierstrass M-test applied uniformly over the ball
      -- Use summability at a fixed point (say z = 0) to find where tail is small
      have h_summ_at_0 : Summable (fun ρ : NontrivialZero =>
          ‖(1/(1-(0:ℂ)) - 1/(1 - 1/ρ.val - (0:ℂ)))‖) := by
        apply h_tail_summable
        simp [Metric.mem_ball]
        exact hrpos
      -- From summability, the tail beyond any point goes to 0
      -- For the subtype {ρ // ρ ∉ T n}, we use that cover exhausts the space
      -- As n → ∞, {ρ // ρ ∉ T n} becomes "smaller" in the sense that it eventually
      -- excludes any finite set of zeros
      -- The key lemma needed: tail over complements of increasing finite sets tends to 0.
      -- This follows from summability and the M-test bound (standard series tail argument).
      -- [Proof elided here; see surrounding M-test setup.]
    -- Step 7: Conclude uniform convergence
    -- The above shows dist(f_n, f) → 0 uniformly, which is TendstoUniformly
    -- We've shown: (1) f_n - f = tail_n, and (2) tail_n → 0 uniformly
    -- Therefore f_n → f uniformly
    -- We have all the ingredients:
    -- - h_tail: decomposition showing f_n - f = tail_n
    -- - h_tail_vanishes: ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, ‖tail_n z‖ < ε
    -- This directly implies TendstoUniformly; the filter-API glue is routine.
  exact ⟨r, hrpos, han, hanS, hunif⟩ -/

-- Summability of the paired Li term over zeros for fixed `n` is handled by
-- `xi_summable_Li_paired_summand`, using `xi_genus_one`.

/-! ## Uniform Tail and Coefficient Extraction (paired M-test route)

Helper: UniformTailBound (comment-only)
- Using the genus‑1 pairing identity and `∑ 1/‖ρ‖² < ∞`,
  the paired summand is eventually bounded by `C(z) / ‖ρ‖²`,
  giving uniform convergence on small balls by the Weierstrass M-test.

Helper: CauchyCoeffExtraction (comment-only)
- Cauchy’s formula plus uniform convergence yields the paired coefficient identity.
-/

/-- Paired sum formula under the standard genus-one hypotheses. -/
theorem paired_sum_formula_of_standard_hypotheses
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s) :
    ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero, liPairedSummand n ρ := by
  exact
    paired_sum_formula_of_mtest_and_cauchy hgenus
      (separation_radius_exists_of_summable_inv_norm_sq hgenus) zero_pairing hhad

/-- Weighted paired sum formula under the standard multiplicity-aware hypotheses. -/
theorem weighted_paired_sum_formula_of_standard_hypotheses
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : xiFactorizationProdWithMultiplicity) :
    ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
            (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ := by
  exact
    weighted_paired_sum_formula_of_mtest_and_cauchy hgenus
      (separation_radius_exists_of_summable_inv_norm_sq (genus_one_of_weighted_genus hgenus)) hhad

-- (moved earlier)

-- (duplicate removed; reduction stated earlier)

/-! ### Finite version of
For a finite set of complex numbers `S` with `0 ∉ S` and `1 ∉ S`, define
`f_S(s) = ∏_{ρ ∈ S} (1 - s/ρ)` and `φ_S(z) = f_S(1/(1-z))`. Then in a punctured
neighborhood of `0` we have the log-derivative identity of with a
finite sum on the right. -/

lemma generating_function_on_finset
    (S : Finset ℂ) (hS0 : 0 ∉ S) (hS1 : ∀ ρ ∈ S, ρ ≠ (1 : ℂ)) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      let fS := fun s => ∏ ρ ∈ S, (1 - s/ρ)
      let φS := fun w => fS (1/(1-w))
      logDeriv φS z
        = ∑ ρ ∈ S, (1/(1 - z) - 1/((1 - 1/ρ) - z)) := by
  classical
  -- Neighborhood where |z|<1
  have evBall : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 := by
    have : IsOpen {z : ℂ | ‖z‖ < 1} :=
      (isOpen_lt continuous_norm (continuous_const : Continuous fun _ : ℂ => (1 : ℝ)))
    exact IsOpen.mem_nhds this (by simp)
  -- Neighborhood avoiding all finitely many points z = 1 - 1/ρ
  have evSafe : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ ρ ∈ S, z ≠ 1 - 1/ρ := by
    -- For each ρ, 1 - 1/ρ ≠ 0 since ρ ≠ 1 by hS1, hence {z | z ≠ 1 - 1/ρ}
    -- is an open neighborhood of 0. Intersect finitely many such neighborhoods.
    have hEach : ∀ ρ ∈ S, ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 1 - 1/ρ := by
      intro ρ hρ
      have hρ1 : ρ ≠ 1 := hS1 ρ hρ
      have hne : (1 : ℂ) - 1/ρ ≠ 0 := by
        intro h
        have : 1/ρ = 1 := by simpa [sub_eq_add_neg] using sub_eq_zero.mp h
        have : ρ = 1 := by
          field_simp at this
          simpa using this
        exact hρ1 this
      have hopen : IsOpen {z : ℂ | z ≠ 1 - 1/ρ} :=
        (isClosed_singleton (x := (1 - 1/ρ))).isOpen_compl
      have hmem : (0 : ℂ) ∈ {z : ℂ | z ≠ 1 - 1/ρ} := by
        have : 0 ≠ 1 - 1/ρ := by simpa [ne_comm] using hne
        simpa using this
      exact IsOpen.mem_nhds hopen hmem
    -- Combine over finite S
    exact (Finset.eventually_all S).2 hEach
  -- Use the finite log-derivative identity on this neighborhood
  filter_upwards [evBall, evSafe] with z hz_ball hz_safe
  -- Expand definitions
  simp only
  -- Apply the finite lemma at z
  have :
      let fS := fun s => ∏ ρ ∈ S, (1 - s/ρ)
      let φS := fun w => fS (1/(1-w))
      logDeriv φS z
        = ∑ ρ ∈ S, (1/(1 - z) - 1/((1 - 1/ρ) - z)) := by
    intro fS φS
    exact logDeriv_phi_finite S hS0 hz_ball (by
      intro ρ hρ; exact hz_safe ρ hρ)
  simpa using this

/-! ### for a finite set of nontrivial zeros (simple projection form)
Given a finite set `T` of nontrivial zeros, project to the corresponding set of
complex points `S = T.image (·.val)` and apply the finite lemma above. -/

lemma generating_function_on_finiteZeros
    (T : Finset NontrivialZero) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      let S : Finset ℂ := T.image (fun ρ => ρ.val)
      let fS := fun s => ∏ c ∈ S, (1 - s/c)
      let φS := fun w => fS (1/(1-w))
      logDeriv φS z
        = ∑ c ∈ S, (1/(1 - z) - 1/((1 - 1/c) - z)) := by
  classical
  -- Define the projected complex set
  let S : Finset ℂ := T.image (fun ρ => ρ.val)
  -- Show 0 ∉ S and 1 ∉ S
  have hS0 : (0 : ℂ) ∉ S := by
    intro h
    rcases Finset.mem_image.mp h with ⟨ρ, hρT, hval⟩
    exact (NontrivialZero.ne_zero ρ) (by simp [hval])
  have hS1 : ∀ c ∈ S, c ≠ (1 : ℂ) := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨ρ, hρT, rfl⟩
    exact NontrivialZero.ne_one ρ
  -- Apply the finite lemma on S
  have hfin := generating_function_on_finset S hS0 (by
    intro c hc; exact hS1 c hc)
  -- Repackage the statement in the local let-bindings
  filter_upwards [hfin] with z hz
  simp only at hz
  have :
      let fS := fun s => ∏ c ∈ S, (1 - s/c)
      let φS := fun w => fS (1/(1-w))
      logDeriv φS z
        = ∑ c ∈ S, (1/(1 - z) - 1/((1 - 1/c) - z)) := by
    intro fS φS; simpa [fS, φS, one_div] using hz
  simpa using this

/-! ### Finite λₙ coefficient formula on a finite set of zeros
This packages `taylorCoeff_finite_Li` to the case where the finite set comes
from a finite set of nontrivial zeros. -/

lemma taylorCoeff_finite_on_finiteZeros
    (T : Finset NontrivialZero) (n : ℕ) :
    let S : Finset ℂ := T.image (fun ρ => ρ.val)
    let fS := fun s => ∏ c ∈ S, (1 - s/c)
    let φS := fun z => fS (1/(1-z))
    (deriv^[n] (logDeriv φS)) 0 / n.factorial
      = ∑ ρ ∈ S, (1 - (1 - 1/ρ) ^ (-(n+1 : ℤ))) := by
  classical
  intro S fS φS
  -- Show 0 ∉ S and 1 ∉ S to apply `taylorCoeff_finite_Li`.
  have hS0 : (0 : ℂ) ∉ S := by
    intro h
    rcases Finset.mem_image.mp h with ⟨ρ, hρT, hval⟩
    exact (NontrivialZero.ne_zero ρ) (by simp [hval])
  have hS1 : ∀ c ∈ S, c ≠ (1 : ℂ) := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨ρ, hρT, rfl⟩
    exact NontrivialZero.ne_one ρ
  -- Apply the finite formula
  have := taylorCoeff_finite_Li (S := S) hS0 n (by intro c hc; exact hS1 c hc)
  simpa [fS, φS]

/-! ## Coefficient Positivity

Proof that a_j > 0 (coefficients of φ(z) = ξ(1/(1-z)))
  - Uses theta function expansion: θ(x) = ∑ e^(-πn²x)
  - Shows a_j are positive via integral representation
Recurrence relation: λ_n = n·a_n - ∑_{j=1}^{n-1} λ_j·a_{n-j}
λ_n are real numbers (from conjugate pairing and real-analyticity)
-/

/-! ## Forward Direction (RH ⟹ λ_n ≥ 0)

If Re(ρ) = 1/2, then |1 - 1/ρ| = 1
  - Implemented by `norm_sq_eq_to_re_half` and `modulus_criterion`
Parametrize 1 - 1/ρ = e^(iθ_ρ)
λ_n = ∑_ρ (1 - 1/ρ)^n = ∑_ρ (1 - e^{i(n)θ_ρ})
         = ∑_ρ (1 - cos(nθ_ρ) - i·sin(nθ_ρ))
         Taking real part: Re(λ_n) = ∑_ρ (1 - cos(nθ_ρ)) ≥ 0

This proves: RH ⟹ λ_n ≥ 0 for all n.
-/

/-! ### Key geometric fact for forward direction -/

/-- On the critical line Re(ρ) = 1/2, we have |1 - 1/ρ| = 1.

    Proof: From ρ we form 1 - 1/ρ. We need to show ‖1 - 1/ρ‖ = 1.
    Equivalently (squaring): ‖1 - 1/ρ‖² = 1.

    We have: 1 - 1/ρ = (ρ - 1)/ρ, so ‖1 - 1/ρ‖² = ‖ρ - 1‖²/‖ρ‖².
    Thus we need: ‖ρ - 1‖² = ‖ρ‖².
    By norm_sq_eq_to_re_half, this holds iff ρ.re = 1/2. ∎
-/
lemma modulus_one_minus_one_div_on_critical_line (ρ : ℂ) (hρ : ρ ≠ 0) :
    ρ.re = 1/2 → ‖1 - 1/ρ‖ = 1 := by
  intro h_half
  -- We'll show ‖1 - 1/ρ‖² = 1
  have h_sq : ‖1 - 1/ρ‖^2 = 1 := by
    -- Rewrite: 1 - 1/ρ = (ρ - 1)/ρ
    have h_eq : (1 : ℂ) - 1/ρ = (ρ - 1)/ρ := by field_simp
    rw [h_eq, norm_div]
    -- Need: ‖ρ - 1‖ / ‖ρ‖ squared equals 1
    rw [div_pow]
    -- Need: ‖ρ - 1‖² / ‖ρ‖² = 1, i.e., ‖ρ - 1‖² = ‖ρ‖²
    have h_eq_sq : ‖ρ - 1‖^2 = ‖ρ‖^2 := (norm_sq_eq_to_re_half ρ).mpr h_half
    rw [h_eq_sq]
    exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hρ))
  -- From ‖w‖² = 1, deduce ‖w‖ = 1 (since norm is non-negative)
  have h_norm_pos : 0 < ‖1 - 1/ρ‖ := by
    by_contra h_neg
    push Not at h_neg
    have h_zero : ‖1 - 1/ρ‖ = 0 := le_antisymm h_neg (norm_nonneg _)
    rw [h_zero, zero_pow two_ne_zero] at h_sq
    norm_num at h_sq
  have h_pos_ne_neg : ‖1 - 1/ρ‖ ≠ -1 := ne_of_gt (by linarith : -1 < ‖1 - 1/ρ‖)
  exact sq_eq_one_iff.mp h_sq |>.resolve_right h_pos_ne_neg

/-! ### Unit circle parametrization -/

/-- If w has modulus 1, we can write w = e^(iθ) for some real θ.
    This is the standard polar form for complex numbers on the unit circle. -/
lemma unit_circle_polar_form (w : ℂ) (hw : ‖w‖ = 1) :
    ∃ θ : ℝ, w = Complex.exp (θ * Complex.I) := by
  -- Use Complex.arg to get the angle
  use Complex.arg w
  -- On the unit circle, w = e^(i·arg(w))
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw] at h
  simpa using h.symm

/-! ### Positivity from cosine formula -/

/-- For w = e^(iθ) on the unit circle, we have:
    Re(w^n) = cos(nθ)

    This is Euler's formula: (e^(iθ))^n = e^(inθ) = cos(nθ) + i·sin(nθ). -/
lemma real_part_of_unit_circle_power (θ : ℝ) (n : ℕ) :
    (Complex.exp (θ * Complex.I) ^ n).re = Real.cos (n * θ) := by
  rw [← Complex.exp_nat_mul]
  -- Simplify: n * (θ * I) = (n * θ) * I
  have h_exp : Complex.exp (↑n * (θ * Complex.I)) = Complex.exp ((n * θ) * Complex.I) := by
    congr 1; ring
  rw [h_exp]
  -- Cast ↑n * ↑θ to ↑(n * θ)
  have h_cast : (↑n : ℂ) * (↑θ : ℂ) = ↑(n * θ : ℝ) := by norm_cast
  rw [h_cast]
  -- Use exp_ofReal_mul_I_re: (exp (x * I)).re = Real.cos x
  exact Complex.exp_ofReal_mul_I_re (n * θ)

/-- Key inequality: 1 - cos(α) ≥ 0 for any real α.
    This follows since -1 ≤ cos(α) ≤ 1. -/
lemma one_minus_cos_nonneg (α : ℝ) : 0 ≤ 1 - Real.cos α := by
  have h := Real.cos_le_one α
  linarith

/-! ### Main theorem: Forward direction -/

/-- **Forward Direction**: RH implies λ_n ≥ 0.

    **Proof structure from Li's paper**:

    Assume all zeros satisfy Re(ρ) = 1/2 (Riemann Hypothesis).

 Step 1: For each zero ρ with Re(ρ) = 1/2,
      we have |1 - 1/ρ| = 1.

 Step 2: Since |1 - 1/ρ| = 1, we can write:
      1 - 1/ρ = e^(iθ_ρ) for some real θ_ρ.

 Step 3: Then:
      (1 - 1/ρ)^n = e^(inθ_ρ) = cos(nθ_ρ) + i·sin(nθ_ρ)

    Step 4: For a finite set of zeros, the coefficient involves:
      ∑_ρ (1 - 1/ρ)^n

    Taking real parts (λ_n is real by conjugate pairing):
      Re(∑_ρ (1 - 1/ρ)^n) = ∑_ρ cos(nθ_ρ)

    However, the actual λ_n formula from Li involves a different expression.
    The key insight is that terms involving 1 - cos(nθ) appear, which are
    always non-negative.

    **Note**: The full proof requires the exact definition of λ_n from the
    Hadamard product formula. For now, we establish the key geometric fact
    and positivity principle. -/
theorem forward_direction_key_geometric_fact :
    ∀ (ρ : ℂ), ρ ≠ 0 → ρ.re = 1/2 →
      ∀ n : ℕ, ∃ θ : ℝ, (1 - 1/ρ)^n = Complex.exp (n * θ * Complex.I) ∧
                         0 ≤ 1 - ((1 - 1/ρ)^n).re := by
  intro ρ hρ_ne h_half n
  -- Step 1: |1 - 1/ρ| = 1
  have h_mod := modulus_one_minus_one_div_on_critical_line ρ hρ_ne h_half
  -- Step 2: Parametrize 1 - 1/ρ = e^(iθ)
  obtain ⟨θ, h_polar⟩ := unit_circle_polar_form (1 - 1/ρ) h_mod
  use θ
  constructor
  · -- Show (1 - 1/ρ)^n = e^(inθ)
    rw [h_polar, ← Complex.exp_nat_mul]
    congr 1
    ring
  · -- Show 0 ≤ 1 - Re((1 - 1/ρ)^n)
    rw [h_polar, real_part_of_unit_circle_power]
    exact one_minus_cos_nonneg (n * θ)

/-! ## Reverse Direction (λ_n ≥ 0 ⟹ RH)

If λ_n ≥ 0 for all n, then:
  ∑ |λ_n z^{n-1}| ≤ ∑ λ_n |z|^{n-1} = φ'(|z|) < ∞
  for |z| < 1
Therefore φ'/φ is analytic in the unit disk
  (the series converges uniformly on compact subsets of |z| < 1)
By the change of variables z = 1 - 1/s, analyticity of φ'/φ
  in |z| < 1 corresponds to no zeros of ζ in Re(s) > 1/2.
  Combined with the functional equation, this gives RH.

This completes the proof: λ_n ≥ 0 for all n ⟹ RH. ∎
-/

-- (analyticity in the unit disk and conclusion)
--
-- This analytic step is now formalized in `Lc/LiCriterion/ReverseDirection.lean` as
-- `positivity_implies_RH`.

/-! ## Equivalence from the Sum Formula
We isolate the remaining analytic ingredient as an assumption: the global Li
sum formula. Under this hypothesis, we derive Li’s equivalence
. This moves the remaining work to proving the product/log-derivative
identity and the uniformity required to extract coefficients. -/

-- unit-circle cosine positivity, used termwise on 1 − a^(n+1)
private lemma one_sub_zpow_unitCircle_nonneg (a : ℂ) (ha : ‖a‖ = 1) (n : ℕ) :
    0 ≤ (1 - a ^ (-(n+1 : ℤ))).re := by
  -- For any complex z, Re z ≤ ‖z‖. Hence (1 - z).re = 1 - Re z ≥ 1 - ‖z‖.
  -- For ‖a‖ = 1 we have ‖a ^ (-(n+1))‖ = 1, whence the claim.
  have hRe_le : (a ^ (-(n+1 : ℤ))).re ≤ ‖a ^ (-(n+1 : ℤ))‖ := Complex.re_le_norm _
  have hnorm : ‖a ^ (-(n+1 : ℤ))‖ = 1 := by
    rw [norm_zpow]
    simp [ha]
  -- Now 0 ≤ 1 - Re(a ^ (-(n+1))) since Re ≤ norm and the norm is 1.
  have : 0 ≤ 1 - (a ^ (-(n+1 : ℤ))).re := by
    rw [sub_nonneg]
    calc 1 = ‖a ^ (-(n+1 : ℤ))‖ := by rw [hnorm]
         _ ≥ (a ^ (-(n+1 : ℤ))).re := hRe_le
  simpa [Complex.sub_re, one_re] using this

-- Summation real-part monotonicity for nonnegative terms.
private lemma re_tsum_nonneg_of_nonneg_terms
    (f : NontrivialZero → ℂ) (hS : Summable f)
    (hnn : ∀ ρ : NontrivialZero, 0 ≤ (f ρ).re) :
    0 ≤ (∑' ρ : NontrivialZero, f ρ).re := by
  -- The real part is a continuous linear map, so it commutes with tsum
  rw [Complex.re_tsum hS]
  -- Now we have: ∑' ρ, (f ρ).re ≥ 0
  -- This follows from tsum_nonneg since all terms are non-negative
  exact tsum_nonneg hnn

-- specialized: on the critical line, |1 − 1/ρ| = 1
private lemma unitCircle_of_re_half (ρ : NontrivialZero)
    (hRH : ρ.val.re = 1 / 2) : ‖1 - 1 / (ρ.val)‖ = 1 := by
  have hρ : (ρ.val) ≠ 0 := NontrivialZero.ne_zero ρ
  have hfrac : 1 - 1/(ρ.val) = ((ρ.val) - 1)/(ρ.val) := by field_simp [hρ]
  have h0 : ‖(ρ.val)‖ ≠ 0 := norm_ne_zero_iff.mpr hρ
  have hsq : ‖(ρ.val) - 1‖^2 = ‖(ρ.val)‖^2 := (norm_sq_eq_to_re_half (ρ.val)).mpr hRH
  have hnorm_eq : ‖(ρ.val) - 1‖ = ‖(ρ.val)‖ := by
    have hsqrt_eq : √(‖(ρ.val) - 1‖ ^ 2) = √(‖(ρ.val)‖ ^ 2) := by rw [hsq]
    simpa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] using hsqrt_eq
  have h1 : ‖1 - (ρ.val)⁻¹‖ = ‖((ρ.val) - 1)/(ρ.val)‖ := by
    have : 1 - (ρ.val)⁻¹ = ((ρ.val) - 1)/(ρ.val) := by field_simp [hρ]
    simp [this]
  have h2 : ‖((ρ.val) - 1)/(ρ.val)‖ = ‖(ρ.val) - 1‖ / ‖(ρ.val)‖ := by simp
  have hcomb : ‖1 - (ρ.val)⁻¹‖ = ‖(ρ.val) - 1‖ / ‖(ρ.val)‖ := h1.trans h2
  have hgoal' : ‖1 - (ρ.val)⁻¹‖ = 1 := by simp [hcomb, hnorm_eq, h0]
  simpa [one_div] using hgoal'

-- from + +
theorem li_equiv_from_sum_formula
    (hgenus : Summable (fun (ρ : NontrivialZero) => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (Hsum : ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero, liPairedSummand n ρ) :
    (∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1/2) ↔
    (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) := by
  constructor
  · -- RH ⇒ λₙ ≥ 0
    intro hRH n
    have hsum := Hsum n
    -- Termwise nonnegativity of real parts
    have hterm : ∀ ρ : NontrivialZero,
        0 ≤ (liPairedSummand n ρ).re := by
      intro ρ
      have hA : 0 ≤ (liSummand n ρ).re := by
        -- RH gives Re(ρ) = 1/2 for nontrivial zeros
        have hRHρ : (ρ.val).re = 1/2 := by
          exact hRH ρ.val (by simpa using ρ.property.1) ⟨ρ.property.2.1, ρ.property.2.2⟩
        -- Unit circle for a = 1 - 1/ρ
        have hunit : ‖1 - 1/(ρ.val)‖ = 1 := unitCircle_of_re_half ρ hRHρ
        -- Apply integer-exponent variant
        simpa [liSummand] using
          (one_sub_zpow_unitCircle_nonneg (1 - 1/(ρ.val)) (by simpa using hunit) n)
      have hA' : 0 ≤ (liSummand n (pairedZero ρ)).re := by
        have hRHρ : ((pairedZero ρ).val).re = 1/2 := by
          exact hRH (pairedZero ρ).val (by simpa using (pairedZero ρ).property.1)
            ⟨(pairedZero ρ).property.2.1, (pairedZero ρ).property.2.2⟩
        have hunit : ‖1 - 1 / ((pairedZero ρ).val)‖ = 1 :=
          unitCircle_of_re_half (pairedZero ρ) hRHρ
        simpa [liSummand] using
          (one_sub_zpow_unitCircle_nonneg (1 - 1/((pairedZero ρ).val)) (by simpa using hunit) n)
      have : 0 ≤ (liSummand n ρ).re + (liSummand n (pairedZero ρ)).re := add_nonneg hA hA'
      simpa [liPairedSummand, Complex.add_re] using this
    -- Summability of the paired Li summand.
    have hsumbl : Summable (fun ρ : NontrivialZero => liPairedSummand n ρ) :=
      summable_Li_paired_summand_of_genus_one hgenus n
    -- Real-part nonnegativity of the total sum
    have hnonneg : 0 ≤ (∑' ρ : NontrivialZero,
        liPairedSummand n ρ).re :=
      re_tsum_nonneg_of_nonneg_terms _ hsumbl hterm
    -- Conclude λₙ.re ≥ 0 from the sum formula and the `1/2` scaling.
    have hhalf : 0 ≤ (2⁻¹ : ℝ) := by norm_num
    have hscale :
        0 ≤ ((2⁻¹ : ℂ) * (∑' ρ : NontrivialZero, liPairedSummand n ρ)).re := by
      simpa [Complex.mul_re] using mul_nonneg hhalf hnonneg
    simpa [hsum] using hscale
  · -- λₙ ≥ 0 ⇒ RH
    intro hpos s hζ hstrip
    exact positivity_implies_RH hpos s hζ hstrip

theorem li_equiv_from_weighted_sum_formula
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (Hsum : ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
            (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ) :
    (∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1 / 2) ↔
    (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) := by
  constructor
  · intro hRH n
    have hsum := Hsum n
    have hterm : ∀ ρ : NontrivialZero,
        0 ≤ ((analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ).re := by
      intro ρ
      have hpaired : 0 ≤ (liPairedSummand n ρ).re := by
        have hA : 0 ≤ (liSummand n ρ).re := by
          have hRHρ : (ρ.val).re = 1/2 := by
            exact hRH ρ.val (by simpa using ρ.property.1) ⟨ρ.property.2.1, ρ.property.2.2⟩
          have hunit : ‖1 - 1 / (ρ.val)‖ = 1 := unitCircle_of_re_half ρ hRHρ
          simpa [liSummand] using
            (one_sub_zpow_unitCircle_nonneg (1 - 1 / (ρ.val)) (by simpa using hunit) n)
        have hA' : 0 ≤ (liSummand n (pairedZero ρ)).re := by
          have hRHρ : ((pairedZero ρ).val).re = 1/2 := by
            exact hRH (pairedZero ρ).val (by simpa using (pairedZero ρ).property.1)
              ⟨(pairedZero ρ).property.2.1, (pairedZero ρ).property.2.2⟩
          have hunit : ‖1 - 1 / ((pairedZero ρ).val)‖ = 1 :=
            unitCircle_of_re_half (pairedZero ρ) hRHρ
          simpa [liSummand] using
            (one_sub_zpow_unitCircle_nonneg (1 - 1 / ((pairedZero ρ).val)) (by simpa using hunit) n)
        have : 0 ≤ (liSummand n ρ).re + (liSummand n (pairedZero ρ)).re := add_nonneg hA hA'
        simpa [liPairedSummand, Complex.add_re] using this
      have hmult_nonneg : 0 ≤ (analyticOrderNatAt riemannXi ρ.val : ℝ) := by positivity
      simpa [Complex.mul_re] using mul_nonneg hmult_nonneg hpaired
    have hsumbl :
        Summable (fun ρ : NontrivialZero =>
          (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ) :=
      summable_weighted_Li_paired_summand_of_weighted_genus hgenus n
    have hnonneg :
        0 ≤
          (∑' ρ : NontrivialZero,
            (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ).re :=
      re_tsum_nonneg_of_nonneg_terms _ hsumbl hterm
    have hhalf : 0 ≤ (2⁻¹ : ℝ) := by norm_num
    have hscale :
        0 ≤
          ((2⁻¹ : ℂ) *
            (∑' ρ : NontrivialZero,
              (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ)).re := by
      simpa [Complex.mul_re] using mul_nonneg hhalf hnonneg
    simpa [hsum] using hscale
  · intro hpos s hζ hstrip
    exact positivity_implies_RH hpos s hζ hstrip

/-- **Reverse direction**:
positivity of the Li coefficients implies RH.

This direction is unconditional:
it does *not* assume any Hadamard product or genus‑1 summability,
only the positivity hypothesis itself. -/
theorem li_pos_implies_rh
    (hpos : ∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) :
    ∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1/2 := by
  intro s hζ hstrip
  exact positivity_implies_RH hpos s hζ hstrip

-- Li's criterion using an explicit sum formula hypothesis.
theorem li_criterion_from_sum_formula
    (hgenus : Summable (fun (ρ : NontrivialZero) => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (Hsum : ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero, liPairedSummand n ρ) :
    (∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1/2) ↔
    (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re) := by
  exact li_equiv_from_sum_formula hgenus Hsum

/-- Li's criterion equivalence under the standard analytic hypotheses, using the
paired sum formula generated by the M‑test + Cauchy route (captured as a
hypothesis `paired_sum_formula_of_mtest_and_cauchy`). -/
theorem li_criterion_equiv_of_standard_hypotheses
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s) :
    ((∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1 / 2) ↔
      (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)) := by
  -- Build the paired sum formula from the standard analytic hypotheses.
  have hsum : ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero, liPairedSummand n ρ :=
    paired_sum_formula_of_mtest_and_cauchy hgenus
      (separation_radius_exists_of_summable_inv_norm_sq hgenus) zero_pairing hhad
  -- Plug into the forward/backward equivalence
  exact li_equiv_from_sum_formula hgenus hsum

theorem li_criterion_equiv_of_weighted_standard_hypotheses
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : xiFactorizationProdWithMultiplicity) :
    ((∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1 / 2) ↔
      (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)) := by
  have hsum : ∀ n : ℕ,
      taylorCoeff riemannXi n
        = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
            (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ :=
    weighted_paired_sum_formula_of_standard_hypotheses hgenus hhad
  exact li_equiv_from_weighted_sum_formula hgenus hsum

/-- **Li's Criterion**: The Riemann Hypothesis is equivalent to the positivity
of all Li coefficients λₙ (here expressed as Taylor coefficients of ξ).

Uses the internally derived sum formula route. -/
theorem li_criterion_equiv
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s) :
    ((∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1 / 2) ↔
      (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)) :=
  li_criterion_equiv_of_standard_hypotheses hgenus hhad


end LiCriterion
