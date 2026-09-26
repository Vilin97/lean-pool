/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


/-
  Li's Criterion for the Riemann Hypothesis

  This file formalizes Li (1997), "The Positivity of a Sequence of Numbers and the Riemann
  Hypothesis".

  ## File Organization

  This file is organized to maintain 1:1 correspondence with the original Li paper:

  **PART I: PREREQUISITES** (NOT in Li's paper, but needed for formalization)
    - Definition of ξ and nontrivial zeros
    - Hadamard factorization theory (see Rh/HadamardFactorization.lean)
    - Functional equation consequences
    - General analysis facts

 ⚠️ These ax_ioms represent facts Li ASSUMES from the literature. For instance,
       Li writes "Write ξ(s) = ∏_ρ (1 - s/ρ)" without proof—this comes from
       Hadamard factorization + functional equation, which are external results.

  **PART II: LI'S PROOF** (following the paper structure exactly)
 - Setup and statement of theorem
 - Product formula (ASSUMED, not proven in Li's paper)
 - Key identity λ_n = ∑_ρ (1 - 1 / ρ)^n
 - Coefficient positivity
 - Forward direction (RH ⟹ λ_n ≥ 0)
 - Reverse direction (λ_n ≥ 0 ⟹ RH)

  ## Key Implementation Notes

 - |1 - 1 / ρ| = 1 on critical line → `modulus_eq_one_of_re_half`
 - Generating function → `logDeriv_phi_finite`,
  `generating_function_on_finset`
 - Recurrence relation → `sum_const_mul`
 - Positivity via unit circle parametrization

 Proof strategies: normalize variables, harvest
  non-vanishing conditions, close algebra with `field_simp` + `ring`.
-/

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Data.EReal.Inv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import LeanPool.LiCriterion.Lc.XiZeros
public import LeanPool.LiCriterion.Hadamard.Basic
public import LeanPool.LiCriterion.Hadamard.OrderOne.MultipliableFactors
public import LeanPool.LiCriterion.Lc.LiCriterion.MobiusMap
public import LeanPool.LiCriterion.Lc.LiCriterion.GenusOne
public import LeanPool.LiCriterion.Lc.LiCriterion.Pringsheim

/-! ## Basic setup and the key geometric observation

These geometric facts connect the critical line to the unit circle via the
Möbius transform z ↦ 1 - 1/z. This is essential in Li's proof.
-/

@[expose] public section

open Complex Real Set Function Filter
open scoped Topology ComplexConjugate


namespace LiCriterion

-- Nontrivial zeros in the critical strip.
--
-- NOTE: this is placed near the top so it can be used by early analytic/M-test lemmas.
/-- The zeros of the Riemann zeta function in the open critical strip. -/
noncomputable def NontrivialZero : Type :=
  {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

lemma NontrivialZero.ne_zero (ρ : NontrivialZero) : ρ.val ≠ 0 := by
  intro h
  exact (ne_of_gt ρ.property.2.1) (by simp [h])

lemma NontrivialZero.ne_one (ρ : NontrivialZero) : ρ.val ≠ 1 := by
  intro h
  exact (ne_of_lt ρ.property.2.2) (by simp [h])

/-
================================================================================
=                                                                              =
=  PART I: PREREQUISITES (External to Li's paper)                             =
=                                                                              =
=  These are facts that Li (1997) ASSUMES from the literature.                =
=  They are NOT proven in the Li paper itself.                                =
=                                                                              =
================================================================================
-/

/-! ### Geometry behind the criterion
The key geometric fact used throughout Li’s proof is that the Möbius transform
z ↦ 1 − 1/z maps the critical line Re(z) = 1 / 2 to the unit circle. We encode
this via exact norm-squared identities and their consequences.
-/

/-- Uniform bound for a single Li-term on a smaller disk.

If `0 < r₀ < r < 1` and `ball 0 r` avoids every pole `1 - 1 / ρ`, then on the smaller
ball `‖z‖ < r₀` we have a uniform bound
`‖1/(1-z) - 1 / (1 - 1 / ρ - z)‖ ≤ C / ‖ρ‖` with `C` depending only on `r₀` and `r`.

We take `C = 1 / ((1 - r₀) * (r - r₀))`, using
`‖1 - z‖ ≥ 1 - r₀` and `‖(1 - 1 / ρ) - z‖ ≥ r - r₀`. -/
lemma li_single_term_bound (r₀ r : ℝ) (_hr₀ : 0 < r₀) (hr₀_lt_r : r₀ < r) (hr_lt_one : r < 1)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ ρ : NontrivialZero, z ≠ 1 - 1/(ρ.val)) :
  ∃ C : ℝ, 0 < C ∧ ∀ ρ : NontrivialZero, ∀ z : ℂ,
    ‖z‖ < r₀ →
    ‖(1 / (1 - z) - 1 / (1 - 1/(ρ.val) - z))‖ ≤ C / ‖ρ.val‖ := by
  classical
  have hr₀_lt_one : r₀ < 1 := lt_trans hr₀_lt_r hr_lt_one
  have h_one_sub : 0 < 1 - r₀ := by linarith
  have h_r_sub : 0 < r - r₀ := by linarith
  let C : ℝ := (1 : ℝ) / ((1 - r₀) * (r - r₀))
  refine ⟨C, ?_, ?_⟩
  · have hden : 0 < (1 - r₀) * (r - r₀) := by positivity
    simpa [C] using (one_div_pos.mpr hden)
  · intro ρ z hz
    have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
    have hz_le : ‖z‖ ≤ r₀ := le_of_lt hz
    -- Poles lie outside the larger ball, hence `r ≤ ‖1 - 1 / ρ‖`.
    have hpole_ge : r ≤ ‖(1 : ℂ) - (1 : ℂ) / ρ.val‖ := by
      have : ¬ ‖(1 : ℂ) - (1 : ℂ) / ρ.val‖ < r := by
        intro hlt
        have hmem :
            ((1 : ℂ) - (1 : ℂ) / ρ.val) ∈ Metric.ball (0 : ℂ) r := by
          simpa [Metric.mem_ball, dist_zero_right] using hlt
        exact (havoid ((1 : ℂ) - (1 : ℂ) / ρ.val) hmem ρ) (by simp)
      exact le_of_not_gt this
    -- Lower bounds on the two denominators.
    have hnorm_one_sub : (1 - r₀) ≤ ‖(1 : ℂ) - z‖ := by
      have htmp : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
        simpa using (norm_sub_norm_le (1 : ℂ) z)
      have hle : (1 : ℝ) - r₀ ≤ (1 : ℝ) - ‖z‖ := by linarith
      exact le_trans hle htmp
    have hnorm_pole_sub : (r - r₀) ≤ ‖((1 : ℂ) - (1 : ℂ) / ρ.val) - z‖ := by
      have htmp :
          ‖(1 : ℂ) - (1 : ℂ) / ρ.val‖ - ‖z‖ ≤ ‖((1 : ℂ) - (1 : ℂ) / ρ.val) - z‖ := by
        simpa using (norm_sub_norm_le ((1 : ℂ) - (1 : ℂ) / ρ.val) z)
      have hle : (r - r₀) ≤ ‖(1 : ℂ) - (1 : ℂ) / ρ.val‖ - ‖z‖ := by linarith
      exact le_trans hle htmp
    have h₁ : (1 : ℂ) - z ≠ 0 := by
      have : 0 < ‖(1 : ℂ) - z‖ := lt_of_lt_of_le h_one_sub hnorm_one_sub
      exact (norm_pos_iff.mp this)
    have h₂ : (1 : ℂ) - (1 : ℂ) / ρ.val - z ≠ 0 := by
      have : 0 < ‖((1 : ℂ) - (1 : ℂ) / ρ.val) - z‖ := lt_of_lt_of_le h_r_sub hnorm_pole_sub
      have : ((1 : ℂ) - (1 : ℂ) / ρ.val) - z ≠ 0 := (norm_pos_iff.mp this)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    -- Clearing denominators introduces an extra factor `ρ - 1 - z*ρ`; supply its nonvanishing.
    have h₂mul : ρ.val - 1 - z * ρ.val ≠ 0 := by
      have hmul : ((1 : ℂ) - (1 : ℂ) / ρ.val - z) * ρ.val ≠ 0 := mul_ne_zero h₂ hρ0
      have heq : ((1 : ℂ) - (1 : ℂ) / ρ.val - z) * ρ.val = ρ.val - 1 - z * ρ.val := by
        field_simp [hρ0]
      intro h
      have : ((1 : ℂ) - (1 : ℂ) / ρ.val - z) * ρ.val = 0 := by
        calc
          ((1 : ℂ) - (1 : ℂ) / ρ.val - z) * ρ.val = ρ.val - 1 - z * ρ.val := heq
          _ = 0 := h
      exact hmul this
    have hdiff :
        (1 / ((1 : ℂ) - z) - 1 / ((1 : ℂ) - (1 : ℂ) / ρ.val - z)) =
          (-(1 / ρ.val)) / (((1 : ℂ) - z) * ((1 : ℂ) - (1 : ℂ) / ρ.val - z)) := by
      field_simp [h₁, h₂, hρ0, h₂mul]
      ring_nf
    have hprod_le :
        (1 - r₀) * (r - r₀) ≤ ‖(1 : ℂ) - z‖ * ‖(1 : ℂ) - (1 : ℂ) / ρ.val - z‖ := by
      have hB : (r - r₀) ≤ ‖(1 : ℂ) - (1 : ℂ) / ρ.val - z‖ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm_pole_sub
      exact mul_le_mul hnorm_one_sub hB (by linarith [h_r_sub]) (by exact norm_nonneg _)
    have hrecip :
        (1 : ℝ) / (‖(1 : ℂ) - z‖ * ‖(1 : ℂ) - (1 : ℂ) / ρ.val - z‖)
          ≤ (1 : ℝ) / ((1 - r₀) * (r - r₀)) :=
      one_div_le_one_div_of_le (by positivity : 0 < (1 - r₀) * (r - r₀)) hprod_le
    have hmul :=
      mul_le_mul_of_nonneg_left hrecip (norm_nonneg ((1 : ℂ) / ρ.val))
    calc
      ‖(1 / (1 - z) - 1 / (1 - 1/(ρ.val) - z))‖
          = ‖(1 / ((1 : ℂ) - z) - 1 / ((1 : ℂ) - (1 : ℂ) / ρ.val - z))‖ := by simp
      _ = ‖(-(1 / ρ.val)) / (((1 : ℂ) - z) * ((1 : ℂ) - (1 : ℂ) / ρ.val - z))‖ := by
          simpa using congrArg (fun w : ℂ => ‖w‖) hdiff
      _ = ‖(1 : ℂ) / ρ.val‖ / (‖(1 : ℂ) - z‖ * ‖(1 : ℂ) - (1 : ℂ) / ρ.val - z‖) := by
          simp
      _ = ‖(1 : ℂ) / ρ.val‖ *
            ((1 : ℝ) / (‖(1 : ℂ) - z‖ * ‖(1 : ℂ) - (1 : ℂ) / ρ.val - z‖)) := by
          simp [div_eq_mul_inv]
      _ ≤ ‖(1 : ℂ) / ρ.val‖ * ((1 : ℝ) / ((1 - r₀) * (r - r₀))) := by
          simpa [mul_left_comm, mul_comm] using hmul
      _ = C / ‖ρ.val‖ := by
          simp [C, div_eq_mul_inv, mul_left_comm, mul_comm]

/-!
### A useful algebraic rewrite for the paired Li term

This is a purely algebraic identity that rewrites the basic expression

`1/(1-z) - 1 / (1 - 1 / ρ - z)`

as a rational function of `s := 1/(1-z)` and `ρ`. It is convenient in genus‑1 arguments because
the paired combination `ρ` with `1-ρ` becomes `O(1/‖ρ‖^2)` after cancellation.
-/

private lemma one_sub_div_sub_one_eq_one_div_one_sub (b : ℂ) (hb : b ≠ 1) :
    (1 : ℂ) - b / (b - 1) = (1 : ℂ) / (1 - b) := by
  have hb0 : (1 : ℂ) - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hinv : (b - 1)⁻¹ = -((1 - b)⁻¹) := by
    have h : b - 1 = -(1 - b) := by ring
    rw [h]
    exact inv_neg (a := (1 - b))
  calc
    (1 : ℂ) - b / (b - 1)
        = (1 : ℂ) - b * (b - 1)⁻¹ := by simp [div_eq_mul_inv]
    _ = (1 : ℂ) - b * (-((1 - b)⁻¹)) := by simp [hinv]
    _ = (1 : ℂ) + b * (1 - b)⁻¹ := by ring
    _ = (1 : ℂ) / (1 - b) := by
          field_simp [hb0]
          ring

/-- Rewrite the basic term as `s^2 / (s - ρ)` with `s = 1/(1-z)`.

This form is the one in which the genus‑1 pairing `ρ ↦ 1-ρ` exhibits cancellation. -/
private lemma paired_term_eq_s_sq_div (ρ z : ℂ) (hz : z ≠ 1) (hρ : ρ ≠ 0)
    (hzρ : z ≠ 1 - 1 / ρ) :
    (1 / (1 - z) - 1 / (1 - 1 / ρ - z)) = (1 / (1 - z)) ^ 2 / ((1 / (1 - z)) - ρ) := by
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : (1 : ℂ) - (1 : ℂ) / ρ - z ≠ 0 := by
    intro h
    have : ((1 : ℂ) - (1 : ℂ) / ρ) - z = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    exact hzρ (sub_eq_zero.mp this).symm
  have h3 : (1 : ℂ) / ((1 : ℂ) - z) - ρ ≠ 0 := by
    intro h
    have hinv : (1 : ℂ) / ((1 : ℂ) - z) = ρ := sub_eq_zero.mp h
    have hmul : (ρ : ℂ) * ((1 : ℂ) - z) = 1 := by
      have := (eq_div_iff h1).1 hinv.symm
      simpa [mul_assoc] using this
    have h2' : (1 : ℂ) - z = (1 : ℂ) / ρ := by
      apply (eq_div_iff hρ).2
      simpa [mul_comm] using hmul
    have hz' : z = 1 - (1 : ℂ) / ρ := by
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - (1 : ℂ) / ρ := by simp [h2']
    exact hzρ hz'
  -- Clear denominators down to the single rational identity needed.
  field_simp [h1, h2, h3, hρ]
  -- Now rewrite the remaining goal as an identity in `b := (1-z)*ρ`.
  set b : ℂ := (1 - z) * ρ
  have hb : b ≠ 1 := by
    intro hb1
    have h1z : (1 : ℂ) - z = (1 : ℂ) / ρ := by
      apply (eq_div_iff hρ).2
      simp [b, hb1]
    have hz' : z = 1 - (1 : ℂ) / ρ := by
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - (1 : ℂ) / ρ := by simp [h1z]
    exact hzρ hz'
  have hden : ρ - 1 - z * ρ = b - 1 := by
    simp [b]
    ring
  simpa [b, hden] using (one_sub_div_sub_one_eq_one_div_one_sub b hb)

/-- Paired cancellation identity for the basic paired Li term.

Writing `s = 1/(1-z)`, the sum of the two terms at `ρ` and `1-ρ` collapses to a single fraction
with denominator `(s-ρ)(s-(1-ρ))`, revealing the `O(1/‖ρ‖²)` tail. -/
private lemma paired_term_pair_eq
    (ρ z : ℂ) (hz : z ≠ 1) (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    (hzρ : z ≠ 1 - 1 / ρ) (hzρ' : z ≠ 1 - 1 / (1 - ρ)) :
    (1 / (1 - z) - 1 / (1 - 1 / ρ - z)) + (1 / (1 - z) - 1 / (1 - 1 / (1 - ρ) - z)) =
      (1 / (1 - z)) ^ 2 * (2 * (1 / (1 - z)) - 1) /
        (((1 / (1 - z)) - ρ) * ((1 / (1 - z)) - (1 - ρ))) := by
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hρ' : (1 - ρ : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  -- Rewrite each term as `s^2/(s-ρ)` using `paired_term_eq_s_sq_div`.
  have hterm1 := paired_term_eq_s_sq_div (ρ := ρ) (z := z) hz hρ hzρ
  have hterm2 := paired_term_eq_s_sq_div (ρ := (1 - ρ)) (z := z) hz hρ' hzρ'
  have hterm :
      (1 / (1 - z) - 1 / (1 - 1 / ρ - z)) + (1 / (1 - z) - 1 / (1 - 1 / (1 - ρ) - z)) =
        (1 / (1 - z)) ^ 2 / ((1 / (1 - z)) - ρ) +
          (1 / (1 - z)) ^ 2 / ((1 / (1 - z)) - (1 - ρ)) := by
    simpa using congrArg₂ (fun x y : ℂ => x + y) hterm1 hterm2
  -- Reduce to an algebraic identity in `s = 1/(1-z)`.
  set s : ℂ := (1 : ℂ) / (1 - z)
  have hsρ : s - ρ ≠ 0 := by
    intro h
    have hs : s = ρ := sub_eq_zero.mp h
    have hinv : (1 : ℂ) / ((1 : ℂ) - z) = ρ := by simpa [s] using hs
    have hmul : (ρ : ℂ) * ((1 : ℂ) - z) = 1 := by
      have := (eq_div_iff h1).1 hinv.symm
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    have h2 : (1 : ℂ) - z = (1 : ℂ) / ρ := by
      apply (eq_div_iff hρ).2
      simpa [mul_comm] using hmul
    have hz' : z = 1 - (1 : ℂ) / ρ := by
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - (1 : ℂ) / ρ := by simp [h2]
    exact hzρ hz'
  have hsρ' : s - (1 - ρ) ≠ 0 := by
    intro h
    have hs : s = (1 - ρ) := sub_eq_zero.mp h
    have hinv : (1 : ℂ) / ((1 : ℂ) - z) = (1 - ρ) := by simpa [s] using hs
    have hmul : ((1 - ρ : ℂ) * ((1 : ℂ) - z)) = 1 := by
      have := (eq_div_iff h1).1 hinv.symm
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    have h2 : (1 : ℂ) - z = (1 : ℂ) / (1 - ρ) := by
      apply (eq_div_iff hρ').2
      simpa [mul_comm] using hmul
    have hz' : z = 1 - (1 : ℂ) / (1 - ρ) := by
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - (1 : ℂ) / (1 - ρ) := by simp [h2]
    exact hzρ' hz'
  -- Finish by clearing denominators.
  have : s ^ 2 / (s - ρ) + s ^ 2 / (s - (1 - ρ)) =
        s ^ 2 * (2 * s - 1) / ((s - ρ) * (s - (1 - ρ))) := by
    field_simp [hsρ, hsρ']
    ring
  have hfrac :
      (1 / (1 - z)) ^ 2 / ((1 / (1 - z)) - ρ) +
          (1 / (1 - z)) ^ 2 / ((1 / (1 - z)) - (1 - ρ))
        =
        (1 / (1 - z)) ^ 2 * (2 * (1 / (1 - z)) - 1) /
          (((1 / (1 - z)) - ρ) * ((1 / (1 - z)) - (1 - ρ))) := by
    simpa [s] using this
  -- Combine the rewrite with the algebraic simplification.
  exact hterm.trans hfrac

/-!
### Bounding the paired term by `O(‖ρ‖⁻²)`

For fixed `z` (away from the poles), the explicit cancellation identity above implies the paired
term is eventually bounded by `C(z) / ‖ρ‖²`. This is the input needed to deduce absolute
convergence of the paired series from the genus‑1 hypothesis `∑ 1/‖ρ‖² < ∞`.
-/

/-- Zeros come in conjugate pairs for real functions -/
lemma zeros_conjugate_pairs {f : ℂ → ℂ} (hf : ∀ z, f (star z) = star (f z))
    (ρ : ℂ) (hzero : f ρ = 0) : f (star ρ) = 0 := by
  rw [← star_eq_zero, ← hf]
  rw [star_star]
  exact hzero

/-! ## The modified function φ and its properties -/

/-- Given an entire function f(s) = ∏(1 - s/ρ), define φ(z) = f(1/(1-z)) -/
noncomputable def phi (f : ℂ → ℂ) (z : ℂ) : ℂ := f (1 / (1 - z))

/-- Eta-expanded form of `phi`, for rewriting under a binder. -/
lemma phi_eq (f : ℂ → ℂ) : phi f = fun z : ℂ => f (1 / (1 - z)) := rfl

/-- `phi` commutes with complex conjugation when `f` does. -/
lemma phi_conj {f : ℂ → ℂ} (hf : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    phi f (conj z) = conj (phi f z) := by
  unfold phi
  have hw : conj (1 / (1 - z)) = (1 : ℂ) / (1 - conj z) := by
    simp [div_eq_mul_inv]
  simpa [hw] using (hf (1 / (1 - z)))

/-- The logarithmic derivative of φ -/
noncomputable def logDeriv (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv φ z / φ z

/-- The project-local `logDeriv` is Mathlib's, definitionally. -/
lemma logDeriv_eq_rootLogDeriv (φ : ℂ → ℂ) : logDeriv φ = _root_.logDeriv φ := rfl

/-- `LiCriterion.logDeriv` commutes with conjugation when `φ` does. -/
lemma logDeriv_conj {φ : ℂ → ℂ} (hφ : ∀ z, φ (conj z) = conj (φ z)) (z : ℂ) :
    LiCriterion.logDeriv φ (conj z) = conj (LiCriterion.logDeriv φ z) := by
  unfold LiCriterion.logDeriv
  have hder : deriv φ (conj z) = conj (deriv φ z) :=
    deriv_conj_eq_of_conj_invariant (f := φ) hφ z
  calc
    deriv φ (conj z) / φ (conj z) = conj (deriv φ z) / conj (φ z) := by
      simp [hder, hφ z]
    _ = conj (deriv φ z / φ z) := by
      symm
      simp

/-- φ vanishes when 1/(1-z) = ρ, i.e., when z = 1 - 1 / ρ -/
lemma phi_zeros {f : ℂ → ℂ} (ρ : ℂ) (hρ : ρ ≠ 0)
    (hf : f ρ = 0) : phi f (1 - 1 / ρ) = 0 := by
  unfold phi
  have h1 : 1 - (1 - 1 / ρ) = 1 / ρ := by ring
  have h2 : 1 / (1 / ρ) = ρ := by field_simp
  rw [h1, h2]
  exact hf

/-- Helper: phi doesn't vanish in the unit disk when Re(ρ) ≤ 1 / 2 for all zeros -/
lemma phi_nonzero_in_unit_disk {f : ℂ → ℂ} (_hf_entire : Differentiable ℂ f)
    (h_zeros : ∀ ρ, f ρ = 0 → ρ ≠ 0 → ρ.re ≤ 1 / 2)
    {z : ℂ} (hz : ‖z‖ < 1) : phi f z ≠ 0 := by
  intro h_contra
  unfold phi at h_contra
  -- If phi f z = 0, then f(1/(1-z)) = 0
  -- So 1/(1-z) is a zero of f, call it ρ
  have h_nonzero : 1 - z ≠ 0 := by
    intro h_eq
    have z_eq_one : z = 1 := by
      rw [sub_eq_zero] at h_eq
      exact h_eq.symm
    have norm_one : ‖(1 : ℂ)‖ = 1 := by norm_num
    rw [z_eq_one] at hz
    rw [norm_one] at hz
    exact absurd hz (lt_irrefl 1)
  set ρ := 1 / (1 - z) with hρ_def
  have hρ_zero : f ρ = 0 := h_contra
  have hρ_ne : ρ ≠ 0 := by
    rw [hρ_def]
    exact one_div_ne_zero h_nonzero
  -- By hypothesis, Re(ρ) ≤ 1 / 2
  have h_re : ρ.re ≤ 1 / 2 := h_zeros ρ hρ_zero hρ_ne
  -- But by modulus_criterion, |z| < 1 implies |1 - 1 / ρ| < 1, which means Re(ρ) > 1 / 2
  have h_eq : z = 1 - 1 / ρ := by
    rw [hρ_def]
    field_simp
    ring
  rw [h_eq] at hz
  have h_mod : ρ.re > 1 / 2 := by
    rw [← modulus_criterion ρ hρ_ne]
    exact hz
  -- Contradiction
  linarith

/-- Helper: phi is differentiable on the unit disk -/
lemma phi_differentiable {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    {z : ℂ} (hz : ‖z‖ < 1) : DifferentiableAt ℂ (phi f) z := by
  unfold phi
  -- f(1/(1-z)) is differentiable at z
  apply hf_entire.differentiableAt.comp
  -- 1/(1-z) is differentiable at z when z ≠ 1
  have h_ne : (1 : ℂ) - z ≠ 0 := by
    intro h_eq
    have z_eq_one : z = 1 := by
      rw [sub_eq_zero] at h_eq
      exact h_eq.symm
    have norm_one : ‖(1 : ℂ)‖ = 1 := by norm_num
    rw [z_eq_one] at hz
    rw [norm_one] at hz
    exact absurd hz (lt_irrefl 1)
  exact DifferentiableAt.div (differentiableAt_const (c := (1 : ℂ)))
    (DifferentiableAt.sub (differentiableAt_const (c := (1 : ℂ))) differentiableAt_id) h_ne

/-- Helper: assumes f is analytic everywhere -/
lemma f_analytic_of_differentiable {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (z : ℂ) : AnalyticAt ℂ f z := by
  -- Use the theorem from CauchyIntegral: complex differentiable implies analytic
  exact hf_entire.analyticAt z

/-- Helper: phi is analytic on the unit disk -/
lemma phi_analytic {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ (phi f) z := by
  unfold phi
  -- phi f = f ∘ (λ w, 1/(1-w))
  apply AnalyticAt.comp
  · -- f is analytic at 1/(1-z)
    exact f_analytic_of_differentiable hf_entire _
  · -- The map w ↦ 1/(1-w) is analytic at z
    have h_ne : (1 : ℂ) - z ≠ 0 := by
      intro h_eq
      have z_eq_one : z = 1 := by
        rw [sub_eq_zero] at h_eq
        exact h_eq.symm
      have norm_one : ‖(1 : ℂ)‖ = 1 := by norm_num
      rw [z_eq_one] at hz
      rw [norm_one] at hz
      exact absurd hz (lt_irrefl 1)
    apply AnalyticAt.div
    · exact analyticAt_const
    · exact analyticAt_const.sub analyticAt_id
    · exact h_ne

/-- The logarithmic derivative is holomorphic on the unit disk
when all zeros satisfy `Re(ρ) ≤ 1 / 2`. -/
lemma logDeriv_holomorphic {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (h_zeros : ∀ ρ, f ρ = 0 → ρ ≠ 0 → ρ.re ≤ 1 / 2) :
    AnalyticOnNhd ℂ (logDeriv (phi f)) {z : ℂ | ‖z‖ < 1} := by
  unfold logDeriv
  intro z hz
  -- We need to show deriv (phi f) z / phi f z is analytic at z
  apply AnalyticAt.fun_div
  · -- deriv (phi f) is analytic at z
    apply AnalyticAt.deriv
    exact phi_analytic hf_entire hz
  · -- phi f is analytic at z
    exact phi_analytic hf_entire hz
  · -- phi f z ≠ 0
    exact phi_nonzero_in_unit_disk hf_entire h_zeros hz

/-! ## Taylor coefficients and their properties -/

/-- The Taylor coefficients of the logarithmic derivative -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (deriv^[n] (logDeriv (phi f))) 0 / n.factorial

/-- Helper: iterated derivatives distribute over multiplication by a constant (field case).

This version does *not* assume differentiability; it matches mathlib's convention that `deriv` is
`0` when the function is not differentiable at the point. -/
private lemma iteratedDeriv_const_mul_field (n : ℕ) (c : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    iteratedDeriv n (fun z => c * f z) x = c * iteratedDeriv n f x := by
  induction n generalizing x with
  | zero =>
      simp [iteratedDeriv_zero]
  | succ n ih =>
      have ih_fun : iteratedDeriv n (fun z => c * f z) = fun y => c * iteratedDeriv n f y := by
        funext y
        exact ih y
      simp [iteratedDeriv_succ]

/-- Helper: finite products of differentiable functions are differentiable -/
lemma differentiableAt_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ℂ)
    (hf : ∀ i ∈ S, DifferentiableAt ℂ (f i) s) :
    DifferentiableAt ℂ (fun t => ∏ i ∈ S, f i t) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableAt_const (c := (1 : ℂ))
  | @insert a T ha ih =>
    simp only [Finset.prod_insert ha]
    apply DifferentiableAt.mul
    · exact hf a (Finset.mem_insert_self a T)
    · apply ih
      intros i hi
      exact hf i (Finset.mem_insert_of_mem hi)

/-- Helper: derivative of a single factor -/
lemma deriv_single_factor (ρ : ℂ) (_ : ρ ≠ 0) (s : ℂ) :
    deriv (fun t => 1 - t/ρ) s = -1 / ρ := by
  have :
      deriv (fun t => (1 : ℂ) - t/ρ) s = deriv (fun t => (1 : ℂ)) s - deriv (fun t => t/ρ) s := by
    apply deriv_sub
    · exact differentiableAt_const (c := (1 : ℂ))
    · apply DifferentiableAt.div_const
      exact differentiableAt_id
  rw [this]
  have h1 : deriv (fun t => (1 : ℂ)) s = 0 := deriv_const _ _
  have h2 : deriv (fun t => t/ρ) s = 1 / ρ := by
    rw [deriv_div_const]
    simp only [deriv_id'', one_div]
  rw [h1, h2]
  simp only [zero_sub, neg_div, one_div]

/-- Iterated derivative of the zero function is the zero function. -/
private lemma iteratedDeriv_zero_fun (n : ℕ) :
    iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) = (fun _ : ℂ => (0 : ℂ)) := by
  induction n with
  | zero =>
      funext x
      simp []
  | succ k hk =>
      funext x
      simp []

/-- Distribute iterated derivatives over a finite sum at a point. -/
lemma iteratedDeriv_finset_sum
    {ι : Type*} (T : Finset ι) (f : ι → ℂ → ℂ) (n : ℕ)
    (hC : ∀ i ∈ T, ContDiffAt ℂ n (f i) 0) :
    iteratedDeriv n (fun z : ℂ => ∑ i ∈ T, f i z) 0
      = ∑ i ∈ T, iteratedDeriv n (f i) 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    -- Base: the sum is the zero function
    have h0 := congrArg (fun g : ℂ → ℂ => g 0) (iteratedDeriv_zero_fun n)
    simp
  | @insert a U ha ih =>
    have hCa : ContDiffAt ℂ n (f a) 0 := hC a (by simp)
    have hCU : ContDiffAt ℂ n (fun z : ℂ => ∑ i ∈ U, f i z) 0 := by
      -- Finite sum of `C^n` functions is `C^n` at the point.
      refine (ContDiffAt.sum (s := U) (f := fun i x => f i x) (x := (0 : ℂ)) (n := n)) ?_
      intro i hi; exact hC i (by exact Finset.mem_insert_of_mem hi)
    have hAdd := iteratedDeriv_add (hf := hCa) (hg := hCU)
    have hsum : iteratedDeriv n (fun z : ℂ => ∑ i ∈ U, f i z) 0
          = ∑ i ∈ U, iteratedDeriv n (f i) 0 :=
      ih (by intro i hi; exact hC i (Finset.mem_insert_of_mem hi))
    -- Chain equalities to rewrite both sides
    have : iteratedDeriv n (fun z : ℂ => ∑ i ∈ insert a U, f i z) 0
          = iteratedDeriv n (fun z : ℂ => f a z + ∑ i ∈ U, f i z) 0 := by
                simp [Finset.sum_insert ha]
    calc
      iteratedDeriv n (fun z : ℂ => ∑ i ∈ insert a U, f i z) 0
          = iteratedDeriv n (fun z : ℂ => f a z + ∑ i ∈ U, f i z) 0 := this
      _ = iteratedDeriv n (f a) 0 + iteratedDeriv n (fun z : ℂ => ∑ i ∈ U, f i z) 0 := hAdd
      _ = iteratedDeriv n (f a) 0 + ∑ i ∈ U, iteratedDeriv n (f i) 0 := by simpa using hsum
    -- Turn the RHS into a sum over insert
    simp [Finset.sum_insert ha]

/-- Helper lemma for algebraic manipulation in `logDeriv_phi_finite`.
    Key identity (with the *correct* pole at `z = 1 - 1 / ρ`). -/
private lemma logDeriv_algebraic_identity
    {z ρ : ℂ} (h_ne : 1 - z ≠ 0) (hρ_ne : ρ ≠ 0)
    (h_safe : (1 - 1 / ρ) - z ≠ 0) :
  (1/(1-z)^2) * ((1 / ρ) / (1 - (1/(1-z))/ρ))
    = 1/((1 - 1 / ρ) - z) - 1/(1-z) := by
  -- Let s = 1 - z
  set s : ℂ := 1 - z with hsdef
  have hs : s ≠ 0 := by simpa [hsdef] using h_ne
  -- From the safe hypothesis we get s - 1 / ρ ≠ 0
  have h_safe' : s - 1 / ρ ≠ 0 := by
    -- (1 - 1 / ρ) - z = (1 - z) - 1 / ρ by commutativity of addition
    simpa [hsdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_safe
  -- Consequently s*ρ - 1 ≠ 0 (since s*ρ - 1 = ρ*(s - 1 / ρ))
  have hsrho1_ne : s*ρ - 1 ≠ 0 := by
    intro h
    -- From s*ρ - 1 = 0, deduce s = 1 / ρ, contradicting h_safe'
    have hsρ1 : s*ρ = 1 := sub_eq_zero.mp h
    have : s = 1 / ρ := (eq_div_iff_mul_eq hρ_ne).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsρ1)
    exact h_safe' (by simp [this])
  -- Prove the identity by clearing denominators in one shot
  have hgoal : (1/s^2) * ((1 / ρ) / (1 - (1/s)/ρ)) = 1/(s - 1 / ρ) - 1/s := by
    field_simp [hs, hρ_ne, hsrho1_ne]; ring
  simpa [hsdef, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hgoal

/-- Helper: logarithmic derivative of a finite product -/
lemma logDeriv_finite_prod (S : Finset ℂ) (hS : 0 ∉ S) (s : ℂ) (hs : ∀ ρ ∈ S, s ≠ ρ) :
    let f := fun t => ∏ ρ ∈ S, (1 - t/ρ)
    deriv f s / f s = - ∑ ρ ∈ S, (1 / ρ) / (1 - s/ρ) := by
  -- Prove by induction on S
  induction S using Finset.induction_on with
  | empty =>
    -- Base case: empty product is 1, derivative is 0
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [deriv_const']
    simp only [zero_div, neg_zero]
  | @insert a T ha ih =>
    -- Inductive step
    intro f
    have ha0 : a ≠ 0 := by
      intro h
      rw [h] at ha
      have : 0 ∈ insert a T := by simp [h]
      exact hS this
    have hT0 : 0 ∉ T := by
      intro h
      have : 0 ∈ insert a T := Finset.mem_insert_of_mem h
      exact hS this
    have hsT : ∀ ρ ∈ T, s ≠ ρ := by
      intros ρ hρ
      exact hs ρ (Finset.mem_insert_of_mem hρ)
    have hsa : s ≠ a := hs a (Finset.mem_insert_self a T)
    -- Key: f(t) = (1 - t/a) * g(t) where g(t) = ∏_{ρ ∈ T} (1 - t/ρ)
    let g := fun t => ∏ ρ ∈ T, (1 - t/ρ)
    -- The product splits
    have prod_split : f = fun t => (1 - t/a) * g t := by
      ext t
      simp only [f, g, Finset.prod_insert ha]
    -- Apply product rule: (fg)' = f'g + fg'
    have deriv_prod : deriv f s = deriv (fun t => 1 - t/a) s * g s + (1 - s/a) * deriv g s := by
      rw [prod_split]
      have h1 : DifferentiableAt ℂ (fun t => (1 : ℂ) - t/a) s := by
        apply DifferentiableAt.sub
        · exact differentiableAt_const (c := (1 : ℂ))
        · apply DifferentiableAt.div_const
          exact differentiableAt_id
      have h2 : DifferentiableAt ℂ g s := by
        simp only [g]
        apply differentiableAt_finset_prod
        intros ρ hρ
        apply DifferentiableAt.sub
        · exact differentiableAt_const (c := (1 : ℂ))
        · apply DifferentiableAt.div_const
          exact differentiableAt_id
      exact deriv_mul h1 h2
    -- Compute f s
    have f_val : f s = (1 - s/a) * g s := by
      simp only [f, g, Finset.prod_insert ha]
    -- Now compute the logarithmic derivative
    calc deriv f s / f s
        = (deriv (fun t => 1 - t/a) s * g s + (1 - s/a) * deriv g s) / ((1 - s/a) * g s) := by
          rw [deriv_prod, f_val]
        _ = deriv (fun t => 1 - t/a) s / (1 - s/a) + deriv g s / g s := by
          -- We need to show:
          -- (deriv (fun t => 1 - t/a) s * g s + (1 - s/a) * deriv g s) / ((1 - s/a) * g s)
          -- = deriv (fun t => 1 - t/a) s / (1 - s/a) + deriv g s / g s
          have h_ne_a : (1 - s/a) ≠ 0 := by
            rw [sub_ne_zero]
            intro h
            have : s/a = 1 := h.symm
            have : s = a := by
              rw [div_eq_one_iff_eq] at this
              · exact this
              · exact ha0
            exact hsa this
          have h_ne_g : g s ≠ 0 := by
            simp only [g]
            apply Finset.prod_ne_zero_iff.mpr
            intros ρ hρ
            rw [sub_ne_zero]
            intro h
            have : s/ρ = 1 := h.symm
            have : s = ρ := by
              have hρ0 : ρ ≠ 0 := by
                intro h0
                rw [h0] at hρ
                exact hT0 hρ
              rw [div_eq_one_iff_eq] at this
              · exact this
              · exact hρ0
            exact hsT ρ hρ this
          -- Split the fraction
          rw [add_div]
          congr 1
          · -- First term: deriv (fun t => 1 - t/a) s * g s / ((1 - s/a) * g s)
            rw [mul_div_mul_right _ _ h_ne_g]
          · -- Second term: (1 - s/a) * deriv g s / ((1 - s/a) * g s)
            rw [mul_div_mul_left _ _ h_ne_a]
        _ = (-1/a) / (1 - s/a) + deriv g s / g s := by
          rw [deriv_single_factor a ha0]
        _ = -1/a / (1 - s/a) + (- ∑ ρ ∈ T, (1 / ρ) / (1 - s/ρ)) := by
          -- Apply induction hypothesis
          have ih_applied := ih hT0 hsT
          rw [ih_applied]
        _ = -(1/a / (1 - s/a) + ∑ ρ ∈ T, (1 / ρ) / (1 - s/ρ)) := by
          ring
        _ = - ∑ ρ ∈ insert a T, (1 / ρ) / (1 - s/ρ) := by
          rw [Finset.sum_insert ha]

/-- Helper: expansion of logarithmic derivative of phi for finite set -/
lemma logDeriv_phi_finite (S : Finset ℂ) (hS : 0 ∉ S) {z : ℂ} (hz : ‖z‖ < 1)
    (hz_safe : ∀ ρ ∈ S, z ≠ 1 - 1 / ρ) :
    let fS := fun s => ∏ ρ ∈ S, (1 - s/ρ)
    let φS := fun w => fS (1/(1-w))
    deriv φS z / φS z = ∑ ρ ∈ S, (1/(1-z) - 1/((1 - 1 / ρ) - z)) := by
  -- Introduce the let-bound definitions
  intro fS φS
  -- By chain rule: φS'(z) = fS'(1/(1-z)) * deriv(1/(1-z))
  -- where deriv(1/(1-z)) = 1/(1-z)²
  have h_ne : 1 - z ≠ 0 := by
    intro h
    have z_eq_one : z = 1 := by
      rw [sub_eq_zero] at h
      exact h.symm
    rw [z_eq_one] at hz
    have : ‖(1 : ℂ)‖ = 1 := by norm_num
    rw [this] at hz
    exact absurd hz (lt_irrefl 1)
  -- Step 1: Prove differentiability of the inverse function
  have h_inv_diff : DifferentiableAt ℂ (fun w => 1/(1-w)) z := by
    apply DifferentiableAt.div
    · exact differentiableAt_const (c := (1 : ℂ))
    · apply DifferentiableAt.sub
      · exact differentiableAt_const (c := (1 : ℂ))
      · exact differentiableAt_id
    · exact h_ne
  -- Step 2: Compute derivative of 1/(1-w)
  have h_inv_deriv : deriv (fun w => 1/(1-w)) z = 1/(1-z)^2 := by
    -- This is the standard derivative d/dw[1/(1-w)] = 1/(1-w)^2
    -- We use composition: 1/(1-w) = (1-w)⁻¹
    have eq_comp : (fun w : ℂ => 1/(1-w)) = (fun u : ℂ => u⁻¹) ∘ (fun w : ℂ => 1 - w) := by
      ext w
      simp only [Function.comp_apply]
      rw [inv_eq_one_div]
    rw [eq_comp]
    rw [deriv_comp z]
    · -- deriv of (u⁻¹) at (1-z) times deriv of (1-w) at z
      rw [deriv_inv]
      have h_deriv_sub : deriv (fun w => 1 - w) z = -1 := by
        have : deriv (fun w => 1 - w) z = deriv (fun w => (1 : ℂ)) z - deriv (fun w => w) z := by
          rw [← deriv_sub]
          · rfl
          · exact differentiableAt_const (c := (1 : ℂ))
          · exact differentiableAt_id
        rw [this, deriv_const]
        have : deriv (fun w : ℂ => w) z = 1 := by
          rw [deriv_id'']
        rw [this]
        ring
      rw [h_deriv_sub]
      simp only [neg_mul]
      rw [sq, inv_eq_one_div, one_div]
      ring
    · -- (1-z)⁻¹ is differentiable at (1-z)
      exact differentiableAt_inv h_ne
    · -- (1-w) is differentiable at z
      exact DifferentiableAt.sub (differentiableAt_const (c := (1 : ℂ))) differentiableAt_id
  -- Step 3: Check that 1/(1-z) ≠ ρ for all ρ ∈ S
  have h_safe : ∀ ρ ∈ S, 1/(1-z) ≠ ρ := by
    intro ρ hρ h_eq
    -- If 1/(1-z) = ρ, then solving for z gives z = 1 - 1 / ρ
    have h_ρ_ne : ρ ≠ 0 := fun h => hS (h ▸ hρ)
    have z_eq : z = 1 - 1 / ρ := by
      -- From 1/(1-z) = ρ, we get 1 = ρ(1-z)
      have h1 : 1 = ρ * (1 - z) := by
        rw [div_eq_iff h_ne] at h_eq
        exact h_eq
      -- So (1 - z) = 1 / ρ
      have hz_form : 1 - z = 1 / ρ := by
        -- From h1: 1 = ρ * (1 - z)
        -- Dividing both sides by ρ gives (1 - z) = 1 / ρ
        have : (1 - z) = 1 / ρ := by
          -- From h1: 1 = ρ * (1 - z), we get ρ * (1 - z) = 1
          have h_inv : ρ * (1 - z) = 1 := h1.symm
          -- Dividing both sides by ρ: (1 - z) = 1 / ρ
          have : (1 - z) * ρ = 1 := by rw [mul_comm]; exact h_inv
          field_simp [h_ρ_ne] at this ⊢
          exact this
        exact this
      -- Therefore z = 1 - 1 / ρ
      calc z = 1 - (1 - z) := by ring
           _ = 1 - 1 / ρ := by rw [hz_form]
    -- But this contradicts hz_safe
    exact hz_safe ρ hρ z_eq
  -- Step 4: Apply chain rule to φS = fS ∘ (λ w, 1/(1-w))
  have h_comp : φS = fS ∘ (fun w => 1/(1-w)) := rfl
  -- "This transformation with kernel K(z, ξ) = ξ z / (ξ - 1) is known as Mellin transform."
  -- The transformation z ↦ 1/(1-z) is key to Li's approach
  -- Step 5: fS is differentiable at 1/(1-z)
  have h_fS_diff : DifferentiableAt ℂ fS (1/(1-z)) := by
    apply differentiableAt_finset_prod
    intro ρ hρ
    apply DifferentiableAt.sub
    · exact differentiableAt_const (c := (1 : ℂ))
    · apply DifferentiableAt.div
      · exact differentiableAt_id
      · exact differentiableAt_const (c := ρ)
      · exact fun h => hS (h ▸ hρ)
  -- Step 6: Apply chain rule for logarithmic derivative
  calc deriv φS z / φS z
      = deriv (fS ∘ (fun w => 1/(1-w))) z / (fS (1/(1-z))) := by
        rw [h_comp]
        rfl
      _ = (deriv fS (1/(1-z)) * deriv (fun w => 1/(1-w)) z) / (fS (1/(1-z))) := by
        have : deriv (fS ∘ (fun w => 1/(1-w))) z =
               deriv fS (1/(1-z)) * deriv (fun w => 1/(1-w)) z := by
          -- Manual application of chain rule
          rw [← h_comp]
          have h1 : (fun w => 1/(1-w)) z = 1/(1-z) := rfl
          rw [← h1]
          exact deriv_comp z h_fS_diff h_inv_diff
        rw [this]
      _ = (deriv fS (1/(1-z)) / fS (1/(1-z))) * (1/(1-z)^2) := by
        rw [h_inv_deriv]
        ring
      _ = (- ∑ ρ ∈ S, (1 / ρ) / (1 - (1/(1-z))/ρ)) * (1/(1-z)^2) := by
        rw [logDeriv_finite_prod S hS (1/(1-z)) h_safe]
      _ = ∑ ρ ∈ S, (1/(1-z) - 1/((1 - 1 / ρ) - z)) := by
        -- EXPANDED ALGEBRAIC PROOF STRATEGY:
        -- We need to show:
        --   -(1 / ρ) / (1 - (1 / (1 - z)) / ρ) * (1 / (1 - z)^2)
        --     = 1 / (1 - z) - 1 / (1 - (1 - 1 / ρ) - z)
        -- Li's key insight:
        -- the transformation `s ↦ 1 / (1 - z)` maps the critical line to the unit circle.
        -- Step 1: Simplify the left denominator
        --   1 - (1 / (1 - z)) / ρ = 1 - 1 / (ρ * (1 - z))
        --     = (ρ * (1 - z) - 1) / (ρ * (1 - z))
        -- Step 2: Rewrite the left side
        --   LHS = -(1 / ρ) / [(ρ * (1 - z) - 1) / (ρ * (1 - z))] * (1 / (1 - z)^2)
        --       = -(1 / ρ) * (ρ * (1 - z)) / (ρ * (1 - z) - 1) * 1 / (1 - z)^2
        --       = -(1 - z) / ((ρ * (1 - z) - 1) * (1 - z))
        --       = -1 / (ρ * (1 - z) - 1)
        -- Step 3: Simplify the right side
        --   Note: 1 - (1 - 1 / ρ) = 1 / ρ, so
        --   `1 / (1 - (1 - 1 / ρ) - z) = 1 / (1 / ρ - z)`.
        --   RHS = 1 / (1 - z) - 1 / (1 / ρ - z)
        --       = [(1 / ρ - z) - (1 - z)] / [(1 - z) * (1 / ρ - z)]
        --       = (1 / ρ - 1) / [(1 - z) * (1 / ρ - z)]
        -- Step 4: Show LHS = RHS by proving:
        --   -1 / (ρ * (1 - z) - 1) = (1 / ρ - 1) / [(1 - z) * (1 / ρ - z)]
        --
        --   Cross multiply:
        --   `-(1 - z) * (1 / ρ - z) = (1 / ρ - 1) * (ρ * (1 - z) - 1)`.
        --
        -- The verification can be completed using field_simp to clear denominators
        -- followed by ring to verify the polynomial equality
        -- The key algebraic identity we need to prove:
        --   (- ∑ ρ ∈ S, (1 / ρ) / (1 - (1 / (1 - z)) / ρ)) * (1 / (1 - z)^2)
        --     = ∑ ρ ∈ S, (1 / (1 - z) - 1 / (1 - (1 - 1 / ρ) - z))
        -- Let's prove this is actually an algebraic identity, despite its complexity.
        -- We document exactly what needs to be proven and discharge it below.
        -- The proof strategy:
        -- 1. Rewrite the left side by pulling the negative inside.
        -- 2. Simplify `1 - (1 / (1 - z)) / ρ`.
        -- 3. Rewrite the rational factor as `-(1 - z) / (ρ * (1 - z) - 1)`.
        -- 4. Multiply by `1 / (1 - z)^2`.
        -- 5. Show the result equals `1 / (1 - z) - 1 / (1 / ρ - z)`.
        -- Let's prove this algebraic identity step by step
        -- We need to show each term in the sum transforms correctly
        -- Simplify the negatives
        simp only [neg_mul]
        -- Now we have:
        --   -(∑ ρ, (1 / ρ) / (1 - (1 / (1 - z)) / ρ)) * (1 / (1 - z)^2)
        --     = ∑ ρ, (1 / (1 - z) - 1 / (1 - (1 - 1 / ρ) - z))
        -- Push multiplication into the sum
        rw [mul_comm, Finset.mul_sum]
        -- Distribute the negative
        rw [← Finset.sum_neg_distrib]
        -- Now need:
        --   ∑ ρ, -((1 / (1 - z)^2) * (1 / ρ) / (1 - (1 / (1 - z)) / ρ))
        --     = ∑ ρ, (1 / (1 - z) - 1 / (1 - (1 - 1 / ρ) - z))
        apply Finset.sum_congr rfl
        intros ρ hρ
        -- For each ρ, we need to show:
        --   -((1 / (1 - z)^2) * (1 / ρ) / (1 - (1 / (1 - z)) / ρ))
        --     = 1 / (1 - z) - 1 / ((1 - 1 / ρ) - z)
        have hρ_ne : ρ ≠ 0 := fun h => hS (h ▸ hρ)
        -- Now need:
        --   -((1 / (1 - z)^2) * (1 / ρ) / (1 - (1 / (1 - z)) / ρ))
        --     = 1 / (1 - z) - 1 / ((1 - 1 / ρ) - z)
        -- First, let's handle the negative sign
        rw [neg_eq_iff_eq_neg]
        rw [neg_sub]
        -- Now the goal is:
        --   ((1 / (1 - z)^2) * ((1 / ρ) / (1 - ((1 / (1 - z)) / ρ))))
        --     = (1 / ((1 - (1 / ρ)) - z) - 1 / (1 - z))
        have h_safe : ((1 - (1 / ρ)) - z) ≠ 0 := by
          intro h
          have : z = (1 - (1 / ρ)) := by
            rw [sub_eq_zero] at h
            exact h.symm
          exact hz_safe ρ hρ this
        -- Apply the algebraic identity directly
        -- Convert x⁻¹ forms to 1/x to match the lemma exactly
        have h := logDeriv_algebraic_identity (z := z) (ρ := ρ) h_ne hρ_ne h_safe
        simpa [one_div] using h

/-- Helper: geometric series expansion -/
lemma geometric_expansion {a : ℂ} (ha : ‖a‖ < 1) :
    1/(1-a) = ∑' n : ℕ, a^n := by
  -- Standard geometric series: (1 - a)⁻¹ = ∑ a^n
  rw [tsum_geometric_of_norm_lt_one ha]
  rw [inv_eq_one_div]

/-- Iterated derivative at 0 of a reciprocal of a linear function.
    For c ≠ 0, we have: (deriv^[n] (fun z => 1/(c - z))) 0 = n! · c^(-(n+1)).
    Reference: uses `iter_deriv_inv_linear` from mathlib. -/
private lemma iter_deriv_inv_linear_eval_zero (n : ℕ) (c : ℂ) (_hc : c ≠ 0) :
    (deriv^[n] (fun z : ℂ => 1 / (c - z))) 0 = (n.factorial : ℂ) * c ^ (-(n+1 : ℤ)) := by
  -- Apply the closed form for derivatives of (c*z + d)⁻¹ with slope c = -1 and intercept d = c.
  have h := iter_deriv_inv_linear (k := n) (-1 : ℂ) c
  -- Evaluate at z = 0
  have h0 := congrArg (fun f => f 0) h
  -- Simplify (-1)^n * (-1)^n = 1, and (-(1:ℂ) * 0 + c) = c
  have hneg : (-1 : ℂ) ^ (n + n) = (1 : ℂ) := by
    rw [← two_mul]
    simp
  have hmul : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = (1 : ℂ) := by
    simpa [pow_add] using hneg
  -- Conclude
  simpa [one_div, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc, hmul] using h0

/-- `z ↦ 1/(c - z)` is analytic at `0` when `c ≠ 0`. -/
private lemma analyticAt_inv_linear (c : ℂ) (hc : c ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => 1 / (c - z)) 0 := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => c - z) 0 := (analyticAt_const.sub analyticAt_id)
  simpa [one_div, Pi.inv_def] using hlin.inv (by simpa using hc)

/-! ### Finite-sum algebra helpers -/

-- We freely use the algebraic identity
--   ∑ (1 - g x) = (S.card : ℂ) - ∑ g x
-- and the constant-pull identity
--   c * ∑ h x = ∑ c * h x
-- inline in the main derivation. These are standard Finset rewrites.

private lemma sum_const_mul
    {α : Type*} (S : Finset α) (c : ℂ) (f : α → ℂ) :
    ∑ x ∈ S, c * f x = c * ∑ x ∈ S, f x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a T ha ih =>
      simp [ha, ih, mul_add]

/-! ### Finite-sum algebra helpers (inline when needed) -/

/-- Li's coefficient formula for finite set (Theorem 1, equation 1.4) -/
lemma taylorCoeff_finite_Li (S : Finset ℂ) (hS : 0 ∉ S) (n : ℕ)
    (hS_safe : ∀ ρ ∈ S, ρ ≠ 1) :
    let fS := fun s => ∏ ρ ∈ S, (1 - s/ρ)
    let φS := fun z => fS (1/(1-z))
    -- Li's λₙ coefficient (note: our indexing is off by 1)
    (deriv^[n] (logDeriv φS)) 0 / n.factorial =
      ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
  intro fS φS
 -- Put φ(z) = ξ(1/(1-z)) = Σ_{n≥0} λ_n z^{n+1} for |z| < 1. (equation (1.4))
 -- By (1.3), λ_n = Σ_ρ [1 - (1 - 1 / ρ)^{n+1}] expressed via zeros of ζ.
  -- This is Li's key formula (1.4) from the 1997 paper
  -- Following Li's proof from the 1997 paper:
  -- Step 1: Use logDeriv_phi_finite to get φ'(z)/φ(z) = ∑ρ [1/(1-z) - 1/( (1-1 / ρ) - z )]
  have expansion : ∀ z, ‖z‖ < 1 → (∀ ρ ∈ S, z ≠ 1 - 1 / ρ) →
      deriv φS z / φS z = ∑ ρ ∈ S, (1/(1-z) - 1/((1-1 / ρ)-z)) := by
    intros z hz hz_safe
    exact logDeriv_phi_finite S hS hz hz_safe
  -- DETAILED POWER SERIES EXPANSION STRATEGY:
  -- Step 2: Power series expansions
  -- For |z| < 1: 1/(1-z) = ∑_{k=0}^∞ z^k (standard geometric series)
  -- For the second term, we need to be careful about the transformation:
  -- 1/(1-(1-1 / ρ)-z) = 1/(1 / ρ-z) = ρ/(1-ρz) when ρ ≠ 0
  -- Now, when |ρz| < 1 (which needs |z| < 1/|ρ|):
  -- ρ/(1-ρz) = ρ ∑_{k=0}^∞ (ρz)^k = ∑_{k=0}^∞ ρ^{k+1} z^k
  -- BUT this is NOT the form Li uses! Li's formula has (1 - (1-1 / ρ)^{n+1})
  -- The key insight: We need a different expansion
  -- Step 3: Alternative expansion using Li's approach
  -- Write a = 1 - 1 / ρ, so 1 - a = 1 / ρ
  -- Then: 1/(1-a-z) = 1/((1-a)(1 - z/(1-a)))
  --                 = (1/(1-a)) · (1 / (1 - z/(1-a)))
  --                 = (1/(1-a)) · ∑_{k=0}^∞ (z/(1-a))^k
  --                 = ∑_{k=0}^∞ (1-a)^{-(k+1)} z^k
  --                 = ∑_{k=0}^∞ (1 / ρ)^{-(k+1)} z^k  [since 1-a = 1 / ρ]
  -- Step 4: The difference of series
  -- 1/(1-z) - 1/(1-(1-1 / ρ)-z) = ∑_{k=0}^∞ z^k - ∑_{k=0}^∞ (1-a)^{-(k+1)} z^k
  --                            = ∑_{k=0}^∞ [1 - (1-a)^{-(k+1)}] z^k
  --                            = ∑_{k=0}^∞ [1 - (1 - 1 / ρ)^{-(k+1)}] z^k
  --                              [substituting back a = 1 - 1 / ρ]
  -- Step 5: Extracting the n-th Taylor coefficient
  -- The coefficient of z^n in φ'(z)/φ(z) is: ∑ρ [1 - (1-1 / ρ)^{-(n+1)}]
  -- But Li's formula has [1 - (1-1 / ρ)^{n+1}], not the negative power!
  -- Step 6: The resolution - sign convention
  -- When |1-1 / ρ| < 1 (which happens when Re(ρ) > 1 / 2):
  -- (1-1 / ρ)^{-(n+1)} = 1/(1-1 / ρ)^{n+1}
  -- So: 1 - (1-1 / ρ)^{-(n+1)} = 1 - 1/(1-1 / ρ)^{n+1}
  --                          = [(1-1 / ρ)^{n+1} - 1]/(1-1 / ρ)^{n+1}
  -- But Li writes it as: 1 - (1-1 / ρ)^{n+1}
  -- The apparent contradiction comes from different conventions in defining λₙ
  -- Li uses the convention where zeros inside |z| < 1 contribute positively
 -- "Let n (cid:31).(z)=1+: a zj. (1.5) We find that n (&amp;1)l&amp;1 * =n:: a }}}a"
 -- This is the recurrence-relation step from the original paper.
  -- The complete proof requires:
  -- 1. Verifying convergence of the power series for φ'(z)/φ(z) near z = 0
  -- 2. Using Cauchy's formula for derivatives: f^(n)(0) = n! · [coefficient of z^n]
  -- 3. Carefully tracking the sign conventions through the transformations
  -- Step 7: Coefficient/derivative extraction at 0 (analytic on a neighborhood of 0)
 -- Equality of the logarithmic derivative with the explicit finite sum
  classical
  let H : ℂ → ℂ := fun z => logDeriv φS z
  let G : ℂ → ℂ := fun z => ∑ ρ ∈ S, (1 / (1 - z) - 1/((1 - 1 / ρ) - z))
  have hEqOn : ∀ ⦃z : ℂ⦄, ‖z‖ < 1 → (∀ ρ ∈ S, z ≠ 1 - 1 / ρ) → H z = G z := by
    intro z hz hzsafe
    simpa [H, G, logDeriv, fS, φS] using (logDeriv_phi_finite S hS hz hzsafe)
  -- Build eventual equality at 0 using basic neighborhoods
  have evBall : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 := by
    have : IsOpen {z : ℂ | ‖z‖ < 1} :=
      (isOpen_lt continuous_norm (continuous_const : Continuous fun _ : ℂ => (1 : ℝ)))
    exact IsOpen.mem_nhds this (by simp)
  have evSafe : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ ρ ∈ S, z ≠ 1 - 1 / ρ := by
    classical
    -- For each ρ ∈ S, exclude the singleton {1 - 1 / ρ}
    have hEach : ∀ ρ ∈ S, ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 1 - 1 / ρ := by
      intro ρ hρ
      have hρne1 : ρ ≠ 1 := hS_safe ρ hρ
      have hne : (1 : ℂ) - 1 / ρ ≠ 0 := by
        intro h
        have : 1 / ρ = 1 := by simpa [sub_eq_add_neg] using sub_eq_zero.mp h
        have : ρ = 1 := by
          field_simp at this
          simpa using this
        exact hρne1 this
      have hopen : IsOpen ({z : ℂ | z ≠ 1 - 1 / ρ}) :=
        (isClosed_singleton (x := (1 - 1 / ρ))).isOpen_compl
      have hmem : (0 : ℂ) ∈ {z : ℂ | z ≠ 1 - 1 / ρ} := by
        have : 0 ≠ 1 - 1 / ρ := by
          simpa [ne_comm] using hne
        simpa using this
      exact IsOpen.mem_nhds hopen hmem
    -- Combine over the finite set S
    exact (Finset.eventually_all S).2 hEach
  have hEv : H =ᶠ[𝓝 (0 : ℂ)] G := by
    filter_upwards [evBall, evSafe] with z hz1 hz2
    exact hEqOn hz1 hz2
  -- Equality of all iterated derivatives at 0
  have hDerivEq : (deriv^[n] H) 0 = (deriv^[n] G) 0 := by
    simpa [iteratedDeriv_eq_iterate] using
      (Filter.EventuallyEq.iteratedDeriv_eq (n := n) hEv)
  -- From here, compute (deriv^[n] G) 0 by distributing over the finite sum and evaluating
  -- each term with `iter_deriv_inv_linear_eval_zero`, then divide by n!.
  classical
  -- Define the summand for each ρ
  let term : ℂ → (ℂ → ℂ) := fun ρ z => (1/((1 : ℂ) - z)) - 1/(((1 : ℂ) - 1 / ρ) - z)
  -- Each summand is analytic at 0 hence `C^n` at 0
  have hTermCont : ∀ ρ ∈ S, ContDiffAt ℂ n (term ρ) 0 := by
    intro ρ hρ
    have hA : AnalyticAt ℂ (fun z : ℂ => 1/((1 : ℂ) - z)) 0 := by
      simpa using analyticAt_inv_linear (1 : ℂ) (by simp)
    have hden : (1 : ℂ) - 1 / ρ ≠ 0 := by
      have hρne1 : ρ ≠ 1 := hS_safe ρ hρ
      intro h
      have : 1 / ρ = 1 := by simpa [sub_eq_add_neg] using sub_eq_zero.mp h
      have : ρ = 1 := by field_simp at this; simpa using this
      exact hρne1 this
    have hB : AnalyticAt ℂ (fun z : ℂ => 1/(((1 : ℂ) - 1 / ρ) - z)) 0 := by
      simpa using analyticAt_inv_linear (1 - 1 / ρ) hden
    have hAnal : AnalyticAt ℂ (fun z => term ρ z) 0 := (hA.sub hB)
    exact hAnal.contDiffAt
  -- Distribute the iterated derivative over the finite sum
  have hDist' : iteratedDeriv n (fun z : ℂ => ∑ ρ ∈ S, term ρ z) 0
      = ∑ ρ ∈ S, iteratedDeriv n (term ρ) 0 :=
    iteratedDeriv_finset_sum S term n hTermCont
  have hDist0 : (deriv^[n] (fun z : ℂ => ∑ ρ ∈ S, term ρ z)) 0
      = ∑ ρ ∈ S, (deriv^[n] (term ρ)) 0 := by
    simpa [iteratedDeriv_eq_iterate] using hDist'
  -- Evaluate each term at 0
  have hEach : ∀ ρ ∈ S,
      (deriv^[n] (term ρ)) 0 = (n.factorial : ℂ) * (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
    intro ρ hρ
    have h1 : (deriv^[n] (fun z : ℂ => 1/((1 : ℂ) - z))) 0 = (n.factorial : ℂ) := by
      simpa using iter_deriv_inv_linear_eval_zero n (1 : ℂ) (by simp)
    have hden : (1 : ℂ) - 1 / ρ ≠ 0 := by
      have hρne1 : ρ ≠ 1 := hS_safe ρ hρ
      intro h
      have : 1 / ρ = 1 := by simpa [sub_eq_add_neg] using sub_eq_zero.mp h
      have : ρ = 1 := by field_simp at this; simpa using this
      exact hρne1 this
    have h2 : (deriv^[n] (fun z : ℂ => 1/(((1 : ℂ) - 1 / ρ) - z))) 0
            = (n.factorial : ℂ) * (1 - 1 / ρ) ^ (-(n+1 : ℤ)) := by
      simpa using iter_deriv_inv_linear_eval_zero n (1 - 1 / ρ) hden
    -- Convenience: align notations with inv/one_div and `(-) - z` form
    have h1' : (deriv^[n] (fun z : ℂ => (1 - z)⁻¹)) 0 = (n.factorial : ℂ) := by
      simpa [one_div] using h1
    have h2' : (deriv^[n] (fun z : ℂ => (1 - ρ⁻¹ - z)⁻¹)) 0
            = (n.factorial : ℂ) * (1 - 1 / ρ) ^ (-(n+1 : ℤ)) := by
      -- rearrange 1 - 1 / ρ - z to ((1 : ℂ) - 1 / ρ) - z and rewrite with one_div
      simpa [one_div, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
    -- Use linearity: (f - g)^{(n)}(0) = f^{(n)}(0) - g^{(n)}(0)
    have hfC : ContDiffAt ℂ n (fun z : ℂ => 1/((1 : ℂ) - z)) 0 :=
      (analyticAt_inv_linear (1 : ℂ) (by simp)).contDiffAt
    have hgC : ContDiffAt ℂ n (fun z : ℂ => 1/(((1 : ℂ) - 1 / ρ) - z)) 0 :=
      (analyticAt_inv_linear (1 - 1 / ρ) hden).contDiffAt
    have hSub := iteratedDeriv_sub (hf := hfC) (hg := hgC)
    have hSub' : (deriv^[n] (term ρ)) 0
          = (deriv^[n] (fun z : ℂ => 1/((1 : ℂ) - z))) 0
            - (deriv^[n] (fun z : ℂ => 1/(((1 : ℂ) - 1 / ρ) - z))) 0 := by
      simpa [term, iteratedDeriv_eq_iterate, sub_eq_add_neg, Pi.add_def, Pi.neg_def,
      Pi.sub_def] using hSub
    -- Combine the previous facts in a `calc` to guide rewriting
    have : (deriv^[n] (term ρ)) 0
          = (n.factorial : ℂ) * (1 - (1 - 1 / ρ) ^ (-(n+1 : ℤ))) := by
      calc
        (deriv^[n] (term ρ)) 0
            = (deriv^[n] (fun z : ℂ => (1 - z)⁻¹)) 0
              - (deriv^[n] (fun z : ℂ => (1 - ρ⁻¹ - z)⁻¹)) 0 := by
                simpa [one_div] using hSub'
        _   = (n.factorial : ℂ) - (n.factorial : ℂ) * (1 - 1 / ρ) ^ (-(n+1 : ℤ)) := by
              simp [h1', h2']
        _   = (n.factorial : ℂ) * (1 - (1 - 1 / ρ) ^ (-(n+1 : ℤ))) := by
              ring
    exact this
  -- Sum and factor out n!
 -- φ(z) = ∑_{n≥0} λₙ z^{n+1}, so λₙ is the zⁿ coefficient of φ′/φ.
 -- λₙ = ∑_ρ [1 − (1 − 1 / ρ)^{n+1}] (Equation (1.4)); the calculation below
  --          turns `(deriv^[n] G) 0` into `n!` times a finite sum of `(1 − a_ρ)`
  --          with `a_ρ = (1 − 1 / ρ)^{−(n+1)}`.
  have hDG : (deriv^[n] G) 0
      = (n.factorial : ℂ) * ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
    classical
    have hcongr : ∀ ρ ∈ S, (deriv^[n] (term ρ)) 0
          = (n.factorial : ℂ) * (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := hEach
    calc
      (deriv^[n] G) 0 = (deriv^[n] (fun z : ℂ => ∑ ρ ∈ S, term ρ z)) 0 := rfl
      _ = ∑ ρ ∈ S, (deriv^[n] (term ρ)) 0 := hDist0
      _ = ∑ ρ ∈ S, (n.factorial : ℂ) * (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
            refine Finset.sum_congr rfl (by
              intro ρ hρ
              simpa using (hcongr ρ hρ))
      _ = (n.factorial : ℂ) * ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
            classical
            simpa using
              (sum_const_mul (S := S) (c := (n.factorial : ℂ))
                (f := fun ρ => (1 - (1 - 1 / ρ)^(-(n+1 : ℤ)))))
  -- (Optional) reshape to `S.card - ∑ a_ρ` form if needed downstream.
  -- kept as a comment: trivial by `Finset.sum_sub_distrib` + `Finset.sum_const`.
  -- Relate derivatives of H and G at 0, then divide by n!
 -- Using φ′/φ = G near 0 and coefficient-extraction via derivatives at 0.
 -- After division by n!, the right side matches Li’s λₙ finite-sum formula.
  have hMain : (deriv^[n] (logDeriv φS)) 0
      = (n.factorial : ℂ) * ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
    -- First, rewrite (deriv^[n] (logDeriv φS)) 0 as (deriv^[n] H) 0
    -- and use hDerivEq to switch to G, then apply hDG.
    calc
      (deriv^[n] (logDeriv φS)) 0
          = (deriv^[n] H) 0 := by rfl
      _   = (deriv^[n] G) 0 := hDerivEq
      _   = (n.factorial : ℂ) * ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := hDG
  -- Divide both sides by n!
 -- This isolates the coefficient:
  -- `(deriv^[n] (logDeriv φS)) 0 / n! = ∑ (1 − a_ρ)`.
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  have hdiv : (deriv^[n] (logDeriv φS)) 0 / (n.factorial : ℂ)
      = ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
    -- From hMain: A = (n!)*B, so A / n! = B
    -- Use `eq_of_mul_eq_mul_left` after rewriting division as multiplication by inverse
    have := hMain
    -- Turn the goal into a `simp` goal using `mul_div_cancel`
    -- by rewriting the target with hMain
    calc
      (deriv^[n] (logDeriv φS)) 0 / (n.factorial : ℂ)
          = ((n.factorial : ℂ) * ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ)))) / (n.factorial : ℂ) := by
                rw [this]
      _   = ∑ ρ ∈ S, (1 - (1 - 1 / ρ)^(-(n+1 : ℤ))) := by
                -- a*b/b = a when b ≠ 0
                have : (n.factorial : ℂ) ≠ 0 := hn0
                simp [this]
  -- Conclude by unfolding the definition of taylorCoeff at φS
  simpa [taylorCoeff, H, φS] using hdiv


/-! ## Further results -/

/-- The Riemann xi function in an entire form: ξ(s) = 1 / 2 · s(s-1) · Λ₀(s) + 1 / 2. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

/-- `riemannXi` commutes with complex conjugation. -/
lemma riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
    simpa using (map_natCast (starRingEnd ℂ) 2)
  unfold riemannXi
  simp [completedRiemannZeta₀_conj, h2, map_add, map_mul, map_sub]

/-- ξ is entire since it is a polynomial times the entire function `Λ₀`, plus a constant. -/
lemma xi_entire : Differentiable ℂ riemannXi := by
  unfold riemannXi
  -- Handle the product: (1 / 2) * s * (s-1) * completedRiemannZeta₀ s, then add the constant
  -- Build `s * (s - 1)`
  have hpoly : Differentiable ℂ (fun s : ℂ => s * (s - 1)) :=
    (differentiable_id.mul (Differentiable.sub differentiable_id (differentiable_const (1 : ℂ))))
  -- Multiply by the entire function `completedRiemannZeta₀`
  have hprod : Differentiable ℂ (fun s : ℂ => (s * (s - 1)) * completedRiemannZeta₀ s) := by
    exact hpoly.mul differentiable_completedZeta₀
  -- Finally multiply by the constant (1 / 2)
  have hconstmul : Differentiable ℂ
      (fun s : ℂ => (1 / 2 : ℂ) * ((s * (s - 1)) * completedRiemannZeta₀ s)) :=
    (differentiable_const (c := (1 / 2 : ℂ))).mul hprod
  -- Reassociate multiplications to match the target, then add the constant term 1 / 2.
  have hmain :
      Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hconstmul
  exact hmain.add (differentiable_const (c := (1 / 2 : ℂ)))

/-!
### Nonvanishing on the half-plane `Re(s) > 1`

This is a convenient bridge for the reverse direction: on `0 ≤ z < 1` we have
`s = 1/(1-z)` with `Re(s) > 1`, so `φ ξ` (and its log-derivative) are analytic there.
-/

lemma completedRiemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have : (1 : ℝ) < 0 := by simpa [h] using hs
    linarith
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  -- Rewrite `ζ(s)` as `Λ(s) / Γℝ(s)` and extract the numerator.
  have hzeta' : completedRiemannZeta s / Gammaℝ s ≠ 0 := by
    simpa [riemannZeta_def_of_ne_zero hs0] using hzeta
  exact (div_ne_zero_iff.1 hzeta').1

lemma riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have : (1 : ℝ) < 0 := by simpa [h] using hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hs' := hs
    simp [h] at hs'
  have hLambda : completedRiemannZeta s ≠ 0 := completedRiemannZeta_ne_zero_of_one_lt_re hs
  have hxi :
      riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
    simpa [LiCriterion.riemannXi, XiZeros.riemannXi] using
      (XiZeros.xi_eq_half_s_sm1_Lambda (s := s) hs0 hs1)
  -- All factors are nonzero on `Re(s) > 1`.
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hlin : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
    have hs_sub_one : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have : ((1 / 2 : ℂ) * s) ≠ 0 := mul_ne_zero hhalf hs0
    simpa [mul_assoc] using mul_ne_zero this hs_sub_one
  have : (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s ≠ 0 := by
    simpa [mul_assoc] using mul_ne_zero hlin hLambda
  simpa [hxi] using this

lemma phi_riemannXi_ne_zero_of_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    phi riemannXi (r : ℂ) ≠ 0 := by
  by_cases hrz : r = 0
  · subst hrz
    simp [phi, riemannXi]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
    have hden_pos : 0 < (1 : ℝ) - r := by linarith
    have hden_lt_one : (1 : ℝ) - r < 1 := sub_lt_self 1 hrpos
    have hs_real : (1 : ℝ) < 1 / ((1 : ℝ) - r) := one_lt_one_div hden_pos hden_lt_one
    have hdiv :
        (1 : ℂ) / (1 - (r : ℂ)) = ((1 / (1 - r) : ℝ) : ℂ) := by
      simp [Complex.ofReal_sub]
    have hs_re : (1 : ℝ) < ((1 : ℂ) / (1 - (r : ℂ))).re := by
      have hre : ((1 : ℂ) / (1 - (r : ℂ))).re = (1 / (1 - r) : ℝ) := by
        calc
          ((1 : ℂ) / (1 - (r : ℂ))).re = (((1 / (1 - r) : ℝ) : ℂ)).re := by
            exact congrArg Complex.re hdiv
          _ = (1 / (1 - r) : ℝ) := Complex.ofReal_re _
      -- Rewrite via `hre` *before* simp unfolds `re` of a division.
      rw [hre]
      simpa [one_div] using hs_real
    have : riemannXi ((1 : ℂ) / (1 - (r : ℂ))) ≠ 0 := riemannXi_ne_zero_of_one_lt_re hs_re
    simpa [phi] using this

lemma analyticAt_logDeriv_phi_riemannXi_of_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    AnalyticAt ℂ (_root_.logDeriv (phi riemannXi)) (r : ℂ) := by
  have hrnorm : ‖(r : ℂ)‖ < 1 := by
    -- `‖(r : ℂ)‖ = |r| = r` for `r ≥ 0`.
    have : ‖(r : ℂ)‖ = |r| := by exact RCLike.norm_ofReal (K := ℂ) r
    simpa [this, abs_of_nonneg hr0] using hr1
  have hphi : AnalyticAt ℂ (phi riemannXi) (r : ℂ) := phi_analytic xi_entire hrnorm
  have hphi_ne : phi riemannXi (r : ℂ) ≠ 0 := phi_riemannXi_ne_zero_of_real hr0 hr1
  have hderiv : AnalyticAt ℂ (deriv (phi riemannXi)) (r : ℂ) := hphi.deriv
  -- `logDeriv f = deriv f / f` as a pointwise quotient.
  simpa [_root_.logDeriv] using hderiv.div hphi hphi_ne

/-!
### Realness of Li coefficients

For the reverse direction, we use that the Taylor coefficients of `logDeriv (phi riemannXi)` at `0`
are real, so “nonnegativity of real parts” is the same as “nonnegativity”.
-/

lemma logDeriv_phi_riemannXi_conj (z : ℂ) :
    LiCriterion.logDeriv (phi riemannXi) (conj z)
      = conj (LiCriterion.logDeriv (phi riemannXi) z) := by
  have hφ : ∀ w : ℂ, phi riemannXi (conj w) = conj (phi riemannXi w) := by
    intro w
    exact phi_conj (f := riemannXi) riemannXi_conj w
  simpa using (logDeriv_conj (φ := phi riemannXi) hφ z)

theorem taylorCoeff_riemannXi_conj (n : ℕ) :
    conj (taylorCoeff riemannXi n) = taylorCoeff riemannXi n := by
  classical
  unfold taylorCoeff
  have hlog :
      ∀ z : ℂ,
        LiCriterion.logDeriv (phi riemannXi) (conj z)
          = conj (LiCriterion.logDeriv (phi riemannXi) z) :=
    logDeriv_phi_riemannXi_conj
  have h0 :
      conj ((deriv^[n] (LiCriterion.logDeriv (phi riemannXi))) 0)
        = (deriv^[n] (LiCriterion.logDeriv (phi riemannXi))) 0 := by
    simpa using
      (conj_iteratedDeriv_zero_of_conj_invariant
        (f := LiCriterion.logDeriv (phi riemannXi)) hlog n)
  have hfac : conj (n.factorial : ℂ) = (n.factorial : ℂ) := by
    simp
  calc
    conj ((deriv^[n] (LiCriterion.logDeriv (phi riemannXi))) 0 / (n.factorial : ℂ))
        =
        conj ((deriv^[n] (LiCriterion.logDeriv (phi riemannXi))) 0) / conj (n.factorial : ℂ) := by
          simp
    _ = (deriv^[n] (LiCriterion.logDeriv (phi riemannXi))) 0 / (n.factorial : ℂ) := by
          simp [h0, hfac]

theorem taylorCoeff_riemannXi_im (n : ℕ) : (taylorCoeff riemannXi n).im = 0 := by
  exact (Complex.conj_eq_iff_im).1 (taylorCoeff_riemannXi_conj n)

/-!
### A small but useful identity: `taylorCoeff` for `ξ^2`

This is the formal version of “the log-derivative of a square is twice the log-derivative”.
-/

/-- `taylorCoeff` for `ξ(s)^2` is twice `taylorCoeff` for `ξ(s)`. -/
theorem taylorCoeff_xi_sq (n : ℕ) :
    taylorCoeff (fun s : ℂ => (riemannXi s) ^ 2) n = (2 : ℂ) * taylorCoeff riemannXi n := by
  classical
  let g1 : ℂ → ℂ := _root_.logDeriv (phi (fun s : ℂ => (riemannXi s) ^ 2))
  let g2 : ℂ → ℂ := fun z => (2 : ℂ) * _root_.logDeriv (phi riemannXi) z
  have hEqOn : (Metric.ball (0 : ℂ) (1 : ℝ)).EqOn g1 g2 := by
    intro z hz
    have hz' : ‖z‖ < (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hdf : DifferentiableAt ℂ (phi riemannXi) z := phi_differentiable xi_entire hz'
    have hpow := logDeriv_fun_pow (f := phi riemannXi) (x := z) hdf 2
    have hphi : phi (fun s : ℂ => riemannXi s ^ 2) = fun x : ℂ => (phi riemannXi x) ^ 2 := by
      funext x
      simp [phi]
    simpa [g1, g2, hphi, LiCriterion.logDeriv, _root_.logDeriv] using hpow
  have hsopen : IsOpen (Metric.ball (0 : ℂ) (1 : ℝ)) := Metric.isOpen_ball
  have hEqIter : iteratedDeriv n g1 0 = iteratedDeriv n g2 0 := by
    have hEqOn' := Set.EqOn.iteratedDeriv_of_isOpen (f := g1) (g := g2)
      (s := Metric.ball (0 : ℂ) (1 : ℝ)) hEqOn hsopen n
    have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
      simp [Metric.mem_ball]
    exact hEqOn' hmem
  have hEqIter' : (deriv^[n] g1) 0 = (deriv^[n] g2) 0 := by
    simpa [iteratedDeriv_eq_iterate] using hEqIter
  have hconst :
      (deriv^[n] g2) 0 = (2 : ℂ) * (deriv^[n] (_root_.logDeriv (phi riemannXi))) 0 := by
    simpa only [g2, iteratedDeriv_eq_iterate] using
      (iteratedDeriv_const_mul_field n (2 : ℂ) (_root_.logDeriv (phi riemannXi)) 0)
  have hlog1 : logDeriv (phi (fun s : ℂ => riemannXi s ^ 2)) = g1 := by rfl
  have hlog2 : logDeriv (phi riemannXi) = _root_.logDeriv (phi riemannXi) := by rfl
  simp [taylorCoeff, hlog1, hlog2, hEqIter', hconst, mul_div_assoc]

/-- Functional equation for ξ: ξ(s) = ξ(1 - s).
    Uses `completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s` and
    `(1 - s) * ((1 - s) - 1) = s * (s - 1)`. -/
lemma xi_functional_equation (s : ℂ) : riemannXi s = riemannXi (1 - s) := by
  have hfe : completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
    completedRiemannZeta₀_one_sub s
  have hpoly : s * (s - 1) = (1 - s) * ((1 - s) - 1) := by ring
  calc
    riemannXi s
        = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ) := by
            rfl
    _   = (1 / 2 : ℂ) * ((1 - s) * ((1 - s) - 1)) * completedRiemannZeta₀ s + (1 / 2 : ℂ) := by
            -- replace the polynomial factor using `hpoly`
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              congrArg (fun t => (1 / 2 : ℂ) * t * completedRiemannZeta₀ s) hpoly
    _   = (1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) * completedRiemannZeta₀ (1 - s) + (1 / 2 : ℂ) := by
            -- replace Λ₀(s) by Λ₀(1 - s)
            have hfe' : completedRiemannZeta₀ s = completedRiemannZeta₀ (1 - s) := by
              simpa using hfe.symm
            simp [hfe', mul_comm, mul_left_comm, mul_assoc]
    _   = riemannXi (1 - s) := by
            unfold riemannXi; rfl
    _   = riemannXi (1 - s) := by
            unfold riemannXi; rfl

-- (Functional equation for ξ: ξ(s) = ξ(1 - s) can be added here; omitted to keep focus.)


/-
================================================================================
=                                                                              =
=  PART II: LI'S PROOF (Following the original paper exactly)                 =
=                                                                              =
=                                                                              =
================================================================================
-/

/-! ## Setup and Statement

Title and Introduction
Definition of λ_n = (1/(n-1)!) d^n/ds^n [s^(n-1) log ξ(s)]|_{s=1}
Theorem 1 statement
Main result: RH ↔ λ_n ≥ 0 for all n
Definition of θ(x) = ∑ e^(-πn²x)
-/

/-! ## Product Formula (ASSUMED in Li's paper)

⚠️ Li's paper states: "Write ξ(s) = ∏_ρ (1 - s/ρ)"

This formula is NOT proven in Li's paper—it is assumed from the literature.
It comes from:
  - Hadamard factorization: ξ(s) = e^(as+b) ∏(1-s/ρ)
  - Functional equation ξ(s) = ξ(1-s) + zero pairing ⟹ a = 0
  - Therefore: ξ(s) = e^b ∏_ρ (1 - s/ρ)

See PART I (Prerequisites) for the ax_ioms encoding these external results.
-/

/-! ## Key Identity

Define φ(z) = ξ(1/(1-z)), then RH ↔ φ'/φ analytic in unit disk
Generating function: φ'/φ = ∑_{n=0}^∞ λ_{n+1} z^n
Explicit formula: λ_n = ∑_ρ (1 - 1 / ρ)^n

This is the heart of Li's criterion.
-/

/-! ### A concrete form of the key identity -/

/-- Finite products of analytic functions are analytic. -/
lemma analyticAt_finset_prod {S : Finset ℂ} {f : ℂ → ℂ → ℂ} {z : ℂ}
    (h : ∀ ρ ∈ S, AnalyticAt ℂ (fun w => f ρ w) z) :
    AnalyticAt ℂ (fun w => ∏ ρ ∈ S, f ρ w) z := by
  induction S using Finset.induction_on with
  | empty =>
    -- Empty product is the constant 1
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a S ha ih =>
    -- Product over insert: (∏ ρ ∈ insert a S, f ρ w) = f a w * (∏ ρ ∈ S, f ρ w)
    simp only [Finset.prod_insert ha]
    apply AnalyticAt.mul
    · exact h a (Finset.mem_insert_self a S)
    · apply ih
      intro ρ hρ
      exact h ρ (Finset.mem_insert_of_mem hρ)

/-! ## Hadamard Product Representation for ξ

**Conway §XI.3**: Hadamard's Factorization Theorem
states that an entire function of finite order has a canonical product representation.
For ξ (entire of order 1), this gives: ξ(s) = C · ∏ρ (1 - s/ρ)
where ρ ranges over nontrivial zeros and C is a nonzero constant.

The connection between completedRiemannZeta₀ and the product formula is
standard in analytic number theory (see Titchmarsh, The Theory of the
Riemann Zeta-function). This will be proved rigorously once we have the
full Hadamard product machinery formalized. -/

/-!
### EXTERNAL PREREQUISITES: Hadamard factorization and ξ properties

⚠️ IMPORTANT: These ax_ioms are NOT proven in Li's paper!

Li's paper ASSUMES: "Write ξ(s) = ∏_ρ (1 - s/ρ)"
This formula comes from:
  1. General Hadamard factorization (see Rh/HadamardFactorization.lean)
  2. Properties of ξ (order 1, genus 1)
  3. Functional equation ξ(s) = ξ(1-s) (implies linear coefficient = 0)
  4. Zero pairing ρ ↔ 1-ρ

These are deep results from complex analysis, external to Li's paper.

References:
- Rh/HadamardFactorization.lean: General Hadamard theorem
- Hadamard's Theorem
- Product formula for ξ
- Titchmarsh, "The Theory of the Riemann Zeta-function"
- Where Li uses this formula
-/
/-- **EXTERNAL AXIOM 1**: The zeros of riemannXi are exactly the nontrivial zeros of ζ.

    ⚠️ NOT proven in Li's paper. This follows from the definition:
    ξ(s) = (1 / 2) s(s-1) π^(-s/2) Γ(s/2) ζ(s)
    and standard properties of Γ.

    Status: Should be provable from mathlib's definitions.
-/
-- External hypotheses: These are facts Li's paper assumes from the literature.
-- We keep the genuinely analytic-number-theory ones as axioms for now, but
-- discharge the definitional one (`xi_zeros_are_nontrivial_zeros`) via `Lc.XiZeros`.
theorem xi_zeros_are_nontrivial_zeros :
  ∀ s : ℂ, riemannXi s = 0 ↔ ∃ ρ : NontrivialZero, s = ρ.val := by
  intro s
  simpa [LiCriterion.riemannXi, XiZeros.riemannXi,
    LiCriterion.NontrivialZero, XiZeros.NontrivialZero] using
    (XiZeros.xi_zeros_are_nontrivial_zeros (s := s))

/-- A cheap “escape to infinity” lemma: a genus‑1 summability hypothesis forces `‖ρ‖ → ∞`
  along `cofinite`. -/
lemma eventually_le_norm_of_summable_inv_norm_sq
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ ρ : NontrivialZero in cofinite, R ≤ ‖ρ.val‖ := by
  have ht :
      Filter.Tendsto (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2) cofinite (𝓝 0) :=
    hgenus.tendsto_cofinite_zero
  have hεpos : 0 < (1 : ℝ) / R ^ 2 := by positivity
  have hsmall :
      ∀ᶠ ρ : NontrivialZero in cofinite, (1 : ℝ) / ‖ρ.val‖ ^ 2 < (1 : ℝ) / R ^ 2 :=
    (tendsto_order.1 ht).2 _ hεpos
  filter_upwards [hsmall] with ρ hρ
  -- If `‖ρ‖ < R` then `1/R^2 < 1/‖ρ‖^2`, contradicting `hρ`.
  have hpos : 0 < ‖ρ.val‖ := norm_pos_iff.2 (NontrivialZero.ne_zero ρ)
  have hpos_sq : 0 < ‖ρ.val‖ ^ 2 := by positivity
  have hRpos_sq : 0 < R ^ 2 := by positivity
  refine le_of_not_gt ?_
  intro hnorm_lt
  have hsq_lt : (‖ρ.val‖ : ℝ) ^ 2 < R ^ 2 := by
    have habs : |(‖ρ.val‖ : ℝ)| < |R| := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_pos hR] using hnorm_lt
    simpa using (sq_lt_sq.2 habs)
  have hcontra : (1 : ℝ) / R ^ 2 < (1 : ℝ) / ‖ρ.val‖ ^ 2 :=
    one_div_lt_one_div_of_lt hpos_sq hsq_lt
  exact (lt_asymm hρ hcontra).elim

/-- **EXTERNAL AXIOM** (genus 1 Hadamard factorization, centered at `1 / 2`).

This is an E₁-product form:

`ξ(s) = exp(a + b*s) * ∏' ρ, weierstrassE 1 ((s - 1 / 2) / (ρ - 1 / 2))`.

The shift by `1 / 2` aligns with the functional equation `ξ(s) = ξ(1-s)` and the pairing
`ρ ↦ 1 - ρ` (so the denominators negate). -/
def xiHadamardGenusOneShifted : Prop :=
  ∃ a b : ℂ, ∀ s : ℂ,
    riemannXi s =
      Complex.exp (a + b * s) *
        ∏' ρ : NontrivialZero,
          Hadamard.weierstrassE 1
            ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ)))

/-- Nontrivial zeros are paired by `ρ ↦ 1 - ρ`.

This is a consequence of the functional equation for the Riemann zeta function
(`riemannZeta_one_sub`) together with the defining inequalities `0 < Re(ρ) < 1`. -/
theorem zero_pairing : ∀ (ρ : NontrivialZero), ∃ (ρ' : NontrivialZero), ρ'.val = 1 - ρ.val := by
  intro ρ
  classical
  let s : ℂ := ρ.val
  have hs_not_neg : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have hs_pos : 0 < s.re := ρ.property.2.1
    have h_re : s.re = (- (n : ℂ)).re := by simp [s, hn]
    have h_re' : s.re = -(n : ℝ) := by simpa using h_re
    have hs_le : s.re ≤ 0 := by
      nlinarith [h_re']
    exact (not_lt.mpr hs_le) hs_pos
  have hs_ne_one : s ≠ 1 := by
    intro hs
    have hs_re : s.re = 1 := by simp [s, hs]
    exact (ne_of_lt ρ.property.2.2) hs_re
  have hζ : riemannZeta (1 - s) = 0 := by
    have hfe := riemannZeta_one_sub (s := s) hs_not_neg hs_ne_one
    -- The functional equation is a nonzero factor times ζ(s).
    simpa [s, ρ.property.1] using hfe
  refine ⟨⟨1 - s, ?_⟩, by simp [s]⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [s] using hζ
  · -- 0 < (1 - s).re  ↔  s.re < 1
    have : 0 < (1 - s).re := by
      -- (1 - s).re = 1 - s.re
      simpa [sub_re, one_re] using sub_pos.mpr ρ.property.2.2
    simpa [s] using this
  · -- (1 - s).re < 1  ↔  0 < s.re
    have : (1 - s).re < 1 := by
      -- (1 - s).re = 1 - s.re < 1 because s.re > 0
      have : 1 - s.re < 1 := sub_lt_self 1 ρ.property.2.1
      simpa [sub_re, one_re] using this
    simpa [s] using this

/-! ### The involution `ρ ↦ 1 - ρ` on nontrivial zeros -/

/-- Choose the paired zero `1 - ρ` given by `zero_pairing`. -/
noncomputable def pairedZero (ρ : NontrivialZero) : NontrivialZero :=
  Classical.choose (zero_pairing ρ)

@[simp] lemma pairedZero_val (ρ : NontrivialZero) : (pairedZero ρ).val = 1 - ρ.val :=
  Classical.choose_spec (zero_pairing ρ)

lemma pairedZero_involutive : Function.Involutive pairedZero := by
  intro ρ
  apply Subtype.ext
  calc
    (pairedZero (pairedZero ρ)).val = 1 - (pairedZero ρ).val := by simp
    _ = 1 - (1 - ρ.val) := by simp
    _ = ρ.val := by ring

/-- The involutive equivalence of nontrivial zeros induced by reflection `ρ ↦ 1 - ρ`. -/
noncomputable def pairedZeroEquiv : NontrivialZero ≃ NontrivialZero :=
  { toFun := pairedZero
    invFun := pairedZero
    left_inv := pairedZero_involutive
    right_inv := pairedZero_involutive }

@[simp] lemma coe_pairedZeroEquiv : ⇑pairedZeroEquiv = pairedZero := rfl

/-! ### Genus‑1 Hadamard: the linear term vanishes (shifted form)

We use the functional equation `ξ(s) = ξ(1-s)` and the involution `ρ ↦ 1-ρ` to show that in the
shifted genus‑1 Hadamard factorization `xiHadamardGenusOneShifted`, the linear coefficient is
forced to be `0`. The key symmetry is that the shifted E₁ product is invariant under `s ↦ 1-s`
(by reindexing via `pairedZeroEquiv`). -/

/-- The genus-one Weierstrass product over nontrivial zeros, centered at one half. -/
noncomputable def xiE1ShiftedProd (s : ℂ) : ℂ :=
  ∏' ρ : NontrivialZero,
    Hadamard.weierstrassE 1 ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ)))

/-- A convenient “already-centered” ξ factorization hypothesis used by the genus‑1 Li pipeline. -/
def xiFactorizationShiftedProd : Prop :=
  ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s

private lemma weierstrass_E_one_mul_neg (w : ℂ) :
    Hadamard.weierstrassE 1 w *
        Hadamard.weierstrassE 1 (-w) = 1 - w ^ 2 := by
  have hexp : Complex.exp w * Complex.exp (-w) = 1 := by
    calc
      Complex.exp w * Complex.exp (-w) = Complex.exp (w + (-w)) := by
        simpa using (Complex.exp_add w (-w)).symm
      _ = 1 := by simp
  calc
    Hadamard.weierstrassE 1 w *
        Hadamard.weierstrassE 1 (-w)
        = ((1 - w) * Complex.exp w) * ((1 - (-w)) * Complex.exp (-w)) := by
            simp [Hadamard.weierstrass_E_one]
    _ = ((1 - w) * (1 + w)) * (Complex.exp w * Complex.exp (-w)) := by
          ring
    _ = (1 - w ^ 2) * (Complex.exp w * Complex.exp (-w)) := by
          ring
    _ = (1 - w ^ 2) * 1 := by
          simp [hexp]
    _ = 1 - w ^ 2 := by simp

private lemma xiE1ShiftedProd_one_sub (s : ℂ) :
    xiE1ShiftedProd (1 - s) = xiE1ShiftedProd s := by
  classical
  -- Reindex by `ρ ↦ 1 - ρ`, which negates `(ρ - 1 / 2)` and hence negates the E₁ argument.
  have hterm (ρ : NontrivialZero) :
      Hadamard.weierstrassE 1
          (((1 - s) - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ)))
        =
      Hadamard.weierstrassE 1
          ((s - (1 / 2 : ℂ)) / ((pairedZero ρ).val - (1 / 2 : ℂ))) := by
    -- Reduce to the purely algebraic identity
    --   (2⁻¹ - s)/(ρ - 2⁻¹) = (s - 2⁻¹)/(2⁻¹ - ρ),
    -- then apply congruence.
    have hs' : (1 : ℂ) - s - (2⁻¹ : ℂ) = (2⁻¹ : ℂ) - s := by ring
    have hr' : (1 : ℂ) - (ρ.val : ℂ) - (2⁻¹ : ℂ) = (2⁻¹ : ℂ) - (ρ.val : ℂ) := by ring
    have hs : (2⁻¹ : ℂ) - s = -(s - (2⁻¹ : ℂ)) := by ring
    have hr : (2⁻¹ : ℂ) - (ρ.val : ℂ) = -((ρ.val : ℂ) - (2⁻¹ : ℂ)) := by ring
    -- First simplify the `pairedZero` denominator to `2⁻¹ - ρ`.
    simp only [one_div, pairedZero_val]
    -- Now prove equality of the E₁ arguments and finish by congruence.
    refine congrArg (Hadamard.weierstrassE 1) ?_
    -- First normalize `1 - s - 2⁻¹` and `1 - ρ - 2⁻¹` to `2⁻¹ - s` and `2⁻¹ - ρ`.
    rw [hs', hr']
    rw [hs, hr]
    calc
      (-(s - (2⁻¹ : ℂ))) / ((ρ.val : ℂ) - (2⁻¹ : ℂ))
          = -((s - (2⁻¹ : ℂ)) / ((ρ.val : ℂ) - (2⁻¹ : ℂ))) := by
              simpa using (neg_div ((ρ.val : ℂ) - (2⁻¹ : ℂ)) (s - (2⁻¹ : ℂ)))
      _ = (s - (2⁻¹ : ℂ)) / (-((ρ.val : ℂ) - (2⁻¹ : ℂ))) := by
              symm
              simpa using (div_neg (a := (s - (2⁻¹ : ℂ))) (b := ((ρ.val : ℂ) - (2⁻¹ : ℂ))))
  -- Now rewrite `xiE1ShiftedProd (1 - s)` pointwise using `hterm`, then reindex back.
  have hreindex :
      xiE1ShiftedProd (1 - s)
        =
        ∏' ρ : NontrivialZero,
          Hadamard.weierstrassE 1
            ((s - (1 / 2 : ℂ)) / ((pairedZero ρ).val - (1 / 2 : ℂ))) := by
    -- Use `tprod_congr` with the pointwise identity `hterm`.
    simpa [xiE1ShiftedProd] using (tprod_congr (fun ρ : NontrivialZero => hterm ρ))
  -- Reindex the right-hand side back to `xiE1ShiftedProd s`.
  let F : NontrivialZero → ℂ := fun ρ =>
    Hadamard.weierstrassE 1 ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ)))
  calc
    xiE1ShiftedProd (1 - s)
        = ∏' ρ : NontrivialZero, F (pairedZero ρ) := by
            -- unfold `F` and use `hreindex`
            simpa [xiE1ShiftedProd, F] using hreindex
    _ = ∏' ρ : NontrivialZero, F ρ := by
          simpa [coe_pairedZeroEquiv] using (pairedZeroEquiv.tprod_eq F)
    _ = xiE1ShiftedProd s := by
          simp [xiE1ShiftedProd, F]

/-- Derived: in a shifted genus‑1 Hadamard factorization for `ξ`, the linear coefficient is `0`. -/
theorem xi_hadamard_genus_one_shifted_linear_coeff_zero
    (hhad : xiHadamardGenusOneShifted) :
    xiFactorizationShiftedProd := by
  classical
  obtain ⟨a, b, hξ⟩ := hhad
  -- Abbreviate the product part.
  have hEq : ∀ s : ℂ,
      Complex.exp (a + b * s) * xiE1ShiftedProd s =
        Complex.exp (a + b * (1 - s)) * xiE1ShiftedProd s := by
    intro s
    -- Use the functional equation and the symmetry of the shifted product.
    calc
      Complex.exp (a + b * s) * xiE1ShiftedProd s = riemannXi s := by
        simpa [xiE1ShiftedProd] using (hξ s).symm
      _ = riemannXi (1 - s) := (xi_functional_equation s)
      _ = Complex.exp (a + b * (1 - s)) * xiE1ShiftedProd (1 - s) := by
        simpa [xiE1ShiftedProd] using (hξ (1 - s))
      _ = Complex.exp (a + b * (1 - s)) * xiE1ShiftedProd s := by
        simp [xiE1ShiftedProd_one_sub]
  -- `xiE1ShiftedProd 0` is nonzero since ξ(0)=1 / 2 and exp is never zero.
  have hP0_ne : xiE1ShiftedProd (0 : ℂ) ≠ 0 := by
    have hxi0_ne : riemannXi (0 : ℂ) ≠ 0 := by
      -- ξ(0) = 1 / 2
      unfold riemannXi; norm_num
    intro hP0
    have hx0 : riemannXi (0 : ℂ) = Complex.exp a * xiE1ShiftedProd (0 : ℂ) := by
      simpa [xiE1ShiftedProd, mul_zero, add_zero] using (hξ (0 : ℂ))
    have : riemannXi (0 : ℂ) = 0 := by
      simpa [hP0] using hx0
    exact hxi0_ne this
  -- First, `exp b = 1` from the functional equation at `s = 0`.
  have hb_exp : Complex.exp b = 1 := by
    have h0 := hEq (0 : ℂ)
    have h0' : Complex.exp a * xiE1ShiftedProd (0 : ℂ) =
        Complex.exp (a + b) * xiE1ShiftedProd (0 : ℂ) := by
      simpa [mul_zero, sub_zero, xiE1ShiftedProd] using h0
    have ha_eq : Complex.exp a = Complex.exp (a + b) :=
      mul_right_cancel₀ hP0_ne h0'
    have ha_ne : Complex.exp a ≠ 0 := Complex.exp_ne_zero a
    have ha_eq' : Complex.exp a = Complex.exp a * Complex.exp b := by
      calc
        Complex.exp a = Complex.exp (a + b) := ha_eq
        _ = Complex.exp a * Complex.exp b := by simpa using (Complex.exp_add a b)
    have ha_mul : Complex.exp a * (1 : ℂ) = Complex.exp a * Complex.exp b := by
      simpa [mul_one] using ha_eq'
    exact (mul_left_cancel₀ ha_ne ha_mul).symm
  -- Now differentiate at `s = 0` to force `b = 0`.
  have hP_diff : DifferentiableAt ℂ xiE1ShiftedProd (0 : ℂ) := by
    -- From the factorization, `xiE1ShiftedProd s = ξ(s) / exp(a + b*s)`.
    have hP_eq : ∀ s : ℂ, xiE1ShiftedProd s = riemannXi s / Complex.exp (a + b * s) := by
      intro s
      have hexp : Complex.exp (a + b * s) ≠ 0 := Complex.exp_ne_zero _
      have := congrArg (fun t => t / Complex.exp (a + b * s)) (hξ s)
      -- `(exp(..) * P s) / exp(..) = P s`
      simpa [xiE1ShiftedProd, mul_div_cancel_left₀, hexp, mul_assoc] using this.symm
    have hxi_diff : DifferentiableAt ℂ riemannXi (0 : ℂ) := xi_entire.differentiableAt
    have hexp_diff : DifferentiableAt ℂ (fun s : ℂ => Complex.exp (a + b * s)) (0 : ℂ) := by
      fun_prop
    have hexp_ne : Complex.exp (a + b * (0 : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hquot_diff :
        DifferentiableAt ℂ (fun s : ℂ => riemannXi s / Complex.exp (a + b * s)) (0 : ℂ) :=
      hxi_diff.div hexp_diff hexp_ne
    -- Rewrite by `hP_eq`.
    have hfun :
        (fun s : ℂ => riemannXi s / Complex.exp (a + b * s)) = xiE1ShiftedProd := by
      funext s
      simpa using (hP_eq s).symm
    simpa [hfun] using hquot_diff
  -- Differentiate the identity `hEq` at `0`.
  have hderiv_eq :
      deriv (fun s : ℂ => Complex.exp (a + b * s) * xiE1ShiftedProd s) (0 : ℂ)
        =
      deriv (fun s : ℂ => Complex.exp (a + b * (1 - s)) * xiE1ShiftedProd s) (0 : ℂ) := by
    have hfun :
        (fun s : ℂ => Complex.exp (a + b * s) * xiE1ShiftedProd s)
          =
        (fun s : ℂ => Complex.exp (a + b * (1 - s)) * xiE1ShiftedProd s) := by
      funext s; exact hEq s
    rw [hfun]
  -- Expand both derivatives using the product rule and simplify.
  have hdiff_exp1 : DifferentiableAt ℂ (fun s : ℂ => Complex.exp (a + b * s)) (0 : ℂ) := by
    fun_prop
  have hdiff_exp2 : DifferentiableAt ℂ (fun s : ℂ => Complex.exp (a + b * (1 - s))) (0 : ℂ) := by
    fun_prop
  have hderiv_mul1 :
      deriv (fun s : ℂ => Complex.exp (a + b * s) * xiE1ShiftedProd s) (0 : ℂ)
        =
      deriv (fun s : ℂ => Complex.exp (a + b * s)) (0 : ℂ) * xiE1ShiftedProd (0 : ℂ)
        + Complex.exp (a + b * (0 : ℂ)) * deriv xiE1ShiftedProd (0 : ℂ) := by
    simpa using
      (deriv_fun_mul (c := fun s : ℂ => Complex.exp (a + b * s)) (d := xiE1ShiftedProd)
        (x := (0 : ℂ)) hdiff_exp1 hP_diff)
  have hderiv_mul2 :
      deriv (fun s : ℂ => Complex.exp (a + b * (1 - s)) * xiE1ShiftedProd s) (0 : ℂ)
        =
      deriv (fun s : ℂ => Complex.exp (a + b * (1 - s))) (0 : ℂ) * xiE1ShiftedProd (0 : ℂ)
        + Complex.exp (a + b * (1 - (0 : ℂ))) * deriv xiE1ShiftedProd (0 : ℂ) := by
    simpa using
      (deriv_fun_mul (c := fun s : ℂ => Complex.exp (a + b * (1 - s))) (d := xiE1ShiftedProd)
        (x := (0 : ℂ)) hdiff_exp2 hP_diff)
  -- Compute the two exponential derivatives at 0.
  have hderiv_exp1 :
      deriv (fun s : ℂ => Complex.exp (a + b * s)) (0 : ℂ) = Complex.exp a * b := by
    have hinner :
        HasDerivAt (fun s : ℂ => a + b * s) b (0 : ℂ) := by
      have hmul : HasDerivAt (fun s : ℂ => b * s) b (0 : ℂ) := by
        -- rewrite `b*s` as `s*b`
        simpa [mul_comm] using (hasDerivAt_mul_const (x := (0 : ℂ)) b)
      -- Add the constant `a` on the left.
      simpa [add_assoc, add_comm, add_left_comm] using (hmul.const_add a)
    simpa [mul_zero, add_zero, mul_assoc] using (hinner.cexp.deriv)
  have hderiv_exp2 :
      deriv (fun s : ℂ => Complex.exp (a + b * (1 - s))) (0 : ℂ) = Complex.exp (a + b) * (-b) := by
    have hinner :
        HasDerivAt (fun s : ℂ => a + b * (1 - s)) (-b) (0 : ℂ) := by
      -- Rewrite `a + b*(1-s) = (a+b) + (-b)*s` and apply `const_add`.
      have hmul : HasDerivAt (fun s : ℂ => (-b) * s) (-b) (0 : ℂ) := by
        simpa [mul_comm] using (hasDerivAt_mul_const (x := (0 : ℂ)) (-b))
      have hrewrite :
          (fun s : ℂ => a + b * (1 - s)) = fun s : ℂ => (a + b) + (-b) * s := by
        funext s; ring
      have hadd : HasDerivAt (fun s : ℂ => (a + b) + (-b) * s) (-b) (0 : ℂ) := by
        simpa [add_assoc, add_comm, add_left_comm] using (hmul.const_add (a + b))
      simpa [hrewrite] using hadd
    simpa [mul_assoc] using (hinner.cexp.deriv)
  -- Use `exp b = 1` to simplify `exp (a + b)` to `exp a`.
  have hexp_ab : Complex.exp (a + b) = Complex.exp a := by
    calc
      Complex.exp (a + b) = Complex.exp a * Complex.exp b := by rw [Complex.exp_add]
      _ = Complex.exp a := by simp [hb_exp]
  -- Finish: cancel the common `deriv xiE1ShiftedProd 0` term and solve for `b = 0`.
  have hb_zero : b = 0 := by
    have hmain := hderiv_eq
    -- Expand both sides and rewrite the exponential derivatives.
    rw [hderiv_mul1, hderiv_mul2, hderiv_exp1, hderiv_exp2, hexp_ab] at hmain
    -- Normalize the remaining explicit evaluation at `0`.
    rw [sub_zero, mul_one, hexp_ab] at hmain
    -- After simplification, `hmain` already compares the `b`-terms; rewrite the right-hand side
    -- as `(exp a * (-b)) * P0`.
    have hcancel :
        (Complex.exp a * b) * xiE1ShiftedProd (0 : ℂ)
          =
        (Complex.exp a * (-b)) * xiE1ShiftedProd (0 : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg] using hmain
    have ha_ne : Complex.exp a ≠ 0 := Complex.exp_ne_zero a
    have hb_eq_neg : b = -b := by
      -- Cancel `xiE1ShiftedProd 0` and then `exp a`.
      have h1 : Complex.exp a * b = Complex.exp a * (-b) :=
        mul_right_cancel₀ hP0_ne (by simpa [mul_assoc] using hcancel)
      exact mul_left_cancel₀ ha_ne h1
    -- Conclude `b = 0` from `b = -b`.
    have hb_add : b + b = 0 := (eq_neg_iff_add_eq_zero).1 hb_eq_neg
    have hb2 : (2 : ℂ) * b = 0 := by
      simpa [two_mul] using hb_add
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hb2).resolve_left htwo
  -- With `b = 0`, the factorization has no linear term.
  refine ⟨a, ?_⟩
  intro s
  simpa [xiE1ShiftedProd, hb_zero] using hξ s

/-! ### Small derived lemmas for the paired/genus‑1 pipeline -/

/-- `ξ(1 / 2)` is nonzero: in the shifted product every factor has argument `0`. -/
lemma xi_half_ne_zero [Fact xiFactorizationShiftedProd] : riemannXi (1 / 2 : ℂ) ≠ 0 := by
  obtain ⟨a, hξ⟩ := (Fact.out : xiFactorizationShiftedProd)
  have hE : xiE1ShiftedProd (2⁻¹ : ℂ) = 1 := by
    -- Every factor is `E₁(0) = 1`.
    simp [xiE1ShiftedProd, Hadamard.weierstrass_E_one]
  have hhalf : riemannXi (2⁻¹ : ℂ) = Complex.exp a * xiE1ShiftedProd (2⁻¹ : ℂ) := by
    simpa using hξ (2⁻¹ : ℂ)
  have : riemannXi (1 / 2 : ℂ) = Complex.exp a := by
    simpa [hE] using hhalf
  -- `exp a` is never zero.
  exact this ▸ Complex.exp_ne_zero a

/-- A nontrivial zero is never equal to `1 / 2` (or else ξ would vanish there). -/
lemma NontrivialZero.ne_half [Fact xiFactorizationShiftedProd] (ρ : NontrivialZero) :
    ρ.val ≠ (1 / 2 : ℂ) := by
  intro hρ
  have hzero : riemannXi ρ.val = 0 :=
    (xi_zeros_are_nontrivial_zeros (s := ρ.val)).2 ⟨ρ, rfl⟩
  have : riemannXi (1 / 2 : ℂ) = 0 := by simpa [hρ] using hzero
  exact xi_half_ne_zero this

private lemma weierstrass_E_one_eq_zero_iff (w : ℂ) :
    Hadamard.weierstrassE 1 w = 0 ↔ w = 1 := by
  constructor
  · intro h
    -- `E₁(w) = (1-w) * exp(w)` and `exp(w) ≠ 0`.
    have : (1 - w) = 0 := by
      have hexp : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
      -- Cancel the nonzero exponential factor.
      have : (1 - w) * Complex.exp w = 0 := by
        simpa [Hadamard.weierstrass_E_one] using h
      exact (mul_eq_zero.mp this).resolve_right hexp
    simpa using (sub_eq_zero.mp this).symm
  · rintro rfl
    simp [Hadamard.weierstrass_E_one]

/-- `taylorCoeff` is invariant under multiplication by a nonzero constant. -/
lemma taylorCoeff_const_mul (c : ℂ) (hc : c ≠ 0) (f : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (fun s => c * f s) n = taylorCoeff f n := by
  classical
  unfold taylorCoeff
  have hlog : logDeriv (phi (fun s => c * f s)) = logDeriv (phi f) := by
    funext z
    have hphi : phi (fun s => c * f s) = fun w => c * phi f w := by
      funext w
      simp [phi]
    -- Drop the constant factor using Mathlib's `logDeriv_const_mul`.
    have : logDeriv (fun w => c * phi f w) z = logDeriv (phi f) z := by
      simpa [logDeriv, _root_.logDeriv, _root_.logDeriv_apply] using
        (logDeriv_const_mul (x := z) (a := c) (f := phi f) hc)
    simpa [hphi] using this
  simp [hlog]

/-- The paired quadratic factor (centered at `1 / 2`) used for ξ². -/
noncomputable def xiPairedFactor (ρ : NontrivialZero) (s : ℂ) : ℂ :=
  1 - (((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) ^ 2)

private lemma xiPairedFactor_eq_const_mul_pairLinear [Fact xiFactorizationShiftedProd]
    (ρ : NontrivialZero) (s : ℂ) :
    xiPairedFactor ρ s =
      (-(ρ.val * (pairedZero ρ).val) / (ρ.val - (1 / 2 : ℂ)) ^ 2) *
        ((1 - s / ρ.val) * (1 - s / (pairedZero ρ).val)) := by
  have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
  have hρ1 : (ρ.val : ℂ) ≠ 1 := NontrivialZero.ne_one ρ
  have hρhalf : (ρ.val : ℂ) - (1 / 2 : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (NontrivialZero.ne_half ρ)
  have h1ρ : (1 - (ρ.val : ℂ)) ≠ 0 := sub_ne_zero.mpr hρ1.symm
  -- Unfold and clear denominators.
  classical
  simp only [xiPairedFactor, pairedZero_val, div_pow]
  have hpoly : (1 - (ρ.val : ℂ) * 4 + (ρ.val : ℂ) ^ 2 * 4) ≠ 0 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    -- `1 - 4ρ + 4ρ^2 = 4*(ρ - 1 / 2)^2`.
    have hpoly_eq : (1 - (ρ.val : ℂ) * 4 + (ρ.val : ℂ) ^ 2 * 4) =
        (4 : ℂ) * ((ρ.val : ℂ) - (1 / 2 : ℂ)) ^ 2 := by ring
    -- The right-hand side is nonzero since `ρ ≠ 1 / 2`.
    refine ne_of_eq_of_ne hpoly_eq ?_
    exact mul_ne_zero h4 (pow_ne_zero 2 hρhalf)
  field_simp [hρ0, h1ρ, hρhalf, hpoly]
  ring_nf
  field_simp [hpoly]
  ring_nf

/-- A `φ`-pullback of the paired factor is nonzero on a “separation radius” ball. -/
lemma xiPairedFactor_phi_ne_zero_of_separation {z : ℂ}
    (hz1 : z ≠ (1 : ℂ))
    (hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ))
    (ρ : NontrivialZero) :
    xiPairedFactor ρ (1 / (1 - z)) ≠ 0 := by
  intro h0
  have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  -- Work directly from the definition of `xiPairedFactor` to avoid extra global hypotheses.
  set s : ℂ := (1 / (1 - z) : ℂ)
  have hx : (((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) ^ 2) = (1 : ℂ) := by
    have h0' :
        (1 : ℂ) - (((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) ^ 2) = 0 := by
      simpa [xiPairedFactor, s] using h0
    have : (1 : ℂ) = (((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) ^ 2) :=
      sub_eq_zero.mp h0'
    simpa using this.symm
  have hden : (ρ.val : ℂ) - (1 / 2 : ℂ) ≠ 0 := by
    intro hden0
    have hx_mul :
        ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) *
            ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) = (1 : ℂ) := by
      simpa [pow_two] using hx
    have hx_mul0 :
        ((s - (1 / 2 : ℂ)) / (0 : ℂ)) * ((s - (1 / 2 : ℂ)) / (0 : ℂ)) = (1 : ℂ) := by
      -- Avoid `simp` rewriting the goal to `False`; we only rewrite the denominator.
      have hx_mul0' := hx_mul
      rwa [hden0] at hx_mul0'
    have : (0 : ℂ) = (1 : ℂ) := by
      rwa [div_zero, zero_mul] at hx_mul0
    exact zero_ne_one this
  have hs : s = ρ.val ∨ s = (pairedZero ρ).val := by
    have hx' :
        ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) = 1 ∨
          ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) = -1 := (sq_eq_one_iff).1 hx
    rcases hx' with hx' | hx'
    · left
      have hsub : (s - (1 / 2 : ℂ)) = (ρ.val : ℂ) - (1 / 2 : ℂ) :=
        (div_eq_one_iff_eq hden).1 hx'
      have := congrArg (fun t : ℂ => t + (1 / 2 : ℂ)) hsub
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    · right
      have hsub : (s - (1 / 2 : ℂ)) = (-1 : ℂ) * ((ρ.val : ℂ) - (1 / 2 : ℂ)) :=
        (div_eq_iff hden).1 hx'
      have hsub' : (s - (1 / 2 : ℂ)) = -((ρ.val : ℂ) - (1 / 2 : ℂ)) := by
        simpa using hsub
      have hplus : s = -((ρ.val : ℂ) - (1 / 2 : ℂ)) + (1 / 2 : ℂ) := by
        have := congrArg (fun t : ℂ => t + (1 / 2 : ℂ)) hsub'
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have : s = (1 : ℂ) - ρ.val := by
        calc
          s = -((ρ.val : ℂ) - (1 / 2 : ℂ)) + (1 / 2 : ℂ) := hplus
          _ = (1 : ℂ) - ρ.val := by ring
      simpa [pairedZero_val] using this
  rcases hs with hs | hs
  · -- `1/(1-z) = ρ` gives the forbidden point `z = 1 - 1 / ρ`.
    have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
    have h1 : (ρ.val : ℂ) * ((1 : ℂ) - z) = 1 := by
      -- rewrite `ρ` as `1/(1-z)` and clear denominators
      have : (ρ.val : ℂ) = (1 : ℂ) / ((1 : ℂ) - z) := by
        simpa [s] using hs.symm
      -- multiply both sides by `(1-z)`
      calc
        (ρ.val : ℂ) * ((1 : ℂ) - z) = ((1 : ℂ) / ((1 : ℂ) - z)) * ((1 : ℂ) - z) := by
          rw [this]
        _ = 1 := by
          field_simp [hzsub]
    have h2 : (1 : ℂ) - z = (1 : ℂ) / ρ.val := by
      apply (eq_div_iff hρ0).2
      simpa [mul_comm] using h1
    have hz_eq : z = 1 - 1 / (ρ.val : ℂ) := by
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - 1 / (ρ.val : ℂ) := by simp [h2]
    exact hzavoid ρ hz_eq
  · -- `1/(1-z) = 1-ρ` gives the forbidden point for the paired zero.
    have hρ0 : ((pairedZero ρ).val : ℂ) ≠ 0 := NontrivialZero.ne_zero (pairedZero ρ)
    have h1 : ((pairedZero ρ).val : ℂ) * ((1 : ℂ) - z) = 1 := by
      have : ((pairedZero ρ).val : ℂ) = (1 : ℂ) / ((1 : ℂ) - z) := by
        simpa [s] using hs.symm
      calc
        ((pairedZero ρ).val : ℂ) * ((1 : ℂ) - z) =
            ((1 : ℂ) / ((1 : ℂ) - z)) * ((1 : ℂ) - z) := by
              rw [this]
        _ = 1 := by
          field_simp [hzsub]
    have h2 : (1 : ℂ) - z = (1 : ℂ) / (pairedZero ρ).val := by
      apply (eq_div_iff hρ0).2
      simpa [mul_comm] using h1
    have hz_eq : z = 1 - 1 / ((pairedZero ρ).val : ℂ) := by
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - 1 / ((pairedZero ρ).val : ℂ) := by simp [h2]
    exact hzavoid (pairedZero ρ) hz_eq

/-- The paired quadratic factor is an entire function of `s`. -/
lemma xiPairedFactor_differentiable (ρ : NontrivialZero) : Differentiable ℂ (xiPairedFactor ρ) := by
  unfold xiPairedFactor
  have hinner :
      Differentiable ℂ (fun s : ℂ => (s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) := by
    exact (differentiable_id.sub (differentiable_const (c := (1 / 2 : ℂ)))).div_const _
  have hsquare :
      Differentiable ℂ (fun s : ℂ => ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) ^ 2) := by
    simpa [pow_two, Pi.mul_def] using (hinner.mul hinner)
  simpa using (differentiable_const (c := (1 : ℂ))).sub hsquare

/-- A `φ`-pullback of the paired factor is differentiable on a ball inside the unit disk. -/
lemma xiPairedFactor_phi_differentiableOn_ball {r : ℝ} (hr_lt_one : r < 1) (ρ : NontrivialZero) :
    DifferentiableOn ℂ (fun z : ℂ => xiPairedFactor ρ (1 / (1 - z))) (Metric.ball (0 : ℂ) r) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by
    have : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact lt_of_lt_of_le this hr_lt_one.le
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    have : ¬ (‖z‖ : ℝ) < 1 := by simp [hz1]
    exact this hz'
  have h_sub_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz_ne_one.symm
  have h_inv_diff : DifferentiableAt ℂ (fun w : ℂ => 1 / (1 - w)) z := by
    apply DifferentiableAt.div
    · exact differentiableAt_const (c := (1 : ℂ))
    · exact (DifferentiableAt.sub (differentiableAt_const (c := (1 : ℂ))) differentiableAt_id)
    · exact h_sub_ne
  have h_pf_at : DifferentiableAt ℂ (xiPairedFactor ρ) (1 / (1 - z)) :=
    (xiPairedFactor_differentiable ρ).differentiableAt
  exact (h_pf_at.comp z h_inv_diff).differentiableWithinAt

/-- A crude M-test bound: on `‖z‖ < r < 1` and for `‖ρ‖ ≥ 1`, the paired factor satisfies
`‖xiPairedFactor ρ (1/(1-z)) - 1‖ = O(1/‖ρ‖²)` uniformly on the ball. -/
lemma xiPairedFactor_phi_norm_sub_one_le_of_one_le_norm {r : ℝ} (hr_lt_one : r < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) {ρ : NontrivialZero} (hρ : (1 : ℝ) ≤ ‖ρ.val‖) :
    ‖xiPairedFactor ρ (1 / (1 - z)) - 1‖
      ≤ (4 * ((1 / (1 - r) + (1 / 2 : ℝ)) ^ 2)) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  -- This lemma is only used for M-test style bounds, so we keep the estimate deliberately crude.
  have hz_norm : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    have hz_lt_one : (‖z‖ : ℝ) < 1 := lt_of_lt_of_le hz_norm hr_lt_one.le
    exact (ne_of_lt hz_lt_one) (by simp [hz1])
  have h_sub_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz_ne_one.symm
  -- Bound `‖1/(1-z)‖` by `1/(1-r)` on the ball.
  have h_inv_bound : ‖(1 : ℂ) / ((1 : ℂ) - z)‖ ≤ (1 : ℝ) / (1 - r) := by
    have h1 : (1 - r) ≤ ‖(1 : ℂ) - z‖ := by
      have htmp : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
        simpa using (norm_sub_norm_le (1 : ℂ) z)
      have hle : (1 : ℝ) - r ≤ (1 : ℝ) - ‖z‖ := by linarith [hz_norm.le]
      exact le_trans hle htmp
    have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
    have hrecip : (1 : ℝ) / ‖(1 : ℂ) - z‖ ≤ (1 : ℝ) / ((1 : ℝ) - r) :=
      one_div_le_one_div_of_le hpos h1
    simpa [div_eq_mul_inv] using hrecip
  -- Bound `‖1/(1-z) - 1 / 2‖` by `1/(1-r) + 1 / 2`.
  have hA : ‖(1 : ℂ) / ((1 : ℂ) - z) - (1 / 2 : ℂ)‖ ≤ (1 : ℝ) / (1 - r) + (1 / 2 : ℝ) := by
    have htri :
        ‖(1 : ℂ) / ((1 : ℂ) - z) - (1 / 2 : ℂ)‖ ≤
          ‖(1 : ℂ) / ((1 : ℂ) - z)‖ + ‖(1 / 2 : ℂ)‖ := by
      simpa [sub_eq_add_neg] using
        (norm_add_le ((1 : ℂ) / ((1 : ℂ) - z)) (-(1 / 2 : ℂ)))
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    nlinarith [htri, h_inv_bound, hhalf]
  -- Compare `‖ρ - 1 / 2‖` to `‖ρ‖`.
  have hρhalf : (ρ.val : ℂ) - (1 / 2 : ℂ) ≠ 0 := by
    have hρne : (ρ.val : ℂ) ≠ (1 / 2 : ℂ) := by
      intro hEq
      have hnorm : (‖ρ.val‖ : ℝ) = (1 / 2 : ℝ) := by
        simp [hEq]
      have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by simpa [hnorm] using hρ
      nlinarith
    exact sub_ne_zero.mpr hρne
  have hden_ge0 : (‖ρ.val‖ : ℝ) - (1 / 2 : ℝ) ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ := by
    simpa using (norm_sub_norm_le (ρ.val : ℂ) (1 / 2 : ℂ))
  have hden_ge : (‖ρ.val‖ : ℝ) / 2 ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ := by
    have : (‖ρ.val‖ : ℝ) / 2 ≤ (‖ρ.val‖ : ℝ) - (1 / 2 : ℝ) := by linarith [hρ]
    exact le_trans this hden_ge0
  have hden_pos : 0 < ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ := norm_pos_iff.2 hρhalf
  -- Rewrite and bound norms, using `‖-(a/b)^2‖ = ‖a‖^2 / ‖b‖^2`.
  have hnorm :
      ‖xiPairedFactor ρ (1 / (1 - z)) - 1‖
        =
        ‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ ^ 2 / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
    calc
      ‖xiPairedFactor ρ (1 / (1 - z)) - 1‖
          =
          ‖-((((1 / (1 - z) : ℂ) - (1 / 2 : ℂ)) / ((ρ.val : ℂ) - (1 / 2 : ℂ))) ^ 2)‖ := by
            simp [xiPairedFactor]
      _ = ‖(((1 / (1 - z) : ℂ) - (1 / 2 : ℂ)) / ((ρ.val : ℂ) - (1 / 2 : ℂ))) ^ 2‖ := by
            simp
      _ = ‖(((1 / (1 - z) : ℂ) - (1 / 2 : ℂ)) / ((ρ.val : ℂ) - (1 / 2 : ℂ)))‖ ^ 2 := by
            exact norm_pow
              (((1 / (1 - z) : ℂ) - (1 / 2 : ℂ)) / ((ρ.val : ℂ) - (1 / 2 : ℂ))) 2
      _ = (‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖) ^ 2 := by
            simp
      _ = ‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ ^ 2 / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
            simp [div_pow]
  -- Use the bound on the numerator and the `‖ρ-1 / 2‖ ≥ ‖ρ‖/2` denominator estimate.
  rw [hnorm]
  have hnum_sq :
      ‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ ^ 2 ≤ ((1 : ℝ) / (1 - r) + (1 / 2 : ℝ)) ^ 2 :=
    by
      -- square `hA`
      have hA_nonneg : 0 ≤ ‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ := by positivity
      have hB_nonneg : 0 ≤ (1 : ℝ) / (1 - r) + (1 / 2 : ℝ) := by
        have hpos : 0 < (1 : ℝ) - r := by linarith [hr_lt_one]
        have hnonneg1 : 0 ≤ (1 : ℝ) / (1 - r) := by
          exact (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hpos.le)
        have hnonneg2 : 0 ≤ (1 / 2 : ℝ) := by norm_num
        linarith
      -- `mul_le_mul` gives `a*a ≤ b*b`
      simpa [pow_two] using mul_le_mul hA hA hA_nonneg hB_nonneg
  have hden_sq :
      ((‖ρ.val‖ : ℝ) / 2) ^ 2 ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
    -- square `hden_ge`
    have hC_nonneg : 0 ≤ (‖ρ.val‖ : ℝ) / 2 := by positivity
    have hD_nonneg : 0 ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ := by positivity
    simpa [pow_two] using mul_le_mul hden_ge hden_ge hC_nonneg hD_nonneg
  have hpos_den : 0 < ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by positivity
  have hpos_rho : 0 < (‖ρ.val‖ : ℝ) := norm_pos_iff.2 (NontrivialZero.ne_zero ρ)
  have hpos_rho_sq : 0 < (‖ρ.val‖ : ℝ) ^ 2 := by positivity
  have hinv_den :
      (1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 ≤ (4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    -- invert the squared inequality
    have hrecip :
        (1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 ≤ (1 : ℝ) / (((‖ρ.val‖ : ℝ) / 2) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hden_sq
    -- simplify
    have hsimp :
        (1 : ℝ) / (((‖ρ.val‖ : ℝ) / 2) ^ 2) = (4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
      field_simp [hpos_rho_sq.ne']
      norm_num
    simpa [hsimp] using hrecip
  -- combine: (num^2 / den^2) ≤ (A^2) * (4/‖ρ‖^2)
  have hmain :
      ‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ ^ 2 / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2
        ≤ ((1 : ℝ) / (1 - r) + (1 / 2 : ℝ)) ^ 2 * ((4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2)) := by
    have hnonneg : 0 ≤ ((1 : ℝ) / (1 - r) + (1 / 2 : ℝ)) ^ 2 := by positivity
    have : ‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ ^ 2 / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2
        = ‖(1 / (1 - z) : ℂ) - (1 / 2 : ℂ)‖ ^ 2 * ((1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2) := by
      simp [div_eq_mul_inv]
    rw [this]
    refine mul_le_mul hnum_sq hinv_den (by positivity) (by positivity)
  -- Rearrange constants to match the statement.
  have hrearr :
      ((1 : ℝ) / (1 - r) + (1 / 2 : ℝ)) ^ 2 * ((4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2))
        = (4 : ℝ) * ((1 : ℝ) / (1 - r) + (1 / 2 : ℝ)) ^ 2 * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    ring
  simpa [hrearr, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Uniform-in-`z` version of
`xiPairedFactor_phi_norm_sub_one_le_of_one_le_norm` on a fixed ball. -/
lemma xiPairedFactor_phi_norm_sub_one_le_of_one_le_norm_on_ball {r : ℝ} (hr_lt_one : r < 1)
    {ρ : NontrivialZero} (hρ : (1 : ℝ) ≤ ‖ρ.val‖) :
    ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖xiPairedFactor ρ (1 / (1 - z)) - 1‖
        ≤ (4 * ((1 / (1 - r) + (1 / 2 : ℝ)) ^ 2)) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  intro z hz
  exact xiPairedFactor_phi_norm_sub_one_le_of_one_le_norm
    (r := r) hr_lt_one (z := z) hz (ρ := ρ) hρ

/-- Cofinite version: for `z` in a fixed ball, the paired factor is eventually `O(1/‖ρ‖²)`. -/
lemma xiPairedFactor_phi_norm_sub_one_le_eventually_of_genus_one {r : ℝ} (hr_lt_one : r < 1)
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) :
    ∀ᶠ ρ : NontrivialZero in Filter.cofinite,
      ‖xiPairedFactor ρ (1 / (1 - z)) - 1‖
        ≤ (4 * ((1 / (1 - r) + (1 / 2 : ℝ)) ^ 2)) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hlarge :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, (1 : ℝ) ≤ ‖ρ.val‖ :=
    eventually_le_norm_of_summable_inv_norm_sq hgenus (R := 1) (by norm_num)
  filter_upwards [hlarge] with ρ hρ
  exact xiPairedFactor_phi_norm_sub_one_le_of_one_le_norm (r := r) hr_lt_one (z := z) hz (ρ := ρ) hρ

/-- The paired factors form a locally uniformly convergent infinite product on any ball
`‖z‖ < r < 1`. -/
lemma xiPairedFactor_phi_multipliableLocallyUniformlyOn_ball_of_genus_one
    {r : ℝ} (hr_lt_one : r < 1)
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2)) :
    MultipliableLocallyUniformlyOn
      (fun ρ : NontrivialZero => fun z : ℂ => xiPairedFactor ρ (1 / (1 - z)))
      (Metric.ball (0 : ℂ) r) := by
  classical
  let K : Set ℂ := Metric.ball (0 : ℂ) r
  let g : NontrivialZero → ℂ → ℂ :=
    fun ρ z => xiPairedFactor ρ (1 / (1 - z)) - 1
  let C : ℝ := (4 * ((1 / (1 - r) + (1 / 2 : ℝ)) ^ 2))
  let u : NontrivialZero → ℝ := fun ρ => C * ((1 : ℝ) / ‖ρ.val‖ ^ 2)
  have hu : Summable u := by
    simpa [u] using (hgenus.mul_left C)
  have hbound :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, ∀ z ∈ K, ‖g ρ z‖ ≤ u ρ := by
    have hlarge :
        ∀ᶠ ρ : NontrivialZero in Filter.cofinite, (1 : ℝ) ≤ ‖ρ.val‖ :=
      eventually_le_norm_of_summable_inv_norm_sq hgenus (R := 1) (by norm_num)
    filter_upwards [hlarge] with ρ hρ z hz
    have h :=
      xiPairedFactor_phi_norm_sub_one_le_of_one_le_norm_on_ball (r := r) hr_lt_one (ρ := ρ) hρ z hz
    simpa [g, u, C] using h
  have hcts : ∀ ρ : NontrivialZero, ContinuousOn (g ρ) K := by
    intro ρ
    have hdiff :
        DifferentiableOn ℂ (fun z : ℂ => xiPairedFactor ρ (1 / (1 - z))) K :=
      xiPairedFactor_phi_differentiableOn_ball (r := r) hr_lt_one ρ
    simpa [g, Pi.sub_def] using (hdiff.continuousOn.sub continuousOn_const)
  have ht : MultipliableLocallyUniformlyOn (fun ρ z ↦ (1 : ℂ) + g ρ z) K :=
    Summable.multipliableLocallyUniformlyOn_one_add (K := K) Metric.isOpen_ball hu hbound hcts
  simpa [K, g, add_sub_assoc] using ht

/-- For `z` in a “separation radius” ball, the paired infinite product does not vanish. -/
lemma xiPairedFactor_phi_tprod_ne_zero_of_separation_of_genus_one {r : ℝ} (hr_lt_one : r < 1)
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r)
    (hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ)) :
    (∏' ρ : NontrivialZero, xiPairedFactor ρ (1 / (1 - z))) ≠ 0 := by
  classical
  let g : NontrivialZero → ℂ := fun ρ => xiPairedFactor ρ (1 / (1 - z)) - 1
  let C : ℝ := (4 * ((1 / (1 - r) + (1 / 2 : ℝ)) ^ 2))
  have hdom : Summable (fun ρ : NontrivialZero => C * ((1 : ℝ) / ‖ρ.val‖ ^ 2)) :=
    hgenus.mul_left C
  have hbound :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, ‖g ρ‖ ≤ C * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    simpa [g, C] using
      (xiPairedFactor_phi_norm_sub_one_le_eventually_of_genus_one
        (r := r) hr_lt_one hgenus (z := z) hz)
  have hsum : Summable (fun ρ : NontrivialZero => ‖g ρ‖) := by
    refine Summable.of_norm_bounded_eventually hdom ?_
    filter_upwards [hbound] with ρ hρ
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (g ρ))] using hρ
  have hz1 : z ≠ (1 : ℂ) := by
    intro hz1
    have hz_norm : ‖z‖ < 1 := by
      have : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      exact lt_of_lt_of_le this hr_lt_one.le
    exact (ne_of_lt hz_norm) (by simp [hz1])
  have hterm_ne : ∀ ρ : NontrivialZero, (1 : ℂ) + g ρ ≠ 0 := by
    intro ρ
    have hfac : xiPairedFactor ρ (1 / (1 - z)) ≠ 0 :=
      xiPairedFactor_phi_ne_zero_of_separation (z := z) hz1 hzavoid ρ
    have : (1 : ℂ) + g ρ = xiPairedFactor ρ (1 / (1 - z)) := by
      simp [g]
    simpa [this] using hfac
  have hprod_ne : (∏' ρ : NontrivialZero, ((1 : ℂ) + g ρ)) ≠ 0 :=
    _root_.tprod_one_add_ne_zero_of_summable (ι := NontrivialZero) (R := ℂ)
      (f := g) (hf := hterm_ne) (hu := hsum)
  have hprod_eq :
      (∏' ρ : NontrivialZero, ((1 : ℂ) + g ρ)) =
        ∏' ρ : NontrivialZero, xiPairedFactor ρ (1 / (1 - z)) := by
    refine tprod_congr ?_
    intro ρ
    simp [g]
  simpa [hprod_eq] using hprod_ne

/-- Explicit derivative of the paired quadratic factor. -/
lemma deriv_xiPairedFactor (ρ : NontrivialZero) (s : ℂ) :
    deriv (xiPairedFactor ρ) s =
      -(2 : ℂ) * ((s - (1 / 2 : ℂ)) / ((ρ.val - (1 / 2 : ℂ)) ^ 2)) := by
  classical
  unfold xiPairedFactor
  -- abbreviate the inner affine map
  let h : ℂ → ℂ := fun s : ℂ => (s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))
  have hdiff : DifferentiableAt ℂ h s := by
    dsimp [h]
    exact (differentiableAt_id.sub (differentiableAt_const (c := (1 / 2 : ℂ)))).div_const _
  have hderiv : deriv h s = (1 : ℂ) / (ρ.val - (1 / 2 : ℂ)) := by
    have h' :=
      (deriv_div_const (c := fun s : ℂ => s - (1 / 2 : ℂ)) (d := (ρ.val - (1 / 2 : ℂ))) (x := s))
    -- `deriv (fun s => s - 1 / 2) = 1`
    convert h' using 1
    simp
  have hpow : deriv (fun s : ℂ => (h s) ^ 2) s = (2 : ℂ) * h s * deriv h s := by
    simpa [pow_two, Pi.mul_def] using (deriv_pow (f := h) (x := s) hdiff 2)
  have hsub : deriv (fun s : ℂ => (1 : ℂ) - (h s) ^ 2) s = -deriv (fun s : ℂ => (h s) ^ 2) s := by
    simp
  have hmul : h s * deriv h s = (s - (1 / 2 : ℂ)) / ((ρ.val - (1 / 2 : ℂ)) ^ 2) := by
    -- substitute and simplify
    simp [h, div_eq_mul_inv, pow_two, mul_left_comm, mul_comm]
  calc
    deriv (fun s : ℂ => (1 : ℂ) - (h s) ^ 2) s
        = -deriv (fun s : ℂ => (h s) ^ 2) s := hsub
    _ = -((2 : ℂ) * h s * deriv h s) := by simp [hpow]
    _ = -((2 : ℂ) * ((s - (1 / 2 : ℂ)) / ((ρ.val - (1 / 2 : ℂ)) ^ 2))) := by
          simpa [mul_assoc] using congrArg (fun z : ℂ => -((2 : ℂ) * z)) hmul
    _ = -(2 : ℂ) * ((s - (1 / 2 : ℂ)) / ((ρ.val - (1 / 2 : ℂ)) ^ 2)) := by
          ring

/-- Derivative of the Möbius map `z ↦ 1/(1-z)` away from `z = 1`. -/
lemma deriv_one_div_one_sub {z : ℂ} (hz : (1 : ℂ) - z ≠ 0) :
    deriv (fun w : ℂ => (1 : ℂ) / ((1 : ℂ) - w)) z = (1 : ℂ) / ((1 : ℂ) - z) ^ 2 := by
  -- Rewrite `1/(1-w)` as `(1-w)⁻¹` and use the derivative of `inv`.
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) - w) z := by
    fun_prop
  have h' :=
    (deriv_fun_inv'' (𝕜 := ℂ) (c := fun w : ℂ => (1 : ℂ) - w) (x := z) hdiff hz)
  have hderiv_sub : deriv (fun w : ℂ => (1 : ℂ) - w) z = (-1 : ℂ) := by
    simp
  simpa [one_div, hderiv_sub] using h'

/-! ### Auxiliary estimates around the shift `1 / 2` (used for genus‑1 products) -/

lemma norm_div_sub_half_le_half (s ρ : ℂ) (hρ1 : (1 : ℝ) ≤ ‖ρ‖)
    (hρbig : (4 * ‖s - (1 / 2 : ℂ)‖ : ℝ) ≤ ‖ρ‖) :
    ‖(s - (1 / 2 : ℂ)) / (ρ - (1 / 2 : ℂ))‖ ≤ (1 / 2 : ℝ) := by
  have hden_ge0 : (‖ρ‖ : ℝ) - (1 / 2 : ℝ) ≤ ‖ρ - (1 / 2 : ℂ)‖ := by
    simpa using (norm_sub_norm_le ρ (1 / 2 : ℂ))
  have hden_ge : (‖ρ‖ : ℝ) / 2 ≤ ‖ρ - (1 / 2 : ℂ)‖ := by
    have : (‖ρ‖ : ℝ) / 2 ≤ (‖ρ‖ : ℝ) - (1 / 2 : ℝ) := by linarith [hρ1]
    exact le_trans this hden_ge0
  have hρpos : 0 < ‖ρ‖ := lt_of_lt_of_le (by norm_num) hρ1
  have hhalfpos : 0 < (‖ρ‖ / 2 : ℝ) := by nlinarith
  have hw : ‖(s - (1 / 2 : ℂ)) / (ρ - (1 / 2 : ℂ))‖ = ‖s - (1 / 2 : ℂ)‖ / ‖ρ - (1 / 2 : ℂ)‖ := by
    simp
  have h1 : ‖s - (1 / 2 : ℂ)‖ / ‖ρ - (1 / 2 : ℂ)‖ ≤ ‖s - (1 / 2 : ℂ)‖ / (‖ρ‖ / 2) := by
    exact
      div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ ‖s - (1 / 2 : ℂ)‖) hhalfpos hden_ge
  have h2' : (2 * ‖s - (1 / 2 : ℂ)‖ : ℝ) / ‖ρ‖ ≤ (1 / 2 : ℝ) := by
    have : (2 * ‖s - (1 / 2 : ℂ)‖ : ℝ) ≤ (1 / 2 : ℝ) * ‖ρ‖ := by
      nlinarith [hρbig]
    exact (div_le_iff₀ hρpos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
  have hrewrite : ‖s - (1 / 2 : ℂ)‖ / (‖ρ‖ / 2) = (2 * ‖s - (1 / 2 : ℂ)‖) / ‖ρ‖ := by
    field_simp [hρpos.ne']
  have h2 : ‖s - (1 / 2 : ℂ)‖ / (‖ρ‖ / 2) ≤ (1 / 2 : ℝ) := by
    rw [hrewrite]
    exact h2'
  have : ‖s - (1 / 2 : ℂ)‖ / ‖ρ - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ) := le_trans h1 h2
  simpa [hw] using this

lemma inv_norm_sub_half_sq_le (ρ : NontrivialZero) (hρ : (1 : ℝ) ≤ ‖ρ.val‖) :
    (1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 ≤ (4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hden_ge0 : (‖ρ.val‖ : ℝ) - (1 / 2 : ℝ) ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ := by
    simpa using (norm_sub_norm_le (ρ.val : ℂ) (1 / 2 : ℂ))
  have hden_ge : (‖ρ.val‖ : ℝ) / 2 ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ := by
    have : (‖ρ.val‖ : ℝ) / 2 ≤ (‖ρ.val‖ : ℝ) - (1 / 2 : ℝ) := by linarith [hρ]
    exact le_trans this hden_ge0
  have hden_sq : ((‖ρ.val‖ : ℝ) / 2) ^ 2 ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
    have hC_nonneg : 0 ≤ (‖ρ.val‖ : ℝ) / 2 := by positivity
    have hD_nonneg : 0 ≤ ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ := by positivity
    simpa [pow_two] using mul_le_mul hden_ge hden_ge hC_nonneg hD_nonneg
  have hpos_rho_sq : 0 < (‖ρ.val‖ : ℝ) ^ 2 := by
    have hpos_rho : 0 < (‖ρ.val‖ : ℝ) := norm_pos_iff.2 (NontrivialZero.ne_zero ρ)
    have : 0 < (‖ρ.val‖ : ℝ) * (‖ρ.val‖ : ℝ) := by positivity
    simpa [pow_two] using this
  have hrecip :
      (1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 ≤ (1 : ℝ) / (((‖ρ.val‖ : ℝ) / 2) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hden_sq
  have hsimp :
      (1 : ℝ) / (((‖ρ.val‖ : ℝ) / 2) ^ 2) = (4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    field_simp [hpos_rho_sq.ne']
    norm_num
  simpa [hsimp] using hrecip

/-! ### Pairing the shifted genus‑1 product into quadratic factors -/

private lemma multipliable_xiE1ShiftedProd_term_of_genus_one (s : ℂ)
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2)) :
    Multipliable (fun ρ : NontrivialZero =>
      Hadamard.weierstrassE 1 ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ)))) := by
  classical
  let f : NontrivialZero → ℂ := fun ρ =>
    Hadamard.weierstrassE 1 ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ)))
  let g : NontrivialZero → ℂ := fun ρ => f ρ - 1
  let C : ℝ := 16 * ‖s - (1 / 2 : ℂ)‖ ^ 2
  have hsum_dom : Summable (fun ρ : NontrivialZero => C * ((1 : ℝ) / ‖ρ.val‖ ^ 2)) :=
    hgenus.const_smul C
  have hbound :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, ‖g ρ‖ ≤ C * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    -- Choose `‖ρ‖` large enough so that the shifted argument has norm ≤ 1 / 2.
    let R : ℝ := max 1 (4 * ‖s - (1 / 2 : ℂ)‖)
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hlarge : ∀ᶠ ρ : NontrivialZero in Filter.cofinite, R ≤ ‖ρ.val‖ :=
      eventually_le_norm_of_summable_inv_norm_sq hgenus (R := R) hRpos
    filter_upwards [hlarge] with ρ hρR
    have hρ1 : (1 : ℝ) ≤ ‖ρ.val‖ := le_trans (le_max_left _ _) hρR
    have hρbig : (4 * ‖s - (1 / 2 : ℂ)‖ : ℝ) ≤ ‖ρ.val‖ := le_trans (le_max_right _ _) hρR
    let w : ℂ := (s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))
    have hw_le : ‖w‖ ≤ (1 / 2 : ℝ) := by
      simpa [w] using norm_div_sub_half_le_half (s := s) (ρ := (ρ.val : ℂ)) hρ1 hρbig
    have hE :
        ‖Hadamard.weierstrassE 1 w - 1‖ ≤ 4 * ‖w‖ ^ (1 + 1) := by
      simpa using
        (Hadamard.weierstrass_E_small_disk_norm_sub_one_le (h := 1) (z := w)
          hw_le)
    have hE' : ‖f ρ - 1‖ ≤ 4 * ‖w‖ ^ 2 := by
      simpa [f, w] using hE
    have hw_sq : ‖w‖ ^ 2 = ‖s - (1 / 2 : ℂ)‖ ^ 2 / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
      simp [w, div_pow]
    have hinv :
        (1 : ℝ) / ‖(ρ.val : ℂ) - (1 / 2 : ℂ)‖ ^ 2 ≤ (4 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) :=
      inv_norm_sub_half_sq_le (ρ := ρ) hρ1
    have hcalc : 4 * ‖w‖ ^ 2 ≤ C * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
      -- Multiply the denominator estimate by `4 * ‖s-1 / 2‖^2`.
      have hmul :=
        mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (4 : ℝ) * ‖s - (1 / 2 : ℂ)‖ ^ 2)
      -- Rewrite `‖w‖^2` and close by `simp`ping constants.
      -- `‖w‖^2 = ‖s-1 / 2‖^2 / ‖ρ-1 / 2‖^2` and `C = 16 * ‖s-1 / 2‖^2`.
      -- (Avoid `ring_nf`/`field_simp` here for performance.)
      have h44 : (4 : ℝ) * 4 = (16 : ℝ) := by norm_num
      simpa [hw_sq, div_eq_mul_inv, C, mul_assoc, mul_left_comm, mul_comm, h44] using hmul
    have hg : ‖g ρ‖ = ‖f ρ - 1‖ := by simp [g]
    have hmain : ‖f ρ - 1‖ ≤ C * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := le_trans hE' hcalc
    simpa [hg] using hmain
  have hsum : Summable (fun ρ : NontrivialZero => ‖g ρ‖) :=
    Summable.of_norm_bounded_eventually hsum_dom (by simpa [C] using hbound)
  have hmul : Multipliable (fun ρ : NontrivialZero => (1 : ℂ) + g ρ) :=
    _root_.multipliable_one_add_of_summable hsum
  simpa [g, f, add_sub_cancel] using hmul

-- The paired `tprod` algebra here triggers a large normalization search in the product
-- regrouping step, so the declaration needs a larger heartbeat budget than the default.
lemma xiE1ShiftedProd_sq_eq_tprod_xiPairedFactor_of_genus_one
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2)) (s : ℂ) :
    (xiE1ShiftedProd s) ^ 2 = ∏' ρ : NontrivialZero, xiPairedFactor ρ s := by
  classical
  let f : NontrivialZero → ℂ := fun ρ =>
    Hadamard.weierstrassE 1 ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ)))
  let g : NontrivialZero → ℂ := fun ρ => f (pairedZero ρ)
  have hf : Multipliable f := multipliable_xiE1ShiftedProd_term_of_genus_one (s := s) hgenus
  have hg : Multipliable g := by
    -- Reindexing by the involution preserves multipliability.
    simpa [g, Function.comp_def, coe_pairedZeroEquiv] using
      (pairedZeroEquiv.multipliable_iff (f := f)).2 hf
  have htprod_g : (∏' ρ : NontrivialZero, g ρ) = ∏' ρ : NontrivialZero, f ρ := by
    simpa [g, coe_pairedZeroEquiv] using (pairedZeroEquiv.tprod_eq f)
  have hmul :
      (∏' ρ : NontrivialZero, f ρ * g ρ)
        =
      (∏' ρ : NontrivialZero, f ρ) * ∏' ρ : NontrivialZero, g ρ := by
    simpa using (hf.tprod_mul hg)
  have hterm : ∀ ρ : NontrivialZero, f ρ * g ρ = xiPairedFactor ρ s := by
    intro ρ
    have harg :
        (s - (1 / 2 : ℂ)) / ((pairedZero ρ).val - (1 / 2 : ℂ))
          =
        -((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))) := by
      -- Avoid `simp` loops around `1 / 2` vs `2⁻¹`.
      rw [pairedZero_val]
      have hden1 :
          (1 : ℂ) - (ρ.val : ℂ) - (1 / 2 : ℂ) = (2⁻¹ : ℂ) - (ρ.val : ℂ) := by
        ring
      rw [hden1]
      have hden2 :
          (2⁻¹ : ℂ) - (ρ.val : ℂ) = -((ρ.val : ℂ) - (2⁻¹ : ℂ)) := by
        ring
      rw [hden2]
      simpa using (div_neg (a := s - (2⁻¹ : ℂ)) (b := (ρ.val : ℂ) - (2⁻¹ : ℂ)))
    -- Use `E₁(w)E₁(-w) = 1 - w^2`.
    dsimp [f, g]
    -- Rewrite the second argument into `-w` using `harg`.
    rw [harg]
    simpa [xiPairedFactor] using
      (weierstrass_E_one_mul_neg ((s - (1 / 2 : ℂ)) / (ρ.val - (1 / 2 : ℂ))))
  have hfg :
      (∏' ρ : NontrivialZero, f ρ * g ρ) = ∏' ρ : NontrivialZero, xiPairedFactor ρ s := by
    refine tprod_congr ?_
    intro ρ
    simp [hterm ρ]
  have : (∏' ρ : NontrivialZero, f ρ) ^ 2 = ∏' ρ : NontrivialZero, xiPairedFactor ρ s := by
    calc
      (∏' ρ : NontrivialZero, f ρ) ^ 2
          = (∏' ρ : NontrivialZero, f ρ) * ∏' ρ : NontrivialZero, f ρ := by
              simp [pow_two]
      _ = (∏' ρ : NontrivialZero, f ρ) * ∏' ρ : NontrivialZero, g ρ := by
            simp [htprod_g]
      _ = ∏' ρ : NontrivialZero, f ρ * g ρ := by
            simpa using hmul.symm
      _ = ∏' ρ : NontrivialZero, xiPairedFactor ρ s := hfg
  simpa [xiE1ShiftedProd, f] using this

-- Squaring the shifted product and folding it into the paired factorization reuses the same
-- heavy `tprod` normalization chain as the previous lemma, so it needs the same budget.
lemma xi_sq_factorization_paired_of_genus_one
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : ∃ a : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp a * xiE1ShiftedProd s) :
    ∃ a₂ : ℂ, ∀ s : ℂ,
      (riemannXi s) ^ 2 = Complex.exp a₂ * ∏' ρ : NontrivialZero, xiPairedFactor ρ s := by
  classical
  obtain ⟨a, hξ⟩ := hhad
  refine ⟨(2 : ℂ) * a, ?_⟩
  intro s
  have hprod : (xiE1ShiftedProd s) ^ 2 = ∏' ρ : NontrivialZero, xiPairedFactor ρ s :=
    xiE1ShiftedProd_sq_eq_tprod_xiPairedFactor_of_genus_one hgenus s
  calc
    (riemannXi s) ^ 2
        = (Complex.exp a * xiE1ShiftedProd s) ^ 2 := by simp [hξ s]
    _ = (Complex.exp a) ^ 2 * (xiE1ShiftedProd s) ^ 2 := by
          simp [mul_pow]
    _ = Complex.exp ((2 : ℂ) * a) * (xiE1ShiftedProd s) ^ 2 := by
          have hexp : (Complex.exp a) ^ 2 = Complex.exp ((2 : ℂ) * a) := by
            simp [pow_two, Complex.exp_add, two_mul]
          simp [hexp]
    _ = Complex.exp ((2 : ℂ) * a) * ∏' ρ : NontrivialZero, xiPairedFactor ρ s := by
          simp [hprod]

/- **DERIVED**: The linear coefficient vanishes from the functional equation ξ(s) = ξ(1-s).

In the shifted genus‑1 Hadamard factorization `xiHadamardGenusOneShifted`, the symmetry
forces the linear coefficient to vanish; see `xi_hadamard_genus_one_shifted_linear_coeff_zero`. -/

/-- The raw Li summand `Aₙ(ρ) = 1 - (1 - 1 / ρ)^{-(n+1)}`. -/
noncomputable def liSummand (n : ℕ) (ρ : NontrivialZero) : ℂ :=
  (1 - (1 - 1 / (ρ.val)) ^ (-(n + 1 : ℤ)))

/-- The paired Li summand `Tₙ(ρ) = Aₙ(ρ) + Aₙ(1-ρ)`.

This is the genus‑1 replacement for summing `liSummand` termwise: for large `‖ρ‖` the two terms
cancel to order `‖ρ‖⁻²`. -/
noncomputable def liPairedSummand (n : ℕ) (ρ : NontrivialZero) : ℂ :=
  liSummand n ρ + liSummand n (pairedZero ρ)

lemma taylorCoeff_singleLinearFactor (ρ : NontrivialZero) (n : ℕ) :
    taylorCoeff (fun s : ℂ => 1 - s / ρ.val) n = liSummand n ρ := by
  let S : Finset ℂ := {ρ.val}
  have hS0 : (0 : ℂ) ∉ S := by
    have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
    simpa [S, eq_comm] using hρ0
  have hS1 : ∀ x ∈ S, x ≠ (1 : ℂ) := by
    intro x hx
    have hx' : x = ρ.val := by
      simpa [S] using hx
    subst hx'
    exact NontrivialZero.ne_one ρ
  have hphiS :
      phi (fun s : ℂ => ∏ x ∈ S, (1 - s / x))
        =
      (fun z : ℂ => ∏ x ∈ S, (1 + -((1 + -z)⁻¹ / x))) := by
    funext z
    simp [phi, one_div, sub_eq_add_neg]
  have hfin :
      taylorCoeff (fun s : ℂ => ∏ x ∈ S, (1 - s / x)) n
        = ∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))) := by
    have h :=
      taylorCoeff_finite_Li (S := S) hS0 n (by
        intro x hx
        exact hS1 x hx)
    simpa [taylorCoeff, hphiS, sub_eq_add_neg, phi_eq] using h
  have hprod : (fun s : ℂ => 1 - s / ρ.val) = fun s : ℂ => ∏ x ∈ S, (1 - s / x) := by
    funext s
    simp [S]
  calc
    taylorCoeff (fun s : ℂ => 1 - s / ρ.val) n
        = taylorCoeff (fun s : ℂ => ∏ x ∈ S, (1 - s / x)) n := by
            simpa using congrArg (fun g : ℂ → ℂ => taylorCoeff g n) hprod
    _ = ∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))) := hfin
    _ = liSummand n ρ := by
          simp [S, liSummand]

private lemma taylorCoeff_square_singleLinearFactor (ρ : NontrivialZero) (n : ℕ) :
    taylorCoeff (fun s : ℂ => (1 - s / ρ.val) ^ 2) n = (2 : ℂ) * liSummand n ρ := by
  let f : ℂ → ℂ := fun s => 1 - s / ρ.val
  let g1 : ℂ → ℂ := logDeriv (phi (fun s : ℂ => (1 - s / ρ.val) ^ 2))
  let g2 : ℂ → ℂ := fun z => (2 : ℂ) * _root_.logDeriv (phi f) z
  have hEqOn : Set.EqOn g1 g2 (Metric.ball (0 : ℂ) (1 : ℝ)) := by
    intro z hz
    have hz' : ‖z‖ < (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hf_diff : DifferentiableAt ℂ (phi f) z := by
      have hf_entire : Differentiable ℂ f := by
        dsimp [f]
        fun_prop
      exact phi_differentiable hf_entire hz'
    have hpow := logDeriv_fun_pow (f := phi f) (x := z) hf_diff 2
    have hphi : phi (fun s : ℂ => (1 - s / ρ.val) ^ 2) = fun x : ℂ => (phi f x) ^ 2 := by
      funext x
      simp [phi, f]
    simpa [g1, g2, hphi, LiCriterion.logDeriv, _root_.logDeriv] using hpow
  have hsopen : IsOpen (Metric.ball (0 : ℂ) (1 : ℝ)) := Metric.isOpen_ball
  have hEqIter : iteratedDeriv n g1 0 = iteratedDeriv n g2 0 := by
    have hEqOn' := Set.EqOn.iteratedDeriv_of_isOpen (f := g1) (g := g2)
      (s := Metric.ball (0 : ℂ) (1 : ℝ)) hEqOn hsopen n
    have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
      simp [Metric.mem_ball]
    exact hEqOn' hmem
  have hEqIter' : (deriv^[n] g1) 0 = (deriv^[n] g2) 0 := by
    simpa [iteratedDeriv_eq_iterate] using hEqIter
  have hconst :
      (deriv^[n] g2) 0 = (2 : ℂ) * (deriv^[n] (_root_.logDeriv (phi f))) 0 := by
    simpa only [g2, iteratedDeriv_eq_iterate] using
      (iteratedDeriv_const_mul_field n (2 : ℂ) (_root_.logDeriv (phi f)) 0)
  have hsingle : taylorCoeff f n = liSummand n ρ := taylorCoeff_singleLinearFactor ρ n
  have hsingle' : (deriv^[n] (_root_.logDeriv (phi f))) 0 / n.factorial = liSummand n ρ := by
    simpa [taylorCoeff, f, logDeriv_eq_rootLogDeriv] using hsingle
  simp [taylorCoeff, g1, hEqIter', hconst, hsingle', f, mul_div_assoc]

/-- Taylor coefficients for a single paired quadratic factor give the paired Li summand. -/
lemma taylorCoeff_xiPairedFactor [Fact xiFactorizationShiftedProd] (ρ : NontrivialZero) (n : ℕ) :
    taylorCoeff (xiPairedFactor ρ) n = liPairedSummand n ρ := by
  classical
  let c : ℂ :=
    (-(ρ.val * (pairedZero ρ).val) / (ρ.val - (1 / 2 : ℂ)) ^ 2)
  have hc : c ≠ 0 := by
    have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
    have hρhalf : (ρ.val : ℂ) - (1 / 2 : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (NontrivialZero.ne_half ρ)
    have hpair0 : (pairedZero ρ).val ≠ 0 := NontrivialZero.ne_zero (pairedZero ρ)
    have hnum : -(ρ.val * (pairedZero ρ).val) ≠ 0 := by
      simpa [neg_eq_zero] using mul_ne_zero hρ0 hpair0
    have hden : (ρ.val - (1 / 2 : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hρhalf
    simpa [c] using (div_ne_zero hnum hden)
  have hxi :
      xiPairedFactor ρ = fun s =>
        c * ((1 - s / ρ.val) * (1 - s / (pairedZero ρ).val)) := by
    funext s
    simpa [c] using (xiPairedFactor_eq_const_mul_pairLinear ρ s)
  have htaylor_const :
      taylorCoeff (fun s => c * ((1 - s / ρ.val) * (1 - s / (pairedZero ρ).val))) n
        =
      taylorCoeff (fun s => (1 - s / ρ.val) * (1 - s / (pairedZero ρ).val)) n := by
    simpa using
      (taylorCoeff_const_mul
        (c := c) (hc := hc) (f := fun s => (1 - s / ρ.val) * (1 - s / (pairedZero ρ).val))
        (n := n))
  let S : Finset ℂ := {ρ.val, (pairedZero ρ).val}
  have hne : (ρ.val : ℂ) ≠ (pairedZero ρ).val := by
    intro h
    have h' : (ρ.val : ℂ) = 1 - (ρ.val : ℂ) := by simpa [pairedZero_val] using h
    have h2 : (2 : ℂ) * (ρ.val : ℂ) = 1 := by
      have := congrArg (fun z => z + (ρ.val : ℂ)) h'
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using this
    have h2' : (ρ.val : ℂ) * (2 : ℂ) = 1 := by simpa [mul_comm] using h2
    have : (ρ.val : ℂ) = (1 / 2 : ℂ) :=
      (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2 h2'
    exact (NontrivialZero.ne_half ρ) this
  have hS0 : (0 : ℂ) ∉ S := by
    have h0pair : (0 : ℂ) ≠ 1 - (ρ.val : ℂ) :=
      (sub_ne_zero.mpr (NontrivialZero.ne_one ρ).symm).symm
    simp [S, (NontrivialZero.ne_zero ρ).symm, h0pair]
  have hS1 : ∀ x ∈ S, x ≠ (1 : ℂ) := by
    intro x hx
    have hx' : x = ρ.val ∨ x = (pairedZero ρ).val := by
      simpa [S] using hx
    rcases hx' with rfl | rfl
    · exact NontrivialZero.ne_one ρ
    · simpa [pairedZero_val] using NontrivialZero.ne_one (pairedZero ρ)
  have hfinite :
      taylorCoeff (fun s : ℂ => ∏ x ∈ S, (1 - s / x)) n
        = ∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))) := by
    have hphiS :
        phi (fun s : ℂ => ∏ x ∈ S, (1 - s / x))
          =
        (fun z : ℂ => ∏ x ∈ S, (1 + -((1 + -z)⁻¹ / x))) := by
      funext z
      simp [phi, one_div, sub_eq_add_neg]
    have hfin :=
      (taylorCoeff_finite_Li (S := S) hS0 n (by intro x hx; exact hS1 x hx))
    simpa [taylorCoeff, hphiS, sub_eq_add_neg, phi_eq] using hfin
  have hprod :
      (fun s : ℂ => (1 - s / ρ.val) * (1 - s / (pairedZero ρ).val))
        =
      fun s : ℂ => ∏ x ∈ S, (1 - s / x) := by
    funext s
    have hR :
        (∏ x ∈ S, (1 - s / x)) = (1 - s / ρ.val) * (1 - s / (pairedZero ρ).val) := by
      -- Expand the 2-element finset product.
      simpa [S] using
        (Finset.prod_pair (f := fun x : ℂ => 1 - s / x) (a := ρ.val) (b := (pairedZero ρ).val)
          hne)
    simpa using hR.symm
  calc
    taylorCoeff (xiPairedFactor ρ) n
        = taylorCoeff (fun s => c * ((1 - s / ρ.val) * (1 - s / (pairedZero ρ).val))) n := by
            simp [hxi]
    _ = taylorCoeff (fun s => (1 - s / ρ.val) * (1 - s / (pairedZero ρ).val)) n := htaylor_const
    _ = taylorCoeff (fun s : ℂ => ∏ x ∈ S, (1 - s / x)) n := by
          simpa using congrArg (fun g => taylorCoeff g n) hprod
    _ = ∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))) := hfinite
    _ = liPairedSummand n ρ := by
          have hsum :
              (∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))))
                = liSummand n (pairedZero ρ) + liSummand n ρ := by
            have hsum_pair :
                (∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))))
                  =
                (1 - (1 - 1 / ρ.val) ^ (-(n + 1 : ℤ)))
                  + (1 - (1 - 1 / (pairedZero ρ).val) ^ (-(n + 1 : ℤ))) := by
              simpa [S] using
                (Finset.sum_pair
                  (f := fun x : ℂ => (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))))
                  (a := ρ.val) (b := (pairedZero ρ).val) hne)
            simpa [liSummand, add_comm] using hsum_pair
          simpa [liPairedSummand, add_comm] using hsum

/-- The paired Li summand is summable along any indexed family of nontrivial zeros
whose inverse squared norms are summable. -/
theorem summable_Li_paired_summand_comp_of_genus_one
    {ι : Type*} (zeros : ι → NontrivialZero)
    (hgenus : Summable (fun i : ι => (1 : ℝ) / ‖(zeros i).val‖ ^ 2)) (n : ℕ) :
    Summable (fun i : ι => liPairedSummand n (zeros i)) := by
  classical
  let m : ℕ := n + 1
  let K : ℝ := ∑ i ∈ Finset.range m, ((3 / 2 : ℝ) ^ i)
  let C : ℝ := ((2 : ℝ) ^ m) * K ^ 2
  have hsum_dom : Summable (fun i : ι => C * ((1 : ℝ) / ‖(zeros i).val‖ ^ 2)) :=
    hgenus.const_smul C
  refine Summable.of_norm_bounded_eventually hsum_dom ?_
  have hsmall :
      ∀ᶠ i : ι in Filter.cofinite, (1 : ℝ) / ‖(zeros i).val‖ ^ 2 ≤ (1 / 4 : ℝ) :=
    hgenus.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < (1 / 4 : ℝ))
  filter_upwards [hsmall] with i hρsmall
  let ρ : NontrivialZero := zeros i
  let w : ℂ := (1 : ℂ) - (1 : ℂ) / ρ.val
  have hcore : liPairedSummand n ρ = core m w := by
    have h0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
    have h1 : (ρ.val : ℂ) ≠ 1 := NontrivialZero.ne_one ρ
    have hA : liSummand n ρ = liTerm m w := by
      simp [liSummand, liTerm, w, m]
    have hA' : liSummand n (pairedZero ρ) = liTerm m ((1 : ℂ) - (1 : ℂ) / (1 - ρ.val)) := by
      simp [liSummand, liTerm, m, pairedZero_val]
    have hcore' : liTerm m w + liTerm m ((1 : ℂ) - (1 : ℂ) / (1 - ρ.val)) = core m w := by
      simpa [w] using (paired_liTerm_eq_core (m := m) (z := (ρ.val : ℂ)) h0 h1)
    simpa [liPairedSummand, hA, hA'] using hcore'
  have hw_sq : ‖w - 1‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hw2 : ‖w - 1‖ ^ 2 = (1 : ℝ) / ‖ρ.val‖ ^ 2 := by
      have : w - 1 = -((1 : ℂ) / ρ.val) := by
        dsimp [w]
        ring
      calc
        ‖w - 1‖ ^ 2 = ‖-((1 : ℂ) / ρ.val)‖ ^ 2 := by simp [this]
        _ = ‖(1 : ℂ) / ρ.val‖ ^ 2 := by simp
        _ = ((1 : ℝ) / ‖ρ.val‖) ^ 2 := by simp
        _ = (1 : ℝ) / ‖ρ.val‖ ^ 2 := by simp
    have : ‖w - 1‖ ^ 2 ≤ (1 / 4 : ℝ) := by
      simpa [hw2] using hρsmall
    have : ‖w - 1‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      simpa using (le_trans this (by norm_num : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ 2))
    exact this
  have hw : ‖w - 1‖ ≤ (1 / 2 : ℝ) := by
    have habs : |‖w - 1‖| ≤ |(1 / 2 : ℝ)| := (sq_le_sq).1 hw_sq
    simpa [abs_of_nonneg (norm_nonneg _)] using habs
  have hnorm_core : ‖core m w‖ ≤ ((2 : ℝ) ^ m) * K ^ 2 * ‖w - 1‖ ^ 2 := by
    have h := norm_core_le_const_mul_norm_sub_one_sq (m := m) (w := w) hw
    simpa [K, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hw2 : ‖w - 1‖ ^ 2 = (1 : ℝ) / ‖ρ.val‖ ^ 2 := by
    have : w - 1 = -((1 : ℂ) / ρ.val) := by
      dsimp [w]
      ring
    calc
      ‖w - 1‖ ^ 2 = ‖-((1 : ℂ) / ρ.val)‖ ^ 2 := by simp [this]
      _ = ‖(1 : ℂ) / ρ.val‖ ^ 2 := by simp
      _ = ((1 : ℝ) / ‖ρ.val‖) ^ 2 := by simp
      _ = (1 : ℝ) / ‖ρ.val‖ ^ 2 := by simp
  have : ‖liPairedSummand n ρ‖ ≤ C * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    calc
      ‖liPairedSummand n ρ‖ = ‖core m w‖ := by simp [hcore]
      _ ≤ ((2 : ℝ) ^ m) * K ^ 2 * ‖w - 1‖ ^ 2 := hnorm_core
      _ = C * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
          simp [C, hw2]
  exact this

/-- Summability of the paired Li summand from a genus‑1 summability hypothesis
`Summable (ρ ↦ 1/‖ρ‖²)`.

The proof uses the algebraic reduction and the `O(‖w-1‖^2)` estimate in
`Lc/LiCriterion/GenusOne.lean`. -/
theorem summable_Li_paired_summand_of_genus_one
    (hgenus : Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2)) (n : ℕ) :
    Summable (fun ρ : NontrivialZero => liPairedSummand n ρ) := by
  exact summable_Li_paired_summand_comp_of_genus_one id hgenus n

/-! ### Multiplicity-aware paired route via linear paired factors -/

/-- Nontrivial zeros repeated according to their analytic order as zeros of `ξ`. -/
noncomputable abbrev XiZeroWithMultiplicity : Type :=
  Σ ρ : NontrivialZero, Fin (analyticOrderNatAt riemannXi ρ.val)

noncomputable instance (ρ : NontrivialZero) :
    Countable (Fin (analyticOrderNatAt riemannXi ρ.val)) := by
  infer_instance

lemma analyticOrderAt_riemannXi_ne_top (s : ℂ) :
    analyticOrderAt riemannXi s ≠ ⊤ := by
  have hxi_analytic : AnalyticOnNhd ℂ riemannXi Set.univ := by
    intro z _
    exact xi_entire.analyticAt z
  have h0_order_ne_top : analyticOrderAt riemannXi 0 ≠ ⊤ := by
    have h0_order_zero : analyticOrderAt riemannXi 0 = 0 := by
      exact (xi_entire.analyticAt 0).analyticOrderAt_eq_zero.2 (by
        unfold riemannXi
        norm_num)
    simp [h0_order_zero]
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (hf := hxi_analytic) (U := Set.univ) (x := 0) (y := s)
    isPreconnected_univ (by simp) (by simp) h0_order_ne_top

lemma analyticOrderNatAt_riemannXi_pairedZero (ρ : NontrivialZero) :
    analyticOrderNatAt riemannXi (pairedZero ρ).val = analyticOrderNatAt riemannXi ρ.val := by
  apply (ENat.natCast_inj).1
  rw [Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top (pairedZero ρ).val),
    Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top ρ.val)]
  have hfun : riemannXi = fun s : ℂ => riemannXi (1 - s) := by
    funext s
    exact xi_functional_equation s
  have hcomp : (fun s : ℂ => riemannXi (1 - s)) = riemannXi ∘ (fun s : ℂ => 1 - s) := rfl
  calc
    analyticOrderAt riemannXi (pairedZero ρ).val
        = analyticOrderAt riemannXi (1 - ρ.val) := by
            simp [pairedZero_val]
    _ = analyticOrderAt (fun s : ℂ => riemannXi (1 - s)) ρ.val := by
          have hlin_an : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ.val := by
            exact analyticAt_const.sub analyticAt_id
          have hlin_deriv_ne : deriv (fun s : ℂ => 1 - s) ρ.val ≠ 0 := by
            have hid : deriv (fun s : ℂ => s) ρ.val = (1 : ℂ) := by
              change deriv id ρ.val = (1 : ℂ)
              exact deriv_id (x := ρ.val)
            have hlin_deriv : deriv (fun s : ℂ => 1 - s) ρ.val = (-1 : ℂ) := by
              rw [deriv_const_sub (c := (1 : ℂ)) (f := fun s : ℂ => s)]
              simp [hid]
            rw [hlin_deriv]
            norm_num
          rw [hcomp, analyticOrderAt_comp_of_deriv_ne_zero hlin_an hlin_deriv_ne]
    _ = analyticOrderAt riemannXi ρ.val := by
          rw [hfun]
          congr 1
          funext s
          simpa using xi_functional_equation s

theorem genus_one_of_weighted_genus
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :
    Summable (fun ρ : NontrivialZero => (1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hmult_ge_one : ∀ ρ : NontrivialZero, 1 ≤ analyticOrderNatAt riemannXi ρ.val := by
    intro ρ
    have hρ_zero : riemannXi ρ.val = 0 :=
      (xi_zeros_are_nontrivial_zeros (s := ρ.val)).2 ⟨ρ, rfl⟩
    have hρ_analytic : AnalyticAt ℂ riemannXi ρ.val := xi_entire.analyticAt ρ.val
    have hρ_orderAt_ne_zero : analyticOrderAt riemannXi ρ.val ≠ 0 :=
      (hρ_analytic.analyticOrderAt_ne_zero).2 hρ_zero
    have hρ_orderNat_ne_zero : analyticOrderNatAt riemannXi ρ.val ≠ 0 := by
      intro hzero
      exact hρ_orderAt_ne_zero
        (by
          simpa [hzero] using
            (Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top ρ.val)).symm)
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hρ_orderNat_ne_zero)
  have hle :
      ∀ ρ : NontrivialZero,
        (1 : ℝ) / ‖ρ.val‖ ^ 2 ≤
          (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by
    intro ρ
    have hmult_ge_one' : (1 : ℝ) ≤ analyticOrderNatAt riemannXi ρ.val := by
      exact_mod_cast hmult_ge_one ρ
    have hnorm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.2 ρ.ne_zero
    have hnorm_sq_pos : 0 < ‖ρ.val‖ ^ 2 := by positivity
    exact (div_le_div_iff_of_pos_right hnorm_sq_pos).2 hmult_ge_one'
  exact hgenus.of_nonneg_of_le (fun ρ => by positivity) hle

/-- Repeat the involution `ρ ↦ 1 - ρ` fiberwise across multiplicity indices. -/
noncomputable def pairedZeroWithMultiplicity
    (i : XiZeroWithMultiplicity) : XiZeroWithMultiplicity :=
  ⟨pairedZero i.1, by
    rw [analyticOrderNatAt_riemannXi_pairedZero i.1]
    exact i.2⟩

lemma pairedZeroWithMultiplicity_involutive : Function.Involutive pairedZeroWithMultiplicity := by
  intro i
  cases i with
  | mk ρ k =>
      apply Sigma.ext
      · exact pairedZero_involutive ρ
      · simp [pairedZeroWithMultiplicity]

/-- Reflection of the indexed xi zeros, preserving each zero’s multiplicity index. -/
noncomputable def pairedZeroWithMultiplicityEquiv :
    XiZeroWithMultiplicity ≃ XiZeroWithMultiplicity :=
  { toFun := pairedZeroWithMultiplicity
    invFun := pairedZeroWithMultiplicity
    left_inv := pairedZeroWithMultiplicity_involutive
    right_inv := pairedZeroWithMultiplicity_involutive }

@[simp] lemma coe_pairedZeroWithMultiplicityEquiv :
    ⇑pairedZeroWithMultiplicityEquiv = pairedZeroWithMultiplicity := rfl

/-- A countable type admits an increasing exhaustion by finite sets. -/
lemma exists_increasing_finite_cover_of_countable (α : Type*) [Countable α] :
    ∃ (T : ℕ → Finset α), Monotone T ∧ (⋃ n, (T n : Set α)) = Set.univ := by
  classical
  by_cases h : Nonempty α
  · have := h
    obtain ⟨default⟩ := h
    let s_countable : (Set.univ : Set α).Countable := Set.to_countable _
    let enum := Set.enumerateCountable s_countable default
    refine ⟨fun n => Finset.image (fun k => enum k) (Finset.range n), ?_, ?_⟩
    · intro n m hnm
      exact Finset.image_subset_image (Finset.range_mono hnm)
    · ext x
      simp only [Set.mem_iUnion, Finset.coe_image, Finset.coe_range, Set.mem_univ, iff_true]
      have : x ∈ Set.range enum := by
        have subset := Set.subset_range_enumerate s_countable default
        exact subset (Set.mem_univ x)
      obtain ⟨k, hk⟩ := this
      refine ⟨k + 1, ?_⟩
      exact ⟨k, Nat.lt_succ_self k, hk⟩
  · refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro n m _
      exact Finset.empty_subset _
    · rw [not_nonempty_iff] at h
      simp [Set.eq_empty_of_isEmpty]

theorem summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :
    Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2) := by
  classical
  have hnonneg : ∀ i : XiZeroWithMultiplicity, 0 ≤ (1 : ℝ) / ‖i.1.val‖ ^ 2 := by
    intro i
    positivity
  refine (summable_sigma_of_nonneg hnonneg).2 ?_
  refine ⟨fun ρ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
  refine hgenus.congr (fun ρ => ?_)
  calc
    (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2
        = (analyticOrderNatAt riemannXi ρ.val : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
            rw [mul_one_div]
    _ = ∑' _k : Fin (analyticOrderNatAt riemannXi ρ.val), (1 : ℝ) / ‖ρ.val‖ ^ 2 := by
          simp
    _ = ∑' k : Fin (analyticOrderNatAt riemannXi ρ.val),
          (1 : ℝ) / ‖((⟨ρ, k⟩ : XiZeroWithMultiplicity).1).val‖ ^ 2 := by
          simp

lemma eventually_le_norm_of_summable_inv_norm_sq_withMultiplicity
    (hgenus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, R ≤ ‖i.1.val‖ := by
  have ht :
      Filter.Tendsto (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2) cofinite (𝓝 0) :=
    hgenus.tendsto_cofinite_zero
  have hεpos : 0 < (1 : ℝ) / R ^ 2 := by positivity
  have hsmall :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, (1 : ℝ) / ‖i.1.val‖ ^ 2 < (1 : ℝ) / R ^ 2 :=
    (tendsto_order.1 ht).2 _ hεpos
  filter_upwards [hsmall] with i hi
  have hpos : 0 < ‖i.1.val‖ := norm_pos_iff.2 (NontrivialZero.ne_zero i.1)
  have hpos_sq : 0 < ‖i.1.val‖ ^ 2 := by positivity
  have hRpos_sq : 0 < R ^ 2 := by positivity
  refine le_of_not_gt ?_
  intro hlt
  have hsq_lt : ‖i.1.val‖ ^ 2 < R ^ 2 := by
    have habs : |‖i.1.val‖| < |R| := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_pos hR] using hlt
    simpa using (sq_lt_sq.2 habs)
  have hcontra : (1 : ℝ) / R ^ 2 < (1 : ℝ) / ‖i.1.val‖ ^ 2 :=
    one_div_lt_one_div_of_lt hpos_sq hsq_lt
  exact (lt_asymm hi hcontra).elim

theorem summable_Li_paired_summand_withMultiplicity_of_genus_one
    (hgenus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2)) (n : ℕ) :
    Summable (fun i : XiZeroWithMultiplicity => liPairedSummand n i.1) := by
  exact summable_Li_paired_summand_comp_of_genus_one (fun i => i.1) hgenus n

theorem tsum_Li_paired_summand_withMultiplicity_eq_weighted_tsum
    (n : ℕ)
    (hsum : Summable (fun i : XiZeroWithMultiplicity => liPairedSummand n i.1)) :
    (∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1)
      =
    ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ := by
  classical
  have hSigma :
      HasSum
        (fun ρ : NontrivialZero =>
          ∑' k : Fin (analyticOrderNatAt riemannXi ρ.val), liPairedSummand n ρ)
        (∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1) := by
    simpa [XiZeroWithMultiplicity] using
      hsum.hasSum.sigma
        (fun ρ =>
          hasSum_fintype (fun _ : Fin (analyticOrderNatAt riemannXi ρ.val) =>
            liPairedSummand n ρ))
  calc
    (∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1)
        =
      ∑' ρ : NontrivialZero,
        ∑' k : Fin (analyticOrderNatAt riemannXi ρ.val), liPairedSummand n ρ := by
            simpa using hSigma.tsum_eq.symm
    _ = ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ := by
          refine tsum_congr ?_
          intro ρ
          calc
            (∑' k : Fin (analyticOrderNatAt riemannXi ρ.val), liPairedSummand n ρ)
                = ∑ k : Fin (analyticOrderNatAt riemannXi ρ.val), liPairedSummand n ρ := by
                    simp
            _ = (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ := by
                  simp [Finset.card_univ, nsmul_eq_mul]

theorem summable_weighted_Li_paired_summand_of_weighted_genus
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (n : ℕ) :
    Summable
      (fun ρ : NontrivialZero =>
        (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ) := by
  classical
  have hsigma_genus := summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus hgenus
  have hsigma :
      Summable (fun i : XiZeroWithMultiplicity => liPairedSummand n i.1) :=
    summable_Li_paired_summand_withMultiplicity_of_genus_one hsigma_genus n
  have hweighted :
      HasSum
        (fun ρ : NontrivialZero =>
          ∑' k : Fin (analyticOrderNatAt riemannXi ρ.val), liPairedSummand n ρ)
        (∑' i : XiZeroWithMultiplicity, liPairedSummand n i.1) := by
    simpa [XiZeroWithMultiplicity] using
      hsigma.hasSum.sigma
        (fun ρ =>
          hasSum_fintype (fun _ : Fin (analyticOrderNatAt riemannXi ρ.val) =>
            liPairedSummand n ρ))
  refine hweighted.summable.congr ?_
  intro ρ
  calc
    (∑' k : Fin (analyticOrderNatAt riemannXi ρ.val), liPairedSummand n ρ)
        = ∑ k : Fin (analyticOrderNatAt riemannXi ρ.val), liPairedSummand n ρ := by
            simp
    _ = (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ := by
          simp [Finset.card_univ, nsmul_eq_mul]

/-- The multiplicity-aware genus-1 canonical product for `ξ`. -/
noncomputable def xiE1ProdWithMultiplicity (s : ℂ) : ℂ :=
  ∏' i : XiZeroWithMultiplicity, Hadamard.weierstrassE 1 (s / i.1.val)

lemma multipliable_xiE1ProdWithMultiplicity_term_of_genus_one (s : ℂ)
    (hgenus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2)) :
    Multipliable (fun i : XiZeroWithMultiplicity => Hadamard.weierstrassE 1 (s / i.1.val)) := by
  let z : XiZeroWithMultiplicity → ℂ := fun i => i.1.val
  have hz0 : ∀ i : XiZeroWithMultiplicity, z i ≠ 0 := by
    intro i
    exact NontrivialZero.ne_zero i.1
  simpa [z] using
    (Hadamard.OrderOne.multipliable_weierstrass_E_one_of_summable_inv_norm_sq
      (z := z) (hz0 := hz0) hgenus s)

/-- The multiplicity-aware order-`≤ 1` Hadamard factorization hypothesis for `ξ`. -/
def xiFactorizationProdWithMultiplicity : Prop :=
  ∃ a b : ℂ, ∀ s : ℂ, riemannXi s = Complex.exp (a * s + b) * xiE1ProdWithMultiplicity s

/-- The paired linear factor attached to a zero `ρ` and its reflected partner `1 - ρ`. -/
noncomputable def xiPairedLinearFactor (ρ : NontrivialZero) (s : ℂ) : ℂ :=
  (1 - s / ρ.val) * (1 - s / (pairedZero ρ).val)

/-- The paired linear factor is an entire function of `s`. -/
lemma xiPairedLinearFactor_differentiable (ρ : NontrivialZero) :
    Differentiable ℂ (xiPairedLinearFactor ρ) := by
  unfold xiPairedLinearFactor
  exact
    ((differentiable_const (c := (1 : ℂ))).sub (differentiable_id.div_const _)).mul
      ((differentiable_const (c := (1 : ℂ))).sub (differentiable_id.div_const _))

private lemma xiPairedLinearFactor_one_sub (ρ : NontrivialZero) (s : ℂ) :
    xiPairedLinearFactor ρ (1 - s) = xiPairedLinearFactor ρ s := by
  have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
  have hρ1 : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (NontrivialZero.ne_one ρ).symm
  simp [xiPairedLinearFactor, pairedZero_val]
  field_simp [hρ0, hρ1]
  ring

private lemma weierstrass_E_one_mul_paired_linear (ρ : NontrivialZero) (s : ℂ) :
    Hadamard.weierstrassE 1 (s / ρ.val) *
        Hadamard.weierstrassE 1 (s / (pairedZero ρ).val)
      =
    Complex.exp (s / (ρ.val * (pairedZero ρ).val)) *
      xiPairedLinearFactor ρ s := by
  have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
  have hρ1 : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (NontrivialZero.ne_one ρ).symm
  have hsum :
      s / ρ.val + s / (1 - ρ.val) = s / (ρ.val * (1 - ρ.val)) := by
    field_simp [hρ0, hρ1]
    ring
  rw [Hadamard.weierstrass_E_one, Hadamard.weierstrass_E_one, pairedZero_val, xiPairedLinearFactor]
  calc
    (1 - s / ρ.val) * Complex.exp (s / ρ.val) *
      ((1 - s / (1 - ρ.val)) * Complex.exp (s / (1 - ρ.val)))
        = ((1 - s / ρ.val) * (1 - s / (1 - ρ.val))) *
            (Complex.exp (s / ρ.val) * Complex.exp (s / (1 - ρ.val))) := by
              ring_nf
    _ = ((1 - s / ρ.val) * (1 - s / (1 - ρ.val))) *
          Complex.exp (s / ρ.val + s / (1 - ρ.val)) := by
            rw [← Complex.exp_add]
    _ = ((1 - s / ρ.val) * (1 - s / (1 - ρ.val))) *
          Complex.exp (s / (ρ.val * (1 - ρ.val))) := by rw [hsum]
    _ = Complex.exp (s / (ρ.val * (1 - ρ.val))) * xiPairedLinearFactor ρ s := by
          simp [xiPairedLinearFactor, mul_comm]

lemma xiPairedLinearFactor_phi_ne_zero_of_separation {z : ℂ}
    (hz1 : z ≠ (1 : ℂ))
    (hzavoid : ∀ ρ : NontrivialZero, z ≠ 1 - 1 / (ρ.val : ℂ))
    (ρ : NontrivialZero) :
    xiPairedLinearFactor ρ (1 / (1 - z)) ≠ 0 := by
  have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  intro h
  have hmul :
      (1 - (1 / (1 - z) : ℂ) / ρ.val) *
        (1 - (1 / (1 - z) : ℂ) / (pairedZero ρ).val) = 0 := by
    simpa [xiPairedLinearFactor] using h
  rcases mul_eq_zero.mp hmul with hleft | hright
  · have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
    have hdiv : (1 / (1 - z) : ℂ) / ρ.val = 1 := by
      simpa using (sub_eq_zero.mp hleft).symm
    have hEq : z = 1 - 1 / (ρ.val : ℂ) := by
      have h1 : (1 / (1 - z) : ℂ) = ρ.val := by
        exact (div_eq_one_iff_eq hρ0).mp hdiv
      have h2 : (ρ.val : ℂ) * ((1 : ℂ) - z) = 1 := by
        calc
          (ρ.val : ℂ) * ((1 : ℂ) - z) = (1 / (1 - z) : ℂ) * ((1 : ℂ) - z) := by simp [h1]
          _ = 1 := by field_simp [hzsub]
      have h3 : (1 : ℂ) - z = (1 : ℂ) / ρ.val := by
        apply (eq_div_iff hρ0).2
        simpa [mul_comm] using h2
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - 1 / (ρ.val : ℂ) := by simp [h3]
    exact hzavoid ρ hEq
  · have hpair0 : ((pairedZero ρ).val : ℂ) ≠ 0 := NontrivialZero.ne_zero (pairedZero ρ)
    have hdiv : (1 / (1 - z) : ℂ) / (pairedZero ρ).val = 1 := by
      simpa using (sub_eq_zero.mp hright).symm
    have hEq : z = 1 - 1 / ((pairedZero ρ).val : ℂ) := by
      have h1 : (1 / (1 - z) : ℂ) = (pairedZero ρ).val := by
        exact (div_eq_one_iff_eq hpair0).mp hdiv
      have h2 : ((pairedZero ρ).val : ℂ) * ((1 : ℂ) - z) = 1 := by
        calc
          ((pairedZero ρ).val : ℂ) * ((1 : ℂ) - z)
              = (1 / (1 - z) : ℂ) * ((1 : ℂ) - z) := by simp [h1]
          _ = 1 := by field_simp [hzsub]
      have h3 : (1 : ℂ) - z = (1 : ℂ) / (pairedZero ρ).val := by
        apply (eq_div_iff hpair0).2
        simpa [mul_comm] using h2
      calc
        z = 1 - ((1 : ℂ) - z) := by ring
        _ = 1 - 1 / ((pairedZero ρ).val : ℂ) := by simp [h3]
    exact hzavoid (pairedZero ρ) hEq

lemma xiPairedLinearFactor_sub_one (ρ : NontrivialZero) (s : ℂ) :
    xiPairedLinearFactor ρ s - 1 =
      s * (s - 1) / (ρ.val * (pairedZero ρ).val) := by
  have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
  have hρ1 : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (NontrivialZero.ne_one ρ).symm
  rw [xiPairedLinearFactor, pairedZero_val]
  field_simp [hρ0, hρ1]
  ring

lemma xiPairedLinearFactor_phi_sub_one {z : ℂ} (hz1 : z ≠ (1 : ℂ))
    (ρ : NontrivialZero) :
    xiPairedLinearFactor ρ (1 / (1 - z)) - 1
      =
    z / ((ρ.val * (pairedZero ρ).val) * (1 - z) ^ 2) := by
  have hzsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
  have hpair0 : ((pairedZero ρ).val : ℂ) ≠ 0 := NontrivialZero.ne_zero (pairedZero ρ)
  rw [xiPairedLinearFactor_sub_one]
  field_simp [hzsub, hρ0, hpair0]
  ring

/-- Explicit derivative of the paired linear factor. -/
lemma deriv_xiPairedLinearFactor (ρ : NontrivialZero) (s : ℂ) :
    deriv (xiPairedLinearFactor ρ) s =
      (2 * s - 1) / (ρ.val * (pairedZero ρ).val) := by
  have hrepr :
      xiPairedLinearFactor ρ =
        fun w : ℂ => 1 + (w * (w - 1)) / (ρ.val * (pairedZero ρ).val) := by
    funext w
    calc
      xiPairedLinearFactor ρ w = (xiPairedLinearFactor ρ w - 1) + 1 := by ring
      _ = w * (w - 1) / (ρ.val * (pairedZero ρ).val) + 1 := by
            rw [xiPairedLinearFactor_sub_one]
      _ = 1 + (w * (w - 1)) / (ρ.val * (pairedZero ρ).val) := by ring
  let c : ℂ := (ρ.val * (pairedZero ρ).val)⁻¹
  have hrepr' :
      (fun w : ℂ => 1 + (w * (w - 1)) / (ρ.val * (pairedZero ρ).val))
        =
      (fun w : ℂ => 1 + (w * (w - 1)) * c) := by
    funext w
    simp [c, div_eq_mul_inv]
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => w * (w - 1)) s := by
    exact differentiableAt_id.mul (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
  have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
  have hpair0 : ((pairedZero ρ).val : ℂ) ≠ 0 := NontrivialZero.ne_zero (pairedZero ρ)
  have hderiv :
      deriv (fun w : ℂ => w * (w - 1)) s = (1 : ℂ) * (s - 1) + s * (1 : ℂ) := by
    have hdiff' : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := by
      exact differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ)))
    have hm := deriv_mul differentiableAt_id hdiff'
    simp
  rw [hrepr, hrepr']
  calc
    deriv (fun w : ℂ => 1 + (w * (w - 1)) * c) s
        = deriv (fun w : ℂ => (w * (w - 1)) * c) s := by
            have h :=
              deriv_const_add (c := (1 : ℂ))
                (f := fun w : ℂ => (w * (w - 1)) * c) (x := s)
            exact h
    _ = deriv (fun w : ℂ => w * (w - 1)) s * c := by
          exact deriv_mul_const hdiff c
    _ = ((1 : ℂ) * (s - 1) + s * (1 : ℂ)) * c := by rw [hderiv]
    _ = (2 * s - 1) / (ρ.val * (pairedZero ρ).val) := by
          have hsimp : ((1 : ℂ) * (s - 1) + s * (1 : ℂ)) = 2 * s - 1 := by ring
          rw [hsimp]
          change (2 * s - 1) * ((ρ.val * (pairedZero ρ).val)⁻¹) =
            (2 * s - 1) / (ρ.val * (pairedZero ρ).val)
          rw [div_eq_mul_inv]

/-- A `φ`-pullback of the paired linear factor is differentiable on a ball inside the unit disk. -/
lemma xiPairedLinearFactor_phi_differentiableOn_ball {r : ℝ} (hr_lt_one : r < 1)
    (ρ : NontrivialZero) :
    DifferentiableOn ℂ (fun z : ℂ => xiPairedLinearFactor ρ (1 / (1 - z)))
      (Metric.ball (0 : ℂ) r) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by
    have : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact lt_of_lt_of_le this hr_lt_one.le
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    have : ¬ (‖z‖ : ℝ) < 1 := by simp [hz1]
    exact this hz'
  have h_sub_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz_ne_one.symm
  have h_inv_diff : DifferentiableAt ℂ (fun w : ℂ => 1 / (1 - w)) z := by
    apply DifferentiableAt.div
    · exact differentiableAt_const (c := (1 : ℂ))
    · exact (DifferentiableAt.sub (differentiableAt_const (c := (1 : ℂ))) differentiableAt_id)
    · exact h_sub_ne
  have h_pf_at : DifferentiableAt ℂ (xiPairedLinearFactor ρ) (1 / (1 - z)) :=
    (xiPairedLinearFactor_differentiable ρ).differentiableAt
  exact (h_pf_at.comp z h_inv_diff).differentiableWithinAt

lemma inv_norm_mul_pairedZero_le_of_two_le_norm (ρ : NontrivialZero)
    (hρ : (2 : ℝ) ≤ ‖ρ.val‖) :
    (1 : ℝ) / ‖(ρ.val : ℂ) * (pairedZero ρ).val‖ ≤
      (2 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hpair_lower : ‖ρ.val‖ / 2 ≤ ‖(pairedZero ρ).val‖ := by
    have hsub : ‖(ρ.val : ℂ)‖ - ‖(1 : ℂ)‖ ≤ ‖(ρ.val : ℂ) - 1‖ := by
      simpa using (norm_sub_norm_le (ρ.val : ℂ) (1 : ℂ))
    have hhalf : ‖ρ.val‖ / 2 ≤ ‖ρ.val‖ - 1 := by
      nlinarith
    calc
      ‖ρ.val‖ / 2 ≤ ‖ρ.val‖ - 1 := hhalf
      _ = ‖(ρ.val : ℂ)‖ - ‖(1 : ℂ)‖ := by norm_num
      _ ≤ ‖(ρ.val : ℂ) - 1‖ := hsub
      _ = ‖(pairedZero ρ).val‖ := by
            simp [pairedZero_val, norm_sub_rev]
  have hprod_lower :
      ‖ρ.val‖ * (‖ρ.val‖ / 2) ≤ ‖(ρ.val : ℂ) * (pairedZero ρ).val‖ := by
    calc
      ‖ρ.val‖ * (‖ρ.val‖ / 2) ≤ ‖ρ.val‖ * ‖(pairedZero ρ).val‖ := by
        gcongr
      _ = ‖(ρ.val : ℂ) * (pairedZero ρ).val‖ := by
            simp
  have hρnorm_pos : 0 < ‖ρ.val‖ := norm_pos_iff.2 ρ.ne_zero
  have hbase_pos : 0 < ‖ρ.val‖ * (‖ρ.val‖ / 2) := by positivity
  have hrecip :
      (1 : ℝ) / ‖(ρ.val : ℂ) * (pairedZero ρ).val‖ ≤
        (1 : ℝ) / (‖ρ.val‖ * (‖ρ.val‖ / 2)) :=
    one_div_le_one_div_of_le hbase_pos hprod_lower
  have hnorm_ne : ‖ρ.val‖ ≠ 0 := by exact ne_of_gt hρnorm_pos
  calc
    (1 : ℝ) / ‖(ρ.val : ℂ) * (pairedZero ρ).val‖
        ≤ (1 : ℝ) / (‖ρ.val‖ * (‖ρ.val‖ / 2)) := hrecip
    _ = (2 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
          field_simp [hnorm_ne]

theorem summable_inv_mul_pairedZero_withMultiplicity_of_genus_one
    (hgenus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2)) :
    Summable (fun i : XiZeroWithMultiplicity => (1 : ℂ) / (i.1.val * (pairedZero i.1).val)) := by
  have hlarge :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, (2 : ℝ) ≤ ‖i.1.val‖ := by
    exact eventually_le_norm_of_summable_inv_norm_sq_withMultiplicity hgenus (R := 2) (by norm_num)
  refine Summable.of_norm_bounded_eventually (hgenus.mul_left (2 : ℝ)) ?_
  filter_upwards [hlarge] with i hi
  have hbound := inv_norm_mul_pairedZero_le_of_two_le_norm i.1 hi
  simpa [norm_div, norm_mul] using hbound

lemma multipliable_xiPairedLinearFactor_withMultiplicity_of_genus_one (s : ℂ)
    (hgenus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2)) :
    Multipliable (fun i : XiZeroWithMultiplicity => xiPairedLinearFactor i.1 s) := by
  have hlarge :
      ∀ᶠ i : XiZeroWithMultiplicity in Filter.cofinite, (2 : ℝ) ≤ ‖i.1.val‖ := by
    exact eventually_le_norm_of_summable_inv_norm_sq_withMultiplicity hgenus (R := 2) (by norm_num)
  have hdom :
      Summable (fun i : XiZeroWithMultiplicity =>
        (‖s * (s - 1)‖ : ℝ) * ((2 : ℝ) * ((1 : ℝ) / ‖i.1.val‖ ^ 2))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hgenus.mul_left ((‖s * (s - 1)‖ : ℝ) * (2 : ℝ)))
  have hnorm :
      Summable (fun i : XiZeroWithMultiplicity => ‖xiPairedLinearFactor i.1 s - 1‖) := by
    refine Summable.of_norm_bounded_eventually hdom ?_
    filter_upwards [hlarge] with i hi
    have hbound := inv_norm_mul_pairedZero_le_of_two_le_norm i.1 hi
    calc
      ‖‖xiPairedLinearFactor i.1 s - 1‖‖ = ‖xiPairedLinearFactor i.1 s - 1‖ := by simp
      _ = ‖s * (s - 1) / (i.1.val * (pairedZero i.1).val)‖ := by
            rw [xiPairedLinearFactor_sub_one]
      _ = ‖s * (s - 1)‖ * ((1 : ℝ) / ‖(i.1.val : ℂ) * (pairedZero i.1).val‖) := by
            rw [norm_div]
            ring
      _ ≤ ‖s * (s - 1)‖ * ((2 : ℝ) * ((1 : ℝ) / ‖i.1.val‖ ^ 2)) := by
            gcongr
  have hmul := _root_.multipliable_one_add_of_summable hnorm
  simpa [sub_eq_add_neg] using hmul

lemma xiE1ProdWithMultiplicity_sq_eq_exp_mul_tprod_xiPairedLinearFactor_of_genus_one
    (hgenus : Summable (fun i : XiZeroWithMultiplicity => (1 : ℝ) / ‖i.1.val‖ ^ 2)) (s : ℂ) :
    (xiE1ProdWithMultiplicity s) ^ 2 =
      Complex.exp
          (s * ∑' i : XiZeroWithMultiplicity, (1 : ℂ) / (i.1.val * (pairedZero i.1).val)) *
        ∏' i : XiZeroWithMultiplicity, xiPairedLinearFactor i.1 s := by
  classical
  let f : XiZeroWithMultiplicity → ℂ := fun i =>
    Hadamard.weierstrassE 1 (s / i.1.val)
  let g : XiZeroWithMultiplicity → ℂ := fun i => f (pairedZeroWithMultiplicity i)
  let d : XiZeroWithMultiplicity → ℂ := fun i =>
    (1 : ℂ) / (i.1.val * (pairedZero i.1).val)
  let q : XiZeroWithMultiplicity → ℂ := fun i => xiPairedLinearFactor i.1 s
  have hf : Multipliable f := by
    simpa [f] using multipliable_xiE1ProdWithMultiplicity_term_of_genus_one s hgenus
  have hg : Multipliable g := by
    simpa [g, Function.comp_def, coe_pairedZeroWithMultiplicityEquiv] using
      (pairedZeroWithMultiplicityEquiv.multipliable_iff).2 hf
  have hd : Summable d := by
    simpa [d] using summable_inv_mul_pairedZero_withMultiplicity_of_genus_one hgenus
  have hq : Multipliable q := by
    simpa [q] using multipliable_xiPairedLinearFactor_withMultiplicity_of_genus_one s hgenus
  have htprod_g : (∏' i : XiZeroWithMultiplicity, g i) = ∏' i : XiZeroWithMultiplicity, f i := by
    simpa [g, coe_pairedZeroWithMultiplicityEquiv] using (pairedZeroWithMultiplicityEquiv.tprod_eq
    f)
  have hmul :
      (∏' i : XiZeroWithMultiplicity, f i * g i)
        =
      (∏' i : XiZeroWithMultiplicity, f i) * ∏' i : XiZeroWithMultiplicity, g i := by
    simpa using (hf.tprod_mul hg)
  have hexp :
      Multipliable (fun i : XiZeroWithMultiplicity => Complex.exp (s * d i)) := by
    simpa [Function.comp_def] using (hd.mul_left s).hasSum.cexp.multipliable
  have hsplit :
      (∏' i : XiZeroWithMultiplicity, Complex.exp (s * d i) * q i)
        =
      (∏' i : XiZeroWithMultiplicity, Complex.exp (s * d i)) *
        ∏' i : XiZeroWithMultiplicity, q i := by
    simpa using (hexp.tprod_mul hq)
  have hterm : ∀ i : XiZeroWithMultiplicity, f i * g i = Complex.exp (s * d i) * q i := by
    intro i
    dsimp [f, g, d, q]
    simpa [pairedZeroWithMultiplicity, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      weierstrass_E_one_mul_paired_linear i.1 s
  have hfg :
      (∏' i : XiZeroWithMultiplicity, f i * g i)
        =
      ∏' i : XiZeroWithMultiplicity, Complex.exp (s * d i) * q i := by
    refine tprod_congr ?_
    intro i
    exact hterm i
  have hexp_tprod :
      (∏' i : XiZeroWithMultiplicity, Complex.exp (s * d i))
        = Complex.exp (∑' i : XiZeroWithMultiplicity, s * d i) := by
    simpa [Function.comp_def] using (hd.mul_left s).hasSum.cexp.tprod_eq
  have hsum_mul :
      (∑' i : XiZeroWithMultiplicity, s * d i)
        = s * ∑' i : XiZeroWithMultiplicity, d i := by
    simpa using hd.tsum_mul_left s
  have : (∏' i : XiZeroWithMultiplicity, f i) ^ 2 =
      Complex.exp (s * ∑' i : XiZeroWithMultiplicity, d i) *
        ∏' i : XiZeroWithMultiplicity, q i := by
    calc
      (∏' i : XiZeroWithMultiplicity, f i) ^ 2
          = (∏' i : XiZeroWithMultiplicity, f i) * ∏' i : XiZeroWithMultiplicity, f i := by
              simp [pow_two]
      _ = (∏' i : XiZeroWithMultiplicity, f i) * ∏' i : XiZeroWithMultiplicity, g i := by
            simp [htprod_g]
      _ = ∏' i : XiZeroWithMultiplicity, f i * g i := by
            simpa using hmul.symm
      _ = ∏' i : XiZeroWithMultiplicity, Complex.exp (s * d i) * q i := hfg
      _ = (∏' i : XiZeroWithMultiplicity, Complex.exp (s * d i)) *
            ∏' i : XiZeroWithMultiplicity, q i := hsplit
      _ = Complex.exp (∑' i : XiZeroWithMultiplicity, s * d i) *
            ∏' i : XiZeroWithMultiplicity, q i := by rw [hexp_tprod]
      _ = Complex.exp (s * ∑' i : XiZeroWithMultiplicity, d i) *
            ∏' i : XiZeroWithMultiplicity, q i := by rw [hsum_mul]
  simpa [xiE1ProdWithMultiplicity, f, d, q] using this

-- The multiplicity-weighted paired factorization expands through both the weighted zero data
-- and the `tprod` regrouping lemmas, so this proof needs a slightly higher heartbeat limit.
theorem xi_sq_factorization_pairedLinear_withMultiplicity_of_weighted_genus
    (hgenus : Summable
      (fun ρ : NontrivialZero => (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2))
    (hhad : xiFactorizationProdWithMultiplicity) :
    ∃ b₂ : ℂ, ∀ s : ℂ,
      (riemannXi s) ^ 2 =
        Complex.exp b₂ * ∏' i : XiZeroWithMultiplicity, xiPairedLinearFactor i.1 s := by
  classical
  obtain ⟨a, b, hξ⟩ := hhad
  have hsigma_genus := summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus hgenus
  let c : ℂ :=
    (2 : ℂ) * a +
      ∑' i : XiZeroWithMultiplicity, (1 : ℂ) / (i.1.val * (pairedZero i.1).val)
  let d : ℂ := (2 : ℂ) * b
  let P : ℂ → ℂ := fun s => ∏' i : XiZeroWithMultiplicity, xiPairedLinearFactor i.1 s
  have hP :
      ∀ s : ℂ, (riemannXi s) ^ 2 = Complex.exp (c * s + d) * P s := by
    intro s
    calc
      (riemannXi s) ^ 2
          = (Complex.exp (a * s + b) * xiE1ProdWithMultiplicity s) ^ 2 := by rw [hξ s]
      _ = (Complex.exp (a * s + b)) ^ 2 * (xiE1ProdWithMultiplicity s) ^ 2 := by
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = Complex.exp ((2 : ℂ) * (a * s + b)) * (xiE1ProdWithMultiplicity s) ^ 2 := by
            rw [pow_two, ← Complex.exp_add]
            ring_nf
      _ = Complex.exp ((2 : ℂ) * (a * s + b)) *
            (Complex.exp
                (s * ∑' i : XiZeroWithMultiplicity,
                  (1 : ℂ) / (i.1.val * (pairedZero i.1).val)) * P s) := by
            rw [xiE1ProdWithMultiplicity_sq_eq_exp_mul_tprod_xiPairedLinearFactor_of_genus_one
              hsigma_genus]
      _ = (Complex.exp ((2 : ℂ) * (a * s + b)) *
            Complex.exp
              (s * ∑' i : XiZeroWithMultiplicity,
                (1 : ℂ) / (i.1.val * (pairedZero i.1).val))) * P s := by
            ring
      _ = Complex.exp
            (((2 : ℂ) * (a * s + b)) +
              s * ∑' i : XiZeroWithMultiplicity,
                (1 : ℂ) / (i.1.val * (pairedZero i.1).val)) * P s := by
            rw [← Complex.exp_add]
      _ = Complex.exp (c * s + d) * P s := by
            have harg :
                ((2 : ℂ) * (a * s + b)) +
                    s * ∑' i : XiZeroWithMultiplicity,
                      (1 : ℂ) / (i.1.val * (pairedZero i.1).val)
                  =
                c * s + d := by
              simp [c, d]
              ring
            rw [harg]
  have hP_one_sub : ∀ s : ℂ, P (1 - s) = P s := by
    intro s
    refine tprod_congr ?_
    intro i
    simpa [P] using xiPairedLinearFactor_one_sub i.1 s
  have hsymm :
      ∀ s : ℂ, Complex.exp (c * s + d) * P s = Complex.exp (c * (1 - s) + d) * P s := by
    intro s
    calc
      Complex.exp (c * s + d) * P s = (riemannXi s) ^ 2 := by
            simpa [P] using (hP s).symm
      _ = (riemannXi (1 - s)) ^ 2 := by
            rw [xi_functional_equation]
      _ = Complex.exp (c * (1 - s) + d) * P (1 - s) := by
            simpa [P] using hP (1 - s)
      _ = Complex.exp (c * (1 - s) + d) * P s := by rw [hP_one_sub]
  have hxi0 : riemannXi (0 : ℂ) ≠ 0 := by
    unfold riemannXi
    norm_num
  have hP0 : P 0 ≠ 0 := by
    intro hPzero
    have hxi0sq : (riemannXi (0 : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hxi0
    have h0 := hP 0
    rw [hPzero, mul_zero] at h0
    exact hxi0sq h0
  let F : ℂ → ℂ := fun s => Complex.exp (c * s + d)
  let G : ℂ → ℂ := fun s => Complex.exp (c * (1 - s) + d)
  have hFG : ∀ s : ℂ, F s * P s = G s * P s := by
    intro s
    simpa [F, G] using hsymm s
  have hFP_eq : F 0 = G 0 := by
    simpa using (mul_right_cancel₀ hP0 (hFG 0))
  have hP_eq :
      P = fun s : ℂ => Complex.exp (-(c * s + d)) * (riemannXi s) ^ 2 := by
    funext s
    calc
      P s = 1 * P s := by simp
      _ = (Complex.exp (-(c * s + d)) * Complex.exp (c * s + d)) * P s := by
            have hexp :
                Complex.exp (-(c * s + d)) * Complex.exp (c * s + d) = (1 : ℂ) := by
              rw [← Complex.exp_add]
              have : -(c * s + d) + (c * s + d) = (0 : ℂ) := by ring
              rw [this]
              simp
            rw [hexp]
      _ = Complex.exp (-(c * s + d)) * (Complex.exp (c * s + d) * P s) := by ring
      _ = Complex.exp (-(c * s + d)) * (riemannXi s) ^ 2 := by rw [← hP s]
  have hF_inner_diff : DifferentiableAt ℂ (fun s : ℂ => c * s + d) 0 := by
    exact
      DifferentiableAt.add
        ((differentiableAt_const (c := c)).mul differentiableAt_id)
        (differentiableAt_const (c := d))
  have hG_inner_diff : DifferentiableAt ℂ (fun s : ℂ => c * (1 - s) + d) 0 := by
    exact
      DifferentiableAt.add
        ((differentiableAt_const (c := c)).mul
          (DifferentiableAt.sub (differentiableAt_const (c := (1 : ℂ))) differentiableAt_id))
        (differentiableAt_const (c := d))
  have hP_diff : DifferentiableAt ℂ P 0 := by
    rw [hP_eq]
    exact hF_inner_diff.neg.cexp.mul ((xi_entire.pow 2).differentiableAt)
  have hF_diff : DifferentiableAt ℂ F 0 := hF_inner_diff.cexp
  have hG_diff : DifferentiableAt ℂ G 0 := hG_inner_diff.cexp
  have hF_deriv : deriv F 0 = F 0 * c := by
    have hmul : deriv (fun s : ℂ => c * s) 0 = c := by
      simp
    have hinner : deriv (fun s : ℂ => c * s + d) 0 = c := by
      have h := deriv_add_const (f := fun s : ℂ => c * s) (c := d) (x := (0 : ℂ))
      rw [hmul] at h
      exact h
    calc
      deriv F 0 = Complex.exp (c * (0 : ℂ) + d) * deriv (fun s : ℂ => c * s + d) 0 := by
            simpa [F] using (deriv_cexp (f := fun s : ℂ => c * s + d) (x := (0 : ℂ)) hF_inner_diff)
      _ = F 0 * c := by simp [F, hinner]
  have hG_deriv : deriv G 0 = G 0 * (-c) := by
    have hsub : deriv (fun s : ℂ => (1 : ℂ) - s) 0 = (-1 : ℂ) := by
      simp
    have hmul : deriv (fun s : ℂ => c * (1 - s)) 0 = -c := by
      calc
        deriv (fun s : ℂ => c * (1 - s)) 0 = c * deriv (fun s : ℂ => (1 : ℂ) - s) 0 := by
          exact deriv_const_mul c
            ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
        _ = -c := by simp [hsub]
    have hinner : deriv (fun s : ℂ => c * (1 - s) + d) 0 = -c := by
      have h := deriv_add_const (f := fun s : ℂ => c * (1 - s)) (c := d) (x := (0 : ℂ))
      rw [hmul] at h
      exact h
    calc
      deriv G 0 = Complex.exp (c * ((1 : ℂ) - (0 : ℂ)) + d) *
            deriv (fun s : ℂ => c * (1 - s) + d) 0 := by
              simpa [G] using
                (deriv_cexp (f := fun s : ℂ => c * (1 - s) + d) (x := (0 : ℂ)) hG_inner_diff)
      _ = G 0 * (-c) := by simp [G, hinner]
  have hderiv_eq :
      deriv (fun s : ℂ => F s * P s) 0 = deriv (fun s : ℂ => G s * P s) 0 := by
    simpa using congrArg (fun f : ℂ → ℂ => deriv f 0) (funext hFG)
  have hmain : (F 0 * ((2 : ℂ) * c)) * P 0 = 0 := by
    have hleft :
        deriv (fun s : ℂ => F s * P s) 0 = deriv F 0 * P 0 + F 0 * deriv P 0 := by
      simpa [Pi.mul_def] using (deriv_mul hF_diff hP_diff)
    have hright :
        deriv (fun s : ℂ => G s * P s) 0 = deriv G 0 * P 0 + G 0 * deriv P 0 := by
      simpa [Pi.mul_def] using (deriv_mul hG_diff hP_diff)
    calc
      (F 0 * ((2 : ℂ) * c)) * P 0
          =
        (deriv F 0 * P 0 + F 0 * deriv P 0) - (deriv G 0 * P 0 + G 0 * deriv P 0) := by
            rw [hF_deriv, hG_deriv, hFP_eq]
            ring
      _ = (deriv (fun s : ℂ => F s * P s) 0) - (deriv (fun s : ℂ => G s * P s) 0) := by
            rw [hleft, hright]
      _ = 0 := by rw [hderiv_eq]; ring
  have hF0_ne : F 0 ≠ 0 := by
    simp [F]
  have hc_two : (2 : ℂ) * c = 0 := by
    have hmain' : ((2 : ℂ) * c) * (F 0 * P 0) = 0 := by
      calc
        ((2 : ℂ) * c) * (F 0 * P 0) = (F 0 * ((2 : ℂ) * c)) * P 0 := by ring
        _ = 0 := hmain
    have hFP_ne : F 0 * P 0 ≠ 0 := mul_ne_zero hF0_ne hP0
    exact (mul_eq_zero.mp hmain').resolve_right hFP_ne
  have hc_zero : c = 0 := by
    rcases mul_eq_zero.mp hc_two with htwo | hc
    · norm_num at htwo
    · exact hc
  refine ⟨d, ?_⟩
  intro s
  simpa [c, d, P, hc_zero] using hP s

/-- Taylor coefficients for a single paired linear factor give the paired Li summand,
counting the self-paired case `ρ = 1 - ρ` with multiplicity two. -/
lemma taylorCoeff_xiPairedLinearFactor (ρ : NontrivialZero) (n : ℕ) :
    taylorCoeff (xiPairedLinearFactor ρ) n = liPairedSummand n ρ := by
  classical
  by_cases hne : (ρ.val : ℂ) = (pairedZero ρ).val
  · have hpair : pairedZero ρ = ρ := by
      exact Subtype.ext hne.symm
    have hsq :
        xiPairedLinearFactor ρ = fun s : ℂ => (1 - s / ρ.val) ^ 2 := by
      funext s
      simp [xiPairedLinearFactor, hpair, pow_two]
    calc
      taylorCoeff (xiPairedLinearFactor ρ) n
          = taylorCoeff (fun s : ℂ => (1 - s / ρ.val) ^ 2) n := by
              simpa using congrArg (fun g : ℂ → ℂ => taylorCoeff g n) hsq
      _ = (2 : ℂ) * liSummand n ρ := taylorCoeff_square_singleLinearFactor ρ n
      _ = liPairedSummand n ρ := by
            simp [liPairedSummand, hpair, two_mul]
  · let S : Finset ℂ := {ρ.val, (pairedZero ρ).val}
    have hS0 : (0 : ℂ) ∉ S := by
      have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
      have hpair0 : ((pairedZero ρ).val : ℂ) ≠ 0 := NontrivialZero.ne_zero (pairedZero ρ)
      intro h0
      have h0' : (0 : ℂ) = ρ.val ∨ (0 : ℂ) = (pairedZero ρ).val := by
        simpa [S, eq_comm] using h0
      rcases h0' with h0ρ | h0pair
      · exact hρ0 h0ρ.symm
      · exact hpair0 h0pair.symm
    have hS1 : ∀ x ∈ S, x ≠ (1 : ℂ) := by
      intro x hx
      have hx' : x = ρ.val ∨ x = (pairedZero ρ).val := by
        simpa [S] using hx
      rcases hx' with rfl | rfl
      · exact NontrivialZero.ne_one ρ
      · exact NontrivialZero.ne_one (pairedZero ρ)
    have hfinite :
        taylorCoeff (fun s : ℂ => ∏ x ∈ S, (1 - s / x)) n
          = ∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))) := by
      have hphiS :
          phi (fun s : ℂ => ∏ x ∈ S, (1 - s / x))
            =
          (fun z : ℂ => ∏ x ∈ S, (1 + -((1 + -z)⁻¹ / x))) := by
        funext z
        simp [phi, one_div, sub_eq_add_neg]
      have hfin :=
        taylorCoeff_finite_Li (S := S) hS0 n (by
          intro x hx
          exact hS1 x hx)
      simpa [taylorCoeff, hphiS, sub_eq_add_neg, phi_eq] using hfin
    have hprod :
        xiPairedLinearFactor ρ = fun s : ℂ => ∏ x ∈ S, (1 - s / x) := by
      funext s
      rw [xiPairedLinearFactor]
      simpa [S] using
        (Finset.prod_pair (f := fun x : ℂ => 1 - s / x) (a := ρ.val)
          (b := (pairedZero ρ).val) hne).symm
    calc
      taylorCoeff (xiPairedLinearFactor ρ) n
          = taylorCoeff (fun s : ℂ => ∏ x ∈ S, (1 - s / x)) n := by
              simpa using congrArg (fun g : ℂ → ℂ => taylorCoeff g n) hprod
      _ = ∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))) := hfinite
      _ = liPairedSummand n ρ := by
            have hsum_pair :
                (∑ x ∈ S, (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))))
                  =
                (1 - (1 - 1 / ρ.val) ^ (-(n + 1 : ℤ)))
                  + (1 - (1 - 1 / (pairedZero ρ).val) ^ (-(n + 1 : ℤ))) := by
              simpa [S] using
                (Finset.sum_pair
                  (f := fun x : ℂ => (1 - (1 - 1 / x) ^ (-(n + 1 : ℤ))))
                  (a := ρ.val) (b := (pairedZero ρ).val) hne)
            simpa [liPairedSummand, liSummand, add_comm] using hsum_pair

/-!
For the Riemann ξ function the raw, unpaired Li summand behaves like `(n+1)/ρ`, so absolute
convergence of the unpaired series fails. We work instead with the paired summand
`liPairedSummand` and its summability lemma `xi_summable_Li_paired_summand`.
-/

-- The nontrivial zeros are precisely the zeros of ξ.
-- Follows from Hadamard product: ξ(w) = C · ∏ρ (1 - w/ρ) with C ≠ 0.
lemma xi_nonzero_away_from_nontrivial_zeros (w : ℂ)
    (h : ∀ ρ : NontrivialZero, w ≠ ρ.val) :
    riemannXi w ≠ 0 := by
  -- If ξ(w) = 0, then by the zeros characterization, w equals some nontrivial zero ρ.
  -- This contradicts the hypothesis h.
  intro hzero
  -- By xi_zeros_are_nontrivial_zeros: ξ(w) = 0 ↔ ∃ ρ, w = ρ.val
  obtain ⟨ρ, hw_eq⟩ := (xi_zeros_are_nontrivial_zeros w).mp hzero
  -- But h says w ≠ ρ.val for all ρ
  exact (h ρ) hw_eq

-- Precise global log-derivative identity near z = 0 will follow from product/log-derivative
-- expansion and uniform convergence; see the comment above.

-- precise: λₙ as a global sum over all nontrivial zeros
/-! ### Weierstrass Theorem: Uniform convergence and Taylor coefficients -/

-- **Weierstrass Theorem for Coefficients**
-- Conway §VII.2: Uniform limits of holomorphic functions
-- If analytic functions f_k → f uniformly on a neighborhood of z, then
-- the n-th derivatives converge pointwise: (deriv^[n] f_k)(z) → (deriv^[n] f)(z).
--
-- This follows from iterating `TendstoLocallyUniformlyOn.deriv` (Mathlib) n times.
-- See: Mathlib/Analysis/Complex/LocallyUniformLimit.lean, theorem at line 150
/-- Uniform limits of analytic partial functions have convergent Taylor coefficients. -/
lemma deriv_iterate_tendsto_of_uniform_of_analytic_partials
    (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n : ℕ)
    (hrpos : 0 < r)
    (han_partial : ∀ k, AnalyticOnNhd ℂ (f k) (Metric.ball z₀ r))
    (hunif_conv : TendstoUniformlyOn f g atTop (Metric.ball z₀ r)) :
    Filter.Tendsto (fun k => (deriv^[n] (f k)) z₀ / n.factorial)
      atTop (𝓝 ((deriv^[n] g) z₀ / n.factorial)) := by
  -- Proof by induction on n
  induction n with
  | zero =>
    -- Base case: deriv^[0] = id, so we need f_k(z₀) → g(z₀)
    simp only [Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one, div_one]
    -- From uniform convergence on the ball, we get pointwise convergence at z₀
    have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hrpos
    exact hunif_conv.tendsto_at hz₀
  | succ n ih =>
    -- Inductive step: prove deriv^[n+1](f_k)(z₀)/(n+1)! → deriv^[n+1](g)(z₀)/(n+1)!
    -- Strategy: iterate derivative convergence n+1 times, then extract pointwise convergence
    -- Helper lemma: uniform convergence of m-th derivatives for m ≤ n+1
    have h_deriv_conv : ∀ m : ℕ, m ≤ n + 1 →
        TendstoLocallyUniformlyOn
          (fun k => deriv^[m] (f k)) (deriv^[m] g) atTop (Metric.ball z₀ r) := by
      intro m hm
      induction m with
      | zero =>
        -- Base: deriv^[0] = id, so this is just hunif_conv converted to locally uniform
        simp only [Function.iterate_zero, id_eq]
        exact hunif_conv.tendstoLocallyUniformlyOn
      | succ m' ih_m' =>
        -- Inductive: apply TendstoLocallyUniformlyOn.deriv
        have hm' : m' ≤ n + 1 := by omega
        have h_prev := ih_m' hm'
        -- Need: eventually all deriv^[m'] (f k) are differentiable
        have h_diff : ∀ᶠ k in atTop, DifferentiableOn ℂ (deriv^[m'] (f k)) (Metric.ball z₀ r) := by
          apply Eventually.of_forall
          intro k
          -- Use: AnalyticOnNhd.iterated_deriv and AnalyticOnNhd.differentiableOn
          have h_iter : AnalyticOnNhd ℂ (deriv^[m'] (f k)) (Metric.ball z₀ r) :=
            (han_partial k).iterated_deriv m'
          exact h_iter.differentiableOn
        -- Ball is open
        have h_open : IsOpen (Metric.ball z₀ r) := Metric.isOpen_ball
        -- Apply the derivative convergence theorem from Mathlib
        -- This is theorem `_root_.TendstoLocallyUniformlyOn.deriv`
        -- from `LocallyUniformLimit.lean` (line 150).
        have h_deriv := TendstoLocallyUniformlyOn.deriv h_prev h_diff h_open
        -- `h_deriv : TendstoLocallyUniformlyOn
        --   (deriv ∘ fun k => deriv^[m'] (f k)) (deriv (deriv^[m'] g))`
        -- We need: TendstoLocallyUniformlyOn (fun k => deriv^[m'+1] (f k)) (deriv^[m'+1] g)
        -- Key: deriv^[m'+1] = deriv ∘ deriv^[m'] by Function.iterate_succ'
        have h_lhs : (fun k => deriv^[m'+1] (f k)) = (deriv ∘ fun k => deriv^[m'] (f k)) := by
          ext k x; simp only [Function.comp_apply, Function.iterate_succ']
        have h_rhs : deriv^[m'+1] g = deriv (deriv^[m'] g) := by
          simp only [Function.iterate_succ', Function.comp_apply]
        rw [h_lhs, h_rhs]
        exact h_deriv
    -- Extract pointwise convergence at z₀ for the (n+1)-th derivative
    have h_conv := h_deriv_conv (n + 1) (le_refl _)
    have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hrpos
    -- Extract pointwise convergence using TendstoLocallyUniformlyOn.tendsto_at
    have h_ptwise : Filter.Tendsto (fun k => (deriv^[n+1] (f k)) z₀)
        atTop (𝓝 ((deriv^[n+1] g) z₀)) :=
      h_conv.tendsto_at hz₀
    -- Divide both sides by (n+1)! to get the desired form
    exact h_ptwise.div_const ((n + 1).factorial : ℂ)

lemma deriv_iterate_tendsto_of_uniform
    (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n : ℕ)
    (hrpos : 0 < r)
    (han_partial : ∀ k, AnalyticOnNhd ℂ (f k) (Metric.ball z₀ r))
    (_han_limit : AnalyticOnNhd ℂ g (Metric.ball z₀ r))
    (hunif_conv : TendstoUniformlyOn f g atTop (Metric.ball z₀ r)) :
    Filter.Tendsto (fun k => (deriv^[n] (f k)) z₀ / n.factorial)
      atTop (𝓝 ((deriv^[n] g) z₀ / n.factorial)) := by
  exact deriv_iterate_tendsto_of_uniform_of_analytic_partials
    f g z₀ r n hrpos han_partial hunif_conv

/-! ### Global Li sum formula via uniform-convergence reduction -/

/- Reduction theorem: passing finite identities to the limit under uniform
convergence and summability. -/
theorem coeff_sum_formula_precise_reduction (n : ℕ)
    (T : ℕ → Finset NontrivialZero) (monoT : Monotone T)
    (cover : (⋃ n, (T n : Set NontrivialZero)) = Set.univ)
    (hunif : ∃ r > 0,
      AnalyticOnNhd ℂ (logDeriv (fun z => riemannXi (1 / (1 - z)))) (Metric.ball 0 r) ∧
      (∀ n, AnalyticOnNhd ℂ
        (logDeriv (fun z => (∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1 / (1 - z)) / ρ))))
        (Metric.ball 0 r)) ∧
      TendstoUniformlyOn (fun n z =>
        logDeriv (fun w => (∏ ρ ∈ (T n).image (fun ρ => ρ.val), (1 - (1 / (1 - w)) / ρ))) z)
        (logDeriv (fun z => riemannXi (1 / (1 - z)))) atTop (Metric.ball 0 r))
    (hsum : Summable (fun ρ : NontrivialZero =>
      (1 - (1 - 1/(ρ.val)) ^ (-(n+1 : ℤ))))) :
    taylorCoeff riemannXi n
      = ∑' ρ : NontrivialZero, (1 - (1 - 1/(ρ.val)) ^ (-(n+1 : ℤ))) := by
  classical
  -- Define the finite approximants φₙ from T n
  let S : ℕ → Finset ℂ := fun k => (T k).image (fun ρ => ρ.val)
  let fS : ℕ → (ℂ → ℂ) := fun k s => ∏ c ∈ S k, (1 - s/c)
  let φS : ℕ → (ℂ → ℂ) := fun k z => fS k (1/(1-z))
  -- Step 1: finite coefficient identity for each k
  have hfin : ∀ k, (deriv^[n] (logDeriv (φS k))) 0 / n.factorial
          = ∑ c ∈ S k, (1 - (1 - 1/c) ^ (-(n+1 : ℤ))) := by
    intro k
    -- Unfold local definitions
    have hS0 : (0 : ℂ) ∉ S k := by
      intro h
      rcases Finset.mem_image.mp h with ⟨ρ, hρT, hval⟩
      exact (NontrivialZero.ne_zero ρ) (by simp [hval])
    have hS1 : ∀ c ∈ S k, c ≠ (1 : ℂ) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨ρ, hρT, rfl⟩
      exact NontrivialZero.ne_one ρ
    simpa [S, fS, φS] using taylorCoeff_finite_Li (S := S k) hS0 n (by intro c hc; exact hS1 c hc)
  -- Step 2: the left side tends to taylorCoeff riemannXi n by uniform convergence
  -- (Weierstrass/Cauchy coefficient extraction on a small disk around 0)
  have hleft :
      Filter.Tendsto (fun k => (deriv^[n] (logDeriv (φS k))) 0 / n.factorial)
        atTop (𝓝 (taylorCoeff riemannXi n)) := by
    -- Extract r and properties from hunif
    obtain ⟨r, hrpos, han_limit, han_partial, hunif_conv⟩ := hunif
    -- Apply Weierstrass theorem: uniform convergence → convergence of Taylor coefficients
    -- The sequence is: logDeriv (φS k)
    -- The limit is: logDeriv (fun z => riemannXi (1/(1-z)))
    have h_coeffs := deriv_iterate_tendsto_of_uniform
      (fun k => logDeriv (φS k))
      (logDeriv (fun z => riemannXi (1/(1-z))))
      0 r n
      hrpos han_partial han_limit hunif_conv
    -- Key: taylorCoeff is DEFINED as (deriv^[n] (logDeriv (phi f))) 0 / n!
    -- where phi f z = f (1/(1-z))
    -- So taylorCoeff riemannXi n = (deriv^[n] (logDeriv (fun z => riemannXi (1/(1-z))))) 0 / n!
    -- This is exactly the limit that Weierstrass gives us!
    -- h_coeffs gives us convergence to (deriv^[n] (logDeriv (fun z => riemannXi (1/(1-z))))) 0 / n!
    -- By definition, taylorCoeff riemannXi n = (deriv^[n] (logDeriv (phi riemannXi))) 0 / n!
    -- and phi riemannXi z = riemannXi (1/(1-z)) by definition
    -- Therefore these are definitionally equal
    exact h_coeffs
  -- Step 3: the right side tends to the `tsum` by summability and the covering
  have hright :
      Filter.Tendsto (fun k => ∑ c ∈ S k, (1 - (1 - 1/c) ^ (-(n+1 : ℤ))))
        atTop (𝓝 (∑' ρ : NontrivialZero, (1 - (1 - 1/(ρ.val)) ^ (-(n+1 : ℤ))))) := by
    -- Standard "partial sums → tsum" for an increasing exhaustion by finite sets.
    -- Strategy: Use that T k exhausts NontrivialZero and sum over T k first
    -- First rewrite: ∑ c ∈ S k, f(c) = ∑ ρ ∈ T k, f(ρ.val)
    have h_rewrite : ∀ k, ∑ c ∈ S k, (1 - (1 - 1/c) ^ (-(n+1 : ℤ))) =
                           ∑ ρ ∈ T k, (1 - (1 - 1/(ρ.val)) ^ (-(n+1 : ℤ))) := by
      intro k
      simp only [S]
      rw [Finset.sum_image]
      -- Need to show the function ρ ↦ ρ.val is injective on T k
      intro ρ₁ _ ρ₂ _ hval
      exact Subtype.ext hval
    -- Now use that Finset.sum over increasing sets → tsum
    rw [Filter.tendsto_congr' (Filter.Eventually.of_forall h_rewrite)]
    -- Key fact: by cover, every ρ is eventually in T k
    -- So the Finset sums converge to the tsum
    -- Strategy: Use that hsum gives us HasSum, and partial sums → tsum for HasSum
    have h_hassum : HasSum (fun ρ : NontrivialZero => (1 - (1 - 1/(ρ.val)) ^ (-(n+1 : ℤ))))
                           (∑' ρ : NontrivialZero, (1 - (1 - 1/(ρ.val)) ^ (-(n+1 : ℤ)))) := by
      exact Summable.hasSum hsum
    -- HasSum means: Tendsto (fun s : Finset NontrivialZero => ∑ ρ ∈ s, ...) atTop (𝓝 tsum)
    -- We need: Tendsto (fun k : ℕ => ∑ ρ ∈ T k, ...) atTop (𝓝 tsum)
    -- Key: T k tends to atTop in the filter of finite sets (by monotonicity + cover)
    -- First show T tends to atTop
    have hT_atTop : Filter.Tendsto T atTop (atTop : Filter (Finset NontrivialZero)) := by
      apply Monotone.tendsto_atTop_finset monoT
      intro ρ
      -- Every ρ is in ⋃ n, (T n).toSet by cover
      have : ρ ∈ (⋃ n, (T n : Set NontrivialZero)) := by
        rw [cover]
        exact Set.mem_univ ρ
      simp only [Set.mem_iUnion] at this
      exact this
    -- Now compose: if F tends to L along atTop, and T tends to atTop, then F ∘ T tends to L
    have := h_hassum.comp hT_atTop
    exact this
  -- Step 4: pass to the limit on both sides
  -- We have: LHS k → taylorCoeff riemannXi n and RHS k → tsum
  -- And LHS k = RHS k for all k (by hfin)
  -- Therefore the limits must be equal
  -- Rewrite hleft using the equality hfin
  have hleft' : Filter.Tendsto (fun k => ∑ c ∈ S k, (1 - (1 - 1/c) ^ (-(n+1 : ℤ))))
        atTop (𝓝 (taylorCoeff riemannXi n)) := by
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall hfin) hleft
  -- Two limits of the same sequence must be equal
  exact tendsto_nhds_unique hleft' hright

/-! ### Separation and Cauchy tools (Conway; normal families and Cauchy's formula) -/

/-- A tiny inequality helper used in the genus‑1 refactor:

If `x ≥ 0` and `1/x² ≤ 1/16`, then `1/x ≤ 1/4`. We avoid square-roots by using
`mul_self_le_mul_self_iff`. -/
lemma one_div_le_quarter_of_one_div_sq_le_sixteenth {x : ℝ} (hx : 0 ≤ x)
    (h : (1 : ℝ) / x ^ 2 ≤ (1 / 16 : ℝ)) : (1 : ℝ) / x ≤ (1 / 4 : ℝ) := by
  have hsq : ((1 : ℝ) / x) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    have : (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ 2 := by norm_num
    simpa [one_div_pow, this] using h
  have ha : 0 ≤ (1 : ℝ) / x := by
    -- `x ≥ 0` implies `x⁻¹ ≥ 0`, hence `1/x ≥ 0` (with `inv 0 = 0`).
    simpa [one_div] using (inv_nonneg.2 hx)
  have hb : 0 ≤ (1 / 4 : ℝ) := by norm_num
  exact (mul_self_le_mul_self_iff ha hb).2 (by simpa [pow_two] using hsq)

/-- Separation radius: there exists `r > 0` (with `r < 1`) such that for all `z` with `‖z‖ < r`,
we have `z ≠ 1` and also `z ≠ 1 - 1 / ρ` for every nontrivial zero `ρ` of ζ.

**Proof**: Since |Im(ρ)| ≥ 14 for all nontrivial zeros (the first zero is at ~14.13i),
we have |ρ| ≥ 14, hence |1 / ρ| ≤ 1/14 < 0.1.
Therefore |1 - 1 / ρ| ≥ |1| - |1 / ρ| ≥ 1 - 1/14 > 0.9.
So for `r = 1 / 2`, the ball `B(0, r)` avoids all points `1 - 1 / ρ`
(which are all at distance `> 0.9` from `0`).
The ball also avoids z = 1 since |1| = 1 > 1 / 2.

Reference: Conway FOOCV, Ch. V (isolated zeros); Titchmarsh Ch. 9 (first zero). -/
theorem separation_radius_exists_of_summable_inv_norm_sq
    (hgenus : Summable (fun (ρ : NontrivialZero) => (1 : ℝ) / ‖ρ.val‖ ^ 2)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) r,
      (z ≠ 1) ∧ (∀ ρ : NontrivialZero, z ≠ 1 - 1/(ρ.val)) := by
  classical
  -- Genus‑1 summability implies `(1/‖ρ‖²) → 0` along `cofinite`, hence eventually
  -- `(1/‖ρ‖²) ≤ 1/16`, so the exceptional set is finite.
  have hsmallSq :
      ∀ᶠ ρ : NontrivialZero in Filter.cofinite, (1 : ℝ) / ‖ρ.val‖ ^ 2 ≤ (1 / 16 : ℝ) :=
    hgenus.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16)
  have hcomp :
      ({ρ : NontrivialZero | (1 : ℝ) / ‖ρ.val‖ ^ 2 ≤ (1 / 16 : ℝ)} : Set NontrivialZero)ᶜ.Finite :=
    (Filter.mem_cofinite).1 (show
      ({ρ : NontrivialZero | (1 : ℝ) / ‖ρ.val‖ ^ 2 ≤ (1 / 16 : ℝ)} : Set NontrivialZero) ∈
        (Filter.cofinite : Filter NontrivialZero) from hsmallSq)
  have hbad_fin :
      ({ρ : NontrivialZero | (1 / 16 : ℝ) < (1 : ℝ) / ‖ρ.val‖ ^ 2} :
        Set NontrivialZero).Finite := by
    simpa [Set.compl_ofPred, not_le] using hcomp
  let bad : Finset NontrivialZero := hbad_fin.toFinset
  -- Define the pole corresponding to a zero.
  let pole : NontrivialZero → ℂ := fun ρ => (1 : ℂ) - (1 : ℂ) / ρ.val
  -- If `ρ ∉ bad` then `(1/‖ρ‖²) ≤ 1/16`, hence `(1/‖ρ‖) ≤ 1/4`, hence `‖pole ρ‖ ≥ 3/4`.
  have h_pole_far_of_not_bad :
      ∀ ρ : NontrivialZero, ρ ∉ bad → (3 / 4 : ℝ) ≤ ‖pole ρ‖ := by
    intro ρ hρ
    have hρ_smallSq : (1 : ℝ) / ‖ρ.val‖ ^ 2 ≤ (1 / 16 : ℝ) := by
      have : ¬ (1 / 16 : ℝ) < (1 : ℝ) / ‖ρ.val‖ ^ 2 := by
        intro hlt
        have : ρ ∈ (bad : Set NontrivialZero) := by
          have : ρ ∈
              ({ρ : NontrivialZero | (1 / 16 : ℝ) < (1 : ℝ) / ‖ρ.val‖ ^ 2} :
                Set NontrivialZero) :=
            hlt
          have : ρ ∈ hbad_fin.toFinset := (hbad_fin.mem_toFinset (a := ρ)).2 this
          simpa [bad] using this
        exact hρ (by simpa using this)
      exact le_of_not_gt this
    have hρ_small : (1 : ℝ) / ‖ρ.val‖ ≤ (1 / 4 : ℝ) :=
      one_div_le_quarter_of_one_div_sq_le_sixteenth (x := ‖ρ.val‖) (norm_nonneg _) hρ_smallSq
    have h_inv_norm : ‖(1 : ℂ) / ρ.val‖ ≤ (1 / 4 : ℝ) := by
      simpa [norm_div, norm_one] using hρ_small
    have htri :
        ‖(1 : ℂ)‖ - ‖(1 : ℂ) / ρ.val‖ ≤ ‖pole ρ‖ := by
      simpa [pole] using norm_sub_norm_le (1 : ℂ) ((1 : ℂ) / ρ.val)
    have hlow : (3 / 4 : ℝ) ≤ ‖(1 : ℂ)‖ - ‖(1 : ℂ) / ρ.val‖ := by
      have : (3 / 4 : ℝ) ≤ (1 : ℝ) - ‖(1 : ℂ) / ρ.val‖ := by linarith [h_inv_norm]
      simpa using this
    exact le_trans hlow htri
  -- For the finite exceptional set, take half the minimum of their pole norms.
  by_cases hbad_empty : bad = ∅
  · refine ⟨(1 / 2 : ℝ), by norm_num, by norm_num, ?_⟩
    intro z hz
    have hz_norm : ‖z‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    constructor
    · intro hz1
      have : ‖z‖ = 1 := by simp [hz1]
      nlinarith
    · intro ρ hzρ
      have hfar : (3 / 4 : ℝ) ≤ ‖pole ρ‖ := by
        -- when `bad = ∅`, every `ρ` is "not bad"
        have : ρ ∉ bad := by simp [hbad_empty]
        exact h_pole_far_of_not_bad ρ this
      have hz_ge : (1 / 2 : ℝ) ≤ ‖pole ρ‖ := by
        have : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) := by norm_num
        exact le_trans this hfar
      have : ‖z‖ ≥ (1 / 2 : ℝ) := by simpa [pole, hzρ] using hz_ge
      exact (not_lt_of_ge this) hz_norm
  · have hbad_nonempty : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbad_empty
    let vals : Finset ℝ := bad.image (fun ρ : NontrivialZero => ‖pole ρ‖)
    have hvals_nonempty : vals.Nonempty := by
      simpa [vals, Finset.image_nonempty] using hbad_nonempty
    let δ : ℝ := vals.min' hvals_nonempty
    have hδ_pos : 0 < δ := by
      have hpos_each : ∀ x ∈ vals, (0 : ℝ) < x := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨ρ, hρ_bad, rfl⟩
        -- `pole ρ ≠ 0` since `ρ ≠ 1`
        have hρ1 : (ρ.val : ℂ) ≠ 1 := NontrivialZero.ne_one ρ
        have hρ0 : (ρ.val : ℂ) ≠ 0 := NontrivialZero.ne_zero ρ
        have hpole_ne : pole ρ ≠ 0 := by
          intro h
          have hdiv : (1 : ℂ) = (1 : ℂ) / ρ.val := sub_eq_zero.mp h
          have hdiv' : (1 : ℂ) / ρ.val = (1 : ℂ) := hdiv.symm
          have : (ρ.val : ℂ) = 1 := by
            -- multiply by ρ.val
            have : (ρ.val : ℂ) * ((1 : ℂ) / ρ.val) = (ρ.val : ℂ) * (1 : ℂ) := by
              simp [hdiv']
            have : (1 : ℂ) = (ρ.val : ℂ) := by
              simpa [div_eq_mul_inv, hρ0] using this
            exact this.symm
          exact hρ1 this
        exact norm_pos_iff.mpr hpole_ne
      have hmin_mem : δ ∈ vals := vals.min'_mem hvals_nonempty
      exact hpos_each δ hmin_mem
    -- Choose r = min(1 / 2, δ/2).
    let r : ℝ := min (1 / 2 : ℝ) (δ / 2)
    refine ⟨r, ?_, ?_, ?_⟩
    · have : 0 < δ / 2 := by nlinarith [hδ_pos]
      exact lt_min (by norm_num) this
    · have : r < 1 := by
        have : (1 / 2 : ℝ) < 1 := by norm_num
        exact lt_of_le_of_lt (min_le_left _ _) this
      simpa [r] using this
    · intro z hz
      have hz_norm : ‖z‖ < r := by
        simpa [Metric.mem_ball, dist_zero_right, r] using hz
      constructor
      · intro hz1
        have hz_eq : ‖z‖ = 1 := by simp [hz1]
        have hz_lt1 : ‖z‖ < (1 : ℝ) :=
          lt_of_lt_of_le hz_norm (le_trans (min_le_left _ _) (le_of_lt (by norm_num)))
        exact (ne_of_lt hz_lt1) hz_eq
      · intro ρ hzρ
        by_cases hρ_bad : ρ ∈ bad
        · have hδ_le : δ ≤ ‖pole ρ‖ := by
            have hx : ‖pole ρ‖ ∈ vals := Finset.mem_image_of_mem _ hρ_bad
            -- `δ` is the minimum of `vals`.
            exact vals.min'_le _ hx
          have hr_le : r ≤ ‖pole ρ‖ := by
            have hr_le_delta_half : r ≤ δ / 2 := min_le_right _ _
            have hdelta_half_le_delta : δ / 2 ≤ δ := by nlinarith [le_of_lt hδ_pos]
            exact le_trans (le_trans hr_le_delta_half hdelta_half_le_delta) hδ_le
          have : ‖z‖ ≥ r := by simpa [pole, hzρ] using hr_le
          exact (not_lt_of_ge this) hz_norm
        · have hfar : (3 / 4 : ℝ) ≤ ‖pole ρ‖ := h_pole_far_of_not_bad ρ hρ_bad
          have hr_le : r ≤ ‖pole ρ‖ := by
            have hr_le_half : r ≤ (1 / 2 : ℝ) := min_le_left _ _
            have hhalf_le : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) := by norm_num
            exact le_trans (le_trans hr_le_half hhalf_le) hfar
          have : ‖z‖ ≥ r := by simpa [pole, hzρ] using hr_le
          exact (not_lt_of_ge this) hz_norm

-- The nontrivial zeros are countable
-- This follows from zeros of analytic functions being isolated
-- The Riemann zeta function is not identically zero
lemma zeros_isolated : ∀ ρ : NontrivialZero, ∃ ε > 0,
    ∀ z ∈ Metric.ball ρ.val ε, z ≠ ρ.val → riemannZeta z ≠ 0 := by
  intro ρ
  -- The Riemann zeta function is differentiable away from s = 1
  have h_ne_one : ρ.val ≠ 1 := by
    intro h
    have hp := ρ.property
    rw [h] at hp
    -- hp.2.2 says 1 < 1, which is false
    exact absurd hp.2.2 (lt_irrefl 1)
  have h_diff : DifferentiableAt ℂ riemannZeta ρ.val := differentiableAt_riemannZeta h_ne_one
  -- The Riemann zeta function is differentiable on ℂ \ {1}
  -- Therefore it's analytic at ρ.val
  have h_analytic : AnalyticAt ℂ riemannZeta ρ.val := by
    -- Use the fact that a function differentiable on an open set is analytic
    have h_diff_on : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw =>
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    exact h_diff_on.analyticAt (isOpen_compl_singleton.mem_nhds h_ne_one)
  -- Apply the isolated zeros theorem
  obtain h_zero | h_nonzero := h_analytic.eventually_eq_zero_or_eventually_ne_zero
  · -- Case: eventually zero near ρ
    -- This would mean zeta is zero in a neighborhood of ρ.val
    -- By the identity theorem for analytic functions, this would make zeta identically zero
    -- But we know zeta(2) ≠ 0, contradiction
    exfalso
    -- The Riemann zeta function is analytic on ℂ \ {1}
    let U := {w : ℂ | w ≠ 1}
    -- U is preconnected (it's the complement of a single point)
    have hU_preconnected : IsPreconnected U := by
      -- The complement of a single point in ℂ is connected
      have : U = ({1} : Set ℂ)ᶜ := by
        ext x
        simp [U]
      rw [this]
      -- Complex numbers have dimension 2 over ℝ, so complement of singleton is connected
      exact (isConnected_compl_singleton_of_one_lt_rank
        (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
    -- zeta is analytic on U
    have hf_analytic : AnalyticOnNhd ℂ riemannZeta U := by
      intros w hw
      have h_diff : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta hw
      -- DifferentiableAt implies AnalyticAt for complex functions
      have h_diff_on : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
        (differentiableAt_riemannZeta hz).differentiableWithinAt
      exact h_diff_on.analyticAt (isOpen_compl_singleton.mem_nhds hw)
    -- The zero function is also analytic
    have hg_analytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) U := by
      exact analyticOnNhd_const
    -- ρ.val is in U (since ρ.val ≠ 1)
    have hρ_in_U : ρ.val ∈ U := h_ne_one
    -- zeta is eventually zero near ρ.val, so it equals zero eventually
    have h_eq : riemannZeta =ᶠ[𝓝 ρ.val] fun _ => 0 := h_zero
    -- By the identity theorem, zeta equals zero on all of U
    have h_eq_on : EqOn riemannZeta (fun _ : ℂ => (0 : ℂ)) U :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        hf_analytic hg_analytic hU_preconnected hρ_in_U h_eq
    -- In particular, zeta(2) = 0
    have h2_in_U : (2 : ℂ) ∈ U := by
      simp only [U, Set.mem_ofPred]
      norm_num
    have h_zeta_2_zero : riemannZeta 2 = 0 := h_eq_on h2_in_U
    -- But we proved zeta(2) ≠ 0
    rw [riemannZeta_two] at h_zeta_2_zero
    have : (Complex.ofReal Real.pi) ^ 2 / 6 ≠ 0 := by
      refine div_ne_zero ?_ ?_
      · refine pow_ne_zero 2 ?_
        exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · norm_num
    exact this h_zeta_2_zero
  · -- Case: eventually non-zero in punctured neighborhood
    -- This gives us exactly what we want
    -- Extract a ball where the function is non-zero except at the center
    -- h_nonzero : ∀ᶠ z in 𝓝[≠] ρ.val, riemannZeta z ≠ 0
    -- We need: ∃ ε > 0, ∀ z ∈ Metric.ball ρ.val ε, z ≠ ρ.val → riemannZeta z ≠ 0
    -- First, let's understand what 𝓝[≠] means
    -- It's the punctured neighborhood, which is 𝓝[{ρ.val}ᶜ] ρ.val
    -- Use the fact that eventually in punctured neighborhoods can be written
    -- with regular neighborhoods.
    rw [eventually_nhdsWithin_iff] at h_nonzero
    -- Now h_nonzero : ∀ᶠ x in 𝓝 ρ.val, x ∈ {ρ.val}ᶜ → riemannZeta x ≠ 0
    -- Convert to metric ball form using eventually_nhds_iff_ball
    rw [Metric.eventually_nhds_iff_ball] at h_nonzero
    -- Now h_nonzero : ∃ ε > 0, ∀ y ∈ ball ρ.val ε, y ∈ {ρ.val}ᶜ → riemannZeta y ≠ 0
    obtain ⟨ε, hε_pos, h_ball⟩ := h_nonzero
    use ε, hε_pos
    intros z hz hzne
    -- Apply h_ball
    exact h_ball z hz (Set.mem_compl_singleton_iff.mpr hzne)

-- A set of isolated points in a metric space is countable
lemma isolated_points_countable {α : Type*} [MetricSpace α] [SecondCountableTopology α]
    (S : Set α) (h_isolated : ∀ s ∈ S, ∃ ε > 0, ∀ t ∈ S, t ∈ Metric.ball s ε → t = s) :
    S.Countable := by
  -- We'll show S is countable by showing we can assign to each point
  -- a distinct element from a countable set
  -- For each s in S, choose εₛ > 0 such that the ball contains only s from S
  choose ε hε using h_isolated
  -- Consider rational balls: for each s, pick a rational q with 0 < q < εₛ
  have h_rational_balls : ∀ s hs, ∃ q : ℚ, 0 < q ∧ q < ε s hs ∧
      ∀ t ∈ S, t ∈ Metric.ball s q → t = s := by
    intro s hs
    have hε_pos := (hε s hs).1
    -- Pick a rational number between 0 and ε s hs
    have : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < ε s hs := by
      -- Use density of rationals: there exists a rational between 0 and ε s hs / 2
      have h_half : (0 : ℝ) < ε s hs / 2 := by linarith
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (0 : ℝ) < ε s hs / 2 from h_half)
      use q
      constructor
      · -- Need to prove: (0 : ℚ) < q
        -- We have: (0 : ℝ) < ↑q
        exact Rat.cast_pos.mp hq1
      · linarith
    obtain ⟨q, hq_pos, hq_lt⟩ := this
    use q
    refine ⟨hq_pos, hq_lt, ?_⟩
    intro t ht ht_ball
    apply (hε s hs).2 t ht
    exact Metric.ball_subset_ball (le_of_lt hq_lt) ht_ball
  -- Now we have an injection from `S` into the countable set of pairs
  -- `(center from basis, rational radius)`.
  -- Get a countable basis for α
  obtain ⟨B, hB_count, empty_set_not_el_of_B, hB_basis⟩ := TopologicalSpace.exists_countable_basis α
  -- For each s ∈ S, we can find a basis element containing s
  -- and a rational radius, giving an injection into B × ℚ
  have h_inj : ∃ f : S → B × ℚ, Function.Injective f := by
    -- For each s, pick a basis element containing it and the rational radius
    choose q hq using h_rational_balls
    -- Pick basis elements
    have : ∀ s : S, ∃ b ∈ B, s.val ∈ b ∧ b ⊆ Metric.ball s.val (q s.val s.prop / 2) := by
      intro ⟨s, hs⟩
      have hq_pos : (0 : ℝ) < q s hs := Rat.cast_pos.mpr (hq s hs).1
      have : Metric.ball s (q s hs / 2) ∈ 𝓝 s :=
        Metric.ball_mem_nhds s (by linarith : 0 < (q s hs : ℝ) / 2)
      obtain ⟨b, hb_B, hs_b, hb_sub⟩ := hB_basis.mem_nhds_iff.mp this
      exact ⟨b, hb_B, hs_b, hb_sub⟩
    choose b hb using this
    use fun s => ⟨⟨b s, (hb s).1⟩, q s.val s.prop⟩
    -- Prove injectivity
    intro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ h_eq
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h_eq
    obtain ⟨hb_eq, hq_eq⟩ := h_eq
    -- If they have the same basis element and radius, they must be the same point
    ext
    -- s₁ is in b s₁ = b s₂, which is contained in ball s₂ (q s₂ hs₂ / 2)
    have hs₁_in : s₁ ∈ b ⟨s₂, hs₂⟩ := by
      rw [← hb_eq]
      exact (hb ⟨s₁, hs₁⟩).2.1
    have : s₁ ∈ Metric.ball s₂ (q s₂ hs₂ / 2) := (hb ⟨s₂, hs₂⟩).2.2 hs₁_in
    -- Similarly, s₂ is in ball s₁ (q s₁ hs₁ / 2)
    have hs₂_in : s₂ ∈ b ⟨s₂, hs₂⟩ := (hb ⟨s₂, hs₂⟩).2.1
    have hb_s₁ : b ⟨s₂, hs₂⟩ = b ⟨s₁, hs₁⟩ := hb_eq.symm
    rw [hb_s₁] at hs₂_in
    have this₂ : s₂ ∈ Metric.ball s₁ (q s₁ hs₁ / 2) := (hb ⟨s₁, hs₁⟩).2.2 hs₂_in
    -- By triangle inequality, they are close to each other
    have hdist : dist s₁ s₂ < ↑(q s₁ hs₁) := by
      have hq_eq_real : (q s₁ hs₁ : ℝ) = (q s₂ hs₂ : ℝ) := by simp [hq_eq]
      rw [Metric.mem_ball] at this this₂
      have this' : dist s₁ s₂ < (q s₂ hs₂ : ℝ) / 2 := this
      have this₂' : dist s₁ s₂ < (q s₂ hs₂ : ℝ) / 2 := by
        rw [dist_comm]
        rw [← hq_eq_real]
        exact this₂
      rw [hq_eq_real]
      have hq_pos : (0 : ℝ) < q s₂ hs₂ := Rat.cast_pos.mpr (hq s₂ hs₂).1
      calc dist s₁ s₂
        _ < (q s₂ hs₂ : ℝ) / 2 + (q s₂ hs₂ : ℝ) / 2 := by linarith [this', hq_pos]
        _ = (q s₂ hs₂ : ℝ) := by ring
    -- Apply the isolation property
    have hdist_ball : s₂ ∈ Metric.ball s₁ (q s₁ hs₁) := by
      rw [Metric.mem_ball, dist_comm]
      exact hdist
    have : s₂ = s₁ := (hq s₁ hs₁).2.2 s₂ hs₂ hdist_ball
    simp [this]
  -- S injects into a countable set, so it's countable
  obtain ⟨f, hf_inj⟩ := h_inj
  have : Countable B := hB_count
  have : Countable ℚ := inferInstance
  have : Countable (B × ℚ) := inferInstance
  have : Function.Injective (fun s : S => f s) := hf_inj
  have : Countable S := this.countable
  exact this.to_set

noncomputable instance : Countable NontrivialZero := by
  -- NontrivialZero is a subtype of ℂ
  -- We proved that zeros of the Riemann zeta function are isolated
  -- Apply isolated_points_countable to the set of nontrivial zeros
  -- The set of values of NontrivialZero
  let S := {z : ℂ | ∃ ρ : NontrivialZero, ρ.val = z}
  -- S is exactly the set of nontrivial zeros in the critical strip
  have hS_eq : S = {z : ℂ | riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1} := by
    ext z
    simp only [Set.mem_ofPred]
    constructor
    · intro ⟨ρ, h_eq⟩
      rw [← h_eq]
      exact ρ.prop
    · intro hz
      use ⟨z, hz⟩
  -- Show S is countable using isolated_points_countable
  have hS_countable : S.Countable := by
    rw [hS_eq]
    apply isolated_points_countable
    intro s hs
    -- We proved zeros are isolated
    obtain ⟨ε, hε_pos, h_ball⟩ := zeros_isolated ⟨s, hs⟩
    use ε, hε_pos
    intro t ht ht_ball
    -- If t is in the ball and is a zero in the critical strip, then t = s
    by_cases h : t = s
    · exact h
    · -- If t ≠ s and t is in the ball, then riemannZeta t ≠ 0
      have : riemannZeta t ≠ 0 := h_ball t ht_ball h
      exact absurd ht.1 this
  -- NontrivialZero is countable because it's in bijection with S
  have h_bij : (Set.range (fun ρ : NontrivialZero => ρ.val)) = S := by
    ext z
    simp only [Set.mem_range]
    constructor
    · intro ⟨ρ, h_eq⟩
      exact ⟨ρ, h_eq⟩
    · intro ⟨ρ, h_eq⟩
      exact ⟨ρ, h_eq⟩
  -- The injection from NontrivialZero to ℂ has image S which is countable
  rw [← h_bij] at hS_countable
  -- Use injection from NontrivialZero to the range subtype
  have : Countable (Set.range (fun ρ : NontrivialZero => ρ.val)) := hS_countable.to_subtype
  have h_inj : Function.Injective
      (fun (ρ : NontrivialZero) =>
        (⟨ρ.val, Set.mem_range_self ρ⟩ :
          Set.range (fun (ρ : NontrivialZero) => ρ.val))) := by
    intro ρ₁ ρ₂ h
    -- h says the two subtype elements are equal, so their values are equal
    have h_val :
        (⟨ρ₁.val, Set.mem_range_self ρ₁⟩ :
          Set.range (fun (ρ : NontrivialZero) => ρ.val)).val =
        (⟨ρ₂.val, Set.mem_range_self ρ₂⟩ :
          Set.range (fun (ρ : NontrivialZero) => ρ.val)).val :=
      congrArg Subtype.val h
    have h_val' : ρ₁.val = ρ₂.val := by
      simpa only using h_val
    exact Subtype.ext h_val'
  exact h_inj.countable

noncomputable instance : Countable XiZeroWithMultiplicity := by
  dsimp [XiZeroWithMultiplicity]
  infer_instance

lemma exists_increasing_finite_cover_zeros_with_multiplicity :
    ∃ (T : ℕ → Finset XiZeroWithMultiplicity), Monotone T ∧
      (⋃ n, (T n : Set XiZeroWithMultiplicity)) = Set.univ := by
  simpa using exists_increasing_finite_cover_of_countable XiZeroWithMultiplicity

-- Existence of an increasing exhaustion by finite zero sets.
lemma exists_increasing_finite_cover_zeros :
    ∃ (T : ℕ → Finset NontrivialZero),
      Monotone T ∧ (⋃ n, (T n : Set NontrivialZero)) = Set.univ := by
  exact exists_increasing_finite_cover_of_countable NontrivialZero

end LiCriterion
