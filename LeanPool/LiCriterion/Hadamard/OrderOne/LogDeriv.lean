/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import LeanPool.LiCriterion.Hadamard.OrderOne.MultipliableFactors
public import LeanPool.LiCriterion.Hadamard.OrderOne.LocallyUniformProduct

/-!
Log-derivative control for genus‑1 canonical products.

The key output is a pointwise formula for the logarithmic derivative of
`w ↦ ∏' i, weierstrassE 1 (w / z i)` in terms of a (provably summable) partial-fraction series.
-/

@[expose] public section

open Complex Filter
open scoped BigOperators

namespace Hadamard
namespace OrderOne

lemma weierstrass_E_one_eq_zero_iff (w : ℂ) : weierstrassE 1 w = 0 ↔ w = 1 := by
  rw [weierstrass_E_one]
  constructor
  · intro h
    have : 1 - w = 0 := by
      have h' : (1 - w = 0) ∨ (Complex.exp w = 0) := by
        simpa [mul_eq_zero] using h
      cases h' with
      | inl h1 => exact h1
      | inr h2 => exact False.elim (Complex.exp_ne_zero w h2)
    exact sub_eq_zero.mp this |>.symm
  · intro hw
    simp [hw]

lemma weierstrass_E_one_ne_zero (w : ℂ) (hw : w ≠ 1) : weierstrassE 1 w ≠ 0 := by
  intro h0
  exact hw ((weierstrass_E_one_eq_zero_iff w).1 h0)

lemma weierstrass_E_one_div_ne_zero {a x : ℂ} (ha : a ≠ 0) (hx : x ≠ a) :
    weierstrassE 1 (x / a) ≠ 0 := by
  refine weierstrass_E_one_ne_zero (w := x / a) ?_
  intro hdiv
  have : x = a := (div_eq_one_iff_eq ha).1 hdiv
  exact hx this

lemma logDeriv_weierstrass_E_one_div {a x : ℂ} (ha : a ≠ 0) (hx : x ≠ a) :
    logDeriv (fun w : ℂ => weierstrassE 1 (w / a)) x = x / (a * (x - a)) := by
  classical
  -- Expand the genus‑1 factor: `E₁(w/a) = (1 - w/a) * exp(w/a)`.
  let f₁ : ℂ → ℂ := fun w => (1 : ℂ) - w / a
  let f₂ : ℂ → ℂ := fun w => Complex.exp (w / a)
  have hE : (fun w : ℂ => weierstrassE 1 (w / a)) = fun w => f₁ w * f₂ w := by
    funext w
    simp [f₁, f₂, weierstrass_E_one]
  have hf₁x : f₁ x ≠ 0 := by
    have hx_div : x / a ≠ 1 := by
      intro hxa
      exact hx ((div_eq_one_iff_eq ha).1 hxa)
    have hx_div' : (1 : ℂ) ≠ x / a := by
      simpa [eq_comm] using hx_div
    simpa [f₁, sub_eq_zero] using hx_div'
  have hf₂x : f₂ x ≠ 0 := by
    dsimp [f₂]
    exact Complex.exp_ne_zero (x / a)
  have hdf₁ : DifferentiableAt ℂ f₁ x := by
    have : DifferentiableAt ℂ (fun w : ℂ => w / a) x := (differentiableAt_id.div_const a)
    dsimp [f₁]
    exact this.const_sub (1 : ℂ)
  have hdf₂ : DifferentiableAt ℂ f₂ x := by
    -- `exp` composed with division by a constant.
    dsimp [f₂]
    exact (Complex.differentiable_exp).differentiableAt.comp x
      (differentiableAt_id.div_const a)
  have hlog_mul : logDeriv (fun w => f₁ w * f₂ w) x = logDeriv f₁ x + logDeriv f₂ x :=
    logDeriv_mul (x := x) hf₁x hf₂x hdf₁ hdf₂
  -- Compute `logDeriv f₂ x = 1/a`.
  have hlog_f₂ : logDeriv f₂ x = (1 : ℂ) / a := by
    have hdiv : HasDerivAt (fun w : ℂ => w / a) ((1 : ℂ) / a) x := by
      simpa using (hasDerivAt_id x).div_const a
    have hexp : HasDerivAt f₂ (Complex.exp (x / a) * ((1 : ℂ) / a)) x := by
      simpa [f₂, Function.comp_def, mul_assoc] using (Complex.hasDerivAt_exp (x / a)).comp x hdiv
    have hxexp_ne : Complex.exp (x / a) ≠ 0 := Complex.exp_ne_zero (x / a)
    have hderiv : deriv f₂ x = Complex.exp (x / a) * ((1 : ℂ) / a) := by
      exact hexp.deriv
    simp [logDeriv_apply, f₂, hderiv, hxexp_ne]
  -- Compute `logDeriv f₁ x = 1/(x-a)`.
  have hlog_f₁ : logDeriv f₁ x = (1 : ℂ) / (x - a) := by
    have hdiv : HasDerivAt (fun w : ℂ => w / a) ((1 : ℂ) / a) x := by
      simpa using (hasDerivAt_id x).div_const a
    have hf₁_deriv : deriv f₁ x = -((1 : ℂ) / a) := by
      have : HasDerivAt f₁ (-((1 : ℂ) / a)) x := by
        simpa [f₁] using (hdiv.const_sub (1 : ℂ))
      simpa using this.deriv
    have hf₁_val : f₁ x = (a - x) / a := by
      calc
        f₁ x = (1 : ℂ) - x / a := by simp [f₁]
        _ = a / a - x / a := by simp [ha]
        _ = (a - x) / a := by
          simpa using (sub_div a x a).symm
    have hax : a - x ≠ 0 := sub_ne_zero.mpr hx.symm
    calc
      logDeriv f₁ x = (-((1 : ℂ) / a)) / ((a - x) / a) := by
        simp [logDeriv_apply, hf₁_deriv, hf₁_val]
      _ = (-((1 : ℂ) / a)) * a / (a - x) := by
        simpa using (div_div_eq_mul_div (-((1 : ℂ) / a)) (a - x) a)
      _ = (-1 : ℂ) / (a - x) := by
        have hmul : (-((1 : ℂ) / a)) * a = (-1 : ℂ) := by
          -- `-(1/a) * a = -1` since `a ≠ 0`.
          simp [ha]
        -- Use `hmul` as a rewrite, avoiding fragile `simp` goals.
        rw [hmul]
      _ = (1 : ℂ) / (x - a) := by
        have hxa' : x - a ≠ 0 := sub_ne_zero.mpr hx
        field_simp [hax, hxa']
        ring
  -- Reassemble and simplify to the standard partial-fraction form.
  -- Rewrite the goal using the factorization `hE`, then substitute the computed log-derivatives.
  have hlog_mul' :
      logDeriv (fun w : ℂ => weierstrassE 1 (w / a)) x = logDeriv f₁ x + logDeriv f₂ x := by
    simpa [hE] using hlog_mul
  rw [hlog_mul', hlog_f₁, hlog_f₂]
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr hx
  field_simp [ha, hxa]
  ring

lemma summable_logDeriv_weierstrass_E_one_div_of_summable_inv_norm_sq
    {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ 2))
    (x : ℂ) (hx : ∀ i, x ≠ z i) :
    Summable (fun i : ι => logDeriv (fun w : ℂ => weierstrassE 1 (w / z i)) x) := by
  classical
  by_cases hx0 : x = 0
  · subst hx0
    -- In this case each term is `0`, so the series is trivially summable.
    have hzero : (fun i : ι => logDeriv (fun w : ℂ => weierstrassE 1 (w / z i)) (0 : ℂ)) = 0 := by
      funext i
      have hz : (0 : ℂ) ≠ z i := by simpa using (hz0 i).symm
      -- Use the explicit formula for the log-derivative, which becomes `0`.
      simpa using (logDeriv_weierstrass_E_one_div (a := z i) (x := (0 : ℂ)) (hz0 i) hz)
    simp only [hzero]
    exact (summable_zero : Summable (0 : ι → ℂ))
  · have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    let g : ι → ℝ := fun i => (2 * ‖x‖) * ((1 : ℝ) / ‖z i‖ ^ 2)
    have hg : Summable g := by
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using h.mul_left (2 * ‖x‖)
    refine Summable.of_norm_bounded_eventually (f := fun i : ι =>
        logDeriv (fun w : ℂ => weierstrassE 1 (w / z i)) x) (g := g) hg ?_
    -- Outside a finite set of small `‖z i‖`, we have `‖x/(z i*(x - z i))‖ ≤ 2‖x‖/‖z i‖²`.
    let S : Set ι := {i : ι | ‖z i‖ ≤ (2 : ℝ) * ‖x‖}
    have hSfinite : S.Finite :=
      finite_norm_le_of_summable_inv_norm_sq (z := z) hz0 h
        (R := (2 : ℝ) * ‖x‖) (by nlinarith [hx_norm_pos])
    have hnotS : ∀ᶠ i in (cofinite : Filter ι), i ∉ S := by
      have : (Sᶜ : Set ι) ∈ (cofinite : Filter ι) := by
        exact Filter.mem_cofinite.2 (by simpa using hSfinite)
      simpa using this
    filter_upwards [hnotS] with i hi
    have hz_gt : (2 : ℝ) * ‖x‖ < ‖z i‖ := by
      have : ¬‖z i‖ ≤ (2 : ℝ) * ‖x‖ := by simpa [S] using hi
      exact lt_of_not_ge this
    have hz_pos : 0 < ‖z i‖ := norm_pos_iff.2 (hz0 i)
    have hxa : x ≠ z i := hx i
    have hdist_pos : 0 < ‖x - z i‖ := norm_pos_iff.2 (sub_ne_zero.mpr hxa)
    have hdist_lower : (1 / 2 : ℝ) * ‖z i‖ ≤ ‖x - z i‖ := by
      have hx_lt : ‖x‖ < (1 / 2 : ℝ) * ‖z i‖ := by linarith [hz_gt]
      have hsub_lt : (1 / 2 : ℝ) * ‖z i‖ < ‖z i‖ - ‖x‖ := by linarith [hx_lt]
      have hsub_le : ‖z i‖ - ‖x‖ ≤ ‖x - z i‖ := by
        have := norm_sub_norm_le (z i) x
        -- `‖z‖ - ‖x‖ ≤ ‖z - x‖ = ‖x - z‖`
        simpa [norm_sub_rev] using this
      exact le_trans (le_of_lt hsub_lt) hsub_le
    -- Reduce to a norm estimate.
    have hterm :
        ‖logDeriv (fun w : ℂ => weierstrassE 1 (w / z i)) x‖ =
          ‖x / (z i * (x - z i))‖ := by
      have := logDeriv_weierstrass_E_one_div (a := z i) (x := x) (hz0 i) hxa
      simp [this]
    rw [hterm]
    have hzxa_pos : 0 < ‖z i‖ * ‖x - z i‖ := mul_pos hz_pos hdist_pos
    have hhalf_pos : 0 < (1 / 2 : ℝ) * ‖z i‖ ^ 2 := by positivity
    have hden_le : (1 / 2 : ℝ) * ‖z i‖ ^ 2 ≤ ‖z i‖ * ‖x - z i‖ := by
      -- `‖x - z‖ ≥ (1/2)‖z‖`.
      have : ‖z i‖ * ((1 / 2 : ℝ) * ‖z i‖) ≤ ‖z i‖ * ‖x - z i‖ :=
        mul_le_mul_of_nonneg_left hdist_lower (le_of_lt hz_pos)
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
    have hinv_le : (1 : ℝ) / (‖z i‖ * ‖x - z i‖) ≤ (2 : ℝ) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
      have hinv_le' :
          (1 : ℝ) / (‖z i‖ * ‖x - z i‖) ≤ (1 : ℝ) / ((1 / 2 : ℝ) * ‖z i‖ ^ 2) :=
        (one_div_le_one_div_of_le hhalf_pos hden_le)
      have : (1 : ℝ) / ((1 / 2 : ℝ) * ‖z i‖ ^ 2) = (2 : ℝ) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
        field_simp
      exact hinv_le'.trans_eq this
    have hnorm :
        ‖x / (z i * (x - z i))‖ ≤ (2 * ‖x‖) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
      -- `‖x/(z*(x-z))‖ = ‖x‖ / (‖z‖*‖x-z‖)`.
      have : ‖x / (z i * (x - z i))‖ = ‖x‖ * ((1 : ℝ) / (‖z i‖ * ‖x - z i‖)) := by
        simp [div_eq_mul_inv, mul_comm]
      rw [this]
      have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
      have hmul :=
        mul_le_mul_of_nonneg_left hinv_le hx_nonneg
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    simpa [g] using hnorm

lemma tprod_weierstrass_E_one_div_ne_zero_of_summable_inv_norm_sq
    {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ 2))
    (x : ℂ) (hx : ∀ i, x ≠ z i) :
    (∏' i : ι, weierstrassE 1 (x / z i)) ≠ 0 := by
  classical
  let f : ι → ℂ := fun i => weierstrassE 1 (x / z i) - 1
  have hf : ∀ i, 1 + f i ≠ 0 := by
    intro i
    have : weierstrassE 1 (x / z i) ≠ 0 :=
      weierstrass_E_one_div_ne_zero (a := z i) (x := x) (hz0 i) (hx i)
    simpa [f, add_assoc, sub_eq_add_neg] using this
  have hsum : Summable fun i : ι => ‖f i‖ := by
    simpa [f] using
      summable_norm_weierstrass_E_one_sub_one_of_summable_inv_norm_sq (z := z) hz0 h x
  have hnez := tprod_one_add_ne_zero_of_summable (f := f) hf hsum
  simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnez

/-- **Rank-`p` version**: `weierstrassE p (x / a) ≠ 0` whenever `a ≠ 0` and `x ≠ a`. -/
lemma weierstrass_E_div_ne_zero (p : ℕ) {a x : ℂ} (ha : a ≠ 0) (hx : x ≠ a) :
    weierstrassE p (x / a) ≠ 0 := by
  refine weierstrass_E_ne_zero_general p (w := x / a) ?_
  intro hdiv
  have : x = a := (div_eq_one_iff_eq ha).1 hdiv
  exact hx this

/-- **Rank-`p` version**: the rank-`p` canonical product is nonzero when the evaluation
point is not one of the zeros. Generalizes
`tprod_weierstrass_E_one_div_ne_zero_of_summable_inv_norm_sq` to exponent `p+1`. -/
lemma tprod_weierstrass_E_div_ne_zero_of_summable_inv_norm_pow
    {ι : Type*} {z : ι → ℂ} {p : ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ (p + 1)))
    (x : ℂ) (hx : ∀ i, x ≠ z i) :
    (∏' i : ι, weierstrassE p (x / z i)) ≠ 0 := by
  classical
  let f : ι → ℂ := fun i => weierstrassE p (x / z i) - 1
  have hf : ∀ i, 1 + f i ≠ 0 := by
    intro i
    have : weierstrassE p (x / z i) ≠ 0 :=
      weierstrass_E_div_ne_zero p (a := z i) (x := x) (hz0 i) (hx i)
    simpa [f, add_assoc, sub_eq_add_neg] using this
  have hsum : Summable fun i : ι => ‖f i‖ := by
    simpa [f] using
      summable_norm_weierstrass_E_sub_one_of_summable_inv_norm_pow
        (z := z) (p := p) hz0 h x
  have hnez := tprod_one_add_ne_zero_of_summable (f := f) hf hsum
  simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hnez

theorem logDeriv_tprod_weierstrass_E_one_eq_tsum_of_summable_inv_norm_sq
    {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ 2))
    (x : ℂ) (hx : ∀ i, x ≠ z i) :
    logDeriv (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) x =
      ∑' i : ι, x / (z i * (x - z i)) := by
  classical
  let s : Set ℂ := Set.univ
  let x0 : s := ⟨x, by simp [s]⟩
  have hf : ∀ i : ι, (fun w : ℂ => weierstrassE 1 (w / z i)) x0 ≠ 0 := by
    intro i
    simpa using weierstrass_E_one_div_ne_zero (a := z i) (x := x) (hz0 i) (hx i)
  have hd : ∀ i : ι, DifferentiableOn ℂ (fun w : ℂ => weierstrassE 1 (w / z i)) s := by
    intro i
    have hE : Differentiable ℂ (weierstrassE 1) := weierstrass_E_differentiable 1
    have hdiv : Differentiable ℂ (fun w : ℂ => w / z i) := by fun_prop
    exact ((hE.comp hdiv : Differentiable ℂ (fun w : ℂ => weierstrassE 1 (w / z i)))
      ).differentiableOn
  have hm :
      Summable fun i : ι => logDeriv (fun w : ℂ => weierstrassE 1 (w / z i)) x0 := by
    simpa using summable_logDeriv_weierstrass_E_one_div_of_summable_inv_norm_sq
      (z := z) hz0 h x hx
  have htend :
      MultipliableLocallyUniformlyOn (fun i (w : ℂ) => weierstrassE 1 (w / z i)) s := by
    have hprod :
        HasProdLocallyUniformlyOn (fun i (w : ℂ) => weierstrassE 1 (w / z i))
          (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) s := by
      simpa [s] using
        hasProdLocallyUniformlyOn_weierstrass_E_one_of_summable_inv_norm_sq (z := z) hz0 h
    exact hprod.multipliableLocallyUniformlyOn
  have hnez :
      (∏' i : ι, (fun w : ℂ => weierstrassE 1 (w / z i)) x0) ≠ 0 := by
    simpa using
      tprod_weierstrass_E_one_div_ne_zero_of_summable_inv_norm_sq (z := z) hz0 h x hx
  have hlog :=
    logDeriv_tprod_eq_tsum (ι := ι) (s := s) (hs := isOpen_univ) (x := x0)
      (hx := by simp [s]) (f := fun i (w : ℂ) => weierstrassE 1 (w / z i))
      hf hd hm htend hnez
  -- Rewrite the RHS as the convergent partial-fraction expression.
  have hterm :
      (fun i : ι => logDeriv (fun w : ℂ => weierstrassE 1 (w / z i)) x0) =
        (fun i : ι => x / (z i * (x - z i))) := by
    funext i
    simpa using logDeriv_weierstrass_E_one_div (a := z i) (x := x) (hz0 i) (hx i)
  simpa [s, hterm] using hlog

theorem logDeriv_exp_mul_tprod_weierstrass_E_one_eq_tsum_of_summable_inv_norm_sq
    {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ 2))
    (x : ℂ) (hx : ∀ i, x ≠ z i) (a b : ℂ) :
    logDeriv
        (fun w : ℂ =>
          Complex.exp (a * w + b) * ∏' i : ι, weierstrassE 1 (w / z i)) x =
      a + ∑' i : ι, x / (z i * (x - z i)) := by
  have hprod_ne : (∏' i : ι, weierstrassE 1 (x / z i)) ≠ 0 :=
    tprod_weierstrass_E_one_div_ne_zero_of_summable_inv_norm_sq (z := z) hz0 h x hx
  have hexp_ne : Complex.exp (a * x + b) ≠ 0 := Complex.exp_ne_zero (a * x + b)
  have hdexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (a * w + b)) x := by
    fun_prop
  have hdprod : DifferentiableAt ℂ (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) x := by
    have hdiff :
        DifferentiableOn ℂ (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) (Set.univ : Set ℂ) :=
      differentiableOn_tprod_weierstrass_E_one_of_summable_inv_norm_sq (z := z) hz0 h
    have hwithin :
        DifferentiableWithinAt ℂ (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) Set.univ x :=
      hdiff x (by simp)
    exact (differentiableWithinAt_univ.1 hwithin)
  have hlog_mul :
      logDeriv
          (fun w : ℂ => Complex.exp (a * w + b) * ∏' i : ι, weierstrassE 1 (w / z i)) x =
        logDeriv (fun w : ℂ => Complex.exp (a * w + b)) x +
          logDeriv (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) x := by
    -- `logDeriv` of a product is a sum, as long as both factors are nonzero at `x`.
    exact logDeriv_mul (x := x) (f := fun w : ℂ => Complex.exp (a * w + b))
      (g := fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) hexp_ne hprod_ne hdexp hdprod
  have hlog_exp : logDeriv (fun w : ℂ => Complex.exp (a * w + b)) x = a := by
    have hlin : HasDerivAt (fun w : ℂ => a * w + b) a x := by
      simpa [mul_comm, add_comm, add_left_comm, add_assoc]
        using (hasDerivAt_const_mul a (x := x)).add_const b
    have hexp : HasDerivAt (fun w : ℂ => Complex.exp (a * w + b)) (Complex.exp (a * x + b) * a) x :=
      (Complex.hasDerivAt_exp (a * x + b)).comp x hlin
    have hderiv : deriv (fun w : ℂ => Complex.exp (a * w + b)) x = Complex.exp (a * x + b) * a := by
      simpa using hexp.deriv
    simp [logDeriv_apply, hderiv, hexp_ne]
  have hlog_prod :
      logDeriv (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) x =
        ∑' i : ι, x / (z i * (x - z i)) :=
    logDeriv_tprod_weierstrass_E_one_eq_tsum_of_summable_inv_norm_sq (z := z) hz0 h x hx
  -- Combine the pieces.
  simp [hlog_mul, hlog_exp, hlog_prod]

end OrderOne
end Hadamard
