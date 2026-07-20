/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Clausen's formula and the hypergeometric differential equations

This file covers chapter 6 of Milla's proof of the Chudnovsky formula (arXiv:1809.00533v6,
`110_Clausen.tex`), together with the representation theorem `darst` from chapter 9
(`140_MainTheorem.tex`) and the Pochhammer/factorial identity used in its proof.

## Main definitions

* `generalizedHypergeometric` (notation `₃F₂`): the generalized hypergeometric function
  `₃F₂(α, β, γ; δ, ε; z) = ∑ (α)ₙ(β)ₙ(γ)ₙ / ((δ)ₙ(ε)ₙ) · zⁿ/n!` (paper Def. `defihyp`),
  defined in a topological algebra by mirroring Mathlib's `ordinaryHypergeometric` (`₂F₁`);
* `Chudnovsky.hyp2F1`: the specific instance `₂F₁(1/12, 5/12; 1; z)`;
* `Chudnovsky.hyp3F2`: the specific instance `₃F₂(1/6, 5/6, 1/2; 1, 1; z)`.

## Main statements

* `generalizedHypergeometric_summable` : absolute convergence for `‖z‖ < 1`
  (paper Thm. `satzkonv`; the `₂F₁` analogue is Mathlib's
  `ordinaryHypergeometricSeries_radius_eq_one`);
* `ordinaryHypergeometric_ode` : the second-order hypergeometric ODE for `₂F₁`
  (paper Thm. `dgl2f1`);
* `generalizedHypergeometric_ode` : the third-order ODE for `₃F₂` (paper Thm. `dgl3f2`);
* `clausen_formula` : **Clausen's formula**
  `(₂F₁(a, b; a+b+1/2; z))² = ₃F₂(2a, 2b, a+b; 2a+2b, a+b+1/2; z)` (paper Thm. `satzclausen`);
* `Chudnovsky.hyp2F1_sq_eq_hyp3F2` : its specialization at `a = 1/12`, `b = 5/12`;
* `Chudnovsky.ascPochhammer_prod_eq_factorial` : the Pochhammer/factorial identity
  `(1/6)ₙ(1/2)ₙ(5/6)ₙ = (6n)! / ((3n)!·12^(3n))` over `ℚ` (paper, proof of `darst`);
* `Chudnovsky.hyp2F1_sq_eq_tsum` : the representation
  `(₂F₁(1/12, 5/12; 1; z))² = ∑ (6n)!/((3n)!(n!)³) · zⁿ/12^(3n)` (paper Thm. `darst`).
-/

noncomputable section

open Nat FormalMultilinearSeries

/-! ## The generalized hypergeometric function `₃F₂` (paper Def. `defihyp`)

The definitions mirror `Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`. -/

section Field

variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- The coefficients in the generalized hypergeometric sum:
`(α)ₙ(β)ₙ(γ)ₙ / ((δ)ₙ(ε)ₙ n!)`, mirroring `ordinaryHypergeometricCoefficient`. -/
abbrev generalizedHypergeometricCoefficient (α β γ δ ε : 𝕂) (n : ℕ) : 𝕂 :=
  (n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval α * (ascPochhammer 𝕂 n).eval β *
    (ascPochhammer 𝕂 n).eval γ * ((ascPochhammer 𝕂 n).eval δ)⁻¹ *
    ((ascPochhammer 𝕂 n).eval ε)⁻¹

/-- `generalizedHypergeometricSeries 𝔸 (α β γ δ ε : 𝕂)` is a `FormalMultilinearSeries`.
Its sum is the `generalizedHypergeometric` map. -/
def generalizedHypergeometricSeries (α β γ δ ε : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 (generalizedHypergeometricCoefficient α β γ δ ε)

variable {𝔸} (α β γ δ ε : 𝕂)

/-- `generalizedHypergeometric (α β γ δ ε : 𝕂) : 𝔸 → 𝔸`, denoted `₃F₂`, is the generalized
hypergeometric map, defined as the sum of the `FormalMultilinearSeries`
`generalizedHypergeometricSeries 𝔸 α β γ δ ε`.

Note that this takes the junk value `0` outside the radius of convergence. -/
def generalizedHypergeometric (x : 𝔸) : 𝔸 :=
  (generalizedHypergeometricSeries 𝔸 α β γ δ ε).sum x

@[inherit_doc]
notation "₃F₂" => generalizedHypergeometric

theorem generalizedHypergeometricSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (generalizedHypergeometricSeries 𝔸 α β γ δ ε n fun _ => x) =
      generalizedHypergeometricCoefficient α β γ δ ε n • x ^ n := by
  rw [generalizedHypergeometricSeries, ofScalars_apply_eq]

theorem generalizedHypergeometric_sum_eq (x : 𝔸) :
    (generalizedHypergeometricSeries 𝔸 α β γ δ ε).sum x =
      ∑' n : ℕ, generalizedHypergeometricCoefficient α β γ δ ε n • x ^ n :=
  tsum_congr fun n => generalizedHypergeometricSeries_apply_eq α β γ δ ε x n

theorem generalizedHypergeometric_eq_tsum : ₃F₂ α β γ δ ε =
    fun x : 𝔸 => ∑' n : ℕ, generalizedHypergeometricCoefficient α β γ δ ε n • x ^ n :=
  funext (generalizedHypergeometric_sum_eq α β γ δ ε)

theorem generalizedHypergeometricSeries_apply_zero (n : ℕ) :
    (generalizedHypergeometricSeries 𝔸 α β γ δ ε n fun _ => 0) =
      Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [generalizedHypergeometricSeries, ofScalars_apply_eq]
  cases n <;> simp [generalizedHypergeometricCoefficient]

@[simp]
theorem generalizedHypergeometric_zero : ₃F₂ α β γ δ ε (0 : 𝔸) = 1 := by
  simp [generalizedHypergeometric_eq_tsum, ← generalizedHypergeometricSeries_apply_eq,
    generalizedHypergeometricSeries_apply_zero]

end Field

/-! ## Convergence (paper Thm. `satzkonv`) -/

open Filter Topology in
/-- The radius of convergence of `generalizedHypergeometricSeries` is unity if none of the
parameters are non-positive integers, mirroring `ordinaryHypergeometricSeries_radius_eq_one`. -/
theorem generalizedHypergeometricSeries_radius_eq_one {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂]
    [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] (α β γ δ ε : 𝕂)
    (h : ∀ kn : ℕ, (kn : 𝕂) ≠ -α ∧ (kn : 𝕂) ≠ -β ∧ (kn : 𝕂) ≠ -γ ∧ (kn : 𝕂) ≠ -δ ∧
      (kn : 𝕂) ≠ -ε) :
    (generalizedHypergeometricSeries 𝔸 α β γ δ ε).radius = 1 := by
  convert! ofScalars_radius_eq_of_tendsto 𝔸 _ one_ne_zero ?_
  -- The `n`-th coefficient ratio `c n / c (n+1)` equals `(δ+n)(ε+n)(1+n) / ((α+n)(β+n)(γ+n))`.
  have hpne : ∀ (x : 𝕂) (n : ℕ), (∀ kn : ℕ, (kn : 𝕂) ≠ -x) →
      (ascPochhammer 𝕂 n).eval x ≠ 0 := by
    intro x n hx hz
    rw [ascPochhammer_eval_eq_zero_iff] at hz
    obtain ⟨k, _, hk⟩ := hz
    exact hx k hk
  have hxn : ∀ (x : 𝕂) (n : ℕ), (∀ kn : ℕ, (kn : 𝕂) ≠ -x) → x + (n : 𝕂) ≠ 0 := by
    intro x n hx he
    rw [add_comm] at he
    exact hx n (eq_neg_of_add_eq_zero_left he)
  have key : ∀ n : ℕ, generalizedHypergeometricCoefficient α β γ δ ε n /
      generalizedHypergeometricCoefficient α β γ δ ε (n + 1) =
      ((δ + n) * (ε + n) * (1 + n)) / ((α + n) * (β + n) * (γ + n)) := by
    intro n
    have hα := hpne α n fun k => (h k).1
    have hβ := hpne β n fun k => (h k).2.1
    have hγ := hpne γ n fun k => (h k).2.2.1
    have hδ := hpne δ n fun k => (h k).2.2.2.1
    have hε := hpne ε n fun k => (h k).2.2.2.2
    have hαn := hxn α n fun k => (h k).1
    have hβn := hxn β n fun k => (h k).2.1
    have hγn := hxn γ n fun k => (h k).2.2.1
    have hδn := hxn δ n fun k => (h k).2.2.2.1
    have hεn := hxn ε n fun k => (h k).2.2.2.2
    have hfac : ((n ! : 𝕂)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hn1 : ((n : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hden : (α + (n : 𝕂)) * (β + n) * (γ + n) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hαn hβn) hγn
    have hcn1 : generalizedHypergeometricCoefficient α β γ δ ε (n + 1) ≠ 0 := by
      simp only [generalizedHypergeometricCoefficient]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
      · exact inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
      · exact hpne α (n + 1) fun k => (h k).1
      · exact hpne β (n + 1) fun k => (h k).2.1
      · exact hpne γ (n + 1) fun k => (h k).2.2.1
      · exact inv_ne_zero (hpne δ (n + 1) fun k => (h k).2.2.2.1)
      · exact inv_ne_zero (hpne ε (n + 1) fun k => (h k).2.2.2.2)
    have hrec : generalizedHypergeometricCoefficient α β γ δ ε n *
          ((α + (n : 𝕂)) * (β + n) * (γ + n)) =
        generalizedHypergeometricCoefficient α β γ δ ε (n + 1) *
          ((δ + (n : 𝕂)) * (ε + n) * (1 + n)) := by
      simp only [generalizedHypergeometricCoefficient, Nat.factorial_succ, ascPochhammer_succ_eval,
        Nat.cast_mul, Nat.cast_succ]
      field_simp
      ring
    exact (div_eq_div_iff hcn1 hden).mpr (hrec.trans (mul_comm _ _))
  have limit : Tendsto
      (fun n : ℕ => ((δ + n) * (ε + n) * (1 + n)) / ((α + n) * (β + n) * (γ + n)))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (δ + (n : 𝕂)) / (α + n)) atTop (𝓝 1) := by
      simpa using tendsto_add_mul_div_add_mul_atTop_nhds δ α (1 : 𝕂) (d := 1) one_ne_zero
    have h2 : Tendsto (fun n : ℕ => (ε + (n : 𝕂)) / (β + n)) atTop (𝓝 1) := by
      simpa using tendsto_add_mul_div_add_mul_atTop_nhds ε β (1 : 𝕂) (d := 1) one_ne_zero
    have h3 : Tendsto (fun n : ℕ => (1 + (n : 𝕂)) / (γ + n)) atTop (𝓝 1) := by
      simpa using tendsto_add_mul_div_add_mul_atTop_nhds (1 : 𝕂) γ (1 : 𝕂) (d := 1) one_ne_zero
    have heq : (fun n : ℕ => ((δ + (n : 𝕂)) * (ε + n) * (1 + n)) / ((α + n) * (β + n) * (γ + n)))
        = fun n : ℕ => (δ + (n : 𝕂)) / (α + n) * ((ε + n) / (β + n)) * ((1 + n) / (γ + n)) := by
      funext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    simpa using (h1.mul h2).mul h3
  have limitn : Tendsto
      (fun n : ℕ => ‖((δ + (n : 𝕂)) * (ε + n) * (1 + n)) / ((α + n) * (β + n) * (γ + n))‖)
      atTop (𝓝 1) := by simpa using Filter.Tendsto.norm limit
  refine limitn.congr (fun n => ?_)
  simp only [Nat.succ_eq_add_one]
  rw [← norm_div, key n]

open Filter Topology in
/-- Paper Thm. `satzkonv`: the generalized hypergeometric series converges absolutely for
`‖z‖ < 1` (ratio test). The `₂F₁` analogue is Mathlib's
`ordinaryHypergeometricSeries_radius_eq_one`. -/
theorem generalizedHypergeometric_summable (α β γ δ ε : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => generalizedHypergeometricCoefficient α β γ δ ε n * z ^ n := by
  by_cases hnz : ∀ kn : ℕ, (kn : ℂ) ≠ -α ∧ (kn : ℂ) ≠ -β ∧ (kn : ℂ) ≠ -γ ∧ (kn : ℂ) ≠ -δ ∧
      (kn : ℂ) ≠ -ε
  · -- Nondegenerate case: the radius of convergence is `1`, so the series converges for `‖z‖ < 1`.
    have hrad := generalizedHypergeometricSeries_radius_eq_one ℂ α β γ δ ε hnz
    have hlt : (‖z‖₊ : ENNReal) < (generalizedHypergeometricSeries ℂ α β γ δ ε).radius := by
      rw [hrad]
      exact_mod_cast hz
    have hsum := (generalizedHypergeometricSeries ℂ α β γ δ ε).summable_norm_mul_pow hlt
    apply Summable.of_norm
    refine hsum.congr (fun n => ?_)
    simp only [generalizedHypergeometricSeries, ofScalars_norm, norm_mul, norm_pow, coe_nnnorm]
  · -- Degenerate case: some parameter is a non-positive integer, so the coefficients eventually
    -- vanish and the series is a finite sum.
    rw [not_forall] at hnz
    obtain ⟨kn, hkn⟩ := hnz
    have hkn' : (kn : ℂ) = -α ∨ (kn : ℂ) = -β ∨ (kn : ℂ) = -γ ∨ (kn : ℂ) = -δ ∨ (kn : ℂ) = -ε := by
      by_contra hc
      push Not at hc
      exact hkn ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
    apply summable_of_ne_finset_zero (s := Finset.range (kn + 1))
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hlt : kn < n := hn
    have hc0 : generalizedHypergeometricCoefficient α β γ δ ε n = 0 := by
      simp only [generalizedHypergeometricCoefficient]
      rcases hkn' with hp | hp | hp | hp | hp
      all_goals
        first
        | (rw [show (ascPochhammer ℂ n).eval α = 0 by
              rw [show α = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; simp)
        | (rw [show (ascPochhammer ℂ n).eval β = 0 by
              rw [show β = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; simp)
        | (rw [show (ascPochhammer ℂ n).eval γ = 0 by
              rw [show γ = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; simp)
        | (rw [show (ascPochhammer ℂ n).eval δ = 0 by
              rw [show δ = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; simp)
        | (rw [show (ascPochhammer ℂ n).eval ε = 0 by
              rw [show ε = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; simp)
    rw [hc0, zero_mul]

/-! ### Term-by-term differentiation of scalar power series on the open unit disc

General infrastructure used to prove the hypergeometric ODEs. For a coefficient sequence
`c : ℕ → ℂ` whose power series is absolutely convergent on the open unit disc, the sum
`z ↦ ∑' n, cₙ zⁿ` is differentiable there, with derivative `∑' n, (n+1) c₍ₙ₊₁₎ zⁿ`. -/

/-- Absolute convergence of the scalar power series `∑ cₙ zⁿ` on the open unit disc. -/
private def DiscSummable (c : ℕ → ℂ) : Prop :=
  ∀ w : ℂ, ‖w‖ < 1 → Summable fun n : ℕ => ‖c n * w ^ n‖

/-- On the open unit disc, the polynomially-weighted coefficient series is summable. -/
private theorem DiscSummable.weighted {c : ℕ → ℂ} (hc : DiscSummable c) (j : ℕ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable fun n : ℕ => (n : ℝ) ^ j * ‖c n‖ * ρ ^ n := by
  obtain ⟨ρ', hρρ', hρ'1⟩ := exists_between hρ1
  have hρ'0 : 0 ≤ ρ' := hρ0.trans hρρ'.le
  have hρ'pos : 0 < ρ' := lt_of_le_of_lt hρ0 hρρ'
  have hS : Summable fun n : ℕ => ‖c n‖ * ρ' ^ n := by
    refine (hc ρ' ?_).congr (fun n => ?_)
    · rw [Complex.norm_of_nonneg hρ'0]; exact hρ'1
    · rw [norm_mul, norm_pow, Complex.norm_of_nonneg hρ'0]
  set t : ℝ := ρ / ρ' with ht
  have ht0 : 0 ≤ t := div_nonneg hρ0 hρ'0
  have ht1 : t < 1 := (div_lt_one hρ'pos).2 hρρ'
  have hgeo : Summable fun n : ℕ => (n : ℝ) ^ j * t ^ n := by
    refine (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) j (r := t) ?_).congr
      (fun n => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hbound : ∀ n : ℕ, (n : ℝ) ^ j * t ^ n ≤ ∑' m : ℕ, (m : ℝ) ^ j * t ^ m :=
    fun n => hgeo.le_tsum n (fun m _ => by positivity)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hS.mul_left (∑' m : ℕ, (m : ℝ) ^ j * t ^ m))
  have hval : (n : ℝ) ^ j * ‖c n‖ * ρ ^ n
      = (‖c n‖ * ρ' ^ n) * ((n : ℝ) ^ j * t ^ n) := by
    rw [ht, div_pow]; field_simp
  rw [hval, mul_comm (∑' m : ℕ, (m : ℝ) ^ j * t ^ m)]
  exact mul_le_mul_of_nonneg_left (hbound n) (by positivity)

/-- The shifted (derivative) coefficient sequence is again disc-summable. -/
private theorem DiscSummable.shift {c : ℕ → ℂ} (hc : DiscSummable c) :
    DiscSummable fun n => ((n : ℂ) + 1) * c (n + 1) := by
  intro w hw
  obtain ⟨ρ, hwρ, hρ1⟩ := exists_between hw
  have hρ0 : 0 ≤ ρ := (norm_nonneg w).trans hwρ.le
  have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg w) hwρ
  have hg : Summable fun m : ℕ => (m : ℝ) * ‖c m‖ * ρ ^ m := by
    simpa using hc.weighted 1 hρ0 hρ1
  have hg1 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖c (n + 1)‖ * ρ ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hg
  have hbnd : Summable fun n : ℕ => ((n : ℝ) + 1) * ‖c (n + 1)‖ * ρ ^ n := by
    refine (hg1.mul_left ρ⁻¹).congr (fun n => ?_)
    push_cast; rw [pow_succ]; field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbnd
  rw [norm_mul, norm_mul, norm_pow]
  have h1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [h1]
  gcongr

/-- Term-by-term differentiation: on the open unit disc, the power series `∑ cₙ wⁿ` has derivative
`∑ (n+1) c₍ₙ₊₁₎ zⁿ`. -/
private theorem DiscSummable.hasDerivAt {c : ℕ → ℂ} (hc : DiscSummable c) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, c n * w ^ n)
      (∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n) z := by
  obtain ⟨ρ, hzρ, hρ1⟩ := exists_between hz
  have hρ0 : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
  have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hzρ
  have hzmem : z ∈ Metric.ball (0 : ℂ) ρ := by
    simp only [Metric.mem_ball, dist_zero_right]; exact hzρ
  have hu : Summable fun n : ℕ => (n : ℝ) * ‖c n‖ * ρ ^ (n - 1) := by
    have hw1 : Summable fun n : ℕ => (n : ℝ) * ‖c n‖ * ρ ^ n := by simpa using hc.weighted 1 hρ0 hρ1
    refine (hw1.mul_left ρ⁻¹).congr (fun n => ?_)
    rcases n with _ | k
    · simp
    · rw [Nat.succ_sub_one, pow_succ]; field_simp
  have hgderiv : ∀ n (y : ℂ), y ∈ Metric.ball (0 : ℂ) ρ →
      HasDerivAt (fun w : ℂ => c n * w ^ n) (c n * ((n : ℂ) * y ^ (n - 1))) y :=
    fun n y _ => (hasDerivAt_pow n y).const_mul (c n)
  have hgbound : ∀ n (y : ℂ), y ∈ Metric.ball (0 : ℂ) ρ →
      ‖c n * ((n : ℂ) * y ^ (n - 1))‖ ≤ (n : ℝ) * ‖c n‖ * ρ ^ (n - 1) := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    calc ‖c n * ((n : ℂ) * y ^ (n - 1))‖
        = ‖c n‖ * ((n : ℝ) * ‖y‖ ^ (n - 1)) := by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ ‖c n‖ * ((n : ℝ) * ρ ^ (n - 1)) := by gcongr
      _ = (n : ℝ) * ‖c n‖ * ρ ^ (n - 1) := by ring
  have hg0 : Summable fun n : ℕ => c n * (0 : ℂ) ^ n := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    rw [Finset.mem_singleton] at hn
    rw [zero_pow hn, mul_zero]
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected hgderiv hgbound
    (Metric.mem_ball_self hρpos) hg0 hzmem
  have hh : Summable fun n : ℕ => c n * ((n : ℂ) * z ^ (n - 1)) :=
    Summable.of_norm_bounded hu (fun n => hgbound n z hzmem)
  have hreindex : (∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n)
      = ∑' n : ℕ, c n * ((n : ℂ) * z ^ (n - 1)) := by
    rw [hh.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
    refine tsum_congr (fun n => ?_)
    rw [Nat.add_sub_cancel]; push_cast; ring
  rw [hreindex]
  exact hderiv

/-- Reindexing: `∑ gₙ z^(n+k) = ∑ (aligned coefficient) zᵐ`, where the aligned coefficient is
`g₍ₘ₋ₖ₎` for `m ≥ k` and `0` otherwise. -/
private theorem tsum_pow_shift (g : ℕ → ℂ) (k : ℕ) {z : ℂ}
    (hg : Summable fun n => g n * z ^ (n + k)) :
    ∑' n, g n * z ^ (n + k) = ∑' m, (if k ≤ m then g (m - k) else 0) * z ^ m := by
  set G : ℕ → ℂ := fun m => (if k ≤ m then g (m - k) else 0) * z ^ m with hGdef
  have hGk : ∀ n, G (n + k) = g n * z ^ (n + k) := by
    intro n
    simp only [hGdef, Nat.le_add_left, if_true, Nat.add_sub_cancel]
  have hGsum : Summable G := (summable_nat_add_iff k).1 (hg.congr (fun n => (hGk n).symm))
  have hzero : ∑ i ∈ Finset.range k, G i = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    simp only [hGdef]
    rw [if_neg (by omega), zero_mul]
  have hsplit := hGsum.sum_add_tsum_nat_add k
  rw [hzero, zero_add] at hsplit
  rw [← hsplit]
  exact (tsum_congr hGk).symm

/-! ## The hypergeometric differential equations (paper Thms. `dgl2f1`, `dgl3f2`) -/

/-- The `₂F₁(a, b; c; ·)` coefficients are disc-summable as soon as `c` is not a non-positive
integer (numerator degeneracy in `a`, `b` merely truncates the series). -/
private theorem ordinaryHypergeometric_discSummable (a b c : ℂ) (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    DiscSummable (ordinaryHypergeometricCoefficient a b c) := by
  intro w hw
  by_cases hab : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b
  · have habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -c :=
      fun kn => ⟨(hab kn).1, (hab kn).2, hc kn⟩
    have hrad := ordinaryHypergeometricSeries_radius_eq_one ℂ a b c habc
    have hlt : (‖w‖₊ : ENNReal) < (ordinaryHypergeometricSeries ℂ a b c).radius := by
      rw [hrad]; exact_mod_cast hw
    have hsum := (ordinaryHypergeometricSeries ℂ a b c).summable_norm_mul_pow hlt
    refine hsum.congr (fun n => ?_)
    simp only [ordinaryHypergeometricSeries, ofScalars_norm, norm_mul, norm_pow, coe_nnnorm]
  · push Not at hab
    obtain ⟨kn, hkn⟩ := hab
    have hkn' : (kn : ℂ) = -a ∨ (kn : ℂ) = -b := by
      by_contra hcon
      push Not at hcon
      exact absurd (hkn hcon.1) (by simpa using hcon.2)
    apply summable_of_ne_finset_zero (s := Finset.range (kn + 1))
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hlt : kn < n := hn
    have hc0 : ordinaryHypergeometricCoefficient a b c n = 0 := by
      simp only [ordinaryHypergeometricCoefficient]
      rcases hkn' with hp | hp
      · rw [show (ascPochhammer ℂ n).eval a = 0 by
              rw [show a = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; ring
      · rw [show (ascPochhammer ℂ n).eval b = 0 by
              rw [show b = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; ring
    rw [hc0, zero_mul, norm_zero]

/-- Paper Thm. `dgl2f1`: on the unit disc, `f = ₂F₁(a, b; c; ·)` satisfies the hypergeometric
differential equation `z(z-1)f'' + [(a+b+1)z - c]f' + ab·f = 0`.

The hypothesis `hc` (`c` is not a non-positive integer) is implicit in the paper: without it
Mathlib's junk-value conventions make the series terms vanish for large `n` and the ODE fails. -/
theorem ordinaryHypergeometric_ode (a b c : ℂ) (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    {z : ℂ} (hz : ‖z‖ < 1) :
    z * (z - 1) * deriv (deriv fun w : ℂ => ₂F₁ a b c w) z
      + ((a + b + 1) * z - c) * deriv (fun w : ℂ => ₂F₁ a b c w) z
      + a * b * ₂F₁ a b c z = 0 := by
  -- Coefficient sequences: `C` for `f`, `C1` for `f'`, `C2` for `f''`.
  set C : ℕ → ℂ := ordinaryHypergeometricCoefficient a b c with hCdef
  set C1 : ℕ → ℂ := fun n => ((n : ℂ) + 1) * C (n + 1) with hC1def
  set C2 : ℕ → ℂ := fun n => ((n : ℂ) + 1) * C1 (n + 1) with hC2def
  have hCsum : DiscSummable C := ordinaryHypergeometric_discSummable a b c hc
  have hC1sum : DiscSummable C1 := by rw [hC1def]; exact hCsum.shift
  have hC2sum : DiscSummable C2 := by rw [hC2def]; exact hC1sum.shift
  -- The coefficient recurrence `(m+a)(m+b) Cₘ = (m+1)(m+c) C₍ₘ₊₁₎` (needs only `hc`).
  have hrec : ∀ m : ℕ, ((m : ℂ) + a) * ((m : ℂ) + b) * C m
      = ((m : ℂ) + 1) * ((m : ℂ) + c) * C (m + 1) := by
    intro m
    have hpc : ∀ i : ℕ, (ascPochhammer ℂ i).eval c ≠ 0 := by
      intro i hz0
      rw [ascPochhammer_eval_eq_zero_iff] at hz0
      obtain ⟨k, _, hk⟩ := hz0
      exact hc k (by linear_combination hk)
    have hfac : ((m ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    have hcadd : c + (m : ℂ) ≠ 0 := fun h => hc m (by linear_combination h)
    simp only [hCdef, ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring
  -- The power-series representations of `f`, `f'`, `f''`.
  have hfun : (fun w : ℂ => ₂F₁ a b c w) = fun w => ∑' n : ℕ, C n * w ^ n := by
    funext w
    rw [ordinaryHypergeometric_eq_tsum]
    exact tsum_congr fun n => smul_eq_mul _ _
  have hHD : ∀ w : ℂ, ‖w‖ < 1 →
      HasDerivAt (fun w : ℂ => ₂F₁ a b c w) (∑' n : ℕ, C1 n * w ^ n) w := by
    intro w hw
    have hval : (∑' n : ℕ, C1 n * w ^ n) = ∑' n : ℕ, ((n : ℂ) + 1) * C (n + 1) * w ^ n :=
      tsum_congr fun n => by simp only [hC1def]
    rw [hfun, hval]
    exact hCsum.hasDerivAt hw
  have hf0 : ₂F₁ a b c z = ∑' n : ℕ, C n * z ^ n := congrFun hfun z
  have hd1 : deriv (fun w : ℂ => ₂F₁ a b c w) z = ∑' n : ℕ, C1 n * z ^ n := (hHD z hz).deriv
  have hd2 : deriv (deriv fun w : ℂ => ₂F₁ a b c w) z = ∑' n : ℕ, C2 n * z ^ n := by
    have hev : deriv (fun w : ℂ => ₂F₁ a b c w) =ᶠ[nhds z] fun w => ∑' n : ℕ, C1 n * w ^ n := by
      have hball : Metric.ball (0 : ℂ) 1 ∈ nhds z :=
        Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hz)
      filter_upwards [hball] with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact (hHD w hw).deriv
    rw [hev.deriv_eq]
    have hval2 : (∑' n : ℕ, C2 n * z ^ n) = ∑' n : ℕ, ((n : ℂ) + 1) * C1 (n + 1) * z ^ n :=
      tsum_congr fun n => by simp only [hC2def]
    rw [hval2]
    exact (hC1sum.hasDerivAt hz).deriv
  rw [hd2, hd1, hf0]
  -- Summability of the three coefficient series at `z`.
  have sC : Summable fun n : ℕ => C n * z ^ n := (hCsum z hz).of_norm
  have sC1 : Summable fun n : ℕ => C1 n * z ^ n := (hC1sum z hz).of_norm
  have sC2 : Summable fun n : ℕ => C2 n * z ^ n := (hC2sum z hz).of_norm
  have sShift : ∀ (g : ℕ → ℂ), (Summable fun n => g n * z ^ n) → ∀ k,
      Summable fun n => g n * z ^ (n + k) := by
    intro g hgs k
    refine (hgs.mul_left (z ^ k)).congr (fun n => ?_)
    rw [pow_add]; ring
  have sAlign : ∀ (g : ℕ → ℂ) (k : ℕ), (Summable fun n => g n * z ^ n) →
      Summable fun m => (if k ≤ m then g (m - k) else 0) * z ^ m := by
    intro g k hgs
    apply (summable_nat_add_iff k).1
    refine (sShift g hgs k).congr (fun n => ?_)
    simp only [Nat.le_add_left, if_true, Nat.add_sub_cancel]
  have iA : (∑' n : ℕ, C2 n * z ^ (n + 2)) = z ^ 2 * ∑' n : ℕ, C2 n * z ^ n := by
    rw [← tsum_mul_left]; exact tsum_congr fun n => by rw [pow_add]; ring
  have iB : (∑' n : ℕ, C2 n * z ^ (n + 1)) = z * ∑' n : ℕ, C2 n * z ^ n := by
    rw [← tsum_mul_left]; exact tsum_congr fun n => by rw [pow_add]; ring
  have iC : (∑' n : ℕ, C1 n * z ^ (n + 1)) = z * ∑' n : ℕ, C1 n * z ^ n := by
    rw [← tsum_mul_left]; exact tsum_congr fun n => by rw [pow_add]; ring
  have shiftA := tsum_pow_shift C2 2 (sShift C2 sC2 2)
  have shiftB := tsum_pow_shift C2 1 (sShift C2 sC2 1)
  have shiftC := tsum_pow_shift C1 1 (sShift C1 sC1 1)
  have s2a := sAlign C2 2 sC2
  have s2b := sAlign C2 1 sC2
  have s1c := sAlign C1 1 sC1
  -- The key coefficient identity: the aligned coefficient of `zᵐ` vanishes.
  have hKzero : ∀ m : ℕ,
      (if 2 ≤ m then C2 (m - 2) else 0) - (if 1 ≤ m then C2 (m - 1) else 0)
        + (a + b + 1) * (if 1 ≤ m then C1 (m - 1) else 0) - c * C1 m + a * b * C m = 0 := by
    intro m
    rcases m with _ | _ | k
    · simp only [show ¬ (2 ≤ 0) by omega, show ¬ (1 ≤ 0) by omega, if_false, mul_zero, hC1def]
      have r := hrec 0; push_cast at r ⊢; linear_combination r
    · simp only [show ¬ (2 ≤ 1) by omega, show (1 ≤ 1) by omega, if_true, if_false,
        Nat.sub_self, hC2def, hC1def]
      have r := hrec 1; push_cast at r ⊢; linear_combination r
    · simp only [show 2 ≤ k + 1 + 1 by omega, show 1 ≤ k + 1 + 1 by omega, if_true,
        show k + 1 + 1 - 2 = k by omega, show k + 1 + 1 - 1 = k + 1 by omega, hC2def, hC1def]
      have r := hrec (k + 2); push_cast at r ⊢; linear_combination r
  -- Collect the differential-equation coefficients into a single (vanishing) series.
  rw [show z * (z - 1) * (∑' n : ℕ, C2 n * z ^ n)
        = (∑' m : ℕ, (if 2 ≤ m then C2 (m - 2) else 0) * z ^ m)
          - (∑' m : ℕ, (if 1 ≤ m then C2 (m - 1) else 0) * z ^ m)
      from by rw [← shiftA, ← shiftB, iA, iB]; ring,
    show ((a + b + 1) * z - c) * (∑' n : ℕ, C1 n * z ^ n)
        = (a + b + 1) * (∑' m : ℕ, (if 1 ≤ m then C1 (m - 1) else 0) * z ^ m)
          - c * (∑' n : ℕ, C1 n * z ^ n)
      from by rw [← shiftC, iC]; ring,
    show a * b * (∑' n : ℕ, C n * z ^ n) = ∑' n : ℕ, a * b * (C n * z ^ n)
      from (tsum_mul_left).symm,
    show c * (∑' n : ℕ, C1 n * z ^ n) = ∑' n : ℕ, c * (C1 n * z ^ n) from (tsum_mul_left).symm,
    show (a + b + 1) * (∑' m : ℕ, (if 1 ≤ m then C1 (m - 1) else 0) * z ^ m)
        = ∑' m : ℕ, (a + b + 1) * ((if 1 ≤ m then C1 (m - 1) else 0) * z ^ m)
      from (tsum_mul_left).symm,
    ← s2a.tsum_sub s2b, ← (s1c.mul_left (a + b + 1)).tsum_sub (sC1.mul_left c),
    ← (s2a.sub s2b).tsum_add ((s1c.mul_left (a + b + 1)).sub (sC1.mul_left c)),
    ← ((s2a.sub s2b).add ((s1c.mul_left (a + b + 1)).sub (sC1.mul_left c))).tsum_add
      (sC.mul_left (a * b))]
  refine (tsum_congr fun m => ?_).trans tsum_zero
  linear_combination (z ^ m) * hKzero m

/-- The `₃F₂` coefficients are disc-summable for all parameters (numerator/denominator degeneracy
merely truncates the series). -/
private theorem generalizedHypergeometric_discSummable (α β γ δ ε : ℂ) :
    DiscSummable (generalizedHypergeometricCoefficient α β γ δ ε) := by
  intro w hw
  by_cases hnz : ∀ kn : ℕ, (kn : ℂ) ≠ -α ∧ (kn : ℂ) ≠ -β ∧ (kn : ℂ) ≠ -γ ∧ (kn : ℂ) ≠ -δ ∧
      (kn : ℂ) ≠ -ε
  · have hrad := generalizedHypergeometricSeries_radius_eq_one ℂ α β γ δ ε hnz
    have hlt : (‖w‖₊ : ENNReal) < (generalizedHypergeometricSeries ℂ α β γ δ ε).radius := by
      rw [hrad]; exact_mod_cast hw
    have hsum := (generalizedHypergeometricSeries ℂ α β γ δ ε).summable_norm_mul_pow hlt
    refine hsum.congr (fun n => ?_)
    simp only [generalizedHypergeometricSeries, ofScalars_norm, norm_mul, norm_pow, coe_nnnorm]
  · rw [not_forall] at hnz
    obtain ⟨kn, hkn⟩ := hnz
    have hkn' : (kn : ℂ) = -α ∨ (kn : ℂ) = -β ∨ (kn : ℂ) = -γ ∨ (kn : ℂ) = -δ ∨ (kn : ℂ) = -ε := by
      by_contra hc
      push Not at hc
      exact hkn ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
    apply summable_of_ne_finset_zero (s := Finset.range (kn + 1))
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hlt : kn < n := hn
    have hc0 : generalizedHypergeometricCoefficient α β γ δ ε n = 0 := by
      simp only [generalizedHypergeometricCoefficient]
      rcases hkn' with hp | hp | hp | hp | hp
      all_goals
        first
        | (rw [show (ascPochhammer ℂ n).eval α = 0 by
              rw [show α = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; ring)
        | (rw [show (ascPochhammer ℂ n).eval β = 0 by
              rw [show β = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; ring)
        | (rw [show (ascPochhammer ℂ n).eval γ = 0 by
              rw [show γ = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; ring)
        | (rw [show (ascPochhammer ℂ n).eval δ = 0 by
              rw [show δ = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; simp)
        | (rw [show (ascPochhammer ℂ n).eval ε = 0 by
              rw [show ε = -(kn : ℂ) by linear_combination hp]
              exact ascPochhammer_eval_neg_coe_nat_of_lt hlt]; simp)
    rw [hc0, zero_mul, norm_zero]

/-- Paper Thm. `dgl3f2`: on the unit disc, `g = ₃F₂(α, β, γ; δ, ε; ·)` satisfies the third-order
differential equation
`(z³-z²)g''' + [(α+β+γ+3)z² - (δ+ε+1)z]g'' + [(1+α+β+γ+αβ+αγ+βγ)z - δε]g' + αβγ·g = 0`.

The hypotheses `hδ`, `hε` are implicit in the paper (cf. `ordinaryHypergeometric_ode`). -/
theorem generalizedHypergeometric_ode (α β γ δ ε : ℂ)
    (hδ : ∀ k : ℕ, (k : ℂ) ≠ -δ) (hε : ∀ k : ℕ, (k : ℂ) ≠ -ε)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (z ^ 3 - z ^ 2) * deriv (deriv (deriv fun w : ℂ => ₃F₂ α β γ δ ε w)) z
      + ((α + β + γ + 3) * z ^ 2 - (δ + ε + 1) * z)
        * deriv (deriv fun w : ℂ => ₃F₂ α β γ δ ε w) z
      + ((α * β + α * γ + β * γ + α + β + γ + 1) * z - δ * ε)
        * deriv (fun w : ℂ => ₃F₂ α β γ δ ε w) z
      + α * β * γ * ₃F₂ α β γ δ ε z = 0 := by
  set D : ℕ → ℂ := generalizedHypergeometricCoefficient α β γ δ ε with hDdef
  set D1 : ℕ → ℂ := fun n => ((n : ℂ) + 1) * D (n + 1) with hD1def
  set D2 : ℕ → ℂ := fun n => ((n : ℂ) + 1) * D1 (n + 1) with hD2def
  set D3 : ℕ → ℂ := fun n => ((n : ℂ) + 1) * D2 (n + 1) with hD3def
  have hDsum : DiscSummable D := generalizedHypergeometric_discSummable α β γ δ ε
  have hD1sum : DiscSummable D1 := by rw [hD1def]; exact hDsum.shift
  have hD2sum : DiscSummable D2 := by rw [hD2def]; exact hD1sum.shift
  have hD3sum : DiscSummable D3 := by rw [hD3def]; exact hD2sum.shift
  -- Coefficient recurrence `(m+α)(m+β)(m+γ) Dₘ = (m+1)(m+δ)(m+ε) D₍ₘ₊₁₎` (needs `hδ`, `hε`).
  have hrec3 : ∀ m : ℕ, ((m : ℂ) + α) * ((m : ℂ) + β) * ((m : ℂ) + γ) * D m
      = ((m : ℂ) + 1) * ((m : ℂ) + δ) * ((m : ℂ) + ε) * D (m + 1) := by
    intro m
    have hpd : ∀ i : ℕ, (ascPochhammer ℂ i).eval δ ≠ 0 := fun i hz0 => by
      rw [ascPochhammer_eval_eq_zero_iff] at hz0
      obtain ⟨k, _, hk⟩ := hz0; exact hδ k (by linear_combination hk)
    have hpe : ∀ i : ℕ, (ascPochhammer ℂ i).eval ε ≠ 0 := fun i hz0 => by
      rw [ascPochhammer_eval_eq_zero_iff] at hz0
      obtain ⟨k, _, hk⟩ := hz0; exact hε k (by linear_combination hk)
    have hfac : ((m ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    have hdadd : δ + (m : ℂ) ≠ 0 := fun h => hδ m (by linear_combination h)
    have headd : ε + (m : ℂ) ≠ 0 := fun h => hε m (by linear_combination h)
    simp only [hDdef, generalizedHypergeometricCoefficient, ascPochhammer_succ_eval,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring
  -- Power-series representations of `g` and its derivatives.
  have hfun : (fun w : ℂ => ₃F₂ α β γ δ ε w) = fun w => ∑' n : ℕ, D n * w ^ n := by
    funext w
    rw [generalizedHypergeometric_eq_tsum]
    exact tsum_congr fun n => smul_eq_mul _ _
  have hHD1 : ∀ w : ℂ, ‖w‖ < 1 →
      HasDerivAt (fun w : ℂ => ₃F₂ α β γ δ ε w) (∑' n : ℕ, D1 n * w ^ n) w := by
    intro w hw
    have hval : (∑' n : ℕ, D1 n * w ^ n) = ∑' n : ℕ, ((n : ℂ) + 1) * D (n + 1) * w ^ n :=
      tsum_congr fun n => by simp only [hD1def]
    rw [hfun, hval]
    exact hDsum.hasDerivAt hw
  have D1eq : ∀ w : ℂ, ‖w‖ < 1 → deriv (fun w : ℂ => ₃F₂ α β γ δ ε w) w = ∑' n : ℕ, D1 n * w ^ n :=
    fun w hw => (hHD1 w hw).deriv
  have hnbhd : ∀ w : ℂ, ‖w‖ < 1 → Metric.ball (0 : ℂ) 1 ∈ nhds w := fun w hw =>
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hw)
  have D2eq : ∀ w : ℂ, ‖w‖ < 1 →
      deriv (deriv fun w : ℂ => ₃F₂ α β γ δ ε w) w = ∑' n : ℕ, D2 n * w ^ n := by
    intro w hw
    have hev : deriv (fun w : ℂ => ₃F₂ α β γ δ ε w) =ᶠ[nhds w] fun u => ∑' n : ℕ, D1 n * u ^ n := by
      filter_upwards [hnbhd w hw] with u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      exact D1eq u hu
    rw [hev.deriv_eq,
      show (∑' n : ℕ, D2 n * w ^ n) = ∑' n : ℕ, ((n : ℂ) + 1) * D1 (n + 1) * w ^ n from
        tsum_congr fun n => by simp only [hD2def]]
    exact (hD1sum.hasDerivAt hw).deriv
  have D3eq : ∀ w : ℂ, ‖w‖ < 1 →
      deriv (deriv (deriv fun w : ℂ => ₃F₂ α β γ δ ε w)) w = ∑' n : ℕ, D3 n * w ^ n := by
    intro w hw
    have hev : deriv (deriv fun w : ℂ => ₃F₂ α β γ δ ε w)
        =ᶠ[nhds w] fun u => ∑' n : ℕ, D2 n * u ^ n := by
      filter_upwards [hnbhd w hw] with u hu
      rw [Metric.mem_ball, dist_zero_right] at hu
      exact D2eq u hu
    rw [hev.deriv_eq,
      show (∑' n : ℕ, D3 n * w ^ n) = ∑' n : ℕ, ((n : ℂ) + 1) * D2 (n + 1) * w ^ n from
        tsum_congr fun n => by simp only [hD3def]]
    exact (hD2sum.hasDerivAt hw).deriv
  rw [D3eq z hz, D2eq z hz, D1eq z hz, congrFun hfun z]
  -- Summabilities at `z`.
  have sD : Summable fun n : ℕ => D n * z ^ n := (hDsum z hz).of_norm
  have sD1 : Summable fun n : ℕ => D1 n * z ^ n := (hD1sum z hz).of_norm
  have sD2 : Summable fun n : ℕ => D2 n * z ^ n := (hD2sum z hz).of_norm
  have sD3 : Summable fun n : ℕ => D3 n * z ^ n := (hD3sum z hz).of_norm
  have sShift : ∀ (g : ℕ → ℂ), (Summable fun n => g n * z ^ n) → ∀ k,
      Summable fun n => g n * z ^ (n + k) := by
    intro g hgs k
    refine (hgs.mul_left (z ^ k)).congr (fun n => ?_)
    rw [pow_add]; ring
  have sAlign : ∀ (g : ℕ → ℂ) (k : ℕ), (Summable fun n => g n * z ^ n) →
      Summable fun m => (if k ≤ m then g (m - k) else 0) * z ^ m := by
    intro g k hgs
    apply (summable_nat_add_iff k).1
    refine (sShift g hgs k).congr (fun n => ?_)
    simp only [Nat.le_add_left, if_true, Nat.add_sub_cancel]
  have iSh : ∀ (g : ℕ → ℂ) (k : ℕ), (∑' n : ℕ, g n * z ^ (n + k)) = z ^ k * ∑' n : ℕ, g n * z ^ n :=
    fun g k => by rw [← tsum_mul_left]; exact tsum_congr fun n => by rw [pow_add]; ring
  have shift3A := tsum_pow_shift D3 3 (sShift D3 sD3 3)
  have shift3B := tsum_pow_shift D3 2 (sShift D3 sD3 2)
  have shiftD2_2 := tsum_pow_shift D2 2 (sShift D2 sD2 2)
  have shiftD2_1 := tsum_pow_shift D2 1 (sShift D2 sD2 1)
  have shiftD1_1 := tsum_pow_shift D1 1 (sShift D1 sD1 1)
  have s1 := sAlign D3 3 sD3
  have s2 := sAlign D3 2 sD3
  have s3 := (sAlign D2 2 sD2).mul_left (α + β + γ + 3)
  have s4 := (sAlign D2 1 sD2).mul_left (δ + ε + 1)
  have s5 := (sAlign D1 1 sD1).mul_left (α * β + α * γ + β * γ + α + β + γ + 1)
  have s6 := sD1.mul_left (δ * ε)
  have s7 := sD.mul_left (α * β * γ)
  -- The aligned coefficient of `zᵐ` vanishes.
  have hKzero3 : ∀ m : ℕ,
      (if 3 ≤ m then D3 (m - 3) else 0) - (if 2 ≤ m then D3 (m - 2) else 0)
        + (α + β + γ + 3) * (if 2 ≤ m then D2 (m - 2) else 0)
        - (δ + ε + 1) * (if 1 ≤ m then D2 (m - 1) else 0)
        + (α * β + α * γ + β * γ + α + β + γ + 1) * (if 1 ≤ m then D1 (m - 1) else 0)
        - δ * ε * D1 m + α * β * γ * D m = 0 := by
    intro m
    rcases m with _ | _ | _ | k
    · simp only [show ¬ (3 ≤ 0) by omega, show ¬ (2 ≤ 0) by omega, show ¬ (1 ≤ 0) by omega,
        if_false, mul_zero, hD1def]
      have r := hrec3 0; push_cast at r ⊢; linear_combination r
    · simp only [show ¬ (3 ≤ 1) by omega, show ¬ (2 ≤ 1) by omega, show (1 ≤ 1) by omega,
        if_true, if_false, mul_zero, Nat.sub_self, hD2def, hD1def]
      have r := hrec3 1; push_cast at r ⊢; linear_combination r
    · simp only [show ¬ (3 ≤ 2) by omega, show (2 ≤ 2) by omega, show (1 ≤ 2) by omega,
        if_true, if_false, Nat.sub_self, show (2 : ℕ) - 1 = 1 by omega, hD3def, hD2def, hD1def]
      have r := hrec3 2; push_cast at r ⊢; linear_combination r
    · simp only [show 3 ≤ k + 1 + 1 + 1 by omega, show 2 ≤ k + 1 + 1 + 1 by omega,
        show 1 ≤ k + 1 + 1 + 1 by omega, if_true,
        show k + 1 + 1 + 1 - 3 = k by omega, show k + 1 + 1 + 1 - 2 = k + 1 by omega,
        show k + 1 + 1 + 1 - 1 = k + 1 + 1 by omega, hD3def, hD2def, hD1def]
      have r := hrec3 (k + 3); push_cast at r ⊢; linear_combination r
  rw [show (z ^ 3 - z ^ 2) * (∑' n : ℕ, D3 n * z ^ n)
        = (∑' m : ℕ, (if 3 ≤ m then D3 (m - 3) else 0) * z ^ m)
          - (∑' m : ℕ, (if 2 ≤ m then D3 (m - 2) else 0) * z ^ m)
      from by rw [← shift3A, ← shift3B, iSh D3 3, iSh D3 2]; ring,
    show ((α + β + γ + 3) * z ^ 2 - (δ + ε + 1) * z) * (∑' n : ℕ, D2 n * z ^ n)
        = (α + β + γ + 3) * (∑' m : ℕ, (if 2 ≤ m then D2 (m - 2) else 0) * z ^ m)
          - (δ + ε + 1) * (∑' m : ℕ, (if 1 ≤ m then D2 (m - 1) else 0) * z ^ m)
      from by rw [← shiftD2_2, ← shiftD2_1, iSh D2 2, iSh D2 1]; ring,
    show ((α * β + α * γ + β * γ + α + β + γ + 1) * z - δ * ε) * (∑' n : ℕ, D1 n * z ^ n)
        = (α * β + α * γ + β * γ + α + β + γ + 1)
            * (∑' m : ℕ, (if 1 ≤ m then D1 (m - 1) else 0) * z ^ m)
          - δ * ε * (∑' n : ℕ, D1 n * z ^ n)
      from by rw [← shiftD1_1, iSh D1 1]; ring,
    show α * β * γ * (∑' n : ℕ, D n * z ^ n) = ∑' n : ℕ, α * β * γ * (D n * z ^ n)
      from (tsum_mul_left).symm,
    show δ * ε * (∑' n : ℕ, D1 n * z ^ n) = ∑' n : ℕ, δ * ε * (D1 n * z ^ n)
      from (tsum_mul_left).symm,
    show (α + β + γ + 3) * (∑' m : ℕ, (if 2 ≤ m then D2 (m - 2) else 0) * z ^ m)
        = ∑' m : ℕ, (α + β + γ + 3) * ((if 2 ≤ m then D2 (m - 2) else 0) * z ^ m)
      from (tsum_mul_left).symm,
    show (δ + ε + 1) * (∑' m : ℕ, (if 1 ≤ m then D2 (m - 1) else 0) * z ^ m)
        = ∑' m : ℕ, (δ + ε + 1) * ((if 1 ≤ m then D2 (m - 1) else 0) * z ^ m)
      from (tsum_mul_left).symm,
    show (α * β + α * γ + β * γ + α + β + γ + 1)
          * (∑' m : ℕ, (if 1 ≤ m then D1 (m - 1) else 0) * z ^ m)
        = ∑' m : ℕ, (α * β + α * γ + β * γ + α + β + γ + 1)
            * ((if 1 ≤ m then D1 (m - 1) else 0) * z ^ m)
      from (tsum_mul_left).symm,
    ← s1.tsum_sub s2, ← s3.tsum_sub s4, ← s5.tsum_sub s6,
    ← (s1.sub s2).tsum_add (s3.sub s4),
    ← ((s1.sub s2).add (s3.sub s4)).tsum_add (s5.sub s6),
    ← (((s1.sub s2).add (s3.sub s4)).add (s5.sub s6)).tsum_add s7]
  refine (tsum_congr fun m => ?_).trans tsum_zero
  linear_combination (z ^ m) * hKzero3 m

/-! ## Clausen's formula (paper Thm. `satzclausen`) -/

/-- The `₂F₁` coefficient recurrence `(m+a)(m+b) cₘ = (m+1)(m+c) c₍ₘ₊₁₎`
(needs `c` non-degenerate). -/
private theorem ordinaryHypergeometric_coeff_rec (a b c : ℂ) (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) (m : ℕ) :
    ((m : ℂ) + a) * ((m : ℂ) + b) * ordinaryHypergeometricCoefficient a b c m
      = ((m : ℂ) + 1) * ((m : ℂ) + c) * ordinaryHypergeometricCoefficient a b c (m + 1) := by
  have hpc : ∀ i : ℕ, (ascPochhammer ℂ i).eval c ≠ 0 := fun i hz0 => by
    rw [ascPochhammer_eval_eq_zero_iff] at hz0
    obtain ⟨k, _, hk⟩ := hz0; exact hc k (by linear_combination hk)
  have hfac : ((m ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have hcadd : c + (m : ℂ) ≠ 0 := fun h => hc m (by linear_combination h)
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

/-- The `₃F₂` coefficient recurrence `(m+α)(m+β)(m+γ) dₘ = (m+1)(m+δ)(m+ε) d₍ₘ₊₁₎`
(needs `δ`, `ε` non-degenerate). -/
private theorem generalizedHypergeometric_coeff_rec (α β γ δ ε : ℂ)
    (hδ : ∀ k : ℕ, (k : ℂ) ≠ -δ) (hε : ∀ k : ℕ, (k : ℂ) ≠ -ε) (m : ℕ) :
    ((m : ℂ) + α) * ((m : ℂ) + β) * ((m : ℂ) + γ) *
        generalizedHypergeometricCoefficient α β γ δ ε m
      = ((m : ℂ) + 1) * ((m : ℂ) + δ) * ((m : ℂ) + ε) *
        generalizedHypergeometricCoefficient α β γ δ ε (m + 1) := by
  have hpd : ∀ i : ℕ, (ascPochhammer ℂ i).eval δ ≠ 0 := fun i hz0 => by
    rw [ascPochhammer_eval_eq_zero_iff] at hz0
    obtain ⟨k, _, hk⟩ := hz0; exact hδ k (by linear_combination hk)
  have hpe : ∀ i : ℕ, (ascPochhammer ℂ i).eval ε ≠ 0 := fun i hz0 => by
    rw [ascPochhammer_eval_eq_zero_iff] at hz0
    obtain ⟨k, _, hk⟩ := hz0; exact hε k (by linear_combination hk)
  have hfac : ((m ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have hdadd : δ + (m : ℂ) ≠ 0 := fun h => hδ m (by linear_combination h)
  have headd : ε + (m : ℂ) ≠ 0 := fun h => hε m (by linear_combination h)
  simp only [generalizedHypergeometricCoefficient, ascPochhammer_succ_eval, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

/-- The general Clausen coefficient identity: the `n`-th Cauchy-product coefficient of
`(₂F₁(a, b; a+b+1/2; ·))²` equals the `n`-th coefficient of `₃F₂(2a, 2b, a+b; 2a+2b, a+b+1/2; ·)`.
Proved by a creative-telescoping (WZ) recurrence with the certificate
`gₙ(k) = -k(2a+2b+2k-1)(2a+2b-2k+3n+2)/2 · cₖ c₍ₙ₊₁₋ₖ₎`; both sides satisfy
`(n+1)(n+2a+2b)(n+a+b+1/2) xₙ₊₁ = (n+2a)(n+2b)(n+a+b) xₙ` with initial value `1`. -/
private theorem clausen_coeff_general (a b : ℂ)
    (h₁ : ∀ k : ℕ, (k : ℂ) ≠ -(a + b + 1 / 2)) (h₂ : ∀ k : ℕ, (k : ℂ) ≠ -(2 * a + 2 * b))
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) k *
          ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) (n - k)
      = generalizedHypergeometricCoefficient (2 * a) (2 * b) (a + b) (2 * a + 2 * b)
          (a + b + 1 / 2) n := by
  set C : ℕ → ℂ := ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) with hCdef
  set D : ℕ → ℂ :=
    generalizedHypergeometricCoefficient (2 * a) (2 * b) (a + b) (2 * a + 2 * b) (a + b + 1 / 2)
    with hDdef
  set A : ℕ → ℂ :=
    fun m => ((m : ℂ) + 1) * ((m : ℂ) + (2 * a + 2 * b)) * ((m : ℂ) + (a + b + 1 / 2))
    with hAdef
  set B : ℕ → ℂ := fun m => ((m : ℂ) + 2 * a) * ((m : ℂ) + 2 * b) * ((m : ℂ) + (a + b)) with hBdef
  set g : ℕ → ℕ → ℂ :=
    fun m k => (-(k : ℂ) * (2 * a + 2 * b + 2 * (k : ℂ) - 1)
      * (2 * a + 2 * b - 2 * (k : ℂ) + 3 * (m : ℂ) + 2) / 2) * C k * C (m + 1 - k) with hgdef
  set E : ℕ → ℂ := fun m => ∑ k ∈ Finset.range (m + 1), C k * C (m - k) with hEdef
  have C0 : C 0 = 1 := by simp [hCdef, ordinaryHypergeometricCoefficient, ascPochhammer_zero]
  have D0 : D 0 = 1 := by simp [hDdef, generalizedHypergeometricCoefficient, ascPochhammer_zero]
  have cc_rec : ∀ k : ℕ,
      ((k : ℂ) + 1) * ((k : ℂ) + (a + b + 1 / 2)) * C (k + 1)
        = ((k : ℂ) + a) * ((k : ℂ) + b) * C k :=
    fun k => (ordinaryHypergeometric_coeff_rec a b (a + b + 1 / 2) h₁ k).symm
  have dd_rec : ∀ m : ℕ, B m * D m = A m * D (m + 1) := by
    intro m
    simp only [hBdef, hAdef, hDdef]
    exact generalizedHypergeometric_coeff_rec (2 * a) (2 * b) (a + b) (2 * a + 2 * b)
      (a + b + 1 / 2) h₂ h₁ m
  have per_term : ∀ (nn k : ℕ), k ≤ nn →
      A nn * (C k * C (nn + 1 - k)) - B nn * (C k * C (nn - k)) = g nn (k + 1) - g nn k := by
    intro nn k hk
    obtain ⟨m, rfl⟩ : ∃ m, nn = k + m := ⟨nn - k, by omega⟩
    have e1 : k + m + 1 - k = m + 1 := by omega
    have e2 : k + m - k = m := by omega
    have e3 : k + m + 1 - (k + 1) = m := by omega
    simp only [hgdef, hAdef, hBdef, e1, e2, e3]
    push_cast
    linear_combination
      ((2 * a + 2 * b + (k : ℂ) + 3 * (m : ℂ)) * C m) * cc_rec k
        + ((2 * a + 2 * b + 3 * (k : ℂ) + (m : ℂ)) * C k) * cc_rec m
  have gg_zero : ∀ nn : ℕ, g nn 0 = 0 := by intro nn; simp [hgdef]
  have gg_top : ∀ nn : ℕ, g nn (nn + 1) = -(A nn) * C (nn + 1) := by
    intro nn
    simp only [hgdef, hAdef, show nn + 1 - (nn + 1) = 0 by omega, C0, mul_one]
    push_cast
    ring
  have ee_rec : ∀ nn : ℕ, A nn * E (nn + 1) = B nn * E nn := by
    intro nn
    have tele : ∑ k ∈ Finset.range (nn + 1), (g nn (k + 1) - g nn k) = g nn (nn + 1) - g nn 0 :=
      Finset.sum_range_sub (g nn) (nn + 1)
    have key : ∑ k ∈ Finset.range (nn + 1),
        (A nn * (C k * C (nn + 1 - k)) - B nn * (C k * C (nn - k))) = g nn (nn + 1) - g nn 0 := by
      rw [← tele]
      exact Finset.sum_congr rfl fun k hk =>
        per_term nn k (by rw [Finset.mem_range, Nat.lt_succ_iff] at hk; exact hk)
    rw [Finset.sum_sub_distrib] at key
    have hmul1 : ∑ k ∈ Finset.range (nn + 1), A nn * (C k * C (nn + 1 - k))
        = A nn * ∑ k ∈ Finset.range (nn + 1), C k * C (nn + 1 - k) := by rw [Finset.mul_sum]
    have hmul2 : ∑ k ∈ Finset.range (nn + 1), B nn * (C k * C (nn - k))
        = B nn * ∑ k ∈ Finset.range (nn + 1), C k * C (nn - k) := by rw [Finset.mul_sum]
    rw [hmul1, hmul2, gg_zero, gg_top] at key
    have hee1 : (∑ k ∈ Finset.range (nn + 1), C k * C (nn + 1 - k)) = E (nn + 1) - C (nn + 1) := by
      have h : E (nn + 1) = (∑ k ∈ Finset.range (nn + 1), C k * C (nn + 1 - k)) + C (nn + 1) := by
        simp only [hEdef]
        rw [Finset.sum_range_succ, show nn + 1 - (nn + 1) = 0 by omega, C0, mul_one]
      rw [h]; ring
    have hee2 : (∑ k ∈ Finset.range (nn + 1), C k * C (nn - k)) = E nn := rfl
    rw [hee1, hee2] at key
    linear_combination key
  have ee0 : E 0 = 1 := by simp [hEdef, C0]
  have hAne : ∀ nn : ℕ, A nn ≠ 0 := by
    intro nn
    simp only [hAdef]
    exact mul_ne_zero (mul_ne_zero (Nat.cast_add_one_ne_zero nn)
      (fun h => h₂ nn (by linear_combination h))) (fun h => h₁ nn (by linear_combination h))
  have ee_eq_dd : ∀ nn : ℕ, E nn = D nn := by
    intro nn
    induction nn with
    | zero => rw [ee0, D0]
    | succ nn ih =>
      have h1 := ee_rec nn
      have h2 := dd_rec nn
      rw [ih] at h1
      exact mul_left_cancel₀ (hAne nn) (h1.trans h2)
  exact ee_eq_dd n

/-- **Clausen's formula** (paper Thm. `satzclausen`, Clausen 1828): for `‖z‖ < 1`,
`(₂F₁(a, b; a+b+1/2; z))² = ₃F₂(2a, 2b, a+b; 2a+2b, a+b+1/2; z)`.

The non-degeneracy hypotheses `h₁`, `h₂` on the lower parameters are implicit in the paper
(they hold in the only instance used, `a = 1/12`, `b = 5/12`). -/
theorem clausen_formula (a b : ℂ)
    (h₁ : ∀ k : ℕ, (k : ℂ) ≠ -(a + b + 1 / 2)) (h₂ : ∀ k : ℕ, (k : ℂ) ≠ -(2 * a + 2 * b))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a b (a + b + 1 / 2) z ^ 2
      = ₃F₂ (2 * a) (2 * b) (a + b) (2 * a + 2 * b) (a + b + 1 / 2) z := by
  have hfsum : Summable fun n : ℕ =>
      ‖ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) n * z ^ n‖ :=
    ordinaryHypergeometric_discSummable a b (a + b + 1 / 2) h₁ z hz
  have hL : ₂F₁ a b (a + b + 1 / 2) z
      = ∑' n : ℕ, ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) n * z ^ n := by
    rw [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq]
    exact tsum_congr fun n => smul_eq_mul _ _
  have hR : ₃F₂ (2 * a) (2 * b) (a + b) (2 * a + 2 * b) (a + b + 1 / 2) z
      = ∑' n : ℕ, generalizedHypergeometricCoefficient (2 * a) (2 * b) (a + b) (2 * a + 2 * b)
          (a + b + 1 / 2) n * z ^ n := by
    rw [generalizedHypergeometric, generalizedHypergeometric_sum_eq]
    exact tsum_congr fun n => smul_eq_mul _ _
  rw [sq, hL, hR, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfsum hfsum]
  refine tsum_congr fun n => ?_
  have hz_pow : ∀ k ∈ Finset.range (n + 1),
      ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) k * z ^ k *
        (ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) (n - k) * z ^ (n - k))
        = ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) k *
          ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) (n - k) * z ^ n := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hpow : z ^ k * z ^ (n - k) = z ^ n := by rw [← pow_add, Nat.add_sub_cancel' hk]
    linear_combination (ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) k *
      ordinaryHypergeometricCoefficient a b (a + b + 1 / 2) (n - k)) * hpow
  rw [Finset.sum_congr rfl hz_pow, ← Finset.sum_mul, clausen_coeff_general a b h₁ h₂ n]

/-- Evaluating an ascending Pochhammer polynomial at a rational point commutes with the
`ℚ → ℂ` coercion. -/
theorem ascPochhammer_eval_ratCast (n : ℕ) (q : ℚ) :
    (((ascPochhammer ℚ n).eval q : ℚ) : ℂ) = (ascPochhammer ℂ n).eval (q : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    push_cast [ih]
    ring

/-- The `₂F₁` coefficient commutes with the `ℚ → ℂ` coercion. -/
theorem ordinaryHypergeometricCoefficient_ratCast (a b c : ℚ) (n : ℕ) :
    ((ordinaryHypergeometricCoefficient a b c n : ℚ) : ℂ) =
      ordinaryHypergeometricCoefficient (a : ℂ) (b : ℂ) (c : ℂ) n := by
  simp only [ordinaryHypergeometricCoefficient, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast,
    ascPochhammer_eval_ratCast]

/-- The `₃F₂` coefficient commutes with the `ℚ → ℂ` coercion. -/
theorem generalizedHypergeometricCoefficient_ratCast (α β γ δ ε : ℚ) (n : ℕ) :
    ((generalizedHypergeometricCoefficient α β γ δ ε n : ℚ) : ℂ) =
      generalizedHypergeometricCoefficient (α : ℂ) (β : ℂ) (γ : ℂ) (δ : ℂ) (ε : ℂ) n := by
  simp only [generalizedHypergeometricCoefficient, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast,
    ascPochhammer_eval_ratCast]

/-- If none of `a, b, c` is a non-positive integer, the `₂F₁` series is absolutely convergent
for `‖z‖ < 1` (norm-summable coefficients). Mirrors `generalizedHypergeometric_summable`. -/
theorem ordinaryHypergeometric_norm_summable (a b c : ℂ)
    (h : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -c) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖ordinaryHypergeometricCoefficient a b c n * z ^ n‖ := by
  have hrad := ordinaryHypergeometricSeries_radius_eq_one ℂ a b c h
  have hlt : (‖z‖₊ : ENNReal) < (ordinaryHypergeometricSeries ℂ a b c).radius := by
    rw [hrad]; exact_mod_cast hz
  have hsum := (ordinaryHypergeometricSeries ℂ a b c).summable_norm_mul_pow hlt
  refine hsum.congr (fun n => ?_)
  simp only [ordinaryHypergeometricSeries, ofScalars_norm, norm_mul, norm_pow, coe_nnnorm]

namespace Chudnovsky

/-! ## The specific instances used in the paper -/

/-- The hypergeometric function `₂F₁(1/12, 5/12; 1; z)` (paper Thms. `darst`, `omegastrich`). -/
def hyp2F1 (z : ℂ) : ℂ := ₂F₁ (1 / 12 : ℂ) (5 / 12) 1 z

/-- The generalized hypergeometric function `₃F₂(1/6, 5/6, 1/2; 1, 1; z)`, the right-hand side
of Clausen's formula at `a = 1/12`, `b = 5/12` (paper Thm. `satzclausen`). -/
def hyp3F2 (z : ℂ) : ℂ := ₃F₂ (1 / 6 : ℂ) (5 / 6) (1 / 2) 1 1 z

/-! ### Proof of the Clausen coefficient identity by a WZ/creative-telescoping recurrence

Writing `cₖ = (1/12)ₖ(5/12)ₖ/(k!)²` and `dₙ = (1/6)ₙ(5/6)ₙ(1/2)ₙ/(n!)³`, we show
`eₙ := ∑_{k=0}^n cₖ c_{n-k}` equals `dₙ` by proving both satisfy the same first-order recurrence
`(n+1)³ · x_{n+1} = (n+1/6)(n+1/2)(n+5/6) · xₙ`.

The recurrence for `eₙ` is a creative-telescoping identity: with the WZ certificate
`gₙ(k) := k²(2k-3n-3) cₖ c_{n+1-k}` one has, for `k ≤ n`,
`(n+1)³ cₖ c_{n+1-k} - (n+1/6)(n+1/2)(n+5/6) cₖ c_{n-k} = gₙ(k+1) - gₙ(k)`,
and summing over `k = 0,…,n` telescopes (both boundary terms cancel automatically). -/

private noncomputable def cc (k : ℕ) : ℚ :=
  ordinaryHypergeometricCoefficient (1 / 12 : ℚ) (5 / 12) 1 k

private noncomputable def dd (n : ℕ) : ℚ :=
  generalizedHypergeometricCoefficient (1 / 6 : ℚ) (5 / 6) (1 / 2) 1 1 n

/-- `AAₙ = (n+1/6)(n+1/2)(n+5/6)`, the numerator of the common recurrence ratio. -/
private noncomputable def AA (n : ℕ) : ℚ :=
  ((n : ℚ) + 1 / 6) * ((n : ℚ) + 1 / 2) * ((n : ℚ) + 5 / 6)

/-- The WZ certificate `gₙ(k) = k²(2k-3n-3) cₖ c_{n+1-k}`. -/
private noncomputable def gg (n k : ℕ) : ℚ :=
  (k : ℚ) ^ 2 * (2 * (k : ℚ) - 3 * (n : ℚ) - 3) * cc k * cc (n + 1 - k)

/-- The Cauchy-product coefficient `eₙ = ∑_{k=0}^n cₖ c_{n-k}`. -/
private noncomputable def ee (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), cc k * cc (n - k)

private theorem cc_zero : cc 0 = 1 := by
  simp [cc, ordinaryHypergeometricCoefficient, ascPochhammer_zero]

private theorem dd_zero : dd 0 = 1 := by
  simp [dd, generalizedHypergeometricCoefficient, ascPochhammer_zero]

/-- The two-term recurrence for the `₂F₁(1/12, 5/12; 1; ·)` coefficients. -/
private theorem cc_rec (k : ℕ) :
    ((k : ℚ) + 1) ^ 2 * cc (k + 1) = (1 / 12 + (k : ℚ)) * (5 / 12 + (k : ℚ)) * cc k := by
  simp only [cc, ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval, ascPochhammer_eval_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hk : (k ! : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The two-term recurrence for the `₃F₂(1/6, 5/6, 1/2; 1, 1; ·)` coefficients. -/
private theorem dd_rec (n : ℕ) : ((n : ℚ) + 1) ^ 3 * dd (n + 1) = AA n * dd n := by
  simp only [dd, AA, generalizedHypergeometricCoefficient, ascPochhammer_succ_eval,
    ascPochhammer_eval_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hn : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The per-term creative-telescoping identity, valid for `k ≤ n`. -/
private theorem per_term (n k : ℕ) (hk : k ≤ n) :
    ((n : ℚ) + 1) ^ 3 * cc k * cc (n + 1 - k) - AA n * cc k * cc (n - k)
      = gg n (k + 1) - gg n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  have e1 : k + m + 1 - k = m + 1 := by omega
  have e2 : k + m - k = m := by omega
  have e3 : k + m + 1 - (k + 1) = m := by omega
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hck : cc (k + 1) = (1 / 12 + (k : ℚ)) * (5 / 12 + (k : ℚ)) * cc k / (((k : ℚ) + 1) ^ 2) := by
    rw [eq_div_iff (by positivity)]; linear_combination cc_rec k
  have hcm : cc (m + 1) = (1 / 12 + (m : ℚ)) * (5 / 12 + (m : ℚ)) * cc m / (((m : ℚ) + 1) ^ 2) := by
    rw [eq_div_iff (by positivity)]; linear_combination cc_rec m
  simp only [gg, AA, e1, e2, e3, hck, hcm]
  push_cast
  field_simp
  ring

private theorem gg_zero (n : ℕ) : gg n 0 = 0 := by simp [gg]

private theorem gg_top (n : ℕ) : gg n (n + 1) = -(((n : ℚ) + 1) ^ 3) * cc (n + 1) := by
  unfold gg
  rw [Nat.sub_self, cc_zero, mul_one]
  push_cast
  ring

/-- The recurrence for the Cauchy-product coefficients, obtained by telescoping. -/
private theorem ee_rec (n : ℕ) : ((n : ℚ) + 1) ^ 3 * ee (n + 1) = AA n * ee n := by
  have tele : ∑ k ∈ Finset.range (n + 1), (gg n (k + 1) - gg n k) = gg n (n + 1) - gg n 0 :=
    Finset.sum_range_sub (gg n) (n + 1)
  have key : ∑ k ∈ Finset.range (n + 1),
      (((n : ℚ) + 1) ^ 3 * cc k * cc (n + 1 - k) - AA n * cc k * cc (n - k))
        = gg n (n + 1) - gg n 0 := by
    rw [← tele]
    exact Finset.sum_congr rfl fun k hk =>
      per_term n k (by rw [Finset.mem_range, Nat.lt_succ_iff] at hk; exact hk)
  rw [Finset.sum_sub_distrib] at key
  have hmul1 : ∑ k ∈ Finset.range (n + 1), ((n : ℚ) + 1) ^ 3 * cc k * cc (n + 1 - k)
      = ((n : ℚ) + 1) ^ 3 * ∑ k ∈ Finset.range (n + 1), cc k * cc (n + 1 - k) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hmul2 : ∑ k ∈ Finset.range (n + 1), AA n * cc k * cc (n - k)
      = AA n * ∑ k ∈ Finset.range (n + 1), cc k * cc (n - k) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hmul1, hmul2, gg_zero, gg_top] at key
  have hee1 : (∑ k ∈ Finset.range (n + 1), cc k * cc (n + 1 - k)) = ee (n + 1) - cc (n + 1) := by
    have h : ee (n + 1) = (∑ k ∈ Finset.range (n + 1), cc k * cc (n + 1 - k)) + cc (n + 1) := by
      unfold ee
      rw [Finset.sum_range_succ, Nat.sub_self, cc_zero, mul_one]
    rw [h]; ring
  have hee2 : (∑ k ∈ Finset.range (n + 1), cc k * cc (n - k)) = ee n := rfl
  rw [hee1, hee2] at key
  linear_combination key

/-- Both coefficient sequences satisfy the same recurrence with the same initial value, hence
they are equal. -/
private theorem ee_zero : ee 0 = 1 := by simp [ee, cc_zero]

private theorem ee_eq_dd (n : ℕ) : ee n = dd n := by
  induction n with
  | zero => rw [ee_zero, dd_zero]
  | succ n ih =>
    have h1 := ee_rec n
    have h2 := dd_rec n
    have hne : ((n : ℚ) + 1) ^ 3 ≠ 0 := by positivity
    rw [ih] at h1
    exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-- The finite coefficient identity underlying Clausen's formula at `a = 1/12`, `b = 5/12`,
stated over `ℚ`. The left-hand side is the `n`-th Cauchy-product coefficient of
`(₂F₁(1/12, 5/12; 1; ·))²` and the right-hand side is the `n`-th coefficient of
`₃F₂(1/6, 5/6, 1/2; 1, 1; ·)`. Equivalently, writing `cₖ = (1/12)ₖ(5/12)ₖ/(k!)²` and
`dₙ = (6n)!/((3n)!(n!)³·1728ⁿ)`, this is `∑_{k=0}^n cₖ c_{n-k} = dₙ`. -/
theorem clausen_coeff_identity (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ordinaryHypergeometricCoefficient (1 / 12 : ℚ) (5 / 12) 1 k *
          ordinaryHypergeometricCoefficient (1 / 12 : ℚ) (5 / 12) 1 (n - k)
      = generalizedHypergeometricCoefficient (1 / 6 : ℚ) (5 / 6) (1 / 2) 1 1 n :=
  ee_eq_dd n

/-- Clausen's formula specialized to `a = 1/12`, `b = 5/12` (paper Thm. `satzclausen`):
`(₂F₁(1/12, 5/12; 1; z))² = ₃F₂(1/6, 5/6, 1/2; 1, 1; z)` for `‖z‖ < 1`.

The analytic reduction (Cauchy product of the square, coefficient comparison) is carried out
here; the remaining arithmetic core is `clausen_coeff_identity`. -/
theorem hyp2F1_sq_eq_hyp3F2 {z : ℂ} (hz : ‖z‖ < 1) : hyp2F1 z ^ 2 = hyp3F2 z := by
  -- Non-degeneracy of the lower parameter `c = 1` (and of `a = 1/12`, `b = 5/12`).
  have hnd : ∀ kn : ℕ, (kn : ℂ) ≠ -(1 / 12) ∧ (kn : ℂ) ≠ -(5 / 12) ∧ (kn : ℂ) ≠ -1 := by
    intro kn
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h0 : ((12 * kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((12 * kn + 5 : ℕ) : ℂ) = 0 := by push_cast; linear_combination 12 * h
      rw [Nat.cast_eq_zero] at h0; omega
    · have h0 : ((kn + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
      rw [Nat.cast_eq_zero] at h0; omega
  -- Absolute convergence of the `₂F₁` series, needed for the Cauchy product.
  have hfsum : Summable fun n : ℕ =>
      ‖ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 n * z ^ n‖ :=
    ordinaryHypergeometric_norm_summable (1 / 12) (5 / 12) 1 hnd hz
  -- `hyp2F1 z` as a `tsum` of `cₖ zᵏ`.
  have hL : hyp2F1 z =
      ∑' n : ℕ, ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 n * z ^ n := by
    rw [hyp2F1, ordinaryHypergeometric, ordinaryHypergeometric_sum_eq]
    exact tsum_congr fun n => smul_eq_mul _ _
  -- `hyp3F2 z` as a `tsum` of `dₙ zⁿ`.
  have hR : hyp3F2 z =
      ∑' n : ℕ, generalizedHypergeometricCoefficient (1 / 6 : ℂ) (5 / 6) (1 / 2) 1 1 n * z ^ n := by
    rw [hyp3F2, generalizedHypergeometric, generalizedHypergeometric_sum_eq]
    exact tsum_congr fun n => smul_eq_mul _ _
  -- The square is the Cauchy product; compare coefficients.
  rw [sq, hL, hR, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfsum hfsum]
  refine tsum_congr fun n => ?_
  -- Pull `zⁿ` out of the finite convolution sum.
  have hz_pow : ∀ k ∈ Finset.range (n + 1),
      ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 k * z ^ k *
        (ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 (n - k) * z ^ (n - k))
        = ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 k *
          ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 (n - k) * z ^ n := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hpow : z ^ k * z ^ (n - k) = z ^ n := by rw [← pow_add, Nat.add_sub_cancel' hk]
    linear_combination (ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 k *
      ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 (n - k)) * hpow
  rw [Finset.sum_congr rfl hz_pow, ← Finset.sum_mul]
  -- Reduce the complex coefficient identity to the rational one.
  congr 1
  have hq := clausen_coeff_identity n
  have hsumcast : (∑ k ∈ Finset.range (n + 1),
        ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 k *
          ordinaryHypergeometricCoefficient (1 / 12 : ℂ) (5 / 12) 1 (n - k))
      = ((∑ k ∈ Finset.range (n + 1),
          ordinaryHypergeometricCoefficient (1 / 12 : ℚ) (5 / 12) 1 k *
            ordinaryHypergeometricCoefficient (1 / 12 : ℚ) (5 / 12) 1 (n - k) : ℚ) : ℂ) := by
    rw [Rat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Rat.cast_mul, ordinaryHypergeometricCoefficient_ratCast,
      ordinaryHypergeometricCoefficient_ratCast]
    norm_num
  have hgencast :
      generalizedHypergeometricCoefficient (1 / 6 : ℂ) (5 / 6) (1 / 2) 1 1 n
        = ((generalizedHypergeometricCoefficient (1 / 6 : ℚ) (5 / 6) (1 / 2) 1 1 n : ℚ) : ℂ) := by
    rw [generalizedHypergeometricCoefficient_ratCast]
    norm_num
  rw [hsumcast, hgencast, hq]

/-- The Pochhammer/factorial identity from the proof of paper Thm. `darst`:
`(1/6)ₙ · (1/2)ₙ · (5/6)ₙ = (6n)! / ((3n)! · 12^(3n))`, stated over `ℚ`. -/
theorem ascPochhammer_prod_eq_factorial (n : ℕ) :
    (ascPochhammer ℚ n).eval (1 / 6 : ℚ) * (ascPochhammer ℚ n).eval (1 / 2 : ℚ) *
      (ascPochhammer ℚ n).eval (5 / 6 : ℚ)
      = ((6 * n)! : ℚ) / (((3 * n)! : ℚ) * 12 ^ (3 * n)) := by
  induction n with
  | zero => simp [ascPochhammer_zero]
  | succ n ih =>
    have e6 : ((6 * (n + 1))! : ℚ)
        = (6 * n + 1) * (6 * n + 2) * (6 * n + 3) * (6 * n + 4) * (6 * n + 5) * (6 * n + 6) *
          ((6 * n)! : ℚ) := by
      rw [show 6 * (n + 1) = 6 * n + 1 + 1 + 1 + 1 + 1 + 1 from by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have e3 : ((3 * (n + 1))! : ℚ)
        = (3 * n + 1) * (3 * n + 2) * (3 * n + 3) * ((3 * n)! : ℚ) := by
      rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 from by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      show (ascPochhammer ℚ n).eval (1 / 6) * (1 / 6 + n) *
          ((ascPochhammer ℚ n).eval (1 / 2) * (1 / 2 + n)) *
          ((ascPochhammer ℚ n).eval (5 / 6) * (5 / 6 + n))
        = (ascPochhammer ℚ n).eval (1 / 6) * (ascPochhammer ℚ n).eval (1 / 2) *
          (ascPochhammer ℚ n).eval (5 / 6) * ((1 / 6 + n) * (1 / 2 + n) * (5 / 6 + n)) from by ring,
      ih, e6, e3, show 3 * (n + 1) = 3 * n + 3 from by ring, pow_add]
    have hf3 : ((3 * n)! : ℚ) ≠ 0 := by positivity
    field_simp
    ring

/-- Paper Thm. `darst` (chapter 9, `140_MainTheorem.tex`): for `‖z‖ < 1`,
`(₂F₁(1/12, 5/12; 1; z))² = ∑ (6n)!/((3n)!(n!)³) · zⁿ/12^(3n)`.
Note `12^(3n) = 1728^n`. -/
theorem hyp2F1_sq_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    hyp2F1 z ^ 2
      = ∑' n : ℕ, ((6 * n)! : ℂ) / (((3 * n)! : ℂ) * (n ! : ℂ) ^ 3) * (z ^ n / 12 ^ (3 * n)) := by
  rw [hyp2F1_sq_eq_hyp3F2 hz, hyp3F2, generalizedHypergeometric,
    generalizedHypergeometric_sum_eq]
  refine tsum_congr fun n => ?_
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h3n : ((3 * n)! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h12 : (12 : ℂ) ^ (3 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  -- The `ℂ`-version of the Pochhammer/factorial identity, in multiplicative form.
  have hprod : (ascPochhammer ℂ n).eval (1 / 6 : ℂ) * (ascPochhammer ℂ n).eval (5 / 6 : ℂ) *
        (ascPochhammer ℂ n).eval (1 / 2 : ℂ) * ((3 * n)! : ℂ) * (12 : ℂ) ^ (3 * n)
      = ((6 * n)! : ℂ) := by
    have hℚ := ascPochhammer_prod_eq_factorial n
    have e6 : (ascPochhammer ℂ n).eval (1 / 6 : ℂ) =
        (((ascPochhammer ℚ n).eval (1 / 6 : ℚ) : ℚ) : ℂ) := by
      rw [show (1 / 6 : ℂ) = ((1 / 6 : ℚ) : ℂ) by norm_num, ← ascPochhammer_eval_ratCast]
    have e56 : (ascPochhammer ℂ n).eval (5 / 6 : ℂ) =
        (((ascPochhammer ℚ n).eval (5 / 6 : ℚ) : ℚ) : ℂ) := by
      rw [show (5 / 6 : ℂ) = ((5 / 6 : ℚ) : ℂ) by norm_num, ← ascPochhammer_eval_ratCast]
    have e12 : (ascPochhammer ℂ n).eval (1 / 2 : ℂ) =
        (((ascPochhammer ℚ n).eval (1 / 2 : ℚ) : ℚ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℚ) : ℂ) by norm_num, ← ascPochhammer_eval_ratCast]
    rw [e6, e56, e12,
      show (((ascPochhammer ℚ n).eval (1 / 6 : ℚ) : ℚ) : ℂ) *
            (((ascPochhammer ℚ n).eval (5 / 6 : ℚ) : ℚ) : ℂ) *
            (((ascPochhammer ℚ n).eval (1 / 2 : ℚ) : ℚ) : ℂ)
          = ((((ascPochhammer ℚ n).eval (1 / 6 : ℚ) * (ascPochhammer ℚ n).eval (1 / 2 : ℚ) *
              (ascPochhammer ℚ n).eval (5 / 6 : ℚ)) : ℚ) : ℂ) from by push_cast; ring,
      hℚ]
    have h3nℚ : ((3 * n)! : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [smul_eq_mul, generalizedHypergeometricCoefficient]
  simp only [ascPochhammer_eval_one]
  field_simp
  linear_combination (z ^ n) * hprod

end Chudnovsky
