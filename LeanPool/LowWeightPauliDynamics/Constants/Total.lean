/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Constants.C0
public import LeanPool.LowWeightPauliDynamics.Constants.StepSum

/-!
# A time threshold from model parameters, and the summed truncation error

This file defines the threshold `tZeroModel = 1/(2 Γ (k_h−1) α)`, which depends on model
parameters only, together with the decay base `q = t/t₀`, and proves `total_truncation_error`:
the norm-level form of the summed bound of `apd:thm:one_step_truncation_error` with that
threshold.

## Main definitions

* `tZeroModel`: the threshold `t₀ = 1/(2 Γ (k_h−1) α)`.
* `decayBase`: the decay base `q = t/t₀`.

## Main results

* `tZeroModel_le_tZero`, `lt_tZero_of_lt_tZeroModel`: the model threshold is at most the paper's
  `t₀ = 1/(c₀ Γ (k_h−1) α)`, so `t < tZeroModel` implies `t < t₀`.
* `decayBase_lt_one`, `pow_decayBase_antitone`: `q < 1` below the threshold, and `q^{m+1}` decays
  in `m`.
* `total_truncation_error`: the summed truncation bound with `t₀ = tZeroModel`.

## A threshold depending on model parameters only

The paper's threshold (`apd:eq:time_condition`) is

  `t₀ = 1/(c₀ Γ (k_h−1) α)`,

where the constant `c₀` of `apd:eq:c0` depends on `m*` and `r`, and through its third factor
`(1+4eβ)^{1/(m*+1)}`, with `β = 2e·w₂·sin(dt)` and `sin(dt) ≤ αt/r`, also on `t`. The rung `m*`
is in turn chosen in terms of `log(t₀/t)` (`apd:thm:truncation_threshold_entangled`).

`tZeroModel` below is

  `t₀ := 1/(2 · Γ · (k_h−1) · α)`,

with the literal `2` in place of `c₀`. Its type is `ℝ → ℝ → ℝ → ℝ`, taking `Γ`, `k_h`, `α`:
there is no `m*`, no `r`, no `c₀` and no `t`. The decay base `q = t/t₀` is therefore fixed before
`m*` and `r` are chosen, and the parameters can be fixed in the order

  `t₀ → q := t/t₀ → m* → w* = k_o + m*(k_h−1) → r`.

That the substitution is *sound* rather than merely convenient is `tZeroModel_le_tZero`: since
`c₀ ≤ 2` under the hypotheses of `Lean4LPD.cZero_le_two` (`m* ≥ 1`, `r ≥ 5`, `B ≤ 1`), the model
threshold is at most the paper's, so `t < t₀^model` implies `t < t₀`. It is a conservative form of
the paper's condition — it can only shrink the admissible window, never enlarge it.
`cZero_le_two_sharp` permits the slightly better **uniform** constant `(384/275)√2`; the ratio
1.0128 compares those two uniform choices only. It is not an upper bound on the loss relative to
the instance-dependent `c₀`: that ratio is `2/c₀`, and can approach two.

The uniform bound `cZero_le_two` is what licenses the substitution: without a bound on `c₀` that
holds for all admissible `(r, m*, Γ)` there would be nothing to compare `tZeroModel` against.

## The `hstep` hypothesis, and where it is discharged

`total_truncation_error` takes the per-step summed bound `hstep` as an argument, which keeps this
file purely scalar. It is deliberately a hypothesis of a theorem rather than a global assumption,
so it stays visible in the statement.

**It is not a hypothesis of the library as a whole.** The derivation of that bound — the `Γ`
layers of each Trotter step, the absorption of the last jump into the chain below it, and
`sum_choose_mul_le` — is assembled on top of `MultiLadder.le_majorant`:
`Lean4LPD.Ladder.ChainBound` for the block inflow and the shifted-chain slot sum,
`Lean4LPD.Constants.AssemblyBound` for the `D`-sector estimate, with
`MultiLadder.sum_block_epsJump_le_cZero` concluding exactly the shape `hstep` asks for.
`Lean4LPD.Pauli.LayerError` instantiates that against `pauliMultiLadder`, so at Pauli level no
caller supplies it either. All of this is at the level of the normalized Pauli 2-norm; the
conversion to an error in expectation (`apd:thm:triangle`) is not part of this file.
-/

public section

namespace Lean4LPD

open Finset

/-- **The threshold from model parameters alone**: `t₀ = 1/(2 Γ (k_h−1) α)`.

The literal `2` replaces the constant `c₀` of `apd:eq:time_condition`, which removes the
dependence of `t₀` on `m*`, `r` and `t` — read the type: no `m*`, no `r`, no `c₀`, no `t`.
`tZeroModel_le_tZero` shows the replacement is sound. -/
noncomputable def tZeroModel (G kh a : ℝ) : ℝ := 1 / (2 * G * (kh - 1) * a)

lemma tZeroModel_pos {G kh a : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a) :
    0 < tZeroModel G kh a := by
  have h1 : (0 : ℝ) < kh - 1 := by linarith
  unfold tZeroModel
  positivity

/-- **The model threshold is a sound under-approximation of the paper's.** Since `c₀ ≤ 2` under
the hypotheses `m* ≥ 1`, `r ≥ 5` and `B ≤ 1` of `Lean4LPD.cZero_le_two`, one has `t₀^model ≤ t₀`,
so restricting to `t < t₀^model` is conservative: it can only shrink the admissible window. This
is the lemma that licenses the substitution, and it is `Lean4LPD.cZero_le_two` that makes it
available — without a uniform bound on `c₀` there would be nothing to compare against. -/
theorem tZeroModel_le_tZero {r m G B kh a : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh : 1 < kh) (ha : 0 < a) :
    tZeroModel G kh a ≤ tZero (cZero r m G B) G kh a := by
  obtain ⟨_, _, hG, _, _⟩ := id h
  have hkh1 : (0 : ℝ) < kh - 1 := by linarith
  have hc2 : cZero r m G B ≤ 2 := cZero_le_two h hm1 hr5 hB0 hB1
  have hcpos : 0 < cZero r m G B := by
    unfold cZero
    obtain ⟨hr', _, _, _, _⟩ := id h
    have hrpos : (0 : ℝ) < r := by linarith
    have h1 : (0 : ℝ) < (r + 1) / r := div_pos (by linarith) hrpos
    have h2 : (0 : ℝ) < Real.exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
    have h3 : (0 : ℝ) < (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hden : 0 < cZero r m G B * G * (kh - 1) * a := by positivity
  unfold tZeroModel tZero
  apply one_div_le_one_div_of_le hden
  nlinarith [hc2, hG.le, hkh1.le, ha.le, mul_pos hG hkh1]

/-- The consequence used downstream: the short-time regime of the model threshold sits inside
that of `apd:eq:time_condition`, i.e. `t < tZeroModel` implies `t < t₀`. -/
theorem lt_tZero_of_lt_tZeroModel {r m G B kh a t : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hr5 : 5 ≤ r) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh : 1 < kh) (ha : 0 < a)
    (ht : t < tZeroModel G kh a) : t < tZero (cZero r m G B) G kh a :=
  lt_of_lt_of_le ht (tZeroModel_le_tZero h hm1 hr5 hB0 hB1 hkh ha)

/-- The decay base `q = t/t₀` with `t₀ = tZeroModel`. Its type is `ℝ → ℝ → ℝ → ℝ → ℝ`, taking
`Γ`, `k_h`, `α`, `t` — so `q` is known before the rung `m*` and the step count `r` are, and `m*`
may be chosen from `q` afterwards (see `Lean4LPD.exists_model_norm_threshold`). -/
noncomputable def decayBase (G kh a t : ℝ) : ℝ := t / tZeroModel G kh a

lemma decayBase_nonneg {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a) (ht : 0 ≤ t) :
    0 ≤ decayBase G kh a t :=
  div_nonneg ht (le_of_lt (tZeroModel_pos hG hkh ha))

/-- `q < 1` in the short-time regime `t < t₀` of `apd:eq:time_condition`, here with
`t₀ = tZeroModel`. -/
lemma decayBase_lt_one {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a)
    (ht : t < tZeroModel G kh a) : decayBase G kh a t < 1 := by
  have h0 := tZeroModel_pos hG hkh ha
  unfold decayBase
  rw [div_lt_one h0]
  exact ht

/-- Under the short-time condition `apd:eq:time_condition` the bound decays in `m*`. Stated as
monotonicity of `q^{m+1}`: `q^{m+2} ≤ q^{m+1}` for `0 ≤ t < tZeroModel`. -/
lemma pow_decayBase_antitone {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a) (ht0 : 0 ≤ t)
    (ht : t < tZeroModel G kh a) (m : ℕ) :
    decayBase G kh a t ^ (m + 2) ≤ decayBase G kh a t ^ (m + 1) :=
  pow_le_pow_of_le_one (decayBase_nonneg hG hkh ha ht0)
    (le_of_lt (decayBase_lt_one hG hkh ha ht)) (by omega)

/-- **The summed truncation error, with a threshold free of `c₀`.**

Given the summed bound in the `c₀` form of `apd:eq:total_high_weight_norm` (`hstep`, the
hypothesis discussed in the module docstring), the bound may be restated with `t₀` taken from
model parameters:

  `S ≤ (t/t₀)^{m*+1} · (∏_{i=1}^{m*+1}(i+c)) / (m*+1)! · ‖O‖`,   `t₀ = 1/(2Γ(k_h−1)α)`.

Two things happen in the algebra and both matter. `c₀ ≤ 2` (`Lean4LPD.cZero_le_two`, whence the
hypotheses `hm1`, `hr5`, `hB0`, `hB1`) replaces the parameter-dependent constant by a literal,
and then the `(k_h−1)^{m*+1}` produced by `prod_rungW_eq` is **absorbed exactly** into the decay
base: since `1/t₀ = 2Γ(k_h−1)α`, one has `(2Γαt)^{m*+1} · (k_h−1)^{m*+1} = (t/t₀)^{m*+1}`. So
besides offsetting the factorial `(m*+1)!` (compare `apd:rmk:comparison`), the rung product is
what supplies the factor `k_h − 1` of the threshold.

The conclusion is the norm-level content of `apd:eq:total_truncation_error` *before* the product
`∏_{i=1}^{m*+1}(i+c)` is estimated. That estimate, `∏_{i=1}^{n}(i+c) ≤ n!·(e·n)^c`, is
`prod_add_one_le_factorial_exp_rpow`; `total_truncation_error_product_bound` composes the two and
is the version downstream code uses. The statement is about real numbers `S` and `M`, standing
for the summed high-weight norm and `‖O‖`; no conversion to an error in expectation is made
here. -/
theorem total_truncation_error {S M t a G kh1 c B : ℝ} {m r : ℕ}
    (hstep : S ≤ (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
              * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
              / (Nat.factorial (m + 1) : ℝ) * M)
    (hadm : Admissible (r : ℝ) (m : ℝ) G) (hm1 : 1 ≤ (m : ℝ)) (hr5 : 5 ≤ (r : ℝ))
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh1 : 0 < kh1) (hc : 0 ≤ c)
    (ha : 0 < a) (ht : 0 ≤ t) (hM : 0 ≤ M) :
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1)
          * (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c))
          / (Nat.factorial (m + 1) : ℝ) * M := by
  obtain ⟨_, _, hG, _, _⟩ := id hadm
  have hc2 : cZero (r : ℝ) (m : ℝ) G B ≤ 2 := cZero_le_two hadm hm1 hr5 hB0 hB1
  have hcpos : 0 ≤ cZero (r : ℝ) (m : ℝ) G B := by
    unfold cZero
    have h3 : (0 : ℝ) < (1 + B) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := Real.rpow_pos_of_pos (by linarith) _
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    positivity
  have hfac : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m + 1)
  have hprodpos : (0 : ℝ) ≤ ∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c) := by
    refine Finset.prod_nonneg fun i _ => ?_
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  -- t₀ from model parameters, and the identity 2*G*a = (1/t₀)/kh1
  have ht0 : tZeroModel G (kh1 + 1) a = 1 / (2 * G * kh1 * a) := by
    unfold tZeroModel; norm_num
  have ht0pos : 0 < tZeroModel G (kh1 + 1) a := tZeroModel_pos hG (by linarith) ha
  have hbase : decayBase G (kh1 + 1) a t = 2 * G * kh1 * a * t := by
    have hne : (2 : ℝ) * G * kh1 * a ≠ 0 := by positivity
    unfold decayBase
    rw [ht0]
    field_simp
  -- step 1: replace c₀ by 2
  have h1 : (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1) ≤ (2 * G * a * t) ^ (m + 1) := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [hc2, hG.le, ha.le, ht, mul_nonneg (mul_nonneg hG.le ha.le) ht]
  -- step 2: the rung product, and the exact cancellation of kh1^(m+1)
  have h2 : (2 * G * a * t) ^ (m + 1) * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
      = decayBase G (kh1 + 1) a t ^ (m + 1) * ∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c) := by
    rw [prod_rungW_eq, hbase]
    rw [show (2 : ℝ) * G * kh1 * a * t = (2 * G * a * t) * kh1 by ring, mul_pow]
    ring
  have hcoef : (0 : ℝ) ≤ M / (Nat.factorial (m + 1) : ℝ) := by positivity
  have hrw : (0 : ℝ) ≤ ∏ j ∈ range (m + 1), rungW kh1 c (j + 2) := by
    rw [prod_rungW_eq]
    have : (0 : ℝ) ≤ kh1 ^ (m + 1) := by positivity
    exact mul_nonneg this hprodpos
  have hAP := mul_le_mul_of_nonneg_right h1 hrw
  calc S ≤ (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
            * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
            / (Nat.factorial (m + 1) : ℝ) * M := hstep
    _ = ((cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
            * ∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
          * (M / (Nat.factorial (m + 1) : ℝ)) := by ring
    _ ≤ ((2 * G * a * t) ^ (m + 1) * ∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
          * (M / (Nat.factorial (m + 1) : ℝ)) := mul_le_mul_of_nonneg_right hAP hcoef
    _ = (decayBase G (kh1 + 1) a t ^ (m + 1) * ∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c))
          * (M / (Nat.factorial (m + 1) : ℝ)) := by rw [h2]
    _ = decayBase G (kh1 + 1) a t ^ (m + 1)
            * (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c))
            / (Nat.factorial (m + 1) : ℝ) * M := by ring

end Lean4LPD
