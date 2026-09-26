/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The constant `c₀` and the time threshold `t₀`

The truncation-error theorem `apd:thm:one_step_truncation_error` holds for times below the
threshold `t₀ = 1 / (c₀ · Γ · (k_h − 1) · α)` (`apd:eq:time_condition`). The constant `c₀`
(`apd:eq:c0`) is what remains when the `(m*+1)`-th root is distributed over the summed truncation
bound `apd:eq:total_high_weight_norm`:

  `c₀ = (r+1)/r · exp[ (9/4)(m*+1)/(rΓ) ] · (1 + 4eβ)^{1/(m*+1)}`,

with `r` the number of Trotter steps, `Γ` the number of layers per step, `m*` the index of the
truncation weight `w* = k_o + m*(k_h−1)`, and `1 + 4eβ` the entry factor of `apd:eq:entry_bound`.
This file defines `c₀` as a function of four real parameters, `cZero r m G B` with `B` standing
for `4eβ`, proves `c₀ ≤ 2` under explicit hypotheses, and exhibits witnesses showing that the
hypotheses `1 ≤ m*` and `5 ≤ r` are needed.

## Main definitions

* `cZero r m G B`: the constant `c₀`.
* `tZero c G kh a`: the threshold `t₀ = 1/(c Γ (k_h − 1) α)`.
* `Admissible r m G`: the step-count conditions `r ≥ m*` and `r ≥ 8(m*+1)²/Γ`
  (`apd:eq:multijump_factor`), together with `1 ≤ r`, `0 ≤ m*` and `0 < Γ`.

## Main results

* `cZero_le_two_sharp`, `cZero_le_two`: if `Admissible r m G`, `1 ≤ m`, `5 ≤ r` and `0 ≤ B ≤ 1`,
  then `c₀ ≤ (384/275)·√2 ≈ 1.9748 ≤ 2`. `cZero_le_two_without_m_le_r` shows that the clauses
  `m ≤ r` and `0 < G` of `Admissible` are not needed for this.
* Alternative sufficient conditions, each with `Admissible r m G` and `0 ≤ B ≤ 1`:
  `cZero_le_two_of_gamma_le_six` (`1 ≤ m` and `Γ ≤ 6`, which forces `5 ≤ r` by
  `le_r_of_gamma_le_six`), `cZero_le_two_of_gamma_le_seven` (`1 ≤ m` and `Γ ≤ 7`), and
  `cZero_le_two_of_three_le_m` (`3 ≤ m`, with no further condition on `r` or `Γ`).
* Necessity witnesses, admissible points with `c₀ > 2`: `two_lt_cZero_of_admissible` at
  `(r, m*, Γ, B) = (1, 1, 32, 0)`, `two_lt_cZero_of_admissible_four` at `(4, 1, 8, 1)`,
  `two_lt_cZero_of_m_zero` at `(5, 0, 2, 1)` and `two_lt_cZero_of_m_two` at `(2, 2, 36, 1)`;
  moreover `two_lt_cZero_of_m_zero_general`: `c₀ > 2` at `m* = 0` for every `r > 0`, `Γ > 0` and
  `B ≥ 1`.
* Dependence on `Γ`: `cZero_antitone_gamma` (at fixed `r`) and `cZero_extremal_isotone_gamma`
  (along the boundary `rΓ = 8(m*+1)²` of the admissible set).
* Constants under weaker hypotheses: `cZero_le_four_mul_exp` (`c₀ ≤ 4e^{9/32}` on `Admissible`
  with `0 ≤ B ≤ 1`), attained by `cZero_eq_four_mul_exp_at_worst`, and
  `cZero_le_ten_thirds_of_one_le_m` (`c₀ ≤ 10/3` once `1 ≤ m`).
* `tZero_anti`: `t₀` is antitone in `c₀`.

## The role of each hypothesis

**`5 ≤ r`.** The smallest `r` allowed by `Admissible` is `max(1, m*, 8(m*+1)²/Γ)`, whose last
argument *shrinks* as `Γ` grows. At `m* ≤ 1` it can reach `1`; the factor `(r+1)/r` is then exactly
`2`, the exponential factor is strictly greater than `1` and the root factor is at least `1`, so
`c₀ > 2` for every `B ≥ 0`, including `B = 0`: the hypothesis concerns `r`, not the entry factor.
`two_lt_cZero_of_admissible` is the instance `(r, m*, Γ) = (1, 1, 32)`, and
`two_lt_cZero_of_admissible_four` shows that `4 ≤ r` is not enough. The layer count that enters is
the effective one, `ΥΓ`, which is `10Γ` for the fourth-order product formula (see the section on
the effective layer count below).

**`1 ≤ m`.** At `m* = 0` the root exponent `1/(m*+1)` is `1` rather than at most `1/2`, so the
third factor is the whole of `1 + B`: at `(r, m*, Γ, B) = (5, 0, 2, 1)` every other hypothesis of
`cZero_le_two` holds and `c₀ ≈ 3.006` (`two_lt_cZero_of_m_zero`). This is why `1 ≤ m` and `5 ≤ r`
are explicit arguments of `cZero_le_two` rather than fields of `Admissible`: the witnesses can then
be stated against `Admissible` itself.

**Larger `m*`.** The mechanism described under `5 ≤ r` needs `m* ≤ 1`. Since `Admissible` contains
`m ≤ r`, the smallest admissible `r` never falls below `m*`, so for `m* ≥ 2` no `Γ` drives
`(r+1)/r` to `2`: at `(r, m*, Γ, B) = (2, 2, 72, 1)`, where `Γ = 8(m*+1)²`, the smallest admissible
`r` is `2` and `c₀ ≈ 1.9806 < 2`. Two consequences, stated here as numerical observations (only the
named theorem is formalized). A *lower* bound on `Γ` can suffice once `m* ≥ 2`: at `m* = 2` and
`B ≤ 1`, every `Γ ≥ 59.60` gives `c₀ ≤ 2` for all admissible `r`. And the maximum of `c₀` over both
`Γ` and `r` drops below `2` from `m* = 3` on (it is `≈ 1.7011` at `m* = 3`), so `3 ≤ m` is a
sufficient condition constraining neither `r` nor `Γ` (`cZero_le_two_of_three_le_m`).

**`B ≤ 1`.** The remaining step-count condition of the theorem, `r ≥ 8e²w₂αt` with
`w₂ = k_o + k_h − 1`, constrains `αt` rather than the triple `(r, m*, Γ)` and so does not enter
`Admissible`. It is what bounds `B`: with `β = 2e·w₂·sin(dt)` and `sin(dt) ≤ αt/r` it gives
`β ≤ 1/(4e)`, that is `B ≤ 1`, which is the range assumed throughout this file.

The script `scripts/c0_scan.py` evaluates `c₀` in floating point on a parameter grid and at the
witness points above.
-/

public section

namespace Lean4LPD

open Real

/-- The constant `c₀` of `apd:thm:one_step_truncation_error`, as `apd:eq:c0` defines it:
`c₀ = (r+1)/r · exp((9/4)(m*+1)/(rΓ)) · (1+B)^{1/(m*+1)}`, where `B` stands for the paper's `4eβ`.
All four arguments are real, so the bounds below apply in particular to natural `r`, `m*`, `Γ`. -/
@[expose]
noncomputable def cZero (r m G B : ℝ) : ℝ :=
  (r + 1) / r * exp (9 / 4 * (m + 1) / (r * G)) * (1 + B) ^ ((1 : ℝ) / (m + 1))

/-- The truncation threshold `t₀ = 1/(c₀ Γ (k_h − 1) α)` of `apd:eq:time_condition`, as a function
of the constant `c`, the layer count `G`, the Hamiltonian locality `kh` and the coupling scale
`a` (standing for `α`). -/
@[expose]
noncomputable def tZero (c G kh a : ℝ) : ℝ := 1 / (c * G * (kh - 1) * a)

/-- The step-count conditions of `apd:thm:one_step_truncation_error` that constrain the triple
`(r, m*, Γ)`, namely `r ≥ m*` and `r ≥ 8(m*+1)²/Γ` (`apd:eq:multijump_factor`), together with the
standing assumptions `1 ≤ r`, `0 ≤ m*` and `0 < Γ`. The second condition is written
multiplicatively, `8(m*+1)² ≤ rΓ`, so that no division appears.

The hypotheses `1 ≤ m*` and `5 ≤ r` of `cZero_le_two` are deliberately not part of this predicate:
they are separate arguments there, and the necessity witnesses (`two_lt_cZero_of_m_zero`,
`two_lt_cZero_of_admissible_four`, …) are stated against `Admissible` itself. -/
@[expose] def Admissible (r m G : ℝ) : Prop :=
  1 ≤ r ∧ 0 ≤ m ∧ 0 < G ∧ m ≤ r ∧ 8 * (m + 1) ^ 2 ≤ r * G

/-- `exp y ≤ 1/(1-y)` for `y < 1`, the upper bound on `Real.exp` used below. It is the
one-line consequence of `1 - y ≤ exp (-y)`. -/
lemma exp_le_one_div_one_sub {y : ℝ} (hy : y < 1) : exp y ≤ 1 / (1 - y) := by
  have h1 : (0 : ℝ) < 1 - y := by linarith
  have h2 : 1 - y ≤ exp (-y) := by
    have := Real.add_one_le_exp (-y)
    linarith
  have h3 : (1 - y) * exp y ≤ exp (-y) * exp y := by
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt (exp_pos y))
  rw [← Real.exp_add] at h3
  simp only [neg_add_cancel, Real.exp_zero] at h3
  rw [le_div_iff₀ h1]
  linarith [h3]

/-- The exponential factor of `c₀` is at most `64/55` when `Admissible r m G` and `1 ≤ m`:
`r·Γ ≥ 8(m*+1)²` bounds the exponent by `9/(32(m*+1)) ≤ 9/64`, and `exp (9/64) ≤ 1/(1 − 9/64)` by
`exp_le_one_div_one_sub`. The clause `m ≤ r` of `Admissible` is not used, and no lower bound on `r`
beyond `1 ≤ r` is needed. -/
lemma exp_factor_le {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) :
    exp (9 / 4 * (m + 1) / (r * G)) ≤ 64 / 55 := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hm2 : (2 : ℝ) ≤ m + 1 := by linarith
  have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 64 := by
    rw [div_le_iff₀ hrGpos]
    nlinarith only [hrG, hm2]
  calc exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 64) := Real.exp_le_exp.mpr hkey
    _ ≤ 1 / (1 - 9 / 64) := exp_le_one_div_one_sub (by norm_num)
    _ = 64 / 55 := by norm_num

/-- The root factor of `c₀` is at most `√2` once `m* ≥ 1` and `0 ≤ B ≤ 1`. The hypothesis `1 ≤ m`
is exactly what halves the exponent; at `m = 0` the factor is the whole of `1 + B`. -/
lemma root_factor_le {m B : ℝ} (hm : 1 ≤ m) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ Real.sqrt 2 := by
  have hbase : (1 : ℝ) ≤ 1 + B := by linarith
  have hexp : (1 : ℝ) / (m + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1 : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ (1 + B) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have h2 : (1 + B) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h3 : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
  rw [← h3]
  linarith

/-- **`c₀ ≤ (384/275)·√2 ≈ 1.9748`** whenever `Admissible r m G`, `1 ≤ m`, `5 ≤ r` and
`0 ≤ B ≤ 1`. The three factors are bounded separately: `(r+1)/r ≤ 6/5` from `r ≥ 5`, the
exponential by `64/55` from `rΓ ≥ 8(m*+1)²` (`exp_factor_le`), and the root by `√2` from `m* ≥ 1`
with `B ≤ 1` (`root_factor_le`).

`B ≤ 1` is the range delivered by the step-count condition `r ≥ 8e²w₂αt` (see the module
docstring); a smaller range such as `B ≤ 1/2` is covered a fortiori.

`hm1` and `hr5` are explicit arguments rather than fields of `Admissible`, and neither can be
dropped: `two_lt_cZero_of_m_zero` and `two_lt_cZero_of_admissible_four` give admissible points with
`c₀ > 2` at which only `1 ≤ m`, respectively only `5 ≤ r`, is violated. -/
theorem cZero_le_two_sharp {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 384 / 275 * Real.sqrt 2 := by
  obtain ⟨hr, hm, hG, hmr, hrG⟩ := h
  have hrpos : (0 : ℝ) < r := by linarith
  have hfrac : (r + 1) / r ≤ 6 / 5 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]
    linarith
  have hexp := exp_factor_le (r := r) (m := m) (G := G) ⟨hr, hm, hG, hmr, hrG⟩ hm1
  have hroot := root_factor_le hm1 hB0 hB1
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) < (1 + B) ^ ((1 : ℝ) / (m + 1)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hsqrt : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  calc cZero r m G B
      = (r + 1) / r * exp (9 / 4 * (m + 1) / (r * G)) * (1 + B) ^ ((1 : ℝ) / (m + 1)) := rfl
    _ ≤ (6 / 5) * (64 / 55) * Real.sqrt 2 := by
        apply mul_le_mul (mul_le_mul hfrac hexp (le_of_lt hexppos) (by norm_num)) hroot
          (le_of_lt hrootpos) (by positivity)
    _ = 384 / 275 * Real.sqrt 2 := by ring

/-- **`c₀ ≤ 2`** whenever `Admissible r m G`, `1 ≤ m`, `5 ≤ r` and `0 ≤ B ≤ 1`: the form in which
the constant enters the threshold `t₀` of `apd:thm:one_step_truncation_error`. It follows from
`cZero_le_two_sharp` and `√2 ≤ 1.4143`. -/
theorem cZero_le_two {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  have := cZero_le_two_sharp h hm1 hr5 hB0 hB1
  nlinarith only [this, hs, Real.sqrt_nonneg 2]

/-- **`c₀ ≤ 2` does not need `Admissible`'s clause `m ≤ r`.** The hypotheses here are
`8(m*+1)² ≤ rΓ`, `1 ≤ m`, `5 ≤ r` and `0 ≤ B ≤ 1`, and this set is strictly weaker than that of
`cZero_le_two`, not a restatement of it: `(r, m*, Γ) = (5, 100, 20000)` satisfies every hypothesis
below and violates `m ≤ r`.

**Nor does it need `0 < Γ`**, which is *derivable*: `8(m*+1)² ≤ rΓ` with `m* ≥ 1` gives
`rΓ ≥ 32 > 0`, and `r ≥ 5 > 0`. So of `Admissible`'s five clauses only `8(m*+1)² ≤ rΓ` remains as
a hypothesis; `1 ≤ r` and `0 ≤ m` are subsumed by `5 ≤ r` and `1 ≤ m`, and the other two are
unnecessary.

The argument is that of `cZero_le_two_sharp`, which never uses `m ≤ r`: it destructures
`Admissible` and passes the clause on to `exp_factor_le`, which discards it.

Scope: this statement concerns the constant `c₀` only. It does not show that the condition
`r ≥ m*` is dispensable elsewhere in the analysis, for instance in the multi-jump majorant
`apd:eq:composition_majorant`. -/
theorem cZero_le_two_without_m_le_r {r m G B : ℝ}
    (hrG : 8 * (m + 1) ^ 2 ≤ r * G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    cZero r m G B ≤ 2 := by
  -- `exp_factor_le` cannot be reused: it takes `Admissible`, and `m ≤ r` is not derivable
  -- here — `(5, 100, 20000)` satisfies everything else and violates it. Argument inlined.
  have hrpos : (0 : ℝ) < r := by linarith
  have hm2 : (2 : ℝ) ≤ m + 1 := by linarith
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hfrac : (r + 1) / r ≤ 6 / 5 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]; linarith
  have hexp : exp (9 / 4 * (m + 1) / (r * G)) ≤ 64 / 55 := by
    have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 64 := by
      rw [div_le_iff₀ hrGpos]; nlinarith only [hrG, hm2]
    calc exp (9 / 4 * (m + 1) / (r * G))
        ≤ exp (9 / 64) := Real.exp_le_exp.mpr hkey
      _ ≤ 1 / (1 - 9 / 64) := exp_le_one_div_one_sub (by norm_num)
      _ = 64 / 55 := by norm_num
  have hroot := root_factor_le hm1 hB0 hB1
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  have hchain : cZero r m G B ≤ 6 / 5 * (64 / 55) * Real.sqrt 2 := by
    unfold cZero
    exact mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos
      (by norm_num)
  nlinarith only [hchain, hs, Real.sqrt_nonneg 2]

/-- **The hypothesis `5 ≤ r` of `cZero_le_two` cannot be dropped, even at `B = 0`.** The triple
`(r, m*, Γ) = (1, 1, 32)` is admissible — `r ≥ m*` reads `1 ≥ 1`, and
`8(m*+1)² = 32 ≤ 1 · 32 = rΓ` — it satisfies `1 ≤ m`, and at `B = 0` it gives
`c₀ = 2·exp(9/64) ≈ 2.302 > 2`.

`B = 0` is the most favourable value of the entry factor, so no improvement of the entry-factor
bound can give `c₀ ≤ 2` from `Admissible` and `1 ≤ m` alone. `scripts/c0_scan.py` evaluates the
same point numerically. -/
theorem two_lt_cZero_of_admissible :
    Admissible 1 1 32 ∧ 2 < cZero 1 1 32 0 := by
  refine ⟨⟨le_refl 1, by norm_num, by norm_num, le_refl 1, by norm_num⟩, ?_⟩
  have hexp : (1 : ℝ) < exp (9 / 4 * (1 + 1) / (1 * 32)) := by
    have h := Real.add_one_le_exp (9 / 4 * (1 + 1) / (1 * 32) : ℝ)
    have harg : (9 : ℝ) / 4 * (1 + 1) / (1 * 32) = 9 / 64 := by norm_num
    rw [harg] at h
    linarith
  have hroot : (1 + (0:ℝ)) ^ ((1 : ℝ) / (1 + 1)) = 1 := by norm_num
  have : cZero 1 1 32 0 = 2 * exp (9 / 4 * (1 + 1) / (1 * 32)) := by
    unfold cZero; rw [hroot]; norm_num
  rw [this]; linarith

/-- **The hypothesis `5 ≤ r` of `cZero_le_two` cannot be weakened to `4 ≤ r`.** At
`(r, m*, Γ, B) = (4, 1, 8, 1)` every other hypothesis holds — the triple is admissible, since
`8(m*+1)² = 32 ≤ 4·8 = rΓ`, and `1 ≤ m`, `0 ≤ B ≤ 1` — and
`c₀ = (5/4)·exp(9/64)·√2 ≈ 2.035 > 2`. -/
theorem two_lt_cZero_of_admissible_four :
    Admissible 4 1 8 ∧ 2 < cZero 4 1 8 1 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hexp : (1 : ℝ) + 9 / 64 ≤ exp (9 / 4 * (1 + 1) / (4 * 8)) := by
    have := Real.add_one_le_exp (9 / 4 * (1 + 1) / (4 * 8) : ℝ)
    have harg : (9 : ℝ) / 4 * (1 + 1) / (4 * 8) = 9 / 64 := by norm_num
    rw [harg] at this
    linarith
  have hroot : (1.414 : ℝ) ≤ (1 + (1:ℝ)) ^ ((1 : ℝ) / (1 + 1)) := by
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
    have h3 : (1.414 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    calc (1.414 : ℝ) ≤ Real.sqrt 2 := h3
      _ = (2 : ℝ) ^ ((1 : ℝ) / 2) := h2.symm
      _ = (1 + (1:ℝ)) ^ ((1 : ℝ) / (1 + 1)) := by norm_num
  have hfrac : ((4:ℝ) + 1) / 4 = 5 / 4 := by norm_num
  have hexppos : (0 : ℝ) < exp (9 / 4 * (1 + 1) / (4 * 8)) := Real.exp_pos _
  unfold cZero
  rw [hfrac]
  nlinarith only [hexp, hroot, hexppos]

/-- **The hypothesis `1 ≤ m` of `cZero_le_two` cannot be dropped.** At
`(r, m*, Γ, B) = (5, 0, 2, 1)` every other hypothesis holds — `r ≥ m*` reads `5 ≥ 0`,
`8(m*+1)² = 8 ≤ 5·2 = rΓ`, `5 ≤ r` and `0 ≤ B ≤ 1` — yet

  `c₀ = (6/5)·exp(9/40)·(1+1)^{1/1} ≈ 3.006 > 2`,

because at `m* = 0` the root exponent `1/(m*+1)` is `1`, so the entry factor `1 + B` enters
undiluted. The middle conjunct `(5 : ℝ) ≥ 5` records that `5 ≤ r` holds at the witness.
`two_lt_cZero_of_m_zero_general` extends this to every `r` and `Γ`. -/
theorem two_lt_cZero_of_m_zero : Admissible 5 0 2 ∧ (5 : ℝ) ≥ 5 ∧ 2 < cZero 5 0 2 1 := by
  refine ⟨⟨by norm_num, le_refl 0, by norm_num, by norm_num, by norm_num⟩, le_refl 5, ?_⟩
  have hroot : (1 + (1 : ℝ)) ^ ((1 : ℝ) / (0 + 1)) = 2 := by
    norm_num
  have hexp : (1 : ℝ) ≤ exp (9 / 4 * (0 + 1) / (5 * 2)) :=
    Real.one_le_exp (by norm_num)
  have hval : cZero 5 0 2 1 = 6 / 5 * exp (9 / 4 * (0 + 1) / (5 * 2)) * 2 := by
    unfold cZero
    rw [hroot]
    norm_num
  rw [hval]
  nlinarith only [hexp]

/-- **`t₀` is antitone in `c₀`**: for `0 < c ≤ c'` (and `0 < G`, `1 < kh`, `0 < a`),
`tZero c' G kh a ≤ tZero c G kh a`. Hence an upper bound on `c₀` is a lower bound on the threshold
`t₀`, and replacing `c₀` by a larger constant `c'` shrinks the guaranteed time window `t < t₀` by
the factor `c'/c₀`. -/
lemma tZero_anti {c c' G kh a : ℝ} (hc : 0 < c) (hcc : c ≤ c') (hG : 0 < G) (hkh : 1 < kh)
    (ha : 0 < a) : tZero c' G kh a ≤ tZero c G kh a := by
  have hpos : (0 : ℝ) < c * G * (kh - 1) * a := by
    have : (0 : ℝ) < kh - 1 := by linarith
    positivity
  have hpos' : (0 : ℝ) < c' * G * (kh - 1) * a := by
    have h1 : (0 : ℝ) < kh - 1 := by linarith
    have : (0 : ℝ) < c' := lt_of_lt_of_le hc hcc
    positivity
  unfold tZero
  apply one_div_le_one_div_of_le hpos
  have h1 : (0 : ℝ) < kh - 1 := by linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hG.le) h1.le) ha.le

/-! ### A cap on the effective layer count

A second sufficient condition for `c₀ ≤ 2`, in which an upper bound on `Γ` takes the place of
`5 ≤ r`. It does **not** supersede `m* ≥ 1 ∧ r ≥ 5`: over the reals the two hypothesis sets are
*incomparable*, since `Γ ≤ 7` admits `r = 32/7 < 5`, and `r ≥ 5` admits `Γ = 32`.

`Γ` occurs in `cZero` exactly once, in the **denominator** of the exponent, so `c₀` is antitone in
`Γ` at fixed `r` (`cZero_antitone_gamma`). Large `Γ` is therefore not by itself what pushes `c₀`
above 2. What does is `r → 1`, which a large `Γ` *permits* through `Admissible`'s
`8(m*+1)² ≤ rΓ`. A cap on `Γ` works only by keeping that lower bound on `r` high, and
`le_r_of_gamma_le_six` makes the mechanism explicit.

**The quantity capped is the effective layer count.** For the `p`th-order product formula
(`apd:eq:suzuki`) one Trotter step consists of `ΥΓ` layers with `Υ = 2·5^{p/2−1}`
(`apd:thm:lightcone`), and `apd:thm:one_step_truncation_error` is applied with `Γ` replaced by
`ΥΓ`. The `G` argument below is that effective count, not the bare number of layers `Γ` of the
Hamiltonian: at bare `Γ = 7` the second-order formula already gives `G = 14`.
-/

/-- **`c₀` is antitone in `Γ` at fixed `r`.** `G` enters `cZero` only through
`exp (9/4·(m+1)/(r·G))`, in the denominator, so raising `Γ` lowers `c₀`.

Stated at fixed `r` deliberately: over the admissible set `r` is *not* free to stay fixed, since its
lower bound `8(m*+1)²/Γ` falls as `Γ` rises, and there the supremum runs the other way.

`cZero_extremal_isotone_gamma` is the statement along the admissible boundary; the two differ in
what is held fixed. -/
theorem cZero_antitone_gamma {r m B G G' : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hG : 0 < G) (hGG' : G ≤ G') : cZero r m G' B ≤ cZero r m G B := by
  have hrG : 0 < r * G := mul_pos hr hG
  have hrG' : 0 < r * G' := mul_pos hr (lt_of_lt_of_le hG hGG')
  have hnum : (0 : ℝ) ≤ 9 / 4 * (m + 1) := by linarith
  have harg : 9 / 4 * (m + 1) / (r * G') ≤ 9 / 4 * (m + 1) / (r * G) := by
    apply div_le_div_of_nonneg_left hnum hrG
    exact mul_le_mul_of_nonneg_left hGG' hr.le
  have hexp := Real.exp_le_exp.mpr harg
  have hfrac : (0 : ℝ) ≤ (r + 1) / r := by positivity
  have hroot : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) :=
    Real.rpow_nonneg (by linarith) _
  unfold cZero
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hfrac) hroot

/-- A sharper bound on the exponential factor than the `64/55` of `exp_factor_le`, under the same
hypotheses: `exp (9/64) ≤ 1439/1250`, via Mathlib's third-order `Real.exp_bound'` rather than
`exp y ≤ 1/(1−y)`.

**The sharpening is needed for `cZero_le_two_of_gamma_le_seven`.** With `Γ ≤ 7` the first factor
is bounded only by `39/32`, and `(39/32)·(64/55)·√2 ≈ 2.0056 > 2`: the two uniform bounds are
attained at different points, so their product overshoots. The cruder estimate
`exp y ≤ 1 + y + y²` is not enough either: it gives `≈ 2.00003`. -/
lemma exp_factor_le_sharp {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) :
    exp (9 / 4 * (m + 1) / (r * G)) ≤ 1439 / 1250 := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hm2 : (2 : ℝ) ≤ m + 1 := by linarith
  have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 64 := by
    rw [div_le_iff₀ hrGpos]
    nlinarith only [hrG, hm2]
  have hb := Real.exp_bound' (x := (9 : ℝ) / 64) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  calc exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 64) := Real.exp_le_exp.mpr hkey
    _ ≤ _ := hb
    _ ≤ 1439 / 1250 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **`Γ ≤ 6` forces `r ≥ 5`**, so under that cap `c₀ ≤ 2` is a *corollary* of `cZero_le_two`,
needing no new estimate. `8(m*+1)² ≤ rΓ ≤ 6r` with `m* ≥ 1` gives `r ≥ 16/3`.

Six is the physically interesting cap: the second-order formula (`Υ = 2`) on a 1D
nearest-neighbour chain with bare `Γ = 3` has effective count exactly 6. -/
theorem le_r_of_gamma_le_six {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hG6 : G ≤ 6) :
    5 ≤ r := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  nlinarith only [hrG, hm1, hr, hG6, sq_nonneg (m - 1)]

/-- **`c₀ ≤ 2` under a cap of 6 on the effective layer count**, with `Admissible r m G`, `1 ≤ m`
and `0 ≤ B ≤ 1`. Immediate from `cZero_le_two` and `le_r_of_gamma_le_six`, so it inherits the
constant `(384/275)√2 ≈ 1.9748` rather than the narrow margin `1.9838` of
`cZero_le_two_of_gamma_le_seven`. -/
theorem cZero_le_two_of_gamma_le_six {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hG6 : G ≤ 6) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 :=
  cZero_le_two h hm1 (le_r_of_gamma_le_six h hm1 hG6) hB0 hB1

/-- **`c₀ ≤ 2` at the integer cap `Γ ≤ 7`**, with `Admissible r m G`, `1 ≤ m` and `0 ≤ B ≤ 1`.
This is *not* a corollary of `cZero_le_two`: here `Admissible` yields only `r ≥ 32/7 ≈ 4.571`, so
`5 ≤ r` is unavailable.

The cap cannot be raised to 8: `two_lt_cZero_of_admissible_four` is `Admissible 4 1 8` with
`c₀ ≈ 2.0347`, so no separate witness is needed. Over the reals the threshold (at `m* = 1`,
`B = 1`) is `32(√2·e^{−9/64} − 1) ≈ 7.3181`; seven is the largest sufficient **integer** cap. The
extremal value is `c₀(32/7, 1, 7, 1) ≈ 1.9838`, a margin of 0.81% below 2, which is why
`exp_factor_le_sharp` is required. -/
theorem cZero_le_two_of_gamma_le_seven {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hG7 : G ≤ 7) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := id h
  have hrpos : (0 : ℝ) < r := by linarith
  have hm2 : (2 : ℝ) ≤ m + 1 := by linarith
  have hr32 : 32 / 7 ≤ r := by nlinarith only [hrG, hm2, hG7, hrpos]
  have hfrac : (r + 1) / r ≤ 39 / 32 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]
    linarith
  have hexp := exp_factor_le_sharp h hm1
  have hroot := root_factor_le hm1 hB0 hB1
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  have hchain : cZero r m G B ≤ 39 / 32 * (1439 / 1250) * Real.sqrt 2 := by
    unfold cZero
    exact mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos (by norm_num)
  nlinarith only [hchain, hs, Real.sqrt_nonneg 2]

/-- **No bound on `Γ` or on `r` can take the place of the hypothesis `1 ≤ m`**: for *every*
`r > 0`, *every* `G > 0` and every `B ≥ 1`, `c₀ > 2` at `m* = 0`.

This generalizes `two_lt_cZero_of_m_zero` from one numeric point to all `r` and `Γ`, and it needs
no numerics: at `m* = 0` the root exponent `1/(m*+1)` is `1`, so the third factor is the whole of
`1 + B ≥ 2`; `(r+1)/r > 1` since `r > 0`; and `exp` of a positive argument exceeds 1.

The hypothesis `B ≥ 1` matters. The step-count condition `r ≥ 8e²w₂αt` gives `B ≤ 1` and no more
(see the module docstring), so `B = 1` is the worst case within the range `0 ≤ B ≤ 1` used in this
file. Under a stronger assumption such as `B ≤ 1/2`, `m* = 0` would satisfy `c₀ ≤ 2` for `r` large
enough, because `c₀ → 1 + B` as `r → ∞`. -/
theorem two_lt_cZero_of_m_zero_general {r G B : ℝ} (hr : 0 < r) (hG : 0 < G) (hB : 1 ≤ B) :
    2 < cZero r 0 G B := by
  have h01 : ((1 : ℝ) / (0 + 1)) = 1 := by norm_num
  have hfrac : 1 < (r + 1) / r := by rw [lt_div_iff₀ hr]; linarith
  have harg : (0 : ℝ) < 9 / 4 * ((0 : ℝ) + 1) / (r * G) := by positivity
  have hexp : 1 < exp (9 / 4 * ((0 : ℝ) + 1) / (r * G)) := by
    have h := Real.add_one_le_exp (9 / 4 * ((0 : ℝ) + 1) / (r * G))
    linarith
  -- the first two factors already exceed 1, and the root factor is the whole of `1 + B ≥ 2`
  have hab : 1 < (r + 1) / r * exp (9 / 4 * ((0 : ℝ) + 1) / (r * G)) := by
    nlinarith only [hfrac, hexp]
  have hc : (2 : ℝ) ≤ 1 + B := by linarith
  unfold cZero
  rw [h01, Real.rpow_one]
  nlinarith only [hab, hc, mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hc)]

/-- **Along the admissible boundary, `c₀` is isotone in `Γ`**, in contrast to
`cZero_antitone_gamma` at fixed `r`; this is the direction relevant to a cap on `Γ`.

Both points below are admissible with `rΓ = 8(m*+1)² = 32` exactly, so both are *extremal* for their
cap, and the value **rises** with `Γ`:

  `c₀(32/6, 1, 6, 1) ≈ 1.9329  <  c₀(32/7, 1, 7, 1) ≈ 1.9838`.

The mechanism is `r`'s floor, not the exponential: `Admissible` forces `r ≥ 32/Γ`, so raising `Γ`
*lowers* the smallest admissible `r` and `(r+1)/r → 2`. At fixed `r` the exponential does fall —
that is `cZero_antitone_gamma` — so the two monotonicity statements have opposite signs and differ
in what is held fixed.

The proof is exact rational arithmetic, which is the cleanest evidence that the exponential is not
what is moving: at both points `rΓ = 32` and `m* = 1`, so `exp (9/4·(m*+1)/(rΓ)) = exp (9/64)` and
`(1+B)^{1/(m*+1)} = √2` are *literally the same factors* on each side, and the comparison reduces to
`(r+1)/r`: `19/16 < 39/32`. -/
theorem cZero_extremal_isotone_gamma :
    Admissible (32 / 6) 1 6 ∧ Admissible (32 / 7) 1 7 ∧
      cZero (32 / 6) 1 6 1 < cZero (32 / 7) 1 7 1 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
          ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have h6 : (9 : ℝ) / 4 * (1 + 1) / (32 / 6 * 6) = 9 / 64 := by norm_num
  have h7 : (9 : ℝ) / 4 * (1 + 1) / (32 / 7 * 7) = 9 / 64 := by norm_num
  have hE : (0 : ℝ) < exp (9 / 64) := Real.exp_pos _
  have hR : (0 : ℝ) < (1 + (1 : ℝ)) ^ ((1 : ℝ) / (1 + 1)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold cZero
  rw [h6, h7]
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (by norm_num) hE) hR

/-! ### `m* ≥ 3`: a sufficient condition on neither Trotter parameter

Unlike `m* ≥ 1 ∧ r ≥ 5` and `m* ≥ 1 ∧ Γ_eff ≤ 7`, this condition constrains neither the number of
steps `r` nor the layer count `Γ`. Since `m* ∈ 𝒪(log(1/ε)/log(t₀/t))` grows with the accuracy
target, it holds in the high-accuracy regime in which the theorem is applied; it can fail for a
coarse accuracy target `ε`, which makes it a different kind of hypothesis from one that holds for
all parameters.
-/

/-- **`m* ≥ 3` gives `c₀ ≤ 2`** on `Admissible r m G` with `0 ≤ B ≤ 1` — no further condition on
`r`, none on `Γ`.

Each factor is bounded separately from `m* ≥ 3`, which is why this needs none of the machinery the
`Γ` route did: `m ≤ r` gives `r ≥ 3` so `(r+1)/r ≤ 4/3`; `8(m*+1)² ≤ rΓ` caps the exponent at
`9/(32(m*+1)) ≤ 9/128`; and `m* + 1 ≥ 4` caps the root at `2^{1/4}`. The product is `1.7210`, a
**13.9%** margin — against 0.81% for `Γ ≤ 7`, so this is much the sturdiest of the three conditions.

**Cost in step count.** `Admissible`'s `8(m*+1)² ≤ rΓ` ties `m*` to `r`: raising `m*` to 3 raises
the step floor to `r ≥ 128/Γ`, which at `Γ_eff = 6` is `r ≥ 21.3`, about four times the floor of
the `r ≥ 5` route at the same `Γ`. The hypothesis itself constrains no Trotter parameter; through
`Admissible` its margin is paid for in step count.

**Three is the least sufficient integer, but not the threshold over ℝ.** `Admissible` quantifies
`m : ℝ`, and numerically the threshold is `m* = 2.14237…`, the root of
`(1+1/m)·e^{9/(32(m+1))}·2^{1/(m+1)} = 2`. So `m* ≥ 9/4` would also suffice (supremum `1.9494`);
these real thresholds are numerical observations and are not formalized. The integer `3` is stated
because `m*` is a rung index, an integer in the paper, not because the bound fails just below it.
`two_lt_cZero_of_m_two` shows `m* ≥ 2` does not suffice, so no integer smaller than 3 works. -/
theorem cZero_le_two_of_three_le_m {r m G B : ℝ} (h : Admissible r m G) (hm3 : 3 ≤ m)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 2 := by
  obtain ⟨hr, hm, hG, hmr, hrG⟩ := h
  have hr3 : (3 : ℝ) ≤ r := le_trans hm3 hmr
  have hrpos : (0 : ℝ) < r := by linarith
  have hm4 : (4 : ℝ) ≤ m + 1 := by linarith
  have hfrac : (r + 1) / r ≤ 4 / 3 := by
    rw [div_le_div_iff₀ hrpos (by norm_num)]; linarith
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hexp : exp (9 / 4 * (m + 1) / (r * G)) ≤ 128 / 119 := by
    have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 128 := by
      rw [div_le_iff₀ hrGpos]; nlinarith only [hrG, hm4]
    calc exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 128) := Real.exp_le_exp.mpr hkey
      _ ≤ 1 / (1 - 9 / 128) := exp_le_one_div_one_sub (by norm_num)
      _ = 128 / 119 := by norm_num
  have hquart : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 1.2 := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
    have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 2 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h4]; norm_num
  have hroot : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ 1.2 := by
    have h1 : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ (2 : ℝ) ^ ((1 : ℝ) / (m + 1)) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / (m + 1)) ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  unfold cZero
  have := mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos (by norm_num)
  nlinarith only [this]

/-- **`m* ≥ 2` does not suffice**, so the `3` of `cZero_le_two_of_three_le_m` is the least
sufficient integer. `(r, m*, Γ, B) = (2, 2, 36, 1)` is admissible — `m ≤ r` reads `2 ≤ 2` and
`8(m*+1)² = 72 = 2·36` holds with equality — and

  `c₀ = (3/2)·e^{3/32}·2^{1/3} ≈ 2.0756`,

3.8% above 2. This point is moreover the **maximizer** of `c₀` at `m* = 2`, `B = 1` over the
admissible set: both constraints on `r` are active, `r = max(1, m*) = 2` and
`Γ = 8(m*+1)²/r = 36`. -/
theorem two_lt_cZero_of_m_two : Admissible 2 2 36 ∧ 2 < cZero 2 2 36 1 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hexp : (1 : ℝ) + 3 / 32 ≤ exp (9 / 4 * (2 + 1) / (2 * 36)) := by
    have h := Real.add_one_le_exp (9 / 4 * (2 + 1) / (2 * 36) : ℝ)
    have harg : (9 : ℝ) / 4 * (2 + 1) / (2 * 36) = 3 / 32 := by norm_num
    rw [harg] at h; linarith
  have hroot : (1.259 : ℝ) ≤ (1 + (1 : ℝ)) ^ ((1 : ℝ) / (2 + 1)) := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Real.rpow_nonneg (by norm_num) _) ?_
    have h3 : ((1 + (1 : ℝ)) ^ ((1 : ℝ) / (2 + 1))) ^ (3 : ℕ) = 2 := by
      rw [← Real.rpow_natCast ((1 + (1 : ℝ)) ^ ((1 : ℝ) / (2 + 1))) 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h3]; norm_num
  have hexppos : (0 : ℝ) < exp (9 / 4 * (2 + 1) / (2 * 36)) := Real.exp_pos _
  unfold cZero
  norm_num
  nlinarith only [hexp, hroot, hexppos]

/-! ### The unconditional constant, and the ladder between it and 2

On `Admissible` alone `c₀ ≤ 2` does not hold, but a larger constant does, with no further
hypothesis on `m*`, `r` or `Γ`. This section gives the sharp one and an intermediate rung, so the
trade is visible: every step down in the constant is a step up in what must be assumed, and
`t₀ = 1/(c₀Γ(k_h−1)α)` is antitone in `c₀` (`tZero_anti`), so a larger constant is a strictly
smaller guaranteed time window. The "sharp `c₀`" column is the supremum of `c₀` over `Admissible`
and `0 ≤ B ≤ 1` under the stated hypothesis, evaluated numerically; the last column names the
formalized statement, whose constant may be a rounder upper bound (`10/3`, `2`).

| hypothesis | sharp `c₀` | |
|---|---|---|
| none | `4e^{9/32} ≈ 5.2991` | `cZero_le_four_mul_exp` |
| `m* ≥ 1` | `2√2·e^{9/64} ≈ 3.2555` | `cZero_le_ten_thirds_of_one_le_m` (at `10/3`) |
| `m* ≥ 2` | `2.0756` | still above 2 — `two_lt_cZero_of_m_two` |
| `m* ≥ 3` | `1.7011` | `cZero_le_two_of_three_le_m` |

`m*` is not a property of the Hamiltonian: `w* = k_o + m*(k_h−1)`, so it is chosen by the user of
the algorithm.

**Where `c₀ ≤ 2` fails on `Admissible`.** The supremum exceeds 2 at `m* ∈ {0, 1, 2}` and is below
2 from `m* = 3` on; over the reals the threshold is `m* ≈ 2.142374`. Only `m* = 0` is degenerate:
there `w* = k_o`, so the truncation **retains nothing above the observable's own weight** (it still
computes the `≤ k_o` sector). `m* = 1` and `m* = 2` are ordinary settings, and the witness
`(1, 1, 32)` of `two_lt_cZero_of_admissible` sits at `m* = 1`.

So the *unconditional supremum* `5.2991` is attained only at the degenerate point `m* = 0`, and in
that sense its size is a boundary effect. **The failure of `c₀ ≤ 2` on `Admissible` alone is not**:
it occurs at ordinary values of `m*` as well.

In summary, `m* ≥ 3` is a hypothesis on the cutoff alone, and the unconditional constant needs no
hypothesis at a cost of `2.65×` in `t₀`.
-/

/-- **The sharp unconditional bound: `c₀ ≤ 4e^{9/32} ≈ 5.2991`**, on `Admissible` and
`0 ≤ B ≤ 1` alone — no further condition on `m*`, `r` or `Γ`.

Each factor is bounded by its own extreme and **all three extremes are attained simultaneously**, at
`(r, m*, Γ, B) = (1, 0, 8, 1)`: `r ≥ 1` gives `(r+1)/r ≤ 2`; `m* ≥ 0` caps the exponent at
`9/(32(m*+1)) ≤ 9/32`; and `1/(m*+1) ≤ 1` caps the root at `1 + B ≤ 2`. So the crude
separate-factor argument loses nothing here, and `cZero_eq_four_mul_exp_at_worst` shows the value is
reached — this is a maximum, not an estimate.

Weakening `2` to this costs a factor `2.6495` in `t₀` (see `tZero_anti`), hence `2.6495^{m*+1}` in
the error bound `(t/t₀)^{m*+1}` at fixed `t`, and it shrinks `log(t₀/t)` — the denominator of
`w* = k_o + 𝒪(log(1/ε)/log(t₀/t))` — by `ln 2.6495 = 0.974`. -/
theorem cZero_le_four_mul_exp {r m G B : ℝ} (h : Admissible r m G) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    cZero r m G B ≤ 4 * exp (9 / 32) := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  have hrpos : (0 : ℝ) < r := by linarith
  have hfrac : (r + 1) / r ≤ 2 := by rw [div_le_iff₀ hrpos]; linarith
  have hrGpos : 0 < r * G := lt_of_lt_of_le (by nlinarith) hrG
  have hkey : 9 / 4 * (m + 1) / (r * G) ≤ 9 / 32 := by
    rw [div_le_iff₀ hrGpos]; nlinarith only [hrG, hm]
  have hexp : exp (9 / 4 * (m + 1) / (r * G)) ≤ exp (9 / 32) := Real.exp_le_exp.mpr hkey
  have hroot : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ 2 := by
    have h1 : (1 + B) ^ ((1 : ℝ) / (m + 1)) ≤ (1 + B) ^ (1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      rw [div_le_one (by linarith)]; linarith
    rw [Real.rpow_one] at h1; linarith
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  have hEpos : (0 : ℝ) < exp (9 / 32) := Real.exp_pos _
  unfold cZero
  have := mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos
    (by positivity)
  nlinarith only [this, hEpos]

/-- **`4e^{9/32}` is attained**, so `cZero_le_four_mul_exp` is sharp and no smaller unconditional
constant exists. `(1, 0, 8)` is admissible with `8(m*+1)² = 8 = 1·8` holding with equality, and
every one of the three factor bounds is tight there at once, so `4e^{9/32} ≈ 5.2991` is the
**maximum** of `c₀` over `Admissible` and `0 ≤ B ≤ 1`. -/
theorem cZero_eq_four_mul_exp_at_worst :
    Admissible 1 0 8 ∧ cZero 1 0 8 1 = 4 * exp (9 / 32) := by
  refine ⟨⟨le_refl 1, le_refl 0, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hroot : (1 + (1 : ℝ)) ^ ((1 : ℝ) / (0 + 1)) = 2 := by norm_num
  have harg : (9 : ℝ) / 4 * (0 + 1) / (1 * 8) = 9 / 32 := by norm_num
  unfold cZero
  rw [hroot, harg]
  ring

/-- **The intermediate rung: `c₀ ≤ 10/3` needs only `m* ≥ 1`** (on `Admissible r m G` with
`0 ≤ B ≤ 1`).

`m* ≥ 1` is the mildest nontrivial hypothesis available — it says merely that the truncation
threshold exceeds the observable's own locality, i.e. that the truncation retains Pauli operators
above the observable's own weight. The supremum there is `2√2·e^{9/64} ≈ 3.2555`, at
`(r, m*, Γ, B) = (1, 1, 32, 1)`; `10/3` is the clean bound above it, proved from `exp_factor_le`
and `root_factor_le` with no new estimate.

Against the unconditional `5.2991` this recovers a factor `1.59` of `t₀`, for a hypothesis that
excludes only the degenerate `w* = k_o`. -/
theorem cZero_le_ten_thirds_of_one_le_m {r m G B : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) : cZero r m G B ≤ 10 / 3 := by
  obtain ⟨hr, hm, hG, _, _⟩ := id h
  have hrpos : (0 : ℝ) < r := by linarith
  have hfrac : (r + 1) / r ≤ 2 := by rw [div_le_iff₀ hrpos]; linarith
  have hexp := exp_factor_le h hm1
  have hroot := root_factor_le hm1 hB0 hB1
  have hexppos : (0 : ℝ) < exp (9 / 4 * (m + 1) / (r * G)) := Real.exp_pos _
  have hrootpos : (0 : ℝ) ≤ (1 + B) ^ ((1 : ℝ) / (m + 1)) := Real.rpow_nonneg (by linarith) _
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    have h2 : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h2
  have hchain : cZero r m G B ≤ 2 * (64 / 55) * Real.sqrt 2 := by
    unfold cZero
    exact mul_le_mul (mul_le_mul hfrac hexp hexppos.le (by norm_num)) hroot hrootpos (by norm_num)
  nlinarith only [hchain, hs, Real.sqrt_nonneg 2]

end Lean4LPD
