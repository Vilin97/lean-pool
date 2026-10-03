/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The part factor `ρ(j,σ) ≤ (9/4)^{j-1}`

This file defines the part factor of the multi-jump accounting (`apd:rmk:multijump`) and proves
the bound `apd:eq:part_factor` analytically: for every part size `j ≥ 2`, every rung boundary
`σ ≥ j` and every real `c ≥ 0`.

In the multi-jump accounting a composition part of size `j` ending at rung boundary `σ` replaces
the `j` single jumps it covers, and the ratio of what it costs to what they would have cost is

  `ρ(j,σ) := ε_j^{(σ)} / ∏_{ν=σ-j+1}^{σ} ε_1^{(ν)}
           = (σ+j-1+c)^j / ( j! · ∏_{i=σ-j+1}^{σ} (i+c) )`,   `c := k_o/(k_h−1)`,

the powers of `sin(dt)` cancelling on both sides. The bound is `ρ(j,σ) ≤ (9/4)^{j-1}`.

## Main definitions

* `partFactor`: the part factor as a function of `j` and the single real variable `s = σ + c`.
* `diagFactor`: its value on the diagonal `s = j`, the sequence `(2j−1)^j/(j!)²`.

## Main results

* `partFactor_antitone`: `partFactor j` is antitone on `[j, ∞)`.
* `partFactor_at_diag`: `partFactor j j = diagFactor j`.
* `diagFactor_ratio`, `diagFactor_le`: `diagFactor (j+1) ≤ (9/4) · diagFactor j` for `j ≥ 2`, hence
  `diagFactor j ≤ (9/4)^{j-1}`.
* `partFactor_le`: `partFactor j s ≤ (9/4)^{j-1}` for `j ≥ 2` and `s ≥ j` (`apd:eq:part_factor`).

## The collapse that makes it short

`ρ` depends on `σ` and `c` only through `s := σ + c`: the denominator's factors are
`s, s−1, …, s−j+1` and the numerator is `(s+j−1)^j`. So monotonicity in `σ` and monotonicity in
`c` are **one** monotonicity in a single real variable, and it is termwise algebra rather
than calculus — writing `s' = s + d`, the `i`-th factor comparison reduces to `d·(i − 2(j−1)) ≤ 0`.
No derivative, and `c` may be any nonnegative real rather than a rational `k_o/(k_h−1)`.

The maximum is then at `s = j` (`σ = j`, `c = 0`), where `ρ = (2j−1)^j/(j!)²`, and that sequence is
below `(9/4)^{j-1}` by an induction whose ratio bound is uniform in `j`, so the result holds for
every `j ≥ 2`; the only numerical input is `exp(4/3) ≤ 4.03`. The bound is attained with equality
at `j = σ = 2`, `c = 0`.
-/

public section

namespace Lean4LPD

open Finset

/-- The **part factor**, in the single variable `s = σ + c` to which the two parameters `σ` and
`c` collapse:

  `partFactor j s = (s + j − 1)^j / ( j! · ∏_{i<j} (s − j + 1 + i) )`.

The product runs over `s−j+1, …, s`, which is the product `∏_{i=σ-j+1}^{σ}(i+c)` of the module
docstring written in increasing order so that no `ℕ` subtraction occurs. -/
@[expose]
noncomputable def partFactor (j : ℕ) (s : ℝ) : ℝ :=
  (s + j - 1) ^ j / ((Nat.factorial j : ℝ) * ∏ i ∈ range j, (s - j + 1 + i))

lemma partFactor_denom_pos {j : ℕ} {s : ℝ} (hs : (j : ℝ) ≤ s) :
    0 < ∏ i ∈ range j, (s - j + 1 + i) := by
  refine Finset.prod_pos fun i _ => ?_
  have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

/-- **The one monotonicity.** `partFactor j` is antitone on `[j, ∞)`. This is monotonicity in the
boundary `σ` and in `c` at once, since `ρ` depends on them only through `s = σ + c`; it is what
places the maximum at `σ = j`, `c = 0`. The proof is termwise: with `s' = s + d`, `d ≥ 0`, the
`i`-th factor comparison is `d · (i − 2(j−1)) ≤ 0`, which holds because `i < j`. -/
theorem partFactor_antitone {j : ℕ} {s s' : ℝ} (hj : 1 ≤ j) (hs : (j : ℝ) ≤ s) (hss : s ≤ s') :
    partFactor j s' ≤ partFactor j s := by
  have hs' : (j : ℝ) ≤ s' := le_trans hs hss
  have hPpos := partFactor_denom_pos hs
  have hP'pos := partFactor_denom_pos hs'
  have hjfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  -- the key termwise product inequality
  have hkey : (s' + j - 1) ^ j * ∏ i ∈ range j, (s - j + 1 + i)
      ≤ (s + j - 1) ^ j * ∏ i ∈ range j, (s' - j + 1 + i) := by
    have hL : (s' + j - 1) ^ j * ∏ i ∈ range j, (s - j + 1 + i)
        = ∏ i ∈ range j, ((s' + j - 1) * (s - j + 1 + i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hR : (s + j - 1) ^ j * ∏ i ∈ range j, (s' - j + 1 + i)
        = ∏ i ∈ range j, ((s + j - 1) * (s' - j + 1 + i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hL, hR]
    refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
    · have hi' : (i : ℝ) ≥ 0 := Nat.cast_nonneg i
      have h1 : (0 : ℝ) ≤ s - j + 1 + i := by linarith
      nlinarith [h1, hs']
    · rw [Finset.mem_range] at hi
      have hij : (i : ℝ) ≤ (j : ℝ) - 1 := by
        have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hi
        linarith
      nlinarith [hss, hij, hj1]
  unfold partFactor
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, hjfac, hPpos, hP'pos]

/-- `∏_{i<n} (i+1) = n!`, over `ℝ`. -/
lemma prod_range_add_one_cast (n : ℕ) : ∏ i ∈ range n, ((i : ℝ) + 1) = (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- The maximum, at `s = j` (`σ = j`, `c = 0`): `ρ(j,j)|_{c=0} = (2j−1)^j/(j!)²`, which is
`diagFactor j`. -/
lemma partFactor_at_diag (j : ℕ) : partFactor j (j : ℝ)
    = (2 * (j : ℝ) - 1) ^ j / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)) := by
  unfold partFactor
  have hprod : ∏ i ∈ range j, ((j : ℝ) - j + 1 + i) = (Nat.factorial j : ℝ) := by
    rw [← prod_range_add_one_cast j]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hprod]
  congr 1
  ring

/-- `exp(4/3) ≤ 4.03`, the one numeric fact the induction below needs. Obtained from
`exp x ≤ 1/(1-x)` at `x = 1/12` and `exp(4/3) = exp(1/12)^16 ≤ (12/11)^16 = 4.0237`. -/
lemma exp_four_thirds_le : Real.exp (4 / 3 : ℝ) ≤ 4.03 := by
  have h12 : Real.exp (1 / 12 : ℝ) ≤ 12 / 11 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 12 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hmul : Real.exp (((16 : ℕ) : ℝ) * (1 / 12 : ℝ)) = Real.exp (1 / 12 : ℝ) ^ (16 : ℕ) :=
    Real.exp_nat_mul _ 16
  have harg : ((16 : ℕ) : ℝ) * (1 / 12 : ℝ) = 4 / 3 := by norm_num
  rw [harg] at hmul
  rw [hmul]
  calc Real.exp (1 / 12 : ℝ) ^ (16 : ℕ)
      ≤ (12 / 11 : ℝ) ^ (16 : ℕ) := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h12 16
    _ ≤ 4.03 := by norm_num

/-- The diagonal sequence `f j = (2j−1)^j/(j!)²`. -/
noncomputable def diagFactor (j : ℕ) : ℝ :=
  (2 * (j : ℝ) - 1) ^ j / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ))

lemma diagFactor_pos {j : ℕ} (hj : 1 ≤ j) : 0 < diagFactor j := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  unfold diagFactor
  apply div_pos (pow_pos (by linarith) j) (by positivity)

/-- The uniform ratio bound: `f(j+1) ≤ (9/4) f(j)` for every `j ≥ 2`, where `f = diagFactor`.
`((2j+1)/(2j−1))^j ≤ exp(2j/(2j−1)) ≤ exp(4/3) ≤ 4.03`, and `(2j+1)·4.03 ≤ (9/4)(j+1)²` for
`j ≥ 2`. -/
lemma diagFactor_ratio {j : ℕ} (hj : 2 ≤ j) : diagFactor (j + 1) ≤ 9 / 4 * diagFactor j := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpos : (0 : ℝ) < 2 * (j : ℝ) - 1 := by linarith
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  -- ((2j+1)/(2j-1))^j = (1 + 2/(2j-1))^j <= exp(2j/(2j-1)) <= exp(4/3)
  have hratio : ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j ≤ 4.03 := by
    have hbase : (2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1) ≤ Real.exp (2 / (2 * (j : ℝ) - 1)) := by
      have h := Real.add_one_le_exp (2 / (2 * (j : ℝ) - 1))
      rw [div_le_iff₀ hpos]
      have hd : 2 / (2 * (j : ℝ) - 1) * (2 * (j : ℝ) - 1) = 2 := by field_simp
      nlinarith [h, Real.exp_pos (2 / (2 * (j : ℝ) - 1)), hd]
    have hb0 : (0 : ℝ) ≤ (2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1) := by positivity
    have hpow : ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
        ≤ Real.exp (2 / (2 * (j : ℝ) - 1)) ^ j := pow_le_pow_left₀ hb0 hbase j
    have hexp : Real.exp (2 / (2 * (j : ℝ) - 1)) ^ j
        = Real.exp ((j : ℝ) * (2 / (2 * (j : ℝ) - 1))) := (Real.exp_nat_mul _ j).symm
    have harg : (j : ℝ) * (2 / (2 * (j : ℝ) - 1)) ≤ 4 / 3 := by
      have hre : (j : ℝ) * (2 / (2 * (j : ℝ) - 1)) = 2 * (j : ℝ) / (2 * (j : ℝ) - 1) := by ring
      rw [hre, div_le_iff₀ hpos]
      linarith [hj2]
    calc ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
        ≤ Real.exp (2 / (2 * (j : ℝ) - 1)) ^ j := hpow
      _ = Real.exp ((j : ℝ) * (2 / (2 * (j : ℝ) - 1))) := hexp
      _ ≤ Real.exp (4 / 3) := Real.exp_le_exp.mpr harg
      _ ≤ 4.03 := exp_four_thirds_le
  -- assemble
  have hnum : (2 * ((j : ℝ) + 1) - 1) ^ (j + 1)
      = (2 * (j : ℝ) + 1) * ((2 * (j : ℝ) - 1) ^ j
          * ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j) := by
    rw [div_pow, ← mul_div_assoc, mul_comm ((2 * (j:ℝ) - 1) ^ j), mul_div_assoc,
      div_self (by positivity), mul_one]
    have : (2 * ((j : ℝ) + 1) - 1) = 2 * (j : ℝ) + 1 := by ring
    rw [this, pow_succ]
    ring
  have hfacsucc : (Nat.factorial (j + 1) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hcast : ((j : ℕ) : ℝ) + 1 = (((j + 1 : ℕ)) : ℝ) := by push_cast; ring
  have hp : (0 : ℝ) < (2 * (j : ℝ) - 1) ^ j := pow_pos hpos j
  unfold diagFactor
  rw [hfacsucc, ← hcast, hnum]
  have hrhs : 9 / 4 * ((2 * (j : ℝ) - 1) ^ j / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)))
      = (9 / 4 * (2 * (j : ℝ) - 1) ^ j) / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)) := by
    ring
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hquad : (2 * (j : ℝ) + 1) * 4.03 ≤ 9 / 4 * ((j : ℝ) + 1) ^ 2 := by
    nlinarith [hj2, sq_nonneg ((j : ℝ) - 2)]
  have hkey : (2 * (j : ℝ) + 1) * ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
      ≤ 9 / 4 * ((j : ℝ) + 1) ^ 2 := by
    have h1 : (2 * (j : ℝ) + 1) * ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) - 1)) ^ j
        ≤ (2 * (j : ℝ) + 1) * 4.03 := mul_le_mul_of_nonneg_left hratio (by linarith)
    linarith [hquad]
  have hBF : (0 : ℝ) < (2 * (j : ℝ) - 1) ^ j
      * ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hkey (le_of_lt hBF)]

/-- **`(2j−1)^j/(j!)² ≤ (9/4)^{j-1}` for every `j ≥ 2`**, with equality at `j = 2`, where both
sides are `9/4`. By induction on `j` from the uniform ratio bound `diagFactor_ratio`. -/
theorem diagFactor_le (j : ℕ) (hj : 2 ≤ j) : diagFactor j ≤ (9 / 4 : ℝ) ^ (j - 1) := by
  induction j with
  | zero => omega
  | succ n ih =>
    match n, hj with
    | 1, _ =>
      norm_num [diagFactor, Nat.factorial]
    | (n + 2), _ =>
      have hn : 2 ≤ n + 2 := by omega
      have hstep := diagFactor_ratio (j := n + 2) hn
      have hih := ih hn
      have hpow : (9 / 4 : ℝ) ^ (n + 2 - 1) = (9 / 4 : ℝ) ^ (n + 1) := by norm_num
      have hgoal : (9 / 4 : ℝ) ^ (n + 2 + 1 - 1) = 9 / 4 * (9 / 4 : ℝ) ^ (n + 1) := by
        have : n + 2 + 1 - 1 = (n + 1) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [hgoal]
      rw [hpow] at hih
      linarith [hstep, hih]

/-- **The part-factor bound** (`apd:eq:part_factor`). For every part size `j ≥ 2` and every
boundary `s = σ + c ≥ j`,

  `ρ(j,σ) ≤ (9/4)^{j-1}`,

with equality at `j = σ = 2`, `c = 0`. The proof descends to the diagonal `s = j` by
`partFactor_antitone` and concludes with `diagFactor_le`; it is analytic throughout and covers
every `j ≥ 2`, every `σ ≥ j` and every real `c ≥ 0`. -/
theorem partFactor_le {j : ℕ} {s : ℝ} (hj : 2 ≤ j) (hs : (j : ℝ) ≤ s) :
    partFactor j s ≤ (9 / 4 : ℝ) ^ (j - 1) :=
  calc partFactor j s ≤ partFactor j (j : ℝ) :=
        partFactor_antitone (by omega) (le_refl _) hs
    _ = diagFactor j := partFactor_at_diag j
    _ ≤ (9 / 4 : ℝ) ^ (j - 1) := diagFactor_le j hj

end Lean4LPD
