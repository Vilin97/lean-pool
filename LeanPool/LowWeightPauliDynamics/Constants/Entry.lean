/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The entry factor `E_ν ≤ ε_ν^{(ν)}(1 + 2β)`

This file defines the scalar quantities of the multi-jump analysis (`apd:rmk:multijump`) — the
rung weights `w_m`, the `j`-jump block norms `ε_j^{(ν)}`, the expansion parameter `β` and the
entry factor `E_ν` of `apd:eq:composition_majorant` — and proves the entry-factor bound
`apd:eq:entry_bound` with the constant `2` where the paper has `4e`.

A single layer may act on one Pauli with `j` anti-commuting rotations, raising it by `j` rungs in
one step. Such a jump may *overshoot* the ladder: a Pauli below rung 1 — weight `≤ w₁`, its norm
controlled by the reservoir bound `‖O‖` — may end above rung `ν` after one layer; this needs
`j > ν` and is therefore not a composition of `ν`. All of these contributions are collected in
the **entry factor**

  `E_ν := ∑_{j≥ν} ε_j^{(ν)}`,  `ε_j^{(ν)} := (w_{ν+j} · sin dt)^j / j!`,

which the paper bounds by `E_ν ≤ ε_ν^{(ν)}(1 + 4eβ)` for `β := 2e w₂ sin(dt) ≤ 1/2`.

## Main definitions

* `rungW`: the rung weight `w_m = (k_h − 1)(m − 1 + c)`, `c = k_o/(k_h − 1)`.
* `epsJump`: the `j`-jump block norm `ε_j^{(ν)}`.
* `betaOf`: the expansion parameter `β = 2e·w₂·a`.
* `entryFactor`: the entry factor `E_ν`, an infinite sum.

## Main results

* `epsJump_ratio`: `ε_{j+1}^{(ν)} ≤ β · ε_j^{(ν)}` for `j ≥ ν ≥ 1`.
* `entryFactor_le_geom`: `E_ν ≤ ε_ν^{(ν)}/(1 − β)` for every `β < 1`.
* `entryFactor_le`: `E_ν ≤ ε_ν^{(ν)}(1 + 2β)` for `β ≤ 1/2` (`apd:eq:entry_bound`).
* `one_add_two_mul_le_source`: `1 + 2β ≤ 1 + 4eβ`, the comparison with the paper's constant.

## The proof: geometric decay of the terms

The *terms* of `E_ν` decay geometrically with ratio `β`,

  `ε_{j+1}^{(ν)} ≤ β · ε_j^{(ν)}`  for every `j ≥ ν ≥ 1`,

because `(w_{ν+j+1}/w_{ν+j})^j ≤ (1 + 1/j)^j ≤ e` and `w_{ν+j+1}·a/(j+1) ≤ 2w₂a = β/e`. Summing
the geometric series gives `E_ν ≤ ε_ν^{(ν)}/(1 − β)`, hence `≤ ε_ν^{(ν)}(1 + 2β)` for `β ≤ 1/2`.
This is **stronger than the paper's statement** `(1 + 4eβ)`, since `4e ≈ 10.87`, and implies it.
The hypothesis `β ≤ 1/2` is not needed for the geometric form: `E_ν ≤ ε_ν^{(ν)}/(1−β)` holds for
every `β < 1`, a larger range than the paper's parameter regime. In that regime the step-count
condition `r ≥ 8e²·w₂·αt` of `apd:eq:multijump_factor`, together with `sin(dt) ≤ αt/r`, gives
`4eβ ≤ 1`, i.e. `β ≤ 1/(4e) < 1/2`, so the hypothesis of `entryFactor_le` is always available
there.

The constant `1 + 2β` is smaller than the paper's `1 + 4eβ`; the bound `c₀ ≤ 2` of
`Lean4LPD.cZero_le_two` is proved with the paper's constant. See `Lean4LPD.Constants.C0`.

`k_o = 0` (hence `c = 0`, hence `w₁ = 0`) is the extremal case of the estimates below, not an
exception to them; only `k_h ≥ 2`, i.e. `k_h − 1 > 0`, is required.
-/

@[expose] public section

namespace Lean4LPD

open Finset

/-- The rung weight `w_m = (k_h − 1)(m − 1 + c)` with `c = k_o/(k_h − 1)`, that is
`w_m = k_o + (m − 1)(k_h − 1)`: the largest weight reachable from weight `k_o` with `m − 1`
anti-commuting `k_h`-local rotations, and the threshold of rung `m` in
`apd:eq:def_high_weight_norm`. It is real-valued so that no `ℕ` subtraction occurs. `kh1` is
`k_h − 1`. Note `w₂ = (k_h−1)(1+c) = k_o+k_h−1`. -/
def rungW (kh1 c : ℝ) (m : ℕ) : ℝ := kh1 * ((m : ℝ) - 1 + c)

/-- The `j`-jump block norm into rung `ν`, `ε_j^{(ν)} = (w_{ν+j}·a)^j / j!`
(`apd:rmk:multijump`), with `a = sin(dt)`. -/
noncomputable def epsJump (kh1 c a : ℝ) (j nu : ℕ) : ℝ :=
  (rungW kh1 c (nu + j) * a) ^ j / (Nat.factorial j : ℝ)

/-- The expansion parameter `β = 2e·w₂·a` of the multi-jump analysis (`apd:rmk:multijump`),
with `a = sin(dt)`. -/
noncomputable def betaOf (kh1 c a : ℝ) : ℝ := 2 * Real.exp 1 * rungW kh1 c 2 * a

lemma rungW_nonneg {kh1 c : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ rungW kh1 c m := by
  have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold rungW
  have : (0 : ℝ) ≤ (m : ℝ) - 1 + c := by linarith
  positivity

lemma epsJump_nonneg {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (j nu : ℕ)
    (h : 1 ≤ nu + j) : 0 ≤ epsJump kh1 c a j nu := by
  have hW := rungW_nonneg hkh hc h
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  unfold epsJump
  positivity

/-- `(1 + 1/j)^j ≤ e` for `j ≥ 1`. -/
lemma one_add_inv_pow_le_exp_one {j : ℕ} (hj : 1 ≤ j) :
    (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp 1 := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hb : (1 : ℝ) + 1 / (j : ℝ) ≤ Real.exp (1 / (j : ℝ)) := by
    have := Real.add_one_le_exp (1 / (j : ℝ))
    linarith
  have hb0 : (0 : ℝ) ≤ 1 + 1 / (j : ℝ) := by positivity
  calc (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp (1 / (j : ℝ)) ^ j :=
        pow_le_pow_left₀ hb0 hb j
    _ = Real.exp ((j : ℝ) * (1 / (j : ℝ))) := (Real.exp_nat_mul _ j).symm
    _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hjpos)]

/-- **The term-ratio bound**: for `j ≥ ν ≥ 1`,

  `ε_{j+1}^{(ν)} ≤ β · ε_j^{(ν)}`.

This geometric decay of the terms is what drives `entryFactor_le_geom`. Two estimates, both
termwise: `w_{ν+j+1} ≤ w_{ν+j}·(1 + 1/j)` because `ν+j−1+c ≥ j`, and
`w_{ν+j+1} ≤ w₂·(ν+j) ≤ 2w₂·j` because `ν ≤ j`. -/
theorem epsJump_ratio {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {j nu : ℕ} (hnu : 1 ≤ nu) (hj : nu ≤ j) :
    epsJump kh1 c a (j + 1) nu ≤ betaOf kh1 c a * epsJump kh1 c a j nu := by
  have hj1 : 1 ≤ j := le_trans hnu hj
  have hnuR : (1 : ℝ) ≤ (nu : ℝ) := by exact_mod_cast hnu
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hnujR : (nu : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  set W := rungW kh1 c (nu + j) with hWdef
  set W' := rungW kh1 c (nu + j + 1) with hW'def
  set w2 := rungW kh1 c 2 with hw2def
  have hcast1 : ((nu + j : ℕ) : ℝ) = (nu : ℝ) + (j : ℝ) := by push_cast; ring
  have hcast2 : ((nu + j + 1 : ℕ) : ℝ) = (nu : ℝ) + (j : ℝ) + 1 := by push_cast; ring
  have hWval : W = kh1 * ((nu : ℝ) + (j : ℝ) - 1 + c) := by
    rw [hWdef]; unfold rungW; rw [hcast1]
  have hW'val : W' = kh1 * ((nu : ℝ) + (j : ℝ) + c) := by
    rw [hW'def]; unfold rungW; rw [hcast2]; ring_nf
  have hw2val : w2 = kh1 * (1 + c) := by
    rw [hw2def]; unfold rungW; norm_num
  have hWpos : 0 < W := by
    rw [hWval]
    have : (1 : ℝ) ≤ (nu : ℝ) + (j : ℝ) - 1 + c := by linarith
    have h2 : (0 : ℝ) < (nu : ℝ) + (j : ℝ) - 1 + c := by linarith
    positivity
  have hW'nonneg : 0 ≤ W' := by
    rw [hW'val]
    have : (0 : ℝ) ≤ (nu : ℝ) + (j : ℝ) + c := by linarith
    positivity
  -- estimate 1: W' ≤ W * (1 + 1/j)
  have hest1 : W' ≤ W * (1 + 1 / (j : ℝ)) := by
    rw [hWval, hW'val]
    have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
    have hkey : (nu : ℝ) + (j : ℝ) + c
        ≤ ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 + 1 / (j : ℝ)) := by
      have hd : (1 : ℝ) ≤ ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 / (j : ℝ)) := by
        rw [mul_one_div, le_div_iff₀ hjpos]
        linarith [hnuR, hc]
      have hexpand : ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 + 1 / (j : ℝ))
          = ((nu : ℝ) + (j : ℝ) - 1 + c) + ((nu : ℝ) + (j : ℝ) - 1 + c) * (1 / (j : ℝ)) := by
        ring
      rw [hexpand]
      linarith [hd]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hkey hkh.le
  -- estimate 2: W' ≤ 2 * w2 * j
  have hest2 : W' ≤ 2 * w2 * (j : ℝ) := by
    rw [hW'val, hw2val]
    have h1 : (nu : ℝ) + (j : ℝ) + c ≤ (1 + c) * (2 * (j : ℝ)) := by
      nlinarith only [hnujR, hjR, hc]
    calc
      _ ≤ kh1 * ((1 + c) * (2 * (j : ℝ))) := mul_le_mul_of_nonneg_left h1 hkh.le
      _ = _ := by ring
  -- assemble
  have hfacj : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfacj1 : (Nat.factorial (j + 1) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpowj : (W' * a) ^ j ≤ (W * (1 + 1 / (j : ℝ)) * a) ^ j :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hest1 ha) j
  have hsplit : (W * (1 + 1 / (j : ℝ)) * a) ^ j = (W * a) ^ j * (1 + 1 / (j : ℝ)) ^ j := by
    rw [show W * (1 + 1 / (j : ℝ)) * a = (W * a) * (1 + 1 / (j : ℝ)) by ring, mul_pow]
  have hexp := one_add_inv_pow_le_exp_one hj1
  have hWa : (0 : ℝ) ≤ (W * a) ^ j := by positivity
  have hchain : (W' * a) ^ j ≤ (W * a) ^ j * Real.exp 1 := by
    calc (W' * a) ^ j ≤ (W * (1 + 1 / (j : ℝ)) * a) ^ j := hpowj
      _ = (W * a) ^ j * (1 + 1 / (j : ℝ)) ^ j := hsplit
      _ ≤ (W * a) ^ j * Real.exp 1 := by
          exact mul_le_mul_of_nonneg_left hexp hWa
  -- (W'a)^{j+1} = (W'a)^j * (W'a) <= (Wa)^j * e * 2 w2 a * (j+1)
  have hlast : (W' * a) ^ (j + 1) ≤ (W * a) ^ j * Real.exp 1 * (2 * w2 * a) * ((j : ℝ) + 1) := by
    have hW'a : (0 : ℝ) ≤ W' * a := by positivity
    have h1 : W' * a ≤ 2 * w2 * a * (j : ℝ) := by
      calc
        _ ≤ (2 * w2 * (j : ℝ)) * a := mul_le_mul_of_nonneg_right hest2 ha
        _ = _ := by ring
    have h2 : (W' * a) ^ (j + 1) = (W' * a) ^ j * (W' * a) := by rw [pow_succ]
    have hep : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
    have hw2a : (0 : ℝ) ≤ 2 * w2 * a := by
      have : 0 ≤ w2 := by rw [hw2val]; positivity
      positivity
    calc (W' * a) ^ (j + 1) = (W' * a) ^ j * (W' * a) := h2
      _ ≤ ((W * a) ^ j * Real.exp 1) * (2 * w2 * a * (j : ℝ)) := by
          apply mul_le_mul hchain h1 hW'a (by positivity)
      _ ≤ (W * a) ^ j * Real.exp 1 * (2 * w2 * a) * ((j : ℝ) + 1) := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num))
              (mul_nonneg (mul_nonneg hWa hep) hw2a)
  -- convert to the statement
  have hnucast : nu + (j + 1) = nu + j + 1 := by omega
  unfold epsJump betaOf
  rw [hnucast, ← hW'def, ← hWdef, ← hw2def, hfacj1]
  have hrhs : 2 * Real.exp 1 * w2 * a * ((W * a) ^ j / (Nat.factorial j : ℝ))
      = (2 * Real.exp 1 * w2 * a * (W * a) ^ j) / (Nat.factorial j : ℝ) := by ring
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right hlast hfacj.le]

/-- The entry factor `E_ν = ∑_{j≥ν} ε_j^{(ν)}` of `apd:eq:composition_majorant`, written as a
`tsum` over the shift `j = ν + i`. This is the only infinite sum in the multi-jump development;
the ladder itself takes `E` abstractly (see `Lean4LPD.MultiLadder`). -/
noncomputable def entryFactor (kh1 c a : ℝ) (nu : ℕ) : ℝ :=
  ∑' i : ℕ, epsJump kh1 c a (nu + i) nu

/-- **The entry-factor bound, geometric form.** For every `β < 1`,

  `E_ν ≤ ε_ν^{(ν)} / (1 − β)`.

No `β ≤ 1/2` is needed; that hypothesis enters only in converting to the affine form
`entryFactor_le`. The proof sums the geometric majorant supplied by `epsJump_ratio`. -/
theorem entryFactor_le_geom {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {nu : ℕ} (hnu : 1 ≤ nu) (hb1 : betaOf kh1 c a < 1) :
    entryFactor kh1 c a nu ≤ epsJump kh1 c a nu nu / (1 - betaOf kh1 c a) := by
  set b := betaOf kh1 c a with hbdef
  have hb0 : 0 ≤ b := by
    rw [hbdef]; unfold betaOf
    have hw2 : 0 ≤ rungW kh1 c 2 := rungW_nonneg hkh hc (by omega)
    have := Real.exp_pos 1
    positivity
  set u : ℕ → ℝ := fun i => epsJump kh1 c a (nu + i) nu with hudef
  have hu0 : ∀ i, 0 ≤ u i := fun i =>
    epsJump_nonneg hkh hc ha (nu + i) nu (by omega)
  have hstep : ∀ i, u (i + 1) ≤ b * u i := by
    intro i
    have h := epsJump_ratio hkh hc ha (j := nu + i) (nu := nu) hnu (by omega)
    have hidx : nu + i + 1 = nu + (i + 1) := by omega
    rw [hidx] at h
    exact h
  have hgeom : ∀ i, u i ≤ b ^ i * u 0 := fun i => le_geom hb0 i fun k _ => hstep k
  have hsummable : Summable (fun i : ℕ => b ^ i) := summable_geometric_of_lt_one hb0 hb1
  have hpartial : ∀ n : ℕ, ∑ i ∈ range n, u i ≤ u 0 / (1 - b) := by
    intro n
    have h1 : ∑ i ∈ range n, u i ≤ ∑ i ∈ range n, b ^ i * u 0 :=
      Finset.sum_le_sum fun i _ => hgeom i
    have h2 : ∑ i ∈ range n, b ^ i * u 0 = (∑ i ∈ range n, b ^ i) * u 0 := by
      rw [Finset.sum_mul]
    have h3 : ∑ i ∈ range n, b ^ i ≤ ∑' i : ℕ, b ^ i :=
      hsummable.sum_le_tsum _ (fun i _ => pow_nonneg hb0 i)
    have h4 : ∑' i : ℕ, b ^ i = (1 - b)⁻¹ := tsum_geometric_of_lt_one hb0 hb1
    have h5 : (0 : ℝ) < 1 - b := by linarith
    calc ∑ i ∈ range n, u i ≤ (∑ i ∈ range n, b ^ i) * u 0 := by rw [← h2]; exact h1
      _ ≤ (1 - b)⁻¹ * u 0 := by
          exact mul_le_mul_of_nonneg_right (by rw [← h4]; exact h3) (hu0 0)
      _ = u 0 / (1 - b) := by rw [inv_mul_eq_div]
  have hzero : u 0 = epsJump kh1 c a nu nu := by simp [hudef]
  have := Real.tsum_le_of_sum_range_le hu0 hpartial
  rw [← hzero]
  exact this

/-- **The entry-factor bound, affine form** (`apd:eq:entry_bound`):

  `E_ν ≤ ε_ν^{(ν)} · (1 + 2β)`  for `β ≤ 1/2`.

The constant `2` is stronger than the paper's statement, which has `4e ≈ 10.87` in its place.
Since `1 + 2β ≤ 1 + 4eβ` for `β ≥ 0` (`one_add_two_mul_le_source`), the bound with `(1 + 4eβ)`
follows, so every downstream use of that factor remains valid. -/
theorem entryFactor_le {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {nu : ℕ} (hnu : 1 ≤ nu) (hb : betaOf kh1 c a ≤ 1 / 2) :
    entryFactor kh1 c a nu ≤ epsJump kh1 c a nu nu * (1 + 2 * betaOf kh1 c a) := by
  set b := betaOf kh1 c a with hbdef
  have hb0 : 0 ≤ b := by
    rw [hbdef]; unfold betaOf
    have hw2 : 0 ≤ rungW kh1 c 2 := rungW_nonneg hkh hc (by omega)
    have := Real.exp_pos 1
    positivity
  have hb1 : b < 1 := by linarith
  have hgeom := entryFactor_le_geom hkh hc ha hnu (by rw [← hbdef] at *; linarith)
  have heps : 0 ≤ epsJump kh1 c a nu nu :=
    epsJump_nonneg hkh hc ha nu nu (by omega)
  have hkey : epsJump kh1 c a nu nu / (1 - b)
      ≤ epsJump kh1 c a nu nu * (1 + 2 * b) := by
    rw [div_le_iff₀ (by linarith)]
    have hprod : (0 : ℝ) ≤ epsJump kh1 c a nu nu * (b * (1 - 2 * b)) :=
      mul_nonneg heps (mul_nonneg hb0 (by linarith))
    nlinarith [hprod]
  rw [← hbdef] at hgeom
  linarith [hgeom, hkey]

/-- Comparison with the paper's constant: `1 + 2β ≤ 1 + 4eβ`, since `2 ≤ 4e`. Stated as a lemma
so that the sharpening in `entryFactor_le` is a checked comparison rather than prose only. -/
lemma one_add_two_mul_le_source {b : ℝ} (hb : 0 ≤ b) :
    1 + 2 * b ≤ 1 + 4 * Real.exp 1 * b := by
  have h : (2 : ℝ) ≤ 4 * Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  nlinarith [hb, h]

end Lean4LPD
