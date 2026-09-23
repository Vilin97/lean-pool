/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import LeanPool.LowWeightPauliDynamics.Constants.PartFactor
import LeanPool.LowWeightPauliDynamics.Ladder.ChainBound

/-!
# Concrete single-jump weights for the multi-jump chain bound

This file instantiates the abstract composition count `chain_le_weighted_choose` with the
concrete jump norms `epsJump` and entry factor `entryFactor` of `apd:rmk:multijump`. The
reference weight is the all-ones chain weight `a^m ∏_{ν=2}^{m+1} w_ν`, the weight carried in
`apd:eq:composition_majorant` by the chain of `m` single jumps.

The file connects `epsJump`, `entryFactor` and `partFactor_le` to that product. The key
identities multiply through the positive part-factor denominator and never divide by `a` or by
the all-ones weight. The zero angle `a = 0` is therefore included, which a statement of
`apd:eq:part_factor` as a ratio of jump weights would not cover.

## Main definitions

* `chainWeight kh1 c a m`: the all-ones chain weight `a^m ∏_{ν=2}^{m+1} w_ν`.

## Main results

* `epsJump_mul_chainWeight_eq_partFactor`: a `j`-jump into rung `m` times the all-ones weight of
  rung `m - j` equals the part factor times the all-ones weight of rung `m`, including `a = 0`.
* `epsJump_mul_chainWeight_le`: hence a `j`-jump weighs no more than `(9/4)^{j-1}` times the
  `j` single jumps that cover the same rungs.
* `entryFactor_le_chainWeight`: the entry factor is at most `(1 + 2β) (9/4)^{m-1}` times the
  all-ones weight.
* `chain_epsJump_le_weighted_choose`: the composition count for the concrete chain, with the
  entry inflation charged once.
* `entryFactor_le_chainWeight_source`, `chain_epsJump_le_weighted_choose_source`: the same two
  bounds with the paper's entry constant `1 + 4eβ` in place of `1 + 2β`.
-/

namespace Lean4LPD

open Finset

/-- The all-ones chain weight `a^m ∏_{ν=2}^{m+1} w_ν`, with value `1` at `m = 0`. It is the
weight of the chain of `m` single jumps in `apd:eq:composition_majorant`, and the reference
weight `W` of `chain_le_weighted_choose` in `apd:eq:total_high_weight_norm`. -/
noncomputable def chainWeight (kh1 c a : ℝ) (m : ℕ) : ℝ :=
  a ^ m * ∏ i ∈ range m, rungW kh1 c (i + 2)

/-- The empty all-ones chain has weight one, as required for the reservoir entry in
`apd:eq:composition_majorant`. -/
@[simp] theorem chainWeight_zero (kh1 c a : ℝ) : chainWeight kh1 c a 0 = 1 := by
  simp [chainWeight]

/-- All-ones weights are nonnegative for the physical nonnegative angle parameter.
Supporting lemma for `apd:eq:total_high_weight_norm`. -/
theorem chainWeight_nonneg {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (m : ℕ) : 0 ≤ chainWeight kh1 c a m := by
  apply mul_nonneg (pow_nonneg ha m)
  exact Finset.prod_nonneg fun i _ => rungW_nonneg hkh hc (by omega)

/-- Splitting off the final `j` single jumps, with no cancellation of the angle parameter.
Supporting algebra for `apd:eq:part_factor`. -/
theorem chainWeight_split (kh1 c a : ℝ) {j m : ℕ} (hjm : j ≤ m) :
    chainWeight kh1 c a m = a ^ j * chainWeight kh1 c a (m - j)
      * ∏ i ∈ range j, rungW kh1 c (m - j + i + 2) := by
  have hprod := Finset.prod_range_add (fun i => rungW kh1 c (i + 2)) (m - j) j
  rw [Nat.sub_add_cancel hjm] at hprod
  have hpow : a ^ j * a ^ (m - j) = a ^ m := by
    rw [← pow_add]
    congr 1
    omega
  unfold chainWeight
  rw [hprod, ← hpow]
  ring

/-- The final `j` rung factors have exactly the denominator product in `partFactor j (m+c)`.
Supporting algebra for `apd:eq:part_factor`. -/
theorem chainWeight_tail_rungs (kh1 c : ℝ) {j m : ℕ} (hjm : j ≤ m) :
    (∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
      = kh1 ^ j * ∏ i ∈ range j, ((m : ℝ) + c - j + 1 + i) := by
  have hterm : ∀ i : ℕ, rungW kh1 c (m - j + i + 2)
      = kh1 * ((m : ℝ) + c - j + 1 + i) := by
    intro i
    unfold rungW
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hjm]
    push_cast
    ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- Multiplying the part factor by its rung product gives the `j`-jump numerator
`w_{m+j}^j / j!`. This is the division-free-in-angle version of `apd:eq:part_factor`. -/
theorem partFactor_mul_tail_rungs {c : ℝ} (hc : 0 ≤ c) (kh1 : ℝ)
    {j m : ℕ} (hjm : j ≤ m) :
    partFactor j ((m : ℝ) + c) * (∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
      = rungW kh1 c (m + j) ^ j / (Nat.factorial j : ℝ) := by
  have hmc : (j : ℝ) ≤ (m : ℝ) + c := by
    exact (by exact_mod_cast hjm : (j : ℝ) ≤ m).trans (le_add_of_nonneg_right hc)
  have hQ : (∏ i ∈ range j, ((m : ℝ) + c - j + 1 + i)) ≠ 0 :=
    ne_of_gt (partFactor_denom_pos hmc)
  have hfac : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnum : rungW kh1 c (m + j) = kh1 * ((m : ℝ) + c + j - 1) := by
    unfold rungW
    push_cast
    ring
  rw [partFactor, chainWeight_tail_rungs kh1 c hjm, hnum, mul_pow]
  field_simp [hQ, hfac]

/-- **The jump/all-ones identity, including `a = 0`.**
This supplies the algebra behind `apd:eq:part_factor`, without dividing
by a possibly-zero angle factor or all-ones weight. The endpoint `j=m` is allowed and
is exactly the reservoir-entry comparison. -/
theorem epsJump_mul_chainWeight_eq_partFactor {c : ℝ} (hc : 0 ≤ c) (kh1 a : ℝ)
    {j m : ℕ} (hjm : j ≤ m) :
    epsJump kh1 c a j m * chainWeight kh1 c a (m - j)
      = partFactor j ((m : ℝ) + c) * chainWeight kh1 c a m := by
  rw [chainWeight_split kh1 c a hjm, epsJump, mul_pow]
  calc (rungW kh1 c (m + j) ^ j * a ^ j / (Nat.factorial j : ℝ))
        * chainWeight kh1 c a (m - j)
      = (rungW kh1 c (m + j) ^ j / (Nat.factorial j : ℝ))
          * (a ^ j * chainWeight kh1 c a (m - j)) := by ring
    _ = (partFactor j ((m : ℝ) + c)
          * ∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
          * (a ^ j * chainWeight kh1 c a (m - j)) := by
        rw [partFactor_mul_tail_rungs hc kh1 hjm]
    _ = _ := by ring

/-- The size-one part factor is exactly one for a positive boundary, rather than merely
bounded by a multi-jump constant. Supporting endpoint of `apd:eq:part_factor`. -/
theorem partFactor_one {s : ℝ} (hs : 0 < s) : partFactor 1 s = 1 := by
  simp [partFactor, ne_of_gt hs]

/-- The part-factor estimate including single jumps. The `j≥2` part is `partFactor_le`;
the `j=1` part is exact. Supporting theorem for `apd:eq:part_factor`. -/
theorem partFactor_le_of_one_le {j : ℕ} {s : ℝ} (hj : 1 ≤ j) (hs : (j : ℝ) ≤ s) :
    partFactor j s ≤ (9 / 4 : ℝ) ^ (j - 1) := by
  by_cases hj1 : j = 1
  · subst j
    rw [partFactor_one (by norm_num at hs; linarith)]
    norm_num
  · exact partFactor_le (by omega) hs

/-- **Every concrete internal jump satisfies the local chain-weight estimate.**
This discharges the ratio premise in the composition count of
`apd:eq:total_high_weight_norm`, with `j=m` retained for the entry estimate. -/
theorem epsJump_mul_chainWeight_le {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    epsJump kh1 c a j m * chainWeight kh1 c a (m - j)
      ≤ (9 / 4 : ℝ) ^ (j - 1) * chainWeight kh1 c a m := by
  rw [epsJump_mul_chainWeight_eq_partFactor hc kh1 a hjm]
  apply mul_le_mul_of_nonneg_right _ (chainWeight_nonneg hkh hc ha m)
  apply partFactor_le_of_one_le hj
  exact (by exact_mod_cast hjm : (j : ℝ) ≤ m).trans (le_add_of_nonneg_right hc)

/-- The first jump's leading term is bounded by its all-ones weight, including a zero angle.
Supporting theorem for `apd:eq:entry_bound` and `apd:eq:total_high_weight_norm`. -/
theorem epsJump_diag_le_chainWeight {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    epsJump kh1 c a m m ≤ (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by
  simpa using epsJump_mul_chainWeight_le hkh hc ha hm (le_refl m)

/-- The concrete expansion parameter is nonnegative. Supporting sign check for
`apd:eq:entry_bound`. -/
theorem betaOf_nonneg_for_chain {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ betaOf kh1 c a := by
  unfold betaOf
  have hw := rungW_nonneg hkh hc (m := 2) (by decide)
  positivity

/-- **The concrete entry estimate charges the overshoot factor once.**
Combines `apd:eq:entry_bound`, in the stronger form `1 + 2β` proved as `entryFactor_le`,
with `apd:eq:part_factor`, as used in `apd:eq:composition_majorant`. -/
theorem entryFactor_le_chainWeight {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    entryFactor kh1 c a m
      ≤ (1 + 2 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by
  have hC : 0 ≤ 1 + 2 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  calc entryFactor kh1 c a m
      ≤ epsJump kh1 c a m m * (1 + 2 * betaOf kh1 c a) :=
        entryFactor_le hkh hc ha hm hb
    _ ≤ ((9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m)
          * (1 + 2 * betaOf kh1 c a) :=
        mul_le_mul_of_nonneg_right (epsJump_diag_le_chainWeight hkh hc ha hm) hC
    _ = _ := by ring

/-- `epsJump` is nonnegative at every index required by the generic chain theorem, including
the otherwise-unneeded `(j,m)=(0,0)` case, where its value is one.
Supporting sign check for `apd:eq:composition_majorant`. -/
theorem epsJump_nonneg_for_chain {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (j m : ℕ) :
    0 ≤ epsJump kh1 c a j m := by
  by_cases h : 1 ≤ m + j
  · exact epsJump_nonneg hkh hc ha j m h
  · have hm : m = 0 := by omega
    have hj : j = 0 := by omega
    subst m
    subst j
    simp [epsJump]

/-- The entry inflation `1 + 2β` proved here is no larger than the paper's `1 + 4eβ`, because
`2 ≤ 4e` and `β ≥ 0`. Supporting comparison for `apd:eq:entry_bound` and
`apd:eq:total_high_weight_norm`. -/
theorem chain_entry_inflation_le_source {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    1 + 2 * betaOf kh1 c a ≤ 1 + 4 * Real.exp 1 * betaOf kh1 c a := by
  have hb0 := betaOf_nonneg_for_chain hkh hc ha
  have he := Real.add_one_le_exp (1 : ℝ)
  have hnum : (2 : ℝ) ≤ 4 * Real.exp 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hnum hb0
  linarith

/-- The concrete entry premise with the paper's constant `1 + 4eβ`, still charged once.
Formalizes the use of `apd:eq:entry_bound` in `apd:eq:composition_majorant`. -/
theorem entryFactor_le_chainWeight_source {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    entryFactor kh1 c a m
      ≤ (1 + 4 * Real.exp 1 * betaOf kh1 c a)
        * (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by
  refine (entryFactor_le_chainWeight hkh hc ha hb hm).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (chain_entry_inflation_le_source hkh hc ha) (by positivity))
    (chainWeight_nonneg hkh hc ha m)

/-- **Concrete chain-product/composition-count bound, with all local and entry premises
discharged.** The overshoot inflation occurs exactly once, not once per composition part.
This is the chain-weight step of `apd:eq:total_high_weight_norm`, with the entry factor
`1 + 2β`, which is stronger than the paper's statement. It remains valid at zero angle. -/
theorem chain_epsJump_le_weighted_choose {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) (k m : ℕ) (hm : 1 ≤ m) :
    chain (epsJump kh1 c a) (entryFactor kh1 c a) (k + 1) m
      ≤ (1 + 2 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - (k + 1))
        * chainWeight kh1 c a m * ((m - 1).choose k : ℝ) := by
  have hC : 0 ≤ 1 + 2 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  exact chain_le_weighted_choose (epsJump_nonneg_for_chain hkh hc ha) hC (by norm_num)
    (fun _ hm => entryFactor_le_chainWeight hkh hc ha hb hm)
    (fun _ _ hj hjm => epsJump_mul_chainWeight_le hkh hc ha hj (Nat.le_of_lt hjm)) k m hm

/-- The same concrete chain bound with the paper's entry factor `1 + 4eβ`, suitable for
direct composition with `apd:eq:total_high_weight_norm`. -/
theorem chain_epsJump_le_weighted_choose_source {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) (k m : ℕ) (hm : 1 ≤ m) :
    chain (epsJump kh1 c a) (entryFactor kh1 c a) (k + 1) m
      ≤ (1 + 4 * Real.exp 1 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - (k + 1))
        * chainWeight kh1 c a m * ((m - 1).choose k : ℝ) := by
  have hC : 0 ≤ 1 + 4 * Real.exp 1 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  exact chain_le_weighted_choose (epsJump_nonneg_for_chain hkh hc ha) hC (by norm_num)
    (fun _ hm => entryFactor_le_chainWeight_source hkh hc ha hb hm)
    (fun _ _ hj hjm => epsJump_mul_chainWeight_le hkh hc ha hj (Nat.le_of_lt hjm)) k m hm

end Lean4LPD
