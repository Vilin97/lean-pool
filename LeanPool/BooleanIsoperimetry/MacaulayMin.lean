/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import LeanPool.BooleanIsoperimetry.Shadow

/-!
# Scalar Macaulay minimization

This file packages the set-family compression and shadow estimates into scalar
Macaulay minimization lemmas consumed by the final Harper theorem.
-/

open scoped BigOperators
open Finset

namespace BooleanIsoperimetry

/-
# Scalar Macaulay minimization as a corollary of the PDF set-family layer

This module sits **downstream** of the Frankl–Füredi paired-compression layer
(`Compression.lean`) and the upper-shadow / Macaulay layer (`Shadow.lean`), and
re-derives the scalar Macaulay minimization theorems (`harper_macaulay_min`,
`harper_compression_descent`) from the genuine PDF set-family statements rather
than the other way round.

The orientation matters.  Previously the two scalar shadow-sum leaves
`macaulay_extremal_pos_step_LE` / `_GT` were the *root* `sorry`s, and the
set-family `franklFuredi_pairedCompression_exchange` was *proved from them* (via
`harper_compression_descent`).  That made the "PDF" theorem a consequence of a
scalar inequality — a scalar disguise of the gap.

Here the flow is the genuine Frankl–Füredi route:

```
pairedCompression_reaches_canonical        -- PDF terminalization (now sorry-free)
  ⟹ franklFuredi_pairedCompression_exchange  -- Compression.lean
  ⟹ H_exchange_max_form_pos                  -- Shadow.lean
  ⟹ H_shadow_LE_sum / H_shadow_GT_sum        -- Shadow.lean
  ⟹ macaulay_extremal_pos_step_LE / _GT      -- here, now PROVED corollaries
  ⟹ macaulay_bc_min ⟹ harper_macaulay_min    -- here
  ⟹ harper_compression_descent               -- here
```

So the two scalar leaves below are **proved wrappers** of the set-family shadow
leaves `H_shadow_LE_sum` / `H_shadow_GT_sum`, exactly as the task requests, and
the set-family terminalization theorem `pairedCompression_reaches_canonical`
is now fully formalized and sorry-free.
-/

/-- **Positive-cascade Case-I (LE) Macaulay shadow-sum leaf.**  Now a *proved*
corollary of the set-family shadow leaf `H_shadow_LE_sum` (which collapses the
Frankl–Füredi paired-compression cost via `H_exchange_max_form_pos`).  The
hypotheses `ih`, `hp`, `hq`, `hpq` are retained to keep the call site signature
stable; the content is entirely the shadow-sum comparison. -/
lemma macaulay_extremal_pos_step_LE (n : ℕ)
    (_ : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (_ : p ≤ 2 ^ n) (_ : q ≤ 2 ^ n)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) (hq_pos : 1 ≤ q)
    (hba : b ≤ a) (hcase : a ≤ H n b) :
    H n p + H n q ≤ H n a + H n b :=
  H_shadow_LE_sum ha hb hcasc hq_pos hba hcase

/-- **Positive-cascade Case-II (GT) Macaulay shadow-sum leaf.**  Now a *proved*
corollary of the set-family GT shadow-deficit leaf `H_shadow_GT_sum`. -/
lemma macaulay_extremal_pos_step_GT (n : ℕ)
    (_ : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (_ : p ≤ 2 ^ n) (_ : q ≤ 2 ^ n)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) (hq_pos : 1 ≤ q)
    (hba : b ≤ a) (hcase : H n b < a) :
    H n p + H n q ≤ H n a + a :=
  H_shadow_GT_sum ha hb hcasc hq_pos hba hcase

/-- Positive-cascade max-form wrapper.  Sorry-free modulo the two oriented
Macaulay shadow-sum leaves `macaulay_extremal_pos_step_LE` and
`macaulay_extremal_pos_step_GT`. -/
lemma macaulay_extremal_pos_step (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) (hq_pos : 1 ≤ q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  cases le_total b a with
  | inl hba =>
      rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : a ≤ H n b
      · rw [boundaryCost_eq_case_le ha hba hcase]
        exact macaulay_extremal_pos_step_LE n ih ha hb hp hq hpq hcasc hq_pos hba hcase
      · push Not at hcase
        rw [boundaryCost_eq_case_gt ha hba hcase]
        exact macaulay_extremal_pos_step_GT n ih ha hb hp hq hpq hcasc hq_pos hba hcase
  | inr hab =>
      rw [boundaryCost_comm n a b]
      have hpq_symm : p + q = b + a := by omega
      have hcasc_symm : CascadeSplit n (b + a) p q := by
        simpa [Nat.add_comm] using hcasc
      rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : b ≤ H n a
      · rw [boundaryCost_eq_case_le hb hab hcase]
        exact macaulay_extremal_pos_step_LE n ih hb ha hp hq hpq_symm hcasc_symm hq_pos hab hcase
      · push Not at hcase
        rw [boundaryCost_eq_case_gt hb hab hcase]
        exact macaulay_extremal_pos_step_GT n ih hb ha hp hq hpq_symm hcasc_symm hq_pos hab hcase

/-- **Scalar boundary-cost minimization at a fixed cascade split.**  Given the
canonical cascade split `(p, q)` of `a + b` at level `n`, the canonical split
minimizes the symmetric max-form boundary cost.  The `q = 0` branch is discharged
sorry-free by `Macaulay.harper_bc_min_q_zero_core`, and the `q ≥ 1` branch by
`macaulay_extremal_pos_step`. -/
lemma macaulay_bc_min (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  by_cases hq_pos : 1 ≤ q
  · exact macaulay_extremal_pos_step n ih ha hb hp hq hpq hcasc hq_pos
  · push Not at hq_pos
    have hq0 : q = 0 := by omega
    subst hq0
    have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
    have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
    rw [hmax1, hmax2]
    cases le_total b a with
    | inl hb_le_a =>
      have hpq_zero : p = a + b := by omega
      exact harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq_zero hcasc
    | inr ha_le_b =>
      rw [boundaryCost_comm n a b]
      have hcasc_symm : CascadeSplit n (b + a) p 0 := by simpa [Nat.add_comm] using hcasc
      have hpq_zero : p = b + a := by omega
      exact harper_bc_min_q_zero_core n hb ha hp ha_le_b hpq_zero hcasc_symm

/-- **Scalar Macaulay minimization — the arithmetic core of Harper.**
For any slice sizes `a, b ≤ 2 ^ N`, the boundary cost `H (N+1) (a+b)` of the
canonical cascade split of the total mass `a + b` is minimal among all ways of
distributing that mass into two `N`-dimensional slices of sizes `a` and `b`.

Proved by strong induction on the dimension `N` (the Frankl–Füredi recursion):
`H_succ_cascade` reduces the LHS to `max (H N p) q + max (H N q) p`, and
`macaulay_bc_min` closes it using the lower-dimensional induction hypothesis. -/
theorem harper_macaulay_min {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    H (N + 1) (a + b) ≤ max (H N a) b + max (H N b) a := by
  suffices key : ∀ n, ∀ a b : ℕ, a ≤ 2 ^ n → b ≤ 2 ^ n →
      H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a by
    exact key N a b ha hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b ha hb
    have hS : a + b ≤ 2 ^ (n + 1) := by
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega
    obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hS
    rw [H_succ_cascade hcasc]
    exact macaulay_bc_min n ih ha hb hp hq hpq hcasc

/-- **Embedded-pair Harper/Macaulay shadow comparison.**  Among families in
`Q_{N+1}` with `a+b` vertices, the simplicial initial segment has closed
neighborhood no larger than the particular two-slice family consisting of
canonical initial segments of sizes `a` and `b`.  Sorry-free corollary of
`harper_macaulay_min` via the cardinality bridge
`neighborhood_initialSlicePair_card`. -/
theorem initialSlicePair_harper_bound {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (simplicialInitSeg (N + 1) (a + b))).card ≤
      (neighborhood 1 (initialSlicePair N a b)).card := by
  change H (N + 1) (a + b) ≤ (neighborhood 1 (initialSlicePair N a b)).card
  rw [neighborhood_initialSlicePair_card ha hb]
  exact harper_macaulay_min ha hb

/-- **Harper's vertex-isoperimetric theorem (family level, slice-induction form).**
The simplicial initial segment of a given size has the smallest closed unit
neighborhood among all families of that size: `|N(initSeg N |A|)| ≤ |N(A)|`.

The proof is the PDF Frankl–Füredi dimension recursion: split a family
`B ⊆ Cube (M+1)` into its two `M`-dimensional slices, use `neighborhood_succ`,
lower-bound each cross term by a maximum via the dimension-`M` induction
hypothesis, and invoke the scalar Macaulay minimization `harper_macaulay_min`. -/
theorem harper_compression_descent {N : ℕ} (A : Finset (Cube N)) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by
  suffices h : ∀ (M : ℕ) (B : Finset (Cube M)), H M B.card ≤ (neighborhood 1 B).card by
    exact h N A
  intro M
  induction M with
  | zero =>
    intro B
    have hsub : B ⊆ neighborhood 1 B := by
      intro x hx
      rw [mem_neighborhood_iff]
      exact ⟨x, hx, by simp [hDist]⟩
    have hge : B.card ≤ (neighborhood 1 B).card := Finset.card_le_card hsub
    have hcard : B.card ≤ 1 := by
      have h := card_le_two_pow B; simpa using h
    rcases (by omega : B.card = 0 ∨ B.card = 1) with h0 | h1
    · rw [h0, H_zero]; exact Nat.zero_le _
    · rw [h1, H_one]; omega
  | succ M ih =>
    intro B
    set a := (slice0 B).card with ha_def
    set b := (slice1 B).card with hb_def
    have hab : a + b = B.card := slice_card_add B
    have ha : a ≤ 2 ^ M := card_le_two_pow (slice0 B)
    have hb : b ≤ 2 ^ M := card_le_two_pow (slice1 B)
    have ih0 : H M a ≤ (neighborhood 1 (slice0 B)).card := ih (slice0 B)
    have ih1 : H M b ≤ (neighborhood 1 (slice1 B)).card := ih (slice1 B)
    have bound1 : max (H M a) b ≤ (neighborhood 1 (slice0 B) ∪ slice1 B).card := by
      apply max_le
      · exact le_trans ih0 (Finset.card_le_card Finset.subset_union_left)
      · exact le_trans (le_of_eq hb_def) (Finset.card_le_card Finset.subset_union_right)
    have bound2 : max (H M b) a ≤ (neighborhood 1 (slice1 B) ∪ slice0 B).card := by
      apply max_le
      · exact le_trans ih1 (Finset.card_le_card Finset.subset_union_left)
      · exact le_trans (le_of_eq ha_def) (Finset.card_le_card Finset.subset_union_right)
    have hnb : (neighborhood 1 B).card =
        (neighborhood 1 (slice0 B) ∪ slice1 B).card +
        (neighborhood 1 (slice1 B) ∪ slice0 B).card := neighborhood_succ B
    have hleaf : H (M + 1) (a + b) ≤ max (H M a) b + max (H M b) a :=
      harper_macaulay_min ha hb
    rw [← hab]
    calc H (M + 1) (a + b)
        ≤ max (H M a) b + max (H M b) a := hleaf
      _ ≤ (neighborhood 1 (slice0 B) ∪ slice1 B).card +
            (neighborhood 1 (slice1 B) ∪ slice0 B).card := Nat.add_le_add bound1 bound2
      _ = (neighborhood 1 B).card := hnb.symm

end BooleanIsoperimetry
