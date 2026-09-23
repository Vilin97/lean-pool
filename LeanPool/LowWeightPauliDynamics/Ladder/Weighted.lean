/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Ladder.HockeyStick
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-!
# The ladder with a rung-dependent damping factor

This file defines `WeightedLadder`, the damped ladder whose damping factor `c m` depends on the
rung being climbed, proves its cumulation bound `N m g ≤ C(g,m) · (∏_{j=1}^{m} c j) · M`, and
specializes it to part (ii) of `apd:cor:norm_cumulation_jump`, the per-layer bound
`apd:eq:layer_cumulation`. A saturating family shows that the cumulation bound is attained.

`Lean4LPD.Ladder` damps every rung by the same factor `a = sin(dt)`, which is what the
single-rotation recursion `apd:thm:local_flow_k_local` provides. For a whole *layer* of
disjointly supported rotations the damping is different. The `j = 1` case of
`apd:eq:layer_inflow` bounds the norm of the block that moves mass up by one rung, into rung
`m`, by

  `C(w_{m+1}, 1) · sin(dt) = w_{m+1} · sin(dt)`,

so the coefficient depends on the rung being climbed.

`WeightedLadder` is a genuine generalization of `Lean4LPD.Ladder` — at `c = fun _ => a` the
product `∏_{j=1}^{m} c j` is `a ^ m` — but `Ladder.cumulation` keeps its own short proof rather
than being derived from `WeightedLadder.cumulation`, so that part (i) of the corollary can be
read and checked on its own.

## The index convention

`w_m := k_o + (m-1)(k_h - 1)` (`Lean4LPD.rungWeight`), so `w_{m+1} = k_o + m(k_h-1)`.
Climbing *into* rung `m` costs `w_{m+1}`, not `w_m`: the row bound in the proof of
`apd:thm:layer_inflow` is taken over destinations `s ∈ R` with
`|s| ≤ w_m + j(k_h-1) = w_{m+j}`, which at `j = 1` is `w_{m+1}`. The bound of part (ii) can be
written in two equivalent ways,

  `N_{≥m}^{(T)} ≤ C(T,m) sin^m(dt) ∏_{j=2}^{m+1} w_j ‖O‖`       (`apd:eq:layer_cumulation`),
  `N_{≥m}^{(T)} ≤ (∏_{j=1}^{m} w_{j+1} sin(dt)) · C(T,m) · ‖O‖`   (the form the induction produces),

related by `∏_{j=1}^{m} (w_{j+1} a) = a^m ∏_{j=2}^{m+1} w_j`, which is `weighted_prod_eq` below.

`w` is kept abstract and real-valued throughout, and instantiated only by the caller. That keeps
`ℕ` truncated subtraction out of the ladder entirely — the same reason rung `0` is a
distinguished reservoir rather than a computed `rungWeight _ _ 0`.

## Main definitions

* `WeightedLadder c M`: the damped ladder with rung-dependent damping factor `c`.
* `satLadder`: the saturating family `N m g = C(g,m) · (∏_{j=1}^{m} c j) · M`.

## Main results

* `WeightedLadder.cumulation`: `N m g ≤ C(g,m) · (∏_{j=1}^{m} c j) · M`.
* `weighted_prod_eq`: the product reindexing between the two forms above.
* `layer_cumulation`: the per-layer bound `apd:eq:layer_cumulation`.
* `satLadder_cumulation_eq`: the cumulation bound is attained by `satLadder`.
-/

@[expose] public section

namespace Lean4LPD

open Finset

/-- A damped ladder whose damping factor depends on the rung being climbed.

`N m g` is the mass strictly above rung `m` after `g` steps, and `c m` is the cost of climbing
*into* rung `m`. The fields are `Lean4LPD.Ladder`'s, with the single constant `a` of `step`
replaced by `c m`; see that structure for what each one means physically and for why `step` is
restricted to `m ≥ 1`. -/
structure WeightedLadder (c : ℕ → ℝ) (M : ℝ) where
  /-- Mass strictly above rung `m` after `g` steps. -/
  N : ℕ → ℕ → ℝ
  nonneg : ∀ m g, 0 ≤ N m g
  reservoir : ∀ g, N 0 g ≤ M
  init : ∀ m, 1 ≤ m → N m 0 = 0
  step : ∀ m g, 1 ≤ m → N m (g + 1) ≤ N m g + c m * N (m - 1) g

namespace WeightedLadder

variable {c : ℕ → ℝ} {M : ℝ} (L : WeightedLadder c M)

/-- Iterating the flow recursion over the `g` layers, using `N m 0 = 0` for `m ≥ 1` to kill the
boundary term. The rung-dependent analogue of `Lean4LPD.Ladder.step_iterate`; like it, this needs
no sign hypothesis on `c`. -/
lemma step_iterate {m : ℕ} (hm : 1 ≤ m) :
    ∀ g : ℕ, L.N m g ≤ c m * ∑ l ∈ range g, L.N (m - 1) l := by
  intro g
  induction g with
  | zero => simp [L.init m hm]
  | succ g ih =>
    calc L.N m (g + 1)
        ≤ L.N m g + c m * L.N (m - 1) g := L.step m g hm
      _ ≤ (c m * ∑ l ∈ range g, L.N (m - 1) l) + c m * L.N (m - 1) g := by linarith
      _ = c m * ∑ l ∈ range (g + 1), L.N (m - 1) l := by
          rw [Finset.sum_range_succ]; ring

/-- **Cumulation with a rung-dependent damping factor.**

  `N_{≥m}^{(g)} ≤ C(g, m) · (∏_{j=1}^{m} c j) · M`.

The same induction as `Lean4LPD.Ladder.cumulation`: iterate the recursion over `g`, insert the
inductive hypothesis, and close with the hockey-stick identity. Only `0 ≤ c j` is needed, never
`c j ≤ 1`, even though the intended `c j = w_{j+1} sin(dt)` need not be below one. -/
theorem cumulation (hc : ∀ j, 0 ≤ c j) :
    ∀ m g : ℕ, L.N m g ≤ (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := by
  intro m
  induction m with
  | zero => intro g; simpa using L.reservoir g
  | succ m ih =>
    intro g
    have hm : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have h1 : L.N (m + 1) g ≤ c (m + 1) * ∑ l ∈ range g, L.N m l := by
      simpa using L.step_iterate hm g
    have h2 : ∑ l ∈ range g, L.N m l
        ≤ ∑ l ∈ range g, ((l.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M) :=
      Finset.sum_le_sum fun l _ => ih l
    have h3 : ∑ l ∈ range g, ((l.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M)
        = (g.choose (m + 1) : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_range_choose_real]
    have h4 : ∏ j ∈ Icc 1 (m + 1), c j = (∏ j ∈ Icc 1 m, c j) * c (m + 1) :=
      Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) c
    calc L.N (m + 1) g
        ≤ c (m + 1) * ∑ l ∈ range g, L.N m l := h1
      _ ≤ c (m + 1) * ∑ l ∈ range g, ((l.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M) :=
          mul_le_mul_of_nonneg_left h2 (hc (m + 1))
      _ = (g.choose (m + 1) : ℝ) * (∏ j ∈ Icc 1 (m + 1), c j) * M := by
          rw [h3, h4]; ring

end WeightedLadder

/-- The product reindexing relating the two ways of writing part (ii) of
`apd:cor:norm_cumulation_jump`: `∏_{j=1}^{m} (w_{j+1} · a) = a^m · ∏_{j=2}^{m+1} w_j`. -/
lemma weighted_prod_eq (w : ℕ → ℝ) (a : ℝ) :
    ∀ m : ℕ, (∏ j ∈ Finset.Icc 1 m, w (j + 1) * a) = a ^ m * ∏ j ∈ Finset.Icc 2 (m + 1), w j := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ∏ j ∈ Finset.Icc 1 (m + 1), w (j + 1) * a
        = (∏ j ∈ Finset.Icc 1 m, w (j + 1) * a) * (w (m + 2) * a) :=
      Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) _
    have h2 : ∏ j ∈ Finset.Icc 2 (m + 2), w j = (∏ j ∈ Finset.Icc 2 (m + 1), w j) * w (m + 2) :=
      Finset.prod_Icc_succ_top (by omega) w
    rw [h1, ih, h2]; ring

/-- **Per-layer high-weight cumulation.** Formalizes part (ii) of
`apd:cor:norm_cumulation_jump`, the bound `apd:eq:layer_cumulation`:

  `N_{≥m}^{(T)} ≤ C(T, m) · sin^m(dt) · (∏_{j=2}^{m+1} w_j) · ‖O‖`,

for a ladder whose per-layer coefficient is the single-jump layer inflow `w_{m+1} · sin(dt)`
(the `j = 1` case of `apd:thm:layer_inflow`).

This counts **single-jump inflow only**, which is the scope of `apd:eq:layer_cumulation`. The
multi-jump and overshoot sectors are additive, not multiplicative — a single layer can already
truncate mass while `C(T,m)` is still zero — and are handled by the first-passage majorant of
`apd:rmk:multijump` (`MultiLadder.le_majorant`), not here. -/
theorem layer_cumulation {M a : ℝ} {w : ℕ → ℝ} (ha : 0 ≤ a) (hw : ∀ j, 0 ≤ w j)
    (L : WeightedLadder (fun m => w (m + 1) * a) M) (m g : ℕ) :
    L.N m g ≤ (g.choose m : ℝ) * a ^ m * (∏ j ∈ Finset.Icc 2 (m + 1), w j) * M := by
  have h := L.cumulation (fun j => mul_nonneg (hw (j + 1)) ha) m g
  rw [weighted_prod_eq w a m] at h
  calc L.N m g ≤ (g.choose m : ℝ) * (a ^ m * ∏ j ∈ Finset.Icc 2 (m + 1), w j) * M := h
    _ = (g.choose m : ℝ) * a ^ m * (∏ j ∈ Finset.Icc 2 (m + 1), w j) * M := by ring

/-! ## Non-vacuity, and exactness

`WeightedLadder c M` is inhabited for every nonnegative `c` and `M`, so the theorems above are not
statements about an empty type. The witness below is the pointwise-maximal family: it satisfies
`step` with **equality** and attains `cumulation` exactly. Hence no smaller constant is provable
from the fields of `WeightedLadder`, and the product `∏ w_j` of `apd:eq:layer_cumulation` is the
true growth rate of the abstract recursion rather than an artefact of the estimate.

Pauli instances of `WeightedLadder` are constructed in `Lean4LPD/Pauli/Flow.lean`
(`PauliString.pauliWeightedLadder`) and `Lean4LPD/Pauli/Truncate.lean`
(`PauliString.pauliWeightedLadderTrunc`). -/

/-- The saturating family: `N m g := C(g,m) · (∏_{j=1}^{m} c j) · M`. -/
noncomputable def satLadder {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, 0 ≤ c j) (hM : 0 ≤ M) :
    WeightedLadder c M where
  N m g := (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M
  nonneg m g := by
    have : (0 : ℝ) ≤ ∏ j ∈ Icc 1 m, c j := Finset.prod_nonneg fun j _ => hc j
    positivity
  reservoir g := by simp
  init m hm := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  step m g hm := by
    match m with
    | 0 => omega
    | (m + 1) =>
      have hprod : ∏ j ∈ Icc 1 (m + 1), c j = (∏ j ∈ Icc 1 m, c j) * c (m + 1) :=
        Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)) c
      have hpascal : ((g + 1).choose (m + 1) : ℝ) = (g.choose m : ℝ) + (g.choose (m + 1) : ℝ) := by
        rw [Nat.choose_succ_succ]; push_cast; ring
      simp only [Nat.add_sub_cancel]
      rw [hprod, hpascal]
      ring_nf
      exact le_refl _

/-- The bound of `cumulation` is **attained**: at the saturating family it is an equality. -/
lemma satLadder_cumulation_eq {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, 0 ≤ c j) (hM : 0 ≤ M) (m g : ℕ) :
    (satLadder hc hM).N m g = (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := rfl

end Lean4LPD
