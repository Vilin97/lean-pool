/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The multi-jump ladder and its first-passage majorant

This file defines the abstract multi-jump ladder `MultiLadder`, in which one layer may raise the
mass by several rungs at once, and proves for it the first-passage majorant
`apd:eq:composition_majorant` of `apd:rmk:multijump` (`MultiLadder.le_majorant`), together with
the monotonicity of the majorant in the number of layers.

The rotations of one layer have pairwise disjoint supports, so several of them can anticommute
with the same Pauli string. When `j ≥ 2` of them do, the string moves up `j` rungs within that
single layer. By `apd:thm:layer_inflow` the corresponding block of the layer's action is
bounded in norm by `ε_j^{(m)} := (w_{m+j} sin dt)^j / j!`. The power of `sin(dt)` is `j`, as for `j`
successive one-rung moves. The difference lies in the number of layers consumed, one
instead of `j`, and in the rung the jump starts from, which is `m - j` instead of `m - 1`.

The contribution of multi-jumps therefore has to enter the recursion as **additional inflow
terms**. It cannot be expressed as a constant factor in front of `apd:eq:layer_cumulation`,
because that bound is proportional to `C(T,m)` and hence zero whenever `T < m`, while mass can
cross the truncation threshold after a single layer. `apd:rmk:multijump` illustrates this with
`O = Z₁Z₂Z₃`, the layer `{X₁X₄, X₂X₅, X₃X₆}` and `w* = 5`: after one layer the evolved observable
contains a Pauli string of weight 6, reached by three simultaneous jumps, with coefficient
`sin³(dt)`. The bound that accounts for these inflows is the first-passage majorant
`apd:eq:composition_majorant`, formalized here.

## What the hypothesis says, and what it already assumes

In `apd:rmk:multijump` the recursion reads

  `N_m^{(T)} ≤ N_m^{(T-1)} + ∑_{j≥1} ε_j^{(m)} N_{m-j}^{(T-1)}`,   with `N_ν := ‖O‖` for `ν ≤ 0`.

Substituting the convention `N_ν := ‖O‖` splits the sum at `j = m`:

  `∑_{j≥1} ε_j^{(m)} N_{m-j}  =  ∑_{j=1}^{m-1} ε_j^{(m)} N_{m-j}  +  (∑_{j≥m} ε_j^{(m)}) · M`,

and the second bracket is the **entry factor** `E_m := ∑_{j≥m} ε_j^{(m)}`. It collects every way
of leaving the reservoir in one jump and landing above rung `m`, including the *overshoot* jumps
`j > m`, which start below rung 1 and which a plain sum over compositions of `m` would omit.
`MultiLadder.step` is that already-substituted form. Two consequences:

* the infinite sum does **not** appear here. `E` is an abstract field, related to `ε` by nothing
  at all, so the theorem below reads "if the recursion holds with *some* `E`, the majorant holds
  with that same `E`" — more general than the paper's statement. The series `∑_{j≥m}` appears
  exactly once in this development, as `Lean4LPD.entryFactor` in
  `Lean4LPD/Constants/Entry.lean`, where it is bounded (`apd:eq:entry_bound`);
* `N_ν = M` for `ν ≤ 0` is the reservoir bound, justified by unitary invariance of the 2-norm
  together with truncation only decreasing every `N`. Here it is part of the hypothesis `step`
  (the term `E m * M`), and it is discharged by the Pauli model in
  `Lean4LPD/Pauli/LayerLadder.lean` (`PauliString.pauliMultiLadder`), just as `Ladder.reservoir`
  is for the single-jump ladder.

## The recursive form of the chain sum

The majorant sums over strictly increasing rung sequences `0 < ν₁ < ⋯ < ν_k = m`. Peeling the
*last* jump gives the recursion that `chain` is **defined** by. `chain_diag` below then proves
the statement of `apd:rmk:multijump` that the all-ones term reproduces the layer-cumulation
bound, which is the check that the definition is the intended object rather than merely a
plausible one.

## Main definitions

* `chain ε E k m`: the total weight of the first-passage paths to rung `m` with exactly `k` jumps.
* `MultiLadder ε E M`: the damped ladder with every jump length retained.
* `MultiLadder.majorant`: the bound of `apd:eq:composition_majorant`, as a function of `m`, `T`.
* `MultiLadder.trivialMultiLadder`: the zero family, showing that the structure is inhabited.

## Main results

* `chain_eq_zero_of_lt`: a path to rung `m` uses at most `m` jumps.
* `chain_diag`: the all-ones term is `E 1 · ∏_{i=2}^{m} ε_1^{(i)}`.
* `MultiLadder.le_majorant`: the first-passage majorant, `N m T ≤ majorant ε E M m T`.
* `MultiLadder.majorant_mono`: the majorant is monotone in the number of layers.
-/

namespace Lean4LPD

open Finset

/-- The inner chain sum of `apd:eq:composition_majorant`, **defined** by peeling
the last jump: `chain ε E k m` is the total weight of all first-passage paths that leave the
reservoir once and climb to rung `m` through exactly `k` jumps at strictly increasing rungs.

  `chain ε E 0 m = 0`,  `chain ε E 1 m = E m`,
  `chain ε E (k+2) m = ∑_{j=1}^{m-1} ε_j^{(m)} · chain ε E (k+1) (m-j)`.

The recursion is on the number of jumps `k`, not on the rung `m`, so it is structural. The sum
over `Finset.Ico 1 m` keeps `1 ≤ j < m`, hence `1 ≤ m - j`: no `ℕ` truncated subtraction is ever
evaluated outside its intended range. -/
def chain (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, m => E m
  | (k + 2), m => ∑ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j)

@[simp] lemma chain_zero (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (m : ℕ) : chain eps E 0 m = 0 := rfl

@[simp] lemma chain_one (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (m : ℕ) : chain eps E 1 m = E m := rfl

lemma chain_succ_succ (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (k m : ℕ) :
    chain eps E (k + 2) m = ∑ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j) := rfl

variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}

lemma chain_nonneg (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) :
    ∀ k m : ℕ, 0 ≤ chain eps E k m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro m; simp
    | 1 => intro m; simpa using hE m
    | (k + 2) =>
      intro m
      rw [chain_succ_succ]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (heps j m) (ih (k + 1) (by omega) (m - j))

/-- A path to rung `m ≥ 1` cannot use more than `m` jumps, each jump climbing at least one rung.
This is what makes the outer sum of `apd:eq:composition_majorant` run to `min(m, T)` even though
`majorant` below sums to `T`. -/
lemma chain_eq_zero_of_lt : ∀ k m : ℕ, 1 ≤ m → m < k → chain eps E k m = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro m _ h; exact absurd h (by omega)
    | 1 => intro m h1 h2; omega
    | (k + 2) =>
      intro m h1 h2
      rw [chain_succ_succ]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      rw [ih (k + 1) (by omega) (m - j) (by omega) (by omega), mul_zero]

/-- **The all-ones term is the single-jump layer-cumulation bound.** Formalizes the statement
of `apd:rmk:multijump` that the term of the majorant with `k = m` jumps, all of length one (so
`ν_i = i`), coincides with the bound `apd:eq:layer_cumulation`:

  `chain ε E m m = E 1 · ∏_{i=2}^{m} ε_1^{(i)}`.

A composition of `m` into `m` parts has every part equal to one: in the defining recursion a
last jump of length `j ≥ 2` would leave `m - 1` jumps to reach rung `m - j < m - 1`, and that
term vanishes by `chain_eq_zero_of_lt`. With `ε_1^{(i)} = w_{i+1} sin(dt)` this product is
`sin^{m-1}(dt) ∏_{j=3}^{m+1} w_j`, which is `Lean4LPD.layer_cumulation`'s product with the entry
rung's factor replaced by `E 1` — the one place the two bounds differ, and the reason the entry
factor is kept separate. -/
lemma chain_diag :
    ∀ m : ℕ, 1 ≤ m → chain eps E m m = E 1 * ∏ i ∈ Ico 2 (m + 1), eps 1 i := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    match m with
    | 0 => simp
    | (m + 1) =>
      have hstep : chain eps E (m + 2) (m + 2)
          = ∑ j ∈ Ico 1 (m + 2), eps j (m + 2) * chain eps E (m + 1) (m + 2 - j) :=
        chain_succ_succ eps E m (m + 2)
      have honly : ∀ j ∈ Ico 1 (m + 2), j ≠ 1 →
          eps j (m + 2) * chain eps E (m + 1) (m + 2 - j) = 0 := by
        intro j hj hne
        rw [Finset.mem_Ico] at hj
        rw [chain_eq_zero_of_lt (m + 1) (m + 2 - j) (by omega) (by omega),
          mul_zero]
      rw [hstep, Finset.sum_eq_single 1 (fun j hj hne => honly j hj hne)
        (fun h => absurd (Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩) h)]
      have h1 : m + 2 - 1 = m + 1 := by omega
      rw [h1, ih (by omega)]
      have h2 : ∏ i ∈ Ico 2 (m + 3), eps 1 i = (∏ i ∈ Ico 2 (m + 2), eps 1 i) * eps 1 (m + 2) := by
        rw [Finset.prod_Ico_succ_top (by omega)]
      have h3 : m + 1 + 1 = m + 2 := rfl
      rw [h2, h3]; ring

/-- A **multi-jump ladder**: the damped ladder with every jump length retained.

`N m T` is the mass strictly above rung `m` after `T` disjoint-support layers, `eps j m` is the
`j`-jump block norm into rung `m`, `E m` the entry factor out of the reservoir into rung `m`, and
`M` the total mass. See the module docstring for why `step` is already in substituted form and for
what that does and does not assume. -/
structure MultiLadder (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (M : ℝ) where
  /-- Mass strictly above rung `m` after `T` layers. -/
  N : ℕ → ℕ → ℝ
  nonneg : ∀ m T, 0 ≤ N m T
  init : ∀ m, 1 ≤ m → N m 0 = 0
  step : ∀ m T, 1 ≤ m →
    N m (T + 1) ≤ N m T + (∑ j ∈ Ico 1 m, eps j m * N (m - j) T) + E m * M

namespace MultiLadder

variable {M : ℝ}

/-- The bound asserted by `apd:eq:composition_majorant`, as a function of the rung `m` and the
number of layers `T`:

  `M · ∑_{k=0}^{T} C(T,k) · chain ε E k m`.

In `apd:eq:composition_majorant` the outer sum is `∑_{k=1}^{min(m,T)}`; the extra terms here
vanish, at `k = 0` by definition and at `k > m` by `chain_eq_zero_of_lt`. Summing to `T` rather
than to `min(m,T)` is what makes the Pascal step below a two-line rewrite. -/
noncomputable def majorant (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (M : ℝ) (m T : ℕ) : ℝ :=
  M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m

variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}

/-- The Pascal recursion satisfied by the majorant's bracket, which is the whole content of the
induction behind `apd:eq:composition_majorant`. Among the paths with `k` jumps in `T` layers,
those whose final layer is idle are counted by `C(T-1,k)` and those that jump in the final layer
by `C(T-1,k-1)`; the two cases add up by Pascal's rule. -/
lemma sum_chain_succ (m T : ℕ) :
    ∑ k ∈ range (T + 2), ((T + 1).choose k : ℝ) * chain eps E k m
      = (∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m)
        + ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m := by
  have hpeel : ∑ k ∈ range (T + 2), ((T + 1).choose k : ℝ) * chain eps E k m
      = ∑ k ∈ range (T + 1), ((T + 1).choose (k + 1) : ℝ) * chain eps E (k + 1) m := by
    rw [Finset.sum_range_succ' (fun k => ((T + 1).choose k : ℝ) * chain eps E k m)]
    simp
  have hpascal : ∀ k ∈ range (T + 1),
      ((T + 1).choose (k + 1) : ℝ) * chain eps E (k + 1) m
        = (T.choose k : ℝ) * chain eps E (k + 1) m
          + (T.choose (k + 1) : ℝ) * chain eps E (k + 1) m := by
    intro k _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have htail : ∑ k ∈ range (T + 1), (T.choose (k + 1) : ℝ) * chain eps E (k + 1) m
      = ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m := by
    rw [Finset.sum_range_succ (fun k => (T.choose (k + 1) : ℝ) * chain eps E (k + 1) m),
      Finset.sum_range_succ' (fun k => (T.choose k : ℝ) * chain eps E k m)]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [hpeel, Finset.sum_congr rfl hpascal, Finset.sum_add_distrib, htail]
  ring

/-- The shifted chain sum, unrolled one level: the `k = 0` term is the entry factor `E m`, and
every remaining term ends with a `j`-jump that starts from rung `m - j`. -/
lemma sum_chain_shift (m T : ℕ) :
    ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m
      = E m + ∑ j ∈ Ico 1 m, eps j m
          * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
  have hpeel : ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m
      = (∑ k ∈ range T, (T.choose (k + 1) : ℝ) * chain eps E (k + 2) m) + E m := by
    rw [Finset.sum_range_succ' (fun k => (T.choose k : ℝ) * chain eps E (k + 1) m)]
    simp
  have hdrop : ∀ j : ℕ, ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j)
      = ∑ k ∈ range T, (T.choose (k + 1) : ℝ) * chain eps E (k + 1) (m - j) := by
    intro j
    rw [Finset.sum_range_succ' (fun k => (T.choose k : ℝ) * chain eps E k (m - j))]
    simp
  have hbody : ∀ k ∈ range T, (T.choose (k + 1) : ℝ) * chain eps E (k + 2) m
      = ∑ j ∈ Ico 1 m, (T.choose (k + 1) : ℝ) * (eps j m * chain eps E (k + 1) (m - j)) := by
    intro k _
    rw [chain_succ_succ, Finset.mul_sum]
  have hinner : ∀ j ∈ Ico 1 m,
      ∑ k ∈ range T, (T.choose (k + 1) : ℝ) * (eps j m * chain eps E (k + 1) (m - j))
        = eps j m * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
    intro j _
    rw [hdrop j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hpeel, Finset.sum_congr rfl hbody, Finset.sum_comm, Finset.sum_congr rfl hinner, add_comm]

/-- **The first-passage majorant.** Formalizes `apd:eq:composition_majorant`:

  `N_m^{(T)} ≤ ‖O‖ · ∑_{k} C(T,k) · chain_k^{(m)}`,
  `chain_k^{(m)} = ∑_{0<ν₁<⋯<ν_k=m} E_{ν₁} ∏_{i=2}^{k} ε_{ν_i-ν_{i-1}}^{(ν_i)}`.

The inner chain sum is `chain`, defined by peeling the last jump. Only nonnegativity of `eps` is
needed; `E` and `M` are unconstrained, so the bound is inherited by any `E` majorizing the
overshoot tail. -/
theorem le_majorant (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m) :
    ∀ T : ℕ, ∀ m : ℕ, 1 ≤ m → L.N m T ≤ majorant eps E M m T := by
  intro T
  induction T with
  | zero =>
    intro m hm
    simp [majorant, L.init m hm]
  | succ T ih =>
    intro m hm
    have hstep := L.step m T hm
    have hmain : L.N m T ≤ M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m := ih m hm
    have hlower : ∀ j ∈ Ico 1 m, eps j m * L.N (m - j) T
        ≤ eps j m * (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      exact mul_le_mul_of_nonneg_left (ih (m - j) (by omega)) (heps j m)
    have hsum : ∑ j ∈ Ico 1 m, eps j m * L.N (m - j) T
        ≤ ∑ j ∈ Ico 1 m, eps j m
            * (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j)) :=
      Finset.sum_le_sum hlower
    have hfactor : ∑ j ∈ Ico 1 m, eps j m
          * (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j))
        = M * ∑ j ∈ Ico 1 m, eps j m
            * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [majorant, sum_chain_succ, sum_chain_shift]
    calc L.N m (T + 1)
        ≤ L.N m T + (∑ j ∈ Ico 1 m, eps j m * L.N (m - j) T) + E m * M := hstep
      _ ≤ (M * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m)
            + (M * ∑ j ∈ Ico 1 m, eps j m
                * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j))
            + E m * M := by
          rw [← hfactor]; linarith [hsum, hmain]
      _ = M * ((∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m)
            + (E m + ∑ j ∈ Ico 1 m, eps j m
                * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j))) := by ring

/-- **The majorant is monotone in the number of layers.** This is what licenses bounding the
rung norms at the intermediate layers of a Trotter step by the majorant taken at the last layer of
the step. The rung norms themselves need not be monotone in the number of layers, so it is the
majorant, not the norm, that is moved to the end of the step; see `MultiLadder.block_inflow_le`. -/
lemma majorant_mono (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) (m T : ℕ) :
    majorant eps E M m T ≤ majorant eps E M m (T + 1) := by
  have hchoose : ∀ k, (T.choose k : ℝ) ≤ ((T + 1).choose k : ℝ) := by
    intro k
    have hn : T.choose k ≤ (T + 1).choose k := by
      match k with
      | 0 => simp
      | (k + 1) => rw [Nat.choose_succ_succ]; exact Nat.le_add_left _ _
    exact_mod_cast hn
  refine mul_le_mul_of_nonneg_left ?_ hM
  calc ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m
      ≤ ∑ k ∈ range (T + 1), ((T + 1).choose k : ℝ) * chain eps E k m :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hchoose k) (chain_nonneg heps hE k m)
    _ ≤ ∑ k ∈ range (T + 2), ((T + 1).choose k : ℝ) * chain eps E k m :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hx)))
          fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (chain_nonneg heps hE k m)

/-! ## Non-vacuity

`MultiLadder eps E M` is inhabited whenever `eps`, `E` and `M` are nonnegative, so the theorems
above are not statements about an empty type.

The witness below is the trivial one, `N ≡ 0`: it shows only that the field constraints are
jointly satisfiable. It is **not** evidence that `le_majorant` is tight. For tightness, note
that `sum_chain_succ` and `sum_chain_shift` combine to show that the majorant itself obeys the
recursion of `step` with equality; that saturating family is not packaged as a `MultiLadder`
here, and `Lean4LPD.satLadder` is the corresponding packaged statement on the single-jump side.

A Pauli instance of `MultiLadder` is constructed in `Lean4LPD/Pauli/LayerLadder.lean`
(`PauliString.pauliMultiLadder`). -/

/-- The zero family `N ≡ 0` is a `MultiLadder` for all nonnegative `eps`, `E` and `M`. -/
def trivialMultiLadder {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}
    (_heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) (hM : 0 ≤ M) : MultiLadder eps E M where
  N _ _ := 0
  nonneg _ _ := le_refl 0
  init _ _ := rfl
  step m T _ := by
    have h1 : (0 : ℝ) ≤ ∑ j ∈ Ico 1 m, eps j m * 0 := by
      exact Finset.sum_nonneg fun j _ => by simp
    have h2 : (0 : ℝ) ≤ E m * M := mul_nonneg (hE m) hM
    simpa using by linarith [h1, h2]

end MultiLadder

end Lean4LPD
