/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Basic

/-!
  Sundogcert/VarWheel.lean — MILESTONE 2 of the `3SAT ≤ 3DM` marathon.

  WHAT THIS FILE PROVIDES (the variable "wheel" / truth-setting gadget + its LOCAL CORRECTNESS):
    The Garey–Johnson truth-setting ring for a 3-CNF formula with `m` clauses.  For each
    `j : Fin m` the gadget owns two INTERNAL nodes `a j`, `b j` (covered exactly once, living only
    here) and two TIP nodes `posTip j`, `negTip j` (shared later with the clause gadgets).  The two
    cover triples are
        positive  t_j  = (posTip j, a j,       b j)
        negative  t⁻_j = (negTip j, a (j+1),   b j)      [index `j+1` CYCLIC in `Fin m`].
    Because `b j` lies ONLY in `{t_j, t⁻_j}`, any valid internal cover selects exactly one triple
    per `j` — i.e. is a `Selection σ : Fin m → Bool` (`σ j = true` picks `t_j`, `false` picks
    `t⁻_j`).  Node `a j` is touched by `t_j` (iff `σ j = true`) and by `t⁻_(j-1)` (iff
    `σ (j-1) = false`); "`a j` covered exactly once" is the EXCLUSIVE-OR of those two facts.

    THE ENGINE (`validCover_iff_const`): the ring has EXACTLY TWO valid internal covers — the
    all-true and all-false selections — the two truth values of the variable.  We also expose,
    per constant state, which tips are left FREE (raw, label-deferred): the true-state frees every
    `negTip` and the false-state frees every `posTip`.

  THE GADGET PICTURE (a ring; arrows are the two triples per spoke `j`, indices cyclic):

        a 0 ──t_0── b 0 ──t⁻_0── a 1 ──t_1── b 1 ──t⁻_1── a 2 ── … ── (wraps to a 0)
          posTip j attaches to t_j;  negTip j attaches to t⁻_j .

  THE IMPORTED WALL (named, NOT proved — mathlib has no complexity framework):
    * the NP complexity class and poly-time-ness of the reduction;
    * 3SAT's OWN NP-hardness — Cook–Levin, the deep terminal wall sourcing every Karp-reduction
      hardness claim in this `3SAT ≤ 3DM ≤ X3C ≤ Decodes` chain.

  STANDING LIMIT: this module proves the wheel's LOCAL correctness only.  The clause gadget, the
  garbage-collection triples, and the global assembly onto `Sundog.MatchingNPHard.ThreeDM`
  (including the obligation that `b j` truly lies only in `{t_j, t⁻_j}`, which makes `σ`
  well-defined) are milestones 3–8.

  Decidability of `ValidCover` is registered explicitly (it is a `∀` over `Fin m` of a decidable
  `Prop`, but does not auto-resolve through the `def`).  This locks the two-cover claim at `m = 3`
  by kernel `decide` — AXIOM-CLEAN (no `Lean.ofReduceBool`; we use `decide`, never `native_decide`).
-/

namespace Sundog.VarWheel

variable {m : ℕ} [NeZero m]

/-- A selection of one triple per spoke: `σ j = true` picks the positive triple `t_j`,
    `σ j = false` picks the negative triple `t⁻_j`. -/
abbrev Selection (m : ℕ) := Fin m → Bool

/-- The internal node `a j` is covered EXACTLY ONCE: exactly one of
    `σ j = true` (the positive triple `t_j` touches `a j`) and
    `σ (j-1) = false` (the negative triple `t⁻_(j-1)` touches `a j`) holds. -/
def aCoveredOnce (σ : Selection m) (j : Fin m) : Prop :=
  Xor (σ j = true) (σ (j - 1) = false)

/-- The covered-once exclusive-or collapses to the local agreement `σ j = σ (j-1)`:
    `xor a (¬b) = (a == b)`. -/
lemma aCoveredOnce_iff (σ : Selection m) (j : Fin m) :
    aCoveredOnce σ j ↔ σ j = σ (j - 1) := by
  unfold aCoveredOnce
  cases h1 : σ j <;> cases h2 : σ (j - 1) <;> simp [Xor]

/-- A valid internal cover: every internal node `a j` is covered exactly once. -/
def ValidCover (σ : Selection m) : Prop :=
  ∀ j : Fin m, aCoveredOnce σ j

/-! ### Decidability.

    `aCoveredOnce` is decidable (it is an `Xor` of two decidable `Prop`s), but the `∀`-wrapper
    `ValidCover` does not auto-resolve through the `def`; we register both instances explicitly so
    `decide` fires at `m = 3` below. -/

instance (σ : Selection m) (j : Fin m) : Decidable (aCoveredOnce σ j) :=
  inferInstanceAs (Decidable (Xor _ _))

instance (σ : Selection m) : Decidable (ValidCover σ) :=
  inferInstanceAs (Decidable (∀ j : Fin m, aCoveredOnce σ j))

/-! ### The engine: local correctness.

    The wheel has EXACTLY TWO valid internal covers, the all-true and all-false selections. -/

/-- Every spoke agreeing with its cyclic predecessor forces a constant selection: each `σ j`
    equals `σ 0`.  Proved by strong induction on `j.val` (the cyclic predecessor strictly
    decreases `.val` away from `0`). -/
private lemma agree_imp_eq_zero (σ : Selection m)
    (hstep : ∀ j : Fin m, σ j = σ (j - 1)) :
    ∀ j : Fin m, σ j = σ ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ := by
  intro j
  induction hk : j.val using Nat.strong_induction_on generalizing j with
  | _ k IH =>
    subst hk
    by_cases hj : j = 0
    · subst hj; rfl
    · have hlt : (j - 1).val < j.val := by
        rw [Fin.val_sub_one_of_ne_zero hj]
        have : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj
        omega
      rw [hstep j, IH (j - 1).val hlt (j - 1) rfl]

/-- **The two-cover engine.**  A selection is a valid internal cover iff it is constant —
    the all-true or the all-false truth value.  (The `hm : 0 < m` hypothesis is kept in the
    signature for the downstream assembly; the wheel itself runs on the `[NeZero m]` instance.) -/
theorem validCover_iff_const (_hm : 0 < m) (σ : Selection m) :
    ValidCover σ ↔ (σ = fun _ => true) ∨ (σ = fun _ => false) := by
  constructor
  · intro h
    have hstep : ∀ j : Fin m, σ j = σ (j - 1) := fun j => (aCoveredOnce_iff σ j).mp (h j)
    have hconst := agree_imp_eq_zero σ hstep
    cases hz : σ ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ with
    | true =>
      left; funext j; rw [hconst j, hz]
    | false =>
      right; funext j; rw [hconst j, hz]
  · intro h j
    rw [aCoveredOnce_iff]
    rcases h with h | h <;> rw [h]

/-! ### Free-tip characterization (raw, per constant state).

    Truth-value LABELING is deferred to milestone 3; here we record, per constant state, which
    family of tips is left uncovered ("free") and thus available to the clause gadgets. -/

/-- The positive tip `posTip j` is free in state `σ` iff its triple `t_j` was NOT selected. -/
def posTipFree (σ : Selection m) (j : Fin m) : Prop := σ j = false

/-- The negative tip `negTip j` is free in state `σ` iff its triple `t⁻_j` was NOT selected. -/
def negTipFree (σ : Selection m) (j : Fin m) : Prop := σ j = true

omit [NeZero m] in
/-- The all-true (one truth value) state frees every negative tip and no positive tip. -/
theorem trueState_frees_neg (σ : Selection m) (h : σ = fun _ => true) :
    (∀ j, ¬ posTipFree σ j) ∧ (∀ j, negTipFree σ j) := by
  subst h
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simp [posTipFree]
  · simp [negTipFree]

omit [NeZero m] in
/-- The all-false (other truth value) state frees every positive tip and no negative tip. -/
theorem falseState_frees_pos (σ : Selection m) (h : σ = fun _ => false) :
    (∀ j, posTipFree σ j) ∧ (∀ j, ¬ negTipFree σ j) := by
  subst h
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simp [posTipFree]
  · simp [negTipFree]

/-! ### Concrete decide-lock at `m = 3` (kernel `decide`, axiom-clean — NOT `native_decide`).

    Mirrors `validCover_iff_const` at `m = 3`: the only two valid covers are the constants
    `![true,true,true]` and `![false,false,false]`. -/

example : ∀ σ : Fin 3 → Bool,
    ValidCover σ ↔ (σ = ![true, true, true]) ∨ (σ = ![false, false, false]) := by
  decide

/-! ### Axiom audit.

    Expect `[propext, Classical.choice, Quot.sound]` (or a subset) — NO `sorryAx`, and NO
    `Lean.ofReduceBool` (the latter would signal a `native_decide`, which we deliberately avoid). -/


end Sundog.VarWheel
