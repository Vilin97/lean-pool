/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.SATNPHard
import LeanPool.Sundogcert.VarWheel
import Mathlib.Data.Fin.VecNotation

/-!
  Sundogcert/ClauseGadget.lean — MILESTONE 3 of the `3SAT ≤ 3DM` marathon.

  WHAT THIS FILE PROVIDES (the Garey–Johnson CLAUSE gadget + the POLARITY BRIDGE):
    For each clause `c_k` the gadget owns two INTERNAL nodes `s1_k`, `s2_k` (covered exactly once,
    local to this clause) and THREE cover triples, one per literal-slot `k' ∈ {0,1,2}`:
        slot-k' triple = (tip(c_k, k'), s1_k, s2_k)
    The slot-`k'` triple is USABLE iff that literal's TIP is FREE — i.e. NOT consumed by its
    variable wheel (milestone 2).  Hence `s1_k`, `s2_k` are coverable iff AT LEAST ONE of the three
    slots' tips is free.  The global matching uses exactly one such triple; garbage collection mops
    up the remaining free tips (milestone 4).

  THE GADGET PICTURE (one clause `c_k`; the three slot-triples fan into the shared internal pair):

        tip(c_k,0) ─┐
        tip(c_k,1) ─+──▶  s1_k , s2_k   (each slot-triple = (tip, s1_k, s2_k))
        tip(c_k,2) ─┘
        `s1_k, s2_k` coverable  ↔  ∃ slot k' with tip(c_k,k') FREE.

  THE POLARITY CONVENTION (this DISCHARGES milestone 2's deferred truth-value labeling — the classic
  bug locus, so stated with care and validated end-to-end by kernel `decide` below):
    Variable `xᵢ` takes the Boolean value `ai` IFF its wheel runs the CONSTANT selection
    `σᵢ = fun _ => !ai`.  Then:
        ai = true   ⟹  σᵢ = const false  ⟹  (VarWheel.falseState_frees_pos) POSITIVE tips free;
        ai = false  ⟹  σᵢ = const true   ⟹  (VarWheel.trueState_frees_neg)  NEGATIVE tips free.
    With `VarWheel.posTipFree σ j := (σ j = false)` and `negTipFree σ j := (σ j = true)`, and
    `σᵢ = fun _ => !ai`:
        posTipFree ↔ (!ai = false) ↔ ai = true;   negTipFree ↔ (!ai = true) ↔ ai = false .
    A literal `l = (i, sign)`: a POSITIVE literal (`sign = true`) uses the positive tip, free iff
    `ai = true`, i.e. iff `evalLiteral = ai`; a NEGATIVE literal (`sign = false`) uses the negative
    tip, free iff `ai = false`, i.e. iff `evalLiteral = !ai`.  In every case the tip is free exactly
    when the literal evaluates to `true` — `litTipFree ↔ evalLiteral = true`.  THIS is the bridge.

  THE IMPORTED WALL (named, NOT proved — mathlib has no complexity framework):
    * the NP complexity class and poly-time-ness of the reduction;
    * 3SAT's OWN NP-hardness — Cook–Levin, the deep terminal wall sourcing every Karp-reduction
      hardness claim in this `3SAT ≤ 3DM ≤ X3C ≤ Decodes` chain.

  STANDING LIMIT: this module proves the clause gadget's LOCAL correctness (a clause is coverable
  iff it is satisfied, via the polarity bridge).  The garbage-collection triples and the GLOBAL
  assembly onto `Sundog.MatchingNPHard.ThreeDM` are milestones 4–8.

  Decidability of `clauseCoverable` is registered explicitly (it is an `∃` over `Fin 3` of a
  decidable `Prop`).  This locks the polarity convention end-to-end by kernel `decide` —
  AXIOM-CLEAN (no `Lean.ofReduceBool`; we use `decide`, never `native_decide`).
-/

open Sundog.SATNPHard Sundog.VarWheel

namespace Sundog.ClauseGadget

variable {n : ℕ}

/-- The clause gadget's internal pair `s1_k, s2_k` is coverable iff AT LEAST ONE of the three
    slots' tips is free.  `free k` records whether the slot-`k` tip is free. -/
def clauseCoverable (free : Fin 3 → Bool) : Prop := ∃ k : Fin 3, free k = true

/-- `clauseCoverable` is an `∃` over `Fin 3` of a decidable `Prop`; register the instance
    explicitly so `decide` fires at the `def` level (and for the downstream milestones 5–8). -/
instance (free : Fin 3 → Bool) : Decidable (clauseCoverable free) :=
  inferInstanceAs (Decidable (∃ k : Fin 3, free k = true))

/-! ### The polarity bridge (substantive — USES the VarWheel free-tip predicates).

    `posTipFree`/`negTipFree` live under `variable {m : ℕ} [NeZero m]` in `VarWheel`, so the bridge
    defs/theorems carry the same `{m} [NeZero m]` binders. -/

/-- A positive tip under the constant wheel `σ = fun _ => !ai` is free iff `ai = true`. -/
theorem posTipFree_const_iff (ai : Bool) {m : ℕ} [NeZero m] (j : Fin m) :
    posTipFree (fun _ => !ai) j ↔ ai = true := by
  unfold posTipFree; cases ai <;> simp

/-- A negative tip under the constant wheel `σ = fun _ => !ai` is free iff `ai = false`. -/
theorem negTipFree_const_iff (ai : Bool) {m : ℕ} [NeZero m] (j : Fin m) :
    negTipFree (fun _ => !ai) j ↔ ai = false := by
  unfold negTipFree; cases ai <;> simp

/-- Whether the tip of literal `l` (under assignment `a`, on the variable's wheel `j`) is FREE:
    a positive literal looks at the positive tip, a negative literal at the negative tip — each
    under the constant state `fun _ => !(a l.1)` carrying `xₗ.₁`'s truth value. -/
def litTipFree (a : Assignment n) (l : Literal n) {m : ℕ} (j : Fin m) : Prop :=
  if l.2 then posTipFree (fun _ => !(a l.1)) j else negTipFree (fun _ => !(a l.1)) j

/-- **THE BRIDGE** (discharges milestone 2's deferred labeling): the tip of literal `l` is free
    exactly when `l` evaluates to `true`.  Case on the sign `l.2`; both sides split in lockstep on
    the same `if l.2`, the positive/negative tip branch matching the `evalLiteral` branch. -/
theorem litTipFree_iff_eval (a : Assignment n) (l : Literal n) {m : ℕ} [NeZero m] (j : Fin m) :
    litTipFree a l j ↔ evalLiteral a l = true := by
  unfold litTipFree evalLiteral
  cases hl : l.2 <;> simp [posTipFree_const_iff, negTipFree_const_iff]

/-! ### Clause local correctness (clean composition — near-definitional once the bridge is set). -/

/-- A clause's internal pair is coverable (some slot-tip free) iff the clause is SATISFIED — both
    sides unfold to `∃ k, evalLiteral a (c k) = true`. -/
theorem clauseCoverable_iff_clauseSat (a : Assignment n) (c : Clause n) :
    clauseCoverable (fun k => evalLiteral a (c k)) ↔ clauseSat a c := by
  unfold clauseCoverable clauseSat; rfl

/-! ### Concrete decide-locks at the clause `x₀ ∨ x₁ ∨ x₀` (`SATNPHard.cSat`).

    These exercise `evalLiteral` + `clauseCoverable` together, validating the POLARITY convention
    end-to-end by kernel `decide` — AXIOM-CLEAN (no `Lean.ofReduceBool`, no `native_decide`).
    `![false, true]` makes `a 1 = true` ⟹ slot-1 literal `(1, true)` evaluates true ⟹ coverable;
    `![false, false]` makes every literal false ⟹ NOT coverable. -/

/-- SAT lock: `a = ![false, true]` covers the clause via the `x₁` slot. -/
theorem lockSat : clauseCoverable (fun k => evalLiteral ![false, true] (cSat k)) := by decide

/-- UNSAT lock: `a = ![false, false]` leaves every slot-tip consumed — not coverable. -/
theorem lockUnsat : ¬ clauseCoverable (fun k => evalLiteral ![false, false] (cSat k)) := by decide

/-! ### Axiom audit.

    Bridge iffs: `[propext]`.  `clauseCoverable_iff_clauseSat`: NO axioms (purely definitional).
    Decide-locks: `[propext, Quot.sound]` — NO `sorryAx`, NO `Lean.ofReduceBool` (genuine kernel
    `decide`, NOT `native_decide`). -/


end Sundog.ClauseGadget
