/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.VecNotation

/-!
  Sundogcert/SATNPHard.lean — MILESTONE 1 of the `3SAT ≤ 3DM` marathon.

  WHAT THIS FILE PROVIDES (the FOUNDATION — definitions + concrete validation, no reduction yet):
    * `Literal n`     — a variable index `Fin n` plus a sign (`true` = `xᵢ`, `false` = `¬xᵢ`).
    * `Assignment n`  — a Boolean assignment `Fin n → Bool`.
    * `evalLiteral`   — evaluate one literal under an assignment.
    * `Clause n`      — an ORDERED triple of literals (`Fin 3 → Literal n`; cleaner than a
                        Finset for the downstream gadget's variable-wheel / clause indexing).
    * `clauseSat`     — a clause is satisfied iff at least one of its 3 literals is true.
    * `Formula n m`   — a 3-CNF formula: `m` indexed clauses.
    * `formulaSat`    — every clause holds.
    * `Satisfiable`   — **3-SAT**: some assignment satisfies the formula.

  Decidability of `clauseSat`/`formulaSat`/`Satisfiable` on concrete instances is AUTOMATIC: the
  `∃`/`∀` range over `Fin _` and `Assignment n = Fin n → Bool` (Fintypes with `DecidableEq`),
  and `evalLiteral … = true` is decidable.  This lets `decide` kernel-reduce the two concrete
  examples below — AXIOM-CLEAN (no `Lean.ofReduceBool`; we use `decide`, never `native_decide`).

  CONCRETE VALIDATION (locks the encoding):
    * `ex_sat`   — `Satisfiable fSat` for `fSat` (`n=2, m=1`, clause `x₀ ∨ x₁ ∨ x₀`).
    * `ex_unsat` — `¬ Satisfiable fUnsat` for `fUnsat` (`n=1, m=2`, clauses `x₀∨x₀∨x₀`,
                   `¬x₀∨¬x₀∨¬x₀`).

  THE IMPORTED WALL (named, NOT proved — mathlib has no complexity framework):
    * the NP complexity class itself, and poly-time-ness of any reduction;
    * 3SAT's OWN NP-hardness — Cook–Levin, the DEEP TERMINAL WALL, a multi-year formalization,
      named forever as the ultimate source of every Karp-reduction hardness claim in this chain.
  STANDING LIMIT: this file defines the 3SAT *problem* and validates the encoding.  The gadget
  reduction (variable wheel, clause gadget, garbage) landing on `Sundog.MatchingNPHard.ThreeDM`,
  and its correctness, is the work to come — milestones 2+ of `3SAT ≤ 3DM ≤ X3C ≤ Decodes`.
-/

namespace Sundog.SATNPHard

/-- A literal: a variable index plus a sign (`true` = positive `xᵢ`, `false` = negated). -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- A Boolean assignment. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- Evaluate a literal under an assignment. -/
def evalLiteral {n : ℕ} (a : Assignment n) (l : Literal n) : Bool :=
  if l.2 then a l.1 else !(a l.1)

/-- A 3-clause: an ORDERED triple of literals (`Fin 3 → Literal` — cleaner than a Finset
    for the downstream gadget's indexing). -/
abbrev Clause (n : ℕ) := Fin 3 → Literal n

/-- A clause is satisfied iff at least one of its 3 literals is true. -/
def clauseSat {n : ℕ} (a : Assignment n) (c : Clause n) : Prop :=
  ∃ k : Fin 3, evalLiteral a (c k) = true

/-- A 3-CNF formula: `m` clauses, indexed. -/
abbrev Formula (n m : ℕ) := Fin m → Clause n

/-- A formula is satisfied iff every clause is. -/
def formulaSat {n m : ℕ} (a : Assignment n) (f : Formula n m) : Prop :=
  ∀ k : Fin m, clauseSat a (f k)

/-- **3-SAT**: a formula is satisfiable iff some assignment satisfies it. -/
def Satisfiable {n m : ℕ} (f : Formula n m) : Prop :=
  ∃ a : Assignment n, formulaSat a f

/-! ### Decidability.

    `evalLiteral … = true` is decidable (`DecidableEq Bool`); the bounded `∃`/`∀` over `Fin _`
    and `Assignment n = Fin n → Bool` (a Fintype) then make `clauseSat`/`formulaSat`/`Satisfiable`
    decidable via `Fintype.decidableExistsFintype` / `Fintype.decidableForallFintype`.  These
    instances let `decide` kernel-reduce the concrete examples below — no `native_decide`. -/

instance {n : ℕ} (a : Assignment n) (c : Clause n) : Decidable (clauseSat a c) :=
  inferInstanceAs (Decidable (∃ k : Fin 3, evalLiteral a (c k) = true))

instance {n m : ℕ} (a : Assignment n) (f : Formula n m) : Decidable (formulaSat a f) :=
  inferInstanceAs (Decidable (∀ k : Fin m, clauseSat a (f k)))

instance {n m : ℕ} (f : Formula n m) : Decidable (Satisfiable f) :=
  inferInstanceAs (Decidable (∃ a : Assignment n, formulaSat a f))

/-! ### Concrete validation (A): a SATISFIABLE formula.

    `n = 2, m = 1`; the single clause is `x₀ ∨ x₁ ∨ x₀`, i.e. literals
    `(0, true), (1, true), (0, true)`.  Satisfiable: take `a = ![true, true]` (or any `a` with
    `a 0 = true`).  `∃` ranges over the 4 assignments of `Fin 2 → Bool` — decidable. -/

/-- The single satisfiable clause `x₀ ∨ x₁ ∨ x₀`. -/
def cSat : Clause 2 := ![(0, true), (1, true), (0, true)]

/-- The satisfiable formula with one clause. -/
def fSat : Formula 2 1 := ![cSat]

theorem ex_sat : Satisfiable fSat := by decide

/-! ### Concrete validation (B): an UNSATISFIABLE formula.

    `n = 1, m = 2`; clauses `x₀ ∨ x₀ ∨ x₀` and `¬x₀ ∨ ¬x₀ ∨ ¬x₀`.  No assignment of the single
    variable can satisfy both.  `¬∃` ranges over the 2 assignments of `Fin 1 → Bool` —
    decidable. -/

/-- The all-positive clause `x₀ ∨ x₀ ∨ x₀`. -/
def cPos : Clause 1 := ![(0, true), (0, true), (0, true)]

/-- The all-negative clause `¬x₀ ∨ ¬x₀ ∨ ¬x₀`. -/
def cNeg : Clause 1 := ![(0, false), (0, false), (0, false)]

/-- The unsatisfiable formula with the two contradictory clauses. -/
def fUnsat : Formula 1 2 := ![cPos, cNeg]

theorem ex_unsat : ¬ Satisfiable fUnsat := by decide

/-! ### Axiom audit.

    Expect `[propext, Classical.choice, Quot.sound]` (or a subset) — NO `sorryAx`, and NO
    `Lean.ofReduceBool` (the latter would signal a `native_decide`, which we deliberately avoid). -/


end Sundog.SATNPHard
