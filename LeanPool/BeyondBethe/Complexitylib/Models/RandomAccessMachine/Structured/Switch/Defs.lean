/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Defs

/-!
# Finite numeric switches for structured RAM programs

`select` compiles a finite family of commands into a decrementing decision
tree. A valid numeric code in `test` selects the corresponding branch. The
register `one` must contain one and be distinct from `test`.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Switch


/-- Store presented to the selected branch after the tested code has been
decremented to zero. -/
def cleared (store : Store) (test : ℕ) : Store :=
  Function.update store test 0

/-- A finite numeric switch. Invalid codes fall through to `skip`; correctness
theorems use the explicit hypothesis `code < count`. -/
def select : (count : ℕ) → (test one : ℕ) → (Fin count → Cmd) → Cmd
  | 0, _, _, _ => .skip
  | count + 1, test, one, branch =>
      .ifZero test (branch ⟨0, by omega⟩)
        (.seq (.basic (.sub test test one))
          (select count test one (fun index => branch index.succ)))

/-- Exact compiled/source transition count for selecting `code`. -/
def stepCount (code branchSteps : ℕ) : ℕ :=
  3 * code + branchSteps + 1

/-- Envelope-based logarithmic-cost bound for selecting `code`.

Each skipped case pays at most seven envelope widths: three for the nonzero
conditional and four for the decrement. The selected zero case pays one. -/
def costBound (code branchCost width : ℕ) : ℕ :=
  (7 * code + 1) * width + branchCost

end Switch

end Structured

end RAM

end Complexity
