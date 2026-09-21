/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Main

/-!
# Proved solution

This module imports the full proof development.  The three declarations named in
`comparator.json`,

* `Nikodym.card_compl_pow_mul_card_le`,
* `Nikodym.card_ge_pow_sub`,
* `Nikodym.exists_isNikodym_card_le`,

are proved in `Nikodym/Main.lean` (with the same names and statements as in `Challenge.lean`)
and are therefore present in this module's environment.  Comparator checks that each one has
exactly the same statement as its counterpart in `Challenge.lean`, that the definition
`Nikodym.IsNikodym` appearing in those statements is identical in both modules, and that the
proofs use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

The `example`s below are a readable local witness of the same facts: they type-check only if
the proved theorems have the advertised types.
-/

namespace Nikodym

example {F : Type*} [Field F] [Fintype F] {d : ℕ} (hd : 2 ≤ d) (N : Finset (Fin d → F))
    (hN : IsNikodym N) :
    (Fintype.card F ^ d - N.card) ^ 2 ^ (d - 1) * Fintype.card F ≤
      (8 * d ^ 2 + 1) ^ 2 ^ (d - 1) * Fintype.card F ^ (d * 2 ^ (d - 1)) :=
  card_compl_pow_mul_card_le hd N hN

example {F : Type*} [Field F] [Fintype F] {d : ℕ} (hd : 2 ≤ d) (N : Finset (Fin d → F))
    (hN : IsNikodym N) :
    (Fintype.card F : ℝ) ^ d -
        (8 * d ^ 2 + 1) * (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ))) ≤
      N.card :=
  card_ge_pow_sub hd N hN

example {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ (F : Type) [Field F] [Fintype F],
      (Fintype.card F).Prime → q₀ ≤ Fintype.card F →
        ∃ N : Finset (Fin d → F), IsNikodym N ∧
          (N.card : ℝ) ≤ (Fintype.card F : ℝ) ^ d -
            (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ)) - ε) :=
  exists_isNikodym_card_le hd hε

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
