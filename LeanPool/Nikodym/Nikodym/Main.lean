/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Definition
import LeanPool.Nikodym.Nikodym.LowerBound.Main
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Assembly
import LeanPool.Nikodym.Nikodym.Construction.Main

/-!
# The sharp Nikodym exponent: target statements

This file records the final theorems of the project; all of them are proved without `sorry`.
The upper bound `exists_isNikodym_card_le` is `Nikodym.Construction.Main`.  The two lower-bound
statements are the conditional theorems of `Nikodym.LowerBound.Main` instantiated with the
commutative-algebra interface `Nikodym.LowerBound.algebraInterface`, which is established for
every field in `Nikodym.LowerBound.Algebra.Assembly` following `docs/algebra_backend_design.md`.

Let `F` be a finite field with `q` elements, `d ≥ 2`, and `N ⊆ F^d` a Nikodym set.

* **Lower bound** (`docs/nikodym_sharp_power_saving.pdf`, Corollary 2).  With
  `C = 8 d ^ 2 + 1`,
  `|N| ≥ q ^ d - C · q ^ (d - 2 ^ (1 - d))`.
  We state it first in the denominator-free natural-number form of the blueprint (node C10),
  `|F^d \ N| ^ (2 ^ (d - 1)) · q ≤ C ^ (2 ^ (d - 1)) · q ^ (d · 2 ^ (d - 1))`,
  and then as the displayed real inequality (node C11).

* **Upper bound** (`docs/Nikodym_construction.pdf`, Corollary 1.2).  For every `ε > 0` and
  all sufficiently large primes `q`, there is a Nikodym set `N ⊆ F_q^d` with
  `|N| ≤ q ^ d - q ^ (d - 2 ^ (1 - d) - ε)`.
-/

open Real

namespace Nikodym

variable {F : Type*} [Field F] [Fintype F] {d : ℕ}

/-- **Lower bound, integer form** (blueprint node C10).  Every Nikodym set `N ⊆ F^d`, `d ≥ 2`,
satisfies `|F^d \ N| ^ (2 ^ (d - 1)) · q ≤ (8 d ^ 2 + 1) ^ (2 ^ (d - 1)) · q ^ (d · 2 ^ (d - 1))`,
where `q = |F|`. -/
theorem card_compl_pow_mul_card_le (hd : 2 ≤ d) (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F ^ d - N.card) ^ 2 ^ (d - 1) * Fintype.card F ≤
      (8 * d ^ 2 + 1) ^ 2 ^ (d - 1) * Fintype.card F ^ (d * 2 ^ (d - 1)) :=
  LowerBound.card_compl_pow_mul_card_le_of_interface (LowerBound.algebraInterface F d) hd N hN

/-- **Lower bound, real form** (blueprint node C11).  Every Nikodym set `N ⊆ F^d`, `d ≥ 2`,
satisfies `|N| ≥ q ^ d - (8 d ^ 2 + 1) · q ^ (d - 2 ^ (1 - d))`, where `q = |F|`. -/
theorem card_ge_pow_sub (hd : 2 ≤ d) (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F : ℝ) ^ d -
        (8 * d ^ 2 + 1) * (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ))) ≤
      N.card :=
  LowerBound.card_ge_pow_sub_of_interface (LowerBound.algebraInterface F d) hd N hN

/-- **Upper bound** (construction).  For `d ≥ 2` and `ε > 0`, every finite field `F` of
sufficiently large prime cardinality `q` contains a Nikodym set `N ⊆ F^d` with
`|N| ≤ q ^ d - q ^ (d - 2 ^ (1 - d) - ε)`. -/
theorem exists_isNikodym_card_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ (F : Type) [Field F] [Fintype F],
      (Fintype.card F).Prime → q₀ ≤ Fintype.card F →
        ∃ N : Finset (Fin d → F), IsNikodym N ∧
          (N.card : ℝ) ≤ (Fintype.card F : ℝ) ^ d -
            (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ)) - ε) :=
  exists_isNikodym_card_le_aux hd hε

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
