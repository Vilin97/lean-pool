/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# LeanPool.Rupert.FinCases

Imported Lean Pool material for `LeanPool.Rupert.FinCases`.
-/

/--
Lemma for helping with goals such as
```
  ∀ i : Fin 8, 0 ≤ ![1.4, 3, 5, 2, 0, 1, 1, 0.2]
```
Usually one would do something like `intro i; fin_cases i <;> norm_num` here.
However, `fin_cases` consumes a considerable number of heartbeats, which
can become problematic if this is done many times in a larger proof.

With this lemma, once can instead do

```
apply all_fin_8_vec <;> norm_num
```
-/
lemma all_fin_8_vec {α : Type} {a b c d e f g h : α} (p : α → Prop) :
    p a → p b → p c → p d → p e → p f → p g → p h →
    ∀ ii : Fin 8, p (![a, b, c, d, e, f, g, h] ii) := by
  intro ha hb hc hd he hf hg hh ii
  fin_cases ii <;> simp_all
