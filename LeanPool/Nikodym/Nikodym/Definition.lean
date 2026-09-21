/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic

/-!
# Finite field Nikodym sets

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Nikodym_set)

A finite field variant of the Nikodym problem considers subsets of `𝔽_qⁿ` such that through
every point of `𝔽_qⁿ` there is a line meeting the complement of the set in at most that point.
-/

namespace Nikodym

/--
A set `S ⊆ 𝔽_qⁿ` is a Nikodym set if for every point `x ∈ 𝔽_qⁿ` there is a line through `x`
all of whose points other than `x` lie in `S`. Lines are parametrised as `x + t • v` with
`v ≠ 0`, so the condition reads `x + t • v ∈ S` for all `t ≠ 0`.
-/
def IsNikodym {F : Type*} [Field F] {n : ℕ} (S : Finset (Fin n → F)) : Prop :=
  ∀ x, ∃ v, v ≠ 0 ∧ ∀ t : F, t ≠ 0 → x + t • v ∈ S

/--
A trivial example: for `n > 0`, the whole space `𝔽_qⁿ` is a Nikodym set.
-/
theorem isNikodym_univ {F : Type*} [Field F] [Fintype F] {n : ℕ} (hn : 0 < n) :
    IsNikodym (Finset.univ : Finset (Fin n → F)) := fun _ ↦
  ⟨Pi.single ⟨0, hn⟩ 1, by simp, fun _ _ ↦ Finset.mem_univ _⟩

/-- Supersets of Nikodym sets are Nikodym. -/
theorem IsNikodym.mono {F : Type*} [Field F] {n : ℕ} {S T : Finset (Fin n → F)}
    (hS : IsNikodym S) (hST : S ⊆ T) : IsNikodym T := fun x ↦
  let ⟨v, hv, h⟩ := hS x
  ⟨v, hv, fun t ht ↦ hST (h t ht)⟩

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
