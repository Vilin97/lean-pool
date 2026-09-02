/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Words for a full symmetric top group

Only the distinguishing-word facts used by the every-base construction are
included here.
-/

namespace Saxl

/-- A colour word has trivial stabilizer under contravariant reindexing. -/
def WordDistinguishing (Q : Type*) {ι C : Type*} [Group Q] [MulAction Q ι]
    (word : ι → C) : Prop :=
  ∀ q : Q, (∀ i, word (q⁻¹ • i) = word i) → q = 1

/-- For the natural action of the full symmetric group, a word is
distinguishing exactly when it has no repeated colour. -/
theorem symmetricTop_wordDistinguishing_iff_injective
    {C D : Type*} (word : C → D) :
    WordDistinguishing (Equiv.Perm C) word ↔ Function.Injective word := by
  classical
  constructor
  · intro hword i j hij
    by_contra hne
    have hswap : Equiv.swap i j = (1 : Equiv.Perm C) := by
      apply hword (Equiv.swap i j)
      intro k
      change word ((Equiv.swap i j).symm k) = word k
      rw [Equiv.symm_swap]
      by_cases hki : k = i
      · subst k
        simpa using hij.symm
      by_cases hkj : k = j
      · subst k
        simpa using hij
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    have := DFunLike.congr_fun hswap i
    have hji : j = i := by simpa using this
    exact hne hji.symm
  · intro hinjective q hq
    apply Equiv.ext
    intro i
    have h := hinjective (hq (q • i))
    simpa [Equiv.Perm.smul_def] using h.symm

/-- A self-colouring of a finite coordinate type distinguishes its full
symmetric group exactly when it is a bijection. -/
theorem symmetricTop_wordDistinguishing_iff_bijective
    {C : Type*} [Finite C] (word : C → C) :
    WordDistinguishing (Equiv.Perm C) word ↔ Function.Bijective word := by
  rw [symmetricTop_wordDistinguishing_iff_injective]
  exact Finite.injective_iff_bijective

end Saxl
