/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Label pairs sharing no label

One condition recurs wherever pairs of labels are handled: two pairs
have all four of their labels distinct across the pair.  It is what
makes a chord diagram well formed, what lets a fold over a list of
pairs be reordered, and what makes the symmetric-difference fold of
a pair list its plain union.  It is stated once here, with named
fields, so that the four inequalities are never read off a nested
conjunction by position.
-/

@[expose] public section

namespace RS

variable {α : Type*}

/-- **Two label pairs sharing no label.** -/
structure PairDisjoint (p q : α × α) : Prop where
  /-- The first labels differ. -/
  fst_ne_fst : p.1 ≠ q.1
  /-- The first label of `p` is not the second of `q`. -/
  fst_ne_snd : p.1 ≠ q.2
  /-- The second label of `p` is not the first of `q`. -/
  snd_ne_fst : p.2 ≠ q.1
  /-- The second labels differ. -/
  snd_ne_snd : p.2 ≠ q.2

/-- Sharing no label survives swapping the ends of the first pair. -/
theorem PairDisjoint.swap_left {p q : α × α} (h : PairDisjoint p q) :
    PairDisjoint p.swap q :=
  ⟨h.snd_ne_fst, h.snd_ne_snd, h.fst_ne_fst, h.fst_ne_snd⟩

/-- Sharing no label survives swapping the ends of the second pair. -/
theorem PairDisjoint.swap_right {p q : α × α} (h : PairDisjoint p q) :
    PairDisjoint p q.swap :=
  ⟨h.fst_ne_snd, h.fst_ne_fst, h.snd_ne_snd, h.snd_ne_fst⟩

end RS
