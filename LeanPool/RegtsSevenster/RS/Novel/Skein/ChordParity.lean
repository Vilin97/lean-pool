/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.PathCanon
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueSplitProof

/-!
# The between-legs parity identity

The abstract heart of the canonical splitting's cut sign: for any
family of chords, the number of chord ends strictly between the
cut labels has the parity of the number of chords crossing the
cut — a nested chord contributes both ends, a crossing chord
exactly one.
-/

@[expose] public section

namespace RS



variable {α : Type}

/-- A chord crosses the cut when exactly one endpoint lies
between the cut labels. -/
def CrossesCut [LinearOrder α]
    (i j : α) (p : α × α) : Prop :=
  Xor (i < p.1 ∧ p.1 < j) (i < p.2 ∧ p.2 < j)

end RS
