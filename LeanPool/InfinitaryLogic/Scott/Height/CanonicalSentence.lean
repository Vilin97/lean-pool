/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.Height.Defs
/-!
# Canonical Scott Sentence

The canonical Scott sentence of a structure M is the Scott formula at Scott
height level for the empty tuple. It is the "optimal" Scott sentence whose
quantifier rank is minimized among Scott formulas.

## Main Definitions

- `canonicalScottSentence`: The Scott formula at Scott height for the empty tuple.

## Main Results

- `canonicalScottSentence_iff_potentialIso`: Characterizes potential isomorphism.
- `canonicalScottSentence_characterizes`: For countable structures, characterizes isomorphism.
- `canonicalScottSentence_equiv_scottSentence`: Semantically equivalent to the standard
Scott sentence.
- `canonicalScottSentence_qrank`: Quantifier rank bounded by scottHeight + ω.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- The canonical Scott sentence of a structure M, defined as the Scott formula at Scott
height level for the empty tuple.

This is the "optimal" Scott sentence in the sense that its quantifier rank is minimized
(among Scott formulas). It characterizes the structure up to potential isomorphism,
and for countable structures, up to isomorphism. -/
noncomputable def canonicalScottSentence (M : Type w) [L.Structure M] [Countable M] :
    L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) Fin.elim0 (scottHeight (L := L) M)

end Language

end FirstOrder
