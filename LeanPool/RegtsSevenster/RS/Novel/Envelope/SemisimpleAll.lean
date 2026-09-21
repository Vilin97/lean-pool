/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockFactorialTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SemisimpleEnd

/-!
# Trace nondegeneracy, in Hom-typed form

`HomSpace.eq_zero_of_traces_vanish` is stated at the `HomSpace`
level; the Karoubi envelope needs it at morphisms of skein objects,
where the closure partner ranges over morphisms rather than
fragments.  Both forms are the same statement read through
`HomSpace.ofFragment`.

With the nilpotent-trace vanishing of `BlockFactorialTrace`, this is
what `isSemisimpleRing_of_trace` consumes to make every skein
endomorphism algebra semisimple.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- Trace nondegeneracy in the fully Hom-typed form: an
endomorphism of a skein object all of whose composites have
vanishing trace is zero. -/
theorem end_eq_zero_of_traces_vanish (Y : SkeinObj f)
    (a : Y ⟶ Y)
    (ha : ∀ b : Y ⟶ Y,
      HomSpace.traceMap f.val Y.arity (a ≫ b) = 0) :
    a = 0 :=
  HomSpace.eq_zero_of_traces_vanish f a
    (fun G => ha (HomSpace.ofFragment f.val G))

/-- Mixed-Hom trace nondegeneracy: a morphism between skein
objects all of whose closures against reverse morphisms have
vanishing trace is zero. -/
theorem hom_eq_zero_of_traces_vanish' (Y Z : SkeinObj f)
    (a : Y ⟶ Z)
    (ha : ∀ b : Z ⟶ Y,
      HomSpace.traceMap f.val Y.arity (a ≫ b) = 0) :
    a = 0 :=
  HomSpace.eq_zero_of_traces_vanish f a
    (fun G => ha (HomSpace.ofFragment f.val G))

end RS
