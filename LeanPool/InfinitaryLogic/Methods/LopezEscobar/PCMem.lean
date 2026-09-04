/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.PCClass
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.StandardModel
/-!
# The López–Escobar PC-class interface (issue #10, Unit 4 commit 1)

The base embedding `baseGraphEmb : L →ᴸ graphLanguage (KLang L)` (available because `L` is
relational), and the code compatibility theorem tying the abstract `PCMem` on `ℕ` to
membership in `codeReduct '' ModelsOf Θ`.  This freezes the PC-class interface independently
of López–Escobar's tree machinery.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The base embedding of `L` into the relationalized `graphLanguage (KLang L)`: functions are
vacuous (`L` is relational), base relations go to their graph-language base image. -/
def baseGraphEmb : L →ᴸ graphLanguage (KLang L) where
  onFunction {_} f := isEmptyElim f
  onRelation {_} R := GraphRelation.base (Sum.inl R)









end FirstOrder.Language
