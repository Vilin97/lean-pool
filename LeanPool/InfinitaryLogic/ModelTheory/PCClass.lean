/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
import Mathlib.ModelTheory.LanguageMap

/-!
# The abstract PC-class membership predicate (issue #10, Unit 4)

`PCMem g Θ M` — a structure `M` for the base language `L` is in the projective class of an
`L'`-sentence `Θ` along `g : L →ᴸ L'` iff **`M` itself** (same carrier) expands to an
`L'`-structure modelling `Θ`.  This is Marker's `PC_{ω₁ω}` notion (Corollary 4.22): membership
is existence of a *same-carrier* expansion, enforced here by `LHom.IsExpansionOn`.

Deliberately language-generic and free of any nonemptiness assumption; the López–Escobar
specialization (`baseGraphEmb`, code compatibility) lives in `Methods/LopezEscobar/PCMem.lean`.
-/

namespace FirstOrder.Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

/-- **Projective-class membership**: `M` (as an `L`-structure) expands, on the same carrier, to
an `L'`-structure satisfying `Θ`.  No nonemptiness is built in. -/
def PCMem (g : L →ᴸ L') (Θ : L'.Sentenceω) (M : Type*) [L.Structure M] : Prop :=
  ∃ S' : L'.Structure M, @LHom.IsExpansionOn L L' g M _ S' ∧ @Sentenceω.Realize L' Θ M S'

end FirstOrder.Language
