/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreAdditive
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModAbelian

/-!
# Split short exact sequences and additive functors

A short exact sequence whose epimorphism admits a section is split,
and a split sequence stays split — hence short exact — under any
additive functor.  This is the mechanism by which the fibre functor
of `RS.Classical.Deligne.FibreAdditive` is seen to carry short exact
sequences to short exact sequences: base change produces a section
of the epimorphism, and the splitting is then transported by
additivity alone, with no exactness hypothesis on the functor.

Both steps are available in Mathlib.  The splitting induced by a
section is `CategoryTheory.ShortComplex.Splitting.ofExactOfSection`,
which needs only a balanced preadditive category, and the transport
is `CategoryTheory.ShortComplex.Splitting.map` followed by
`CategoryTheory.ShortComplex.Splitting.shortExact`.  The three
two results below are the packaged forms used in this development,
naming the general statements at the shape in which they are
consumed.
-/

@[expose] public section

namespace RS

open CategoryTheory Limits

universe v u v' u'

section General

variable {C : Type u}

/-- **A section of the epimorphism splits a short exact sequence.**
The retraction is the factorization of `𝟙 - g ≫ s` through the
kernel `f`. -/
noncomputable def ShortComplex.ShortExact.splittingOfSplitEpi
    [Category.{v} C] [Abelian C]
    {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact)
    (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    S.Splitting :=
  CategoryTheory.ShortComplex.Splitting.ofExactOfSection S hS.exact s
    hs hS.mono_f

end General

end RS
