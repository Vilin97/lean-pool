/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitExact

/-!
# Exactness from short exact sequences

An additive functor between abelian categories that carries short
exact sequences to short exact sequences preserves finite limits and
finite colimits.  Mathlib supplies the equivalence as
`CategoryTheory.Functor.exact_tfae`, whose first and fourth entries
are exactly the hypothesis and the pair of conclusions; the general
results below are the named projections of that equivalence, and
the third of them records the intermediate entry, preservation of
homology.

-/

@[expose] public section

namespace RS

open CategoryTheory Limits

universe v u v' u'

section General

variable {C : Type u}

/-- **A functor carrying short exact sequences to short exact
sequences preserves finite limits.** -/
theorem preservesFiniteLimits_of_shortExact
    [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ (S : CategoryTheory.ShortComplex C), S.ShortExact →
      (S.map F).ShortExact) :
    Limits.PreservesFiniteLimits F :=
  have hboth : Limits.PreservesFiniteLimits F ∧
      Limits.PreservesFiniteColimits F :=
    ((CategoryTheory.Functor.exact_tfae F).out 1 4).mp h
  hboth.1

/-- **A functor carrying short exact sequences to short exact
sequences preserves finite colimits.** -/
theorem preservesFiniteColimits_of_shortExact
    [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D)
    [F.Additive]
    (h : ∀ (S : CategoryTheory.ShortComplex C), S.ShortExact →
      (S.map F).ShortExact) :
    Limits.PreservesFiniteColimits F :=
  have hboth : Limits.PreservesFiniteLimits F ∧
      Limits.PreservesFiniteColimits F :=
    ((CategoryTheory.Functor.exact_tfae F).out 1 4).mp h
  hboth.2

/-- **A functor carrying short exact sequences to short exact
sequences preserves homology.**  This is the intermediate entry of
the same equivalence, from which both preservation statements
above are read off. -/
theorem preservesHomology_of_shortExact
    [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ (S : CategoryTheory.ShortComplex C), S.ShortExact →
      (S.map F).ShortExact) :
    F.PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae F).out 1 3).mp h

end General

end RS
