/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVariable

/-!
# Random families

Indexed random-object vocabulary shared by stochastic-process,
empirical-process, and later finite-family APIs.

This file keeps the repository's unbundled model: a family is an indexed
collection of random variables, and measurability is tracked by predicates.
-/

namespace HighDimProb

open MeasureTheory

/-- An indexed family of `E`-valued random variables. -/
abbrev RandomFamily (Omega I E : Type*) :=
  I -> RandomVariable Omega E

/-- An indexed family of real-valued random variables. -/
abbrev RealRandomFamily (Omega I : Type*) :=
  RandomFamily Omega I Real

/-- Pointwise measurability predicate for indexed random-variable families. -/
abbrev IsRandomFamily {Omega I E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (X : RandomFamily Omega I E) : Prop :=
  forall i, IsRandomVariable P (X i)

/-- Pointwise measurability predicate for real-valued random-variable families. -/
abbrev IsRealRandomFamily {Omega I : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : RealRandomFamily Omega I) : Prop :=
  IsRandomFamily P X

/-- Evaluation of a random family at an index. -/
def familyAt {Omega I E : Type*}
    (X : RandomFamily Omega I E) (i : I) : RandomVariable Omega E :=
  X i

@[simp]
theorem familyAt_apply {Omega I E : Type*} [MeasurableSpace Omega]
    (X : RandomFamily Omega I E) (i : I) (omega : Omega) :
    familyAt X i omega = X i omega :=
  rfl

@[simp]
theorem isRandomFamily_iff {Omega I E : Type*} [MeasurableSpace Omega]
    [MeasurableSpace E] (P : Measure Omega) (X : RandomFamily Omega I E) :
    IsRandomFamily P X <-> forall i, Measurable (X i) :=
  Iff.rfl

theorem isRealRandomFamily_iff {Omega I : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : RealRandomFamily Omega I) :
    IsRealRandomFamily P X <-> forall i, Measurable (X i) :=
  Iff.rfl

/-- A measurable random family has measurable members. -/
theorem isRandomVariable_familyAt {Omega I E : Type*} [MeasurableSpace Omega]
    [MeasurableSpace E] {P : Measure Omega} {X : RandomFamily Omega I E}
    (hX : IsRandomFamily P X) (i : I) :
    IsRandomVariable P (familyAt X i) :=
  hX i

/-- A measurable real-valued random family has measurable real members. -/
theorem isRealRandomVariable_familyAt {Omega I : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {X : RealRandomFamily Omega I}
    (hX : IsRealRandomFamily P X) (i : I) :
    IsRealRandomVariable P (familyAt X i) :=
  hX i

/-- Pointwise map of an indexed random family by a deterministic function. -/
def mapRandomFamily {Omega I E F : Type*}
    (f : E -> F) (X : RandomFamily Omega I E) : RandomFamily Omega I F :=
  fun i omega => f (X i omega)

@[simp]
theorem mapRandomFamily_apply {Omega I E F : Type*} [MeasurableSpace Omega]
    (f : E -> F) (X : RandomFamily Omega I E) (i : I) (omega : Omega) :
    mapRandomFamily f X i omega = f (X i omega) :=
  rfl

/-- Measurable deterministic maps preserve pointwise random-family measurability. -/
theorem isRandomFamily_map {Omega I E F : Type*} [MeasurableSpace Omega]
    [MeasurableSpace E] [MeasurableSpace F] {P : Measure Omega}
    {X : RandomFamily Omega I E} {f : E -> F}
    (hf : Measurable f) (hX : IsRandomFamily P X) :
    IsRandomFamily P (mapRandomFamily f X) := by
  intro i
  exact hf.comp (hX i)

end HighDimProb
