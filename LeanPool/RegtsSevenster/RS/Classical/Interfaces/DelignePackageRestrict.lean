/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DelignePackage

/-!
# Restriction of Deligne packages

A Deligne fibre-functor package restricts along any braided
monoidal, additive, ℂ-linear functor: compose the fibre functor
with the embedding.
-/

namespace RS

open CategoryTheory

/-- Restrict a Deligne package along a braided linear functor. -/
noncomputable def DelignePackage.restrict
    {A : Type*} [Category A] [MonoidalCategory A]
    [SymmetricCategory A] [Preadditive A] [Linear ℂ A]
    {B : Type*} [Category B] [MonoidalCategory B]
    [SymmetricCategory B] [Preadditive B] [Linear ℂ B]
    (F : B ⥤ A) [F.Braided] [F.Additive] [F.Linear ℂ]
    (P : DelignePackage A) : DelignePackage B where
  ω := F ⋙ P.ω
  braided :=
    letI := P.braided
    inferInstance
  additive :=
    letI := P.additive
    inferInstance
  linear :=
    letI := P.additive
    letI := P.linear
    inferInstance

end RS
