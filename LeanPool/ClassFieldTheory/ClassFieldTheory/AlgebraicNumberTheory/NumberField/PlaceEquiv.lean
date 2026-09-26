/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
/-!
# Places under a number-field equivalence

A field equivalence bijects both the finite and infinite places. These
equivalences reindex placewise products without changing their mathematics.
-/

@[expose] public section

noncomputable
section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- Finite places correspond via the induced equivalence of rings of integers. -/
def finitePlaceEquivOfRingEquiv
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) :
    HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 G) :=
  IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (NumberField.RingOfIntegers.mapRingEquiv e)

/-- Infinite places correspond by pulling embeddings back along the inverse
field equivalence. -/
def infinitePlaceEquivOfRingEquiv
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) :
    NumberField.InfinitePlace F ≃ NumberField.InfinitePlace G where
  toFun w := w.comap e.symm.toRingHom
  invFun w := w.comap e.toRingHom
  left_inv w := by
    change (w.comap e.symm.toRingHom).comap e.toRingHom = w
    rw [← NumberField.InfinitePlace.comap_comp]
    have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id F := by
      ext x
      simp
    rw [hcomp, NumberField.InfinitePlace.comap_id]
  right_inv w := by
    change (w.comap e.toRingHom).comap e.symm.toRingHom = w
    rw [← NumberField.InfinitePlace.comap_comp]
    have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id G := by
      ext x
      simp
    rw [hcomp, NumberField.InfinitePlace.comap_id]

end ClassFieldTheory
