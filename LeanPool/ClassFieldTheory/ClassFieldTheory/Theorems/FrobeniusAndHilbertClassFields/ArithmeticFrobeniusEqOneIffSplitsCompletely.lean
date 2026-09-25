/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusOrder
/-!
# Trivial arithmetic Frobenius and complete splitting

In a finite abelian extension, the Frobenius at an unramified prime is the
identity exactly when the base prime splits completely.  Complete splitting
is expressed only with Mathlib's ramification indices and residue degrees.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

universe u v

/-- An unramified finite prime splits completely exactly when its arithmetic
Frobenius is trivial. -/
theorem arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal)
    (hunram : Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) :
    arithmeticFrobeniusAt (K := K) w = 1 ↔
      FinitePrimeSplitsCompletely K L v := by
  have hunramw : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    hunram w.asIdeal inferInstance hw
  have horder :=
    orderOf_arithmeticFrobeniusAt_eq_inertiaDegree v w hw hunramw
  constructor
  · intro h
    have hdeg : w.asIdeal.inertiaDeg (𝓞 K) = 1 :=
      horder.symm.trans (orderOf_eq_one_iff.mpr h)
    intro w' hw'
    let : w.asIdeal.LiesOver v.asIdeal := hw
    let : w'.asIdeal.LiesOver v.asIdeal := hw'
    have hsame : w'.asIdeal.inertiaDeg (𝓞 K) =
        w.asIdeal.inertiaDeg (𝓞 K) :=
      Ideal.inertiaDeg_eq_of_isGaloisGroup
        v.asIdeal w'.asIdeal w.asIdeal (L ≃ₐ[K] L)
    exact ⟨hunram.ramificationIdx_eq_one hw', hsame.trans hdeg⟩
  · intro h
    exact orderOf_eq_one_iff.mp (horder.trans (h w hw).2)

end ClassFieldTheory
