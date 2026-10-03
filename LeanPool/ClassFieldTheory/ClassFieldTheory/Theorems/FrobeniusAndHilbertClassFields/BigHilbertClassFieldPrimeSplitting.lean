/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusEqOneIffSplitsCompletely
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldArtinEquiv
/-!
# Prime splitting in the big Hilbert class field

A finite prime splits completely in the big Hilbert class field precisely
when its narrow ideal class is trivial.  Real-place ramification does not
affect this finite-prime criterion.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

open scoped Classical in
/-- A finite prime splits completely in the big Hilbert class field exactly
when its narrow ray class is trivial. -/
theorem finitePrime_splitsCompletelyInBigHilbertClassField_iff
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K E v ↔
      narrowRayClassOfFinitePrime v = 1 := by
  obtain ⟨artin, hartin⟩ := bigHilbertClassField_artinEquiv K E hE
  have hunram : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := hE.1 v
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 E) v.asIdeal
  let : Q.LiesOver v.asIdeal := hQover
  let w : HeightOneSpectrum (𝓞 E) :=
    ⟨Q, hQmax.isPrime,
      Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw : w.asIdeal.LiesOver v.asIdeal := hQover
  constructor
  · intro hsplit
    apply artin.injective
    rw [map_one, hartin v w hw]
    exact (arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
      v w hw hunram).2 hsplit
  · intro hclass
    apply (arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
      v w hw hunram).1
    rw [← hartin v w hw, hclass, map_one]

end ClassFieldTheory
