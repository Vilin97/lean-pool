/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceComparison
/-!
# Finite-place local--global Kummer transport

This file compares the two splitting fields of the finite-place Kummer
polynomial: the simple Kummer extension chosen directly over the completion
and the localization of the chosen global simple Kummer extension.  The
completion input, finiteness, splitting-field, and equivalence data are kept
as separate declarations so the eventual root-character comparison does not
rebuild their instance towers.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open AlgebraicNumberTheory.Valuations

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- The Kummer polynomial obtained by mapping a global radicand into the
finite-place completion. -/
abbrev finitePlaceKummerPolynomial
    (n : ℕ+) (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) :=
  Polynomial.X ^ (n : ℕ) -
    Polynomial.C
      (algebraMap K (finitePlaceKummerBaseCompletion K v) (b : K))

open scoped Classical in
/-- The simple Kummer extension chosen intrinsically over the finite-place
completion. -/
noncomputable abbrev finitePlaceKummerLocalExtension
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) :=
  chosenSimpleKummerExtension
    (finitePlaceKummerBaseCompletion K v) n
    (finitePlaceHilbert_natCast_ne_zero K n hnK v)
    (finitePlaceHilbertCompletionUnit K v b)

open scoped Classical in
/-- Mapping a global unit through the concrete adic-completion model and
then back through the canonical completion equivalence gives its ordinary
image in the absolute-value completion. -/
theorem finitePlaceLocalArtinInput_globalUnit
    (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    finitePlaceLocalArtinInput v
        (Units.map
          (algebraMap K (v.adicCompletion K)).toMonoidHom a) =
      finitePlaceHilbertCompletionUnit K v a := by
  apply Units.ext
  apply (finitePlaceCompletionRingEquiv v).injective
  let x : (v.adicCompletion K)ˣ :=
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
  have hleft :
      finitePlaceCompletionRingEquiv v
          (finitePlaceLocalArtinInput v x :
            finitePlaceKummerBaseCompletion K v) =
        (x : v.adicCompletion K) := by
    exact congrArg Units.val
      ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply x)
  calc
    finitePlaceCompletionRingEquiv v
        (finitePlaceLocalArtinInput v
          (Units.map
            (algebraMap K (v.adicCompletion K)).toMonoidHom a) :
          finitePlaceKummerBaseCompletion K v) =
      (x : v.adicCompletion K) := hleft
    _ = algebraMap K (v.adicCompletion K) (a : K) := rfl
    _ = finitePlaceCompletionRingEquiv v
        (finitePlaceHilbertCompletionUnit K v a :
          finitePlaceKummerBaseCompletion K v) := by
      change
        algebraMap K (v.adicCompletion K) (a : K) =
          finitePlaceCompletionRingEquiv v
            (algebraMap K (finitePlaceKummerBaseCompletion K v) (a : K))
      rw [finitePlaceCompletionRingEquiv_eq_relative]
      exact (relativeFinitePlaceCompletionAlgEquiv v).commutes (a : K) |>.symm

open scoped Classical in
/-- The named finite-dimensional certificate for the Kummer extension
chosen directly over the completion. -/
theorem finitePlaceKummerLocalFiniteDimensional
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) :
    FiniteDimensional (finitePlaceKummerBaseCompletion K v)
      (finitePlaceKummerLocalExtension K n hnK v b) :=
  chosenSimpleKummerExtension_finiteDimensional
    (finitePlaceKummerBaseCompletion K v) n
    (finitePlaceHilbert_natCast_ne_zero K n hnK v)
    (finitePlaceHilbertCompletionUnit K v b)

open scoped Classical in
/-- The simple Kummer extension chosen directly over the completion is a
splitting field of the finite-place Kummer polynomial. -/
theorem finitePlaceKummerLocal_isSplittingField
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) :
    Polynomial.IsSplittingField
      (finitePlaceKummerBaseCompletion K v)
      (finitePlaceKummerLocalExtension K n hnK v b)
      (finitePlaceKummerPolynomial K n v b) := by
  let C := finitePlaceKummerBaseCompletion K v
  let hnC := finitePlaceHilbert_natCast_ne_zero K n hnK v
  let bC := finitePlaceHilbertCompletionUnit K v b
  let S := chosenSimpleKummerExtension C n hnC bC
  let : FiniteDimensional C S :=
    finitePlaceKummerLocalFiniteDimensional K n hnK v b
  change Polynomial.IsSplittingField C S
    (Polynomial.X ^ (n : ℕ) - Polynomial.C (bC : C))
  apply
    isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top_of_primitiveRoots
      C S n (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
      (bC : C)
      ((chosenSimpleKummerRootUnit C n hnC bC : Sˣ) : S)
  · apply Subtype.ext
    exact chosenSimpleKummerRoot_pow C n hnC bC
  · exact chosenSimpleKummerExtension_adjoin_root_eq_top C n hnC bC

open scoped Classical in
/-- A canonical algebra equivalence between the intrinsically local Kummer
extension and the localization of the chosen global Kummer extension.  It is
constructed solely from the fact that both fields split the same polynomial;
no compatibility between their chosen roots is assumed. -/
noncomputable def finitePlaceKummerLocalGlobalAlgEquiv
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
    letI : Algebra C E :=
      finitePlaceKummerLocalizedAlgebra K n hnK v b w
    S ≃ₐ[C] E := by
  let C := finitePlaceKummerBaseCompletion K v
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let f := finitePlaceKummerPolynomial K n v b
  letI : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  letI : FiniteDimensional C S :=
    finitePlaceKummerLocalFiniteDimensional K n hnK v b
  letI : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  letI : Polynomial.IsSplittingField C S f :=
    finitePlaceKummerLocal_isSplittingField K n hnK hmu v b
  letI : Polynomial.IsSplittingField C E f :=
    finitePlaceKummerLocalized_isSplittingField K n hnK hmu v b w
  exact
    (Polynomial.IsSplittingField.algEquiv S f).trans
      (Polynomial.IsSplittingField.algEquiv E f).symm

end Reciprocity
end GlobalClassFieldTheory
