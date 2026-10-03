/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.Core
/-!
# Finite-place local--global Kummer comparison

This file isolates the completion factor used to compare the global Kummer
root character with the local Hilbert symbol.  The algebra, finiteness, root,
and splitting-field data are named separately so downstream proofs do not
rebuild the localized-completion instance tower.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- The absolute-value completion used at the finite place `v`. -/
abbrev finitePlaceKummerBaseCompletion
    (v : HeightOneSpectrum (𝓞 K)) :=
  (NumberField.HeightOneSpectrum.adicAbv K v).Completion

open scoped Classical in
/-- The localized completion of the chosen global simple Kummer extension. -/
abbrev finitePlaceKummerLocalizedCompletion
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :=
  LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv K v) w

open scoped Classical in
/-- The canonical completion algebra for the localized global Kummer
extension. -/
@[reducible]
noncomputable def finitePlaceKummerLocalizedAlgebra
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    Algebra (finitePlaceKummerBaseCompletion K v)
      (finitePlaceKummerLocalizedCompletion K n hnK v b w) :=
  finitePlaceLocalArtinLocalizedAlgebra
    (K := K) (L := chosenSimpleKummerExtension K n hnK b) v w

open scoped Classical in
/-- The named finite-dimensional certificate for the localized global
Kummer extension. -/
theorem finitePlaceKummerLocalizedFiniteDimensional
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    letI : Algebra (finitePlaceKummerBaseCompletion K v)
        (finitePlaceKummerLocalizedCompletion K n hnK v b w) :=
      finitePlaceKummerLocalizedAlgebra K n hnK v b w
    FiniteDimensional (finitePlaceKummerBaseCompletion K v)
      (finitePlaceKummerLocalizedCompletion K n hnK v b w) := by
  let : FiniteDimensional K (chosenSimpleKummerExtension K n hnK b) :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  exact finitePlaceLocalArtinFiniteDimensional
    (K := K) (L := chosenSimpleKummerExtension K n hnK b) v w

open scoped Classical in
/-- The image of the global chosen radical as a unit of the localized
completion. -/
noncomputable def finitePlaceKummerLocalizedRootUnit
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    (finitePlaceKummerLocalizedCompletion K n hnK v b w)ˣ :=
  Units.map
    (AbsoluteValue.toAlgebraicLocalization
      (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2).toMonoidHom
    (chosenSimpleKummerRootUnit K n hnK b)

open scoped Classical in
/-- The localized global radical is an `n`-th root of the image of `b` in
the finite-place completion. -/
theorem finitePlaceKummerLocalizedRootUnit_pow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    letI : Algebra (finitePlaceKummerBaseCompletion K v)
        (finitePlaceKummerLocalizedCompletion K n hnK v b w) :=
      finitePlaceKummerLocalizedAlgebra K n hnK v b w
    finitePlaceKummerLocalizedRootUnit K n hnK v b w ^ (n : ℕ) =
      Units.map
        (algebraMap (finitePlaceKummerBaseCompletion K v)
          (finitePlaceKummerLocalizedCompletion K n hnK v b w)).toMonoidHom
        (finitePlaceHilbertCompletionUnit K v b) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  have hroot_val :
      (((chosenSimpleKummerRootUnit K n hnK b :
          (chosenSimpleKummerExtension K n hnK b)ˣ) :
        chosenSimpleKummerExtension K n hnK b) ^ (n : ℕ)) =
        algebraMap K (chosenSimpleKummerExtension K n hnK b) (b : K) := by
    apply Subtype.ext
    exact chosenSimpleKummerRoot_pow K n hnK b
  let L := chosenSimpleKummerExtension K n hnK b
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  apply Units.ext
  simp only [finitePlaceKummerLocalizedRootUnit,
    finitePlaceHilbertCompletionUnit, Units.val_pow_eq_pow_val, Units.coe_map]
  calc
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
          (((chosenSimpleKummerRootUnit K n hnK b : Lˣ) : L)) ^ (n : ℕ) =
        AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
          (((chosenSimpleKummerRootUnit K n hnK b : Lˣ) : L) ^ (n : ℕ)) := by
      exact (map_pow
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)
        (((chosenSimpleKummerRootUnit K n hnK b : Lˣ) : L)) (n : ℕ)).symm
    _ = AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
          (algebraMap K L (b : K)) := by rw [hroot_val]
    _ = algebraMap vK.Completion E
          (algebraMap K vK.Completion (b : K)) :=
      AbsoluteValue.toAlgebraicLocalization_algebraMap
        vK w.1 w.2 (b : K)

open scoped Classical in
/-- The localized image of the global chosen radical generates the whole
localized extension over the base completion. -/
theorem finitePlaceKummerLocalizedRoot_adjoin_eq_top
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    letI : Algebra (finitePlaceKummerBaseCompletion K v)
        (finitePlaceKummerLocalizedCompletion K n hnK v b w) :=
      finitePlaceKummerLocalizedAlgebra K n hnK v b w
    IntermediateField.adjoin (finitePlaceKummerBaseCompletion K v)
      {((finitePlaceKummerLocalizedRootUnit K n hnK v b w :
          (finitePlaceKummerLocalizedCompletion K n hnK v b w)ˣ) :
        finitePlaceKummerLocalizedCompletion K n hnK v b w)} = ⊤ := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let L := chosenSimpleKummerExtension K n hnK b
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let : Algebra K E := localizedCompletionGlobalAlgebra vK w
  let : SMul K E := (localizedCompletionGlobalAlgebra vK w).toSMul
  let : IsScalarTower K vK.Completion E :=
    localizedCompletionIsScalarTower vK w
  exact localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top
    vK w
    (((chosenSimpleKummerRootUnit K n hnK b : Lˣ) : L))
    (chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b)

open scoped Classical in
/-- The localized global simple Kummer extension is a splitting field for
the local Kummer polynomial. -/
theorem finitePlaceKummerLocalized_isSplittingField
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
    letI : Algebra C E :=
      finitePlaceKummerLocalizedAlgebra K n hnK v b w
    letI : FiniteDimensional C E :=
      finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
    Polynomial.IsSplittingField C E
      (Polynomial.X ^ (n : ℕ) -
        Polynomial.C (algebraMap K C (b : K))) := by
  let C := finitePlaceKummerBaseCompletion K v
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  exact
    isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top_of_primitiveRoots
      C E n (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
      (algebraMap K C (b : K))
      ((finitePlaceKummerLocalizedRootUnit K n hnK v b w : Eˣ) : E)
      (congrArg Units.val
        (finitePlaceKummerLocalizedRootUnit_pow K n hnK v b w))
      (finitePlaceKummerLocalizedRoot_adjoin_eq_top K n hnK v b w)

end Reciprocity
end GlobalClassFieldTheory
