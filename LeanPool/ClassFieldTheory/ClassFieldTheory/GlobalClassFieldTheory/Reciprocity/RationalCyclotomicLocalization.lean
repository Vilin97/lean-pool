/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicField
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
/-!
# Localized rational cyclotomic levels

This file identifies the algebraic localization of an actual finite
rational cyclotomic level with a cyclotomic extension of the completed
base.  The primitive root is the image of a genuine primitive root in
the global level under the canonical global-to-local map.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- A genuine primitive root in the actual `m`-th rational cyclotomic
level. -/
noncomputable def rationalCyclotomicLevelPrimitiveRoot
    (m : ℕ+) : KummerTheory.rationalCyclotomicLevel m :=
  Classical.choose
    (IsCyclotomicExtension.exists_isPrimitiveRoot
      (S := {(m : ℕ)})
      (n := (m : ℕ))
      ℚ (KummerTheory.rationalCyclotomicLevel m)
      (by simp) m.ne_zero)

/-- The finite adic absolute value of the rational base at `v`. -/
abbrev rationalCyclotomicAdicAbsoluteValue
    (v : HeightOneSpectrum (𝓞 ℚ)) :=
  HeightOneSpectrum.adicAbv ℚ v

/-- The chosen extension of the rational finite-place absolute value to
the actual `m`-th cyclotomic level. -/
noncomputable def rationalCyclotomicChosenFinitePlaceExtension
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    AbsoluteValueExtension
      (rationalCyclotomicAdicAbsoluteValue v)
      (KummerTheory.rationalCyclotomicLevel m) :=
  chosenFinitePlaceExtension
    (L := KummerTheory.rationalCyclotomicLevel m) v

/-- The canonical algebra structure on the selected extension completion
over the rational finite completion. -/
noncomputable instance rationalCyclotomicCompletionAlgebra
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra (rationalCyclotomicAdicAbsoluteValue v).Completion
      (rationalCyclotomicChosenFinitePlaceExtension m v).1.Completion :=
  AbsoluteValue.completionAlgebra
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v).1
    (rationalCyclotomicChosenFinitePlaceExtension m v).2

/-- The actual algebraic localization of the rational cyclotomic level at `v`. -/
abbrev rationalCyclotomicLocalizedCompletion
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :=
  LocalizedCompletion
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v)

/-- The selected rational cyclotomic localization is finite over the finite completion. -/
noncomputable instance rationalCyclotomicLocalizedCompletionFinite
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    FiniteDimensional (rationalCyclotomicAdicAbsoluteValue v).Completion
      (rationalCyclotomicLocalizedCompletion m v) :=
  localizedCompletionModuleFinite
    (rationalCyclotomicAdicAbsoluteValue v)
    (RayClass.adicAbv_isNontrivial v)
    (rationalCyclotomicChosenFinitePlaceExtension m v)

/-- The selected rational cyclotomic localization is algebraic over the finite completion. -/
noncomputable instance rationalCyclotomicLocalizedCompletionIsAlgebraic
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra.IsAlgebraic (rationalCyclotomicAdicAbsoluteValue v).Completion
      (rationalCyclotomicLocalizedCompletion m v) :=
  AbsoluteValue.algebraicLocalization_isAlgebraic
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v).1
    (rationalCyclotomicChosenFinitePlaceExtension m v).2

/-- The selected root in the actual rational cyclotomic level is
primitive of order `m`. -/
theorem rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot
    (m : ℕ+) :
    IsPrimitiveRoot (rationalCyclotomicLevelPrimitiveRoot m)
      (m : ℕ) :=
  Classical.choose_spec
    (IsCyclotomicExtension.exists_isPrimitiveRoot
      (S := {(m : ℕ)})
      (n := (m : ℕ))
      ℚ (KummerTheory.rationalCyclotomicLevel m)
      (by simp) m.ne_zero)

section RationalGlobalToLocalized

private theorem rationalCyclotomicLocalizedCompletion_charZero
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    CharZero (rationalCyclotomicLocalizedCompletion m v) :=
  charZero_of_injective_ringHom
    ((AbsoluteValue.toAlgebraicLocalization
      (rationalCyclotomicAdicAbsoluteValue v)
      (rationalCyclotomicChosenFinitePlaceExtension m v).1
      (rationalCyclotomicChosenFinitePlaceExtension m v).2).comp
      (algebraMap ℚ (KummerTheory.rationalCyclotomicLevel m))).injective

attribute [local instance] rationalCyclotomicLocalizedCompletion_charZero

/-- The actual global-to-local embedding of the selected rational
cyclotomic level, regarded as a rational algebra homomorphism. -/
noncomputable def rationalCyclotomicGlobalToLocalizedAlgHom
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    KummerTheory.rationalCyclotomicLevel m →ₐ[ℚ]
      rationalCyclotomicLocalizedCompletion m v :=
  (AbsoluteValue.toAlgebraicLocalization
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v).1
    (rationalCyclotomicChosenFinitePlaceExtension m v).2).toRatAlgHom

/-- The named rational algebra homomorphism has the canonical
global-to-local ring homomorphism as its underlying map. -/
@[simp]
theorem rationalCyclotomicGlobalToLocalizedAlgHom_apply
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ))
    (x : KummerTheory.rationalCyclotomicLevel m) :
    rationalCyclotomicGlobalToLocalizedAlgHom m v x =
      AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicAdicAbsoluteValue v)
        (rationalCyclotomicChosenFinitePlaceExtension m v).1
        (rationalCyclotomicChosenFinitePlaceExtension m v).2 x :=
  rfl

/-- The image of the selected global primitive root in the algebraic
localization at `v`. -/
noncomputable def rationalCyclotomicLocalizedPrimitiveRoot
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicLocalizedCompletion m v :=
  AbsoluteValue.toAlgebraicLocalization
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v).1
    (rationalCyclotomicChosenFinitePlaceExtension m v).2
    (rationalCyclotomicLevelPrimitiveRoot m)

/-- The selected localized root is the actual global-to-local image of
the selected global primitive root. -/
theorem rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicGlobalToLocalizedAlgHom m v
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLocalizedPrimitiveRoot m v :=
  rfl

/-- The localized global root remains primitive because the canonical
global-to-local homomorphism is injective. -/
theorem rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsPrimitiveRoot
      (rationalCyclotomicLocalizedPrimitiveRoot m v) (m : ℕ) := by
  exact
    (rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m).map_of_injective
      (rationalCyclotomicGlobalToLocalizedAlgHom m v).injective

end RationalGlobalToLocalized

/-- The selected primitive root generates the actual rational cyclotomic
level over `ℚ`. -/
theorem rationalCyclotomicLevelPrimitiveRoot_adjoin_eq_top
    (m : ℕ+) :
    IntermediateField.adjoin ℚ
        ({rationalCyclotomicLevelPrimitiveRoot m} :
          Set (KummerTheory.rationalCyclotomicLevel m)) =
      ⊤ := by
  let : NeZero (m : ℕ) := ⟨m.ne_zero⟩
  exact
    IntermediateField.adjoin_eq_top_of_algebra
      ℚ
      ({rationalCyclotomicLevelPrimitiveRoot m} :
        Set (KummerTheory.rationalCyclotomicLevel m))
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top
        (rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m))

/-- The localized primitive root generates the whole algebraic
localization over the completed rational field. -/
theorem
    rationalCyclotomicLocalizedPrimitiveRoot_adjoin_eq_top
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    IntermediateField.adjoin
        (rationalCyclotomicAdicAbsoluteValue v).Completion
        {rationalCyclotomicLocalizedPrimitiveRoot m v} =
      ⊤ := by
  let vQ := rationalCyclotomicAdicAbsoluteValue v
  let w := rationalCyclotomicChosenFinitePlaceExtension m v
  let hℚ :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := ℚ) w.1
  let : SMul ℚ w.1.Completion := hℚ.toSMul
  let : Algebra vQ.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vQ w.1 w.2
  let : Algebra ℚ (LocalizedCompletion vQ w) :=
    localizedCompletionGlobalAlgebra vQ w
  let : SMul ℚ (LocalizedCompletion vQ w) :=
    (localizedCompletionGlobalAlgebra vQ w).toSMul
  let : IsScalarTower ℚ vQ.Completion
      (LocalizedCompletion vQ w) :=
    localizedCompletionIsScalarTower vQ w
  exact
    localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top
      vQ w (rationalCyclotomicLevelPrimitiveRoot m)
      (rationalCyclotomicLevelPrimitiveRoot_adjoin_eq_top m)

/-- The localized primitive root generates the same top subalgebra as its
intermediate-field closure.  This avoids reducing the two adjoin constructions. -/
theorem rationalCyclotomicLocalizedPrimitiveRoot_algebraAdjoin_eq_top
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra.adjoin (rationalCyclotomicAdicAbsoluteValue v).Completion
      ({rationalCyclotomicLocalizedPrimitiveRoot m v} :
        Set (rationalCyclotomicLocalizedCompletion m v)) = ⊤ := by
  exact
    IntermediateField.adjoin_eq_top_iff.mp
      (show
        IntermediateField.adjoin
            (rationalCyclotomicAdicAbsoluteValue v).Completion
            {rationalCyclotomicLocalizedPrimitiveRoot m v} =
          ⊤
        from
          rationalCyclotomicLocalizedPrimitiveRoot_adjoin_eq_top
            m v)

/-- The algebraic localization of the actual `m`-th rational cyclotomic
level is itself a cyclotomic extension of the completed rational field. -/
theorem rationalCyclotomicLevel_localizedCompletion_isCyclotomicExtension
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCyclotomicExtension {(m : ℕ)}
      (rationalCyclotomicAdicAbsoluteValue v).Completion
      (rationalCyclotomicLocalizedCompletion m v) := by
  let : NeZero (m : ℕ) := ⟨m.ne_zero⟩
  let ζv : rationalCyclotomicLocalizedCompletion m v :=
    rationalCyclotomicLocalizedPrimitiveRoot m v
  have hζv : IsPrimitiveRoot ζv (m : ℕ) :=
    rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot m v
  have hAdjoin :
      Algebra.adjoin (rationalCyclotomicAdicAbsoluteValue v).Completion
        ({ζv} : Set (rationalCyclotomicLocalizedCompletion m v)) = ⊤ := by
    simpa [ζv] using
      rationalCyclotomicLocalizedPrimitiveRoot_algebraAdjoin_eq_top m v
  exact
    IsCyclotomicExtension.equiv {(m : ℕ)}
      (rationalCyclotomicAdicAbsoluteValue v).Completion
      (Algebra.adjoin (rationalCyclotomicAdicAbsoluteValue v).Completion
        ({ζv} : Set (rationalCyclotomicLocalizedCompletion m v)))
      (h := hζv.adjoin_isCyclotomicExtension
        (rationalCyclotomicAdicAbsoluteValue v).Completion)
      ((Subalgebra.equivOfEq _ _ hAdjoin).trans Subalgebra.topEquiv)

end Reciprocity
end GlobalClassFieldTheory
