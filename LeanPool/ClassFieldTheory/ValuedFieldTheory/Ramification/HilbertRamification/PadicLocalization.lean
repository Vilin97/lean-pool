/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.Padic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionFieldLocalization
import Mathlib.FieldTheory.Galois.Abelian
/-!
# Localizations at rational p-adic absolute values

This file collects the reusable algebra, finiteness, Galois, and
nonarchimedean facts needed to compare a global algebraic localization with
an extension of `ℚ_[p]`.
-/

noncomputable section

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

/-- Transport an algebra structure across an equivalence of its base ring. -/
@[reducible] noncomputable def transportedAlgebraAlongRingEquiv
    {K K' E : Type*} [CommSemiring K] [CommSemiring K'] [CommSemiring E]
    [Algebra K E] (e : K ≃+* K') : Algebra K' E :=
  ((algebraMap K E).comp e.symm.toRingHom).toAlgebra

/-- The transported algebra map is the original algebra map precomposed with
the inverse base-ring equivalence. -/
@[simp]
theorem transportedAlgebraAlongRingEquiv_algebraMap
    {K K' E : Type*} [CommSemiring K] [CommSemiring K'] [CommSemiring E]
    [Algebra K E] (e : K ≃+* K') (x : K') :
    @algebraMap K' E _ _ (transportedAlgebraAlongRingEquiv e) x =
      algebraMap K E (e.symm x) :=
  rfl

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [Field L] [Algebra ℚ L]
  [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]

/-- The localization of a finite global extension is finite over the
completed base field. -/
theorem globalPadicLocalizationModuleFinite
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) :
    let vK := Rat.AbsoluteValue.padic p
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
    letI : SMul ℚ w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Module.Finite vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) := by
  let vK := Rat.AbsoluteValue.padic p
  let hvK := padicAbsoluteValue_isNontrivial p
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  let : SMul ℚ w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let : Module.Finite vK.Completion w.1.Completion :=
    completionModuleFinite vK hvK w
  exact FiniteDimensional.of_injective E.val.toLinearMap E.val.injective

omit [FiniteDimensional ℚ L] in
/-- The localization of a finite abelian global extension is abelian Galois
over the completed base. -/
theorem globalPadicLocalization_isAbelianGalois
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) :
    let vK := Rat.AbsoluteValue.padic p
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
    letI : SMul ℚ w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    IsAbelianGalois vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) := by
  let vK := Rat.AbsoluteValue.padic p
  let hvK := padicAbsoluteValue_isNontrivial p
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  let : SMul ℚ w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let : IsGalois vK.Completion E :=
    algebraicLocalization_isGalois vK w
  let e := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  exact
    { is_comm.comm := fun σ τ ↦ by
        apply e.symm.injective
        rw [map_mul, map_mul]
        apply Subtype.ext
        exact
          (inferInstance :
            IsMulCommutative (L ≃ₐ[ℚ] L)).is_comm.comm _ _
    }

/-- The rational `p`-adic absolute value is nonarchimedean in the bounded
natural-number sense used by the ramification API. -/
theorem rationalPadicAbsoluteValue_nonarchimedean :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (Rat.AbsoluteValue.padic p) := by
  apply LubinTate.Valuations.nonarchimedean_of_strong_triangle
  intro x y
  change
    ((padicNorm p (x + y) : ℚ) : ℝ) ≤
      max ((padicNorm p x : ℚ) : ℝ) ((padicNorm p y : ℚ) : ℝ)
  exact_mod_cast padicNorm.nonarchimedean

end HilbertRamification
