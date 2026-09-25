/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExactReal
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TangentSingularValues
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded

/-! # Tan Two Theta Unbounded Reducing Real -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The real `tan 2Θ` endpoints, with the doubled tangent read off the doubled sine

`TanTwoThetaUnboundedReducing.lean` and `TangentSingularValues.lean` give, over
`ℂ`, the singular-value identity a `tan 2Θ` statement needs:

```
aₙ(|tan 2Θ|) = tan (arcsin aₙ(sin 2Θ))
```

with `sin 2Θ` the projector difference between `U` and its mirror image in `V`.
This module carries that to `ℝ` by complexification, so a source-facing `tan 2Θ`
statement can be read at either field with the same shape.

**The doubled angle is presented by its own sine.**  There is no indexwise
identity taking `aₙ(sin Θ)` to `aₙ(sin 2Θ)`: `θ ↦ sin 2θ` is not monotone on
`[0, π/2]`, and principal angles `75°` and `30°` already order the two sequences
oppositely.  Only the monotone `u ↦ tan (arcsin u)` may be applied to an ordered
singular-value sequence.

## Main results

* `tanTwoTheta_ambient_unbounded_reducing_sineSequence_symmetricNorming_real`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan
open TauCeti.ApproximationNumber
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open RealComplexification

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete.  `local instance` does not propagate through imports, so it
is reinstalled here. -/
local instance instCompleteSpaceCoeTanTwoReducingReal
    (W : Submodule ℝ E) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

section AmbientReal

variable {A : E →ₗ.[ℝ] E} {B : E →L[ℝ] E} {U : Submodule ℝ E}
  [U.HasOrthogonalProjection] {a b : ℝ}

/-- Complexification does not change an approximation number, in the
`approximationNumber` spelling the clause statements use. -/
private theorem approximationNumber_complexify_eq {F : Type u}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (n : ℕ) :
    (complexify T).approximationNumber n = T.approximationNumber n :=
  ComplexificationApproximation.approximationSingularValue_complexify T n

/-- The real ambient double-angle sine: the projector difference between `U` and
its mirror image in `V`.  Private, because the endpoint below states it inline --
a named abbreviation in the conclusion would make the consumer's definitional
check carry an extra unfolding for no gain. -/
private def realAmbientDoubleSine (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℝ] E :=
  (U.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection - U.starProjection

/-- The complexified ambient double-angle sine of the complexified pair has the
same approximation numbers as the real one. -/
private theorem approximationNumber_realAmbientDoubleSine_complexify
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (n : ℕ) :
    (((complexifySubmodule U).map
        ((complexifySubmodule V).reflection.toLinearEquiv :
          RealComplexification E →ₗ[ℂ] RealComplexification E)).starProjection -
      (complexifySubmodule U).starProjection).approximationNumber n =
      (realAmbientDoubleSine U V).approximationNumber n := by
  have hsame := sameSingular_sinTwoAngleOperatorR_reflectedProjectorDifference U V
  have hleft : (sinTwoAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)).approximationNumber n =
      (complexify (sinTwoAngleOperatorR U V)).approximationNumber n := by
    rw [complexify_sinTwoAngleOperatorR]
  have hmodulus := approximationNumber_sinTwoAngleOperatorC
    (complexifySubmodule U) (complexifySubmodule V) n
  have hright := approximationNumber_complexify_eq (realAmbientDoubleSine U V) n
  calc (((complexifySubmodule U).map
          ((complexifySubmodule V).reflection.toLinearEquiv :
            RealComplexification E →ₗ[ℂ] RealComplexification E)).starProjection -
        (complexifySubmodule U).starProjection).approximationNumber n
      = (sinTwoAngleOperatorC (complexifySubmodule U)
          (complexifySubmodule V)).approximationNumber n := hmodulus.symm
    _ = (complexify (sinTwoAngleOperatorR U V)).approximationNumber n := hleft
    _ = (complexify (realAmbientDoubleSine U V)).approximationNumber n := hsame n
    _ = (realAmbientDoubleSine U V).approximationNumber n := hright

variable (hA : _root_.IsSelfAdjoint A)
  (hred : TauCeti.LinearPMap.ReducesSubspace A U)
  (hB : TauCeti.IsOddFor U B)
  (hUa : ∀ x : A.domain, (x : E) ∈ U → ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
  (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ → b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
  (hab : a < b)

include hA hred hB hUa hUb hab

/-- **Davis--Kahan 1970, `tan 2Θ`, unbounded ambient form over `ℝ`, at an
arbitrary reducing subspace, with the doubled tangent read off the doubled
sine.**

`(b − a) N(|tan 2Θ|) ≤ 2 N(B)`, together with the two facts that make the
left-hand side a statement about the sequence `|tan 2θⱼ|`: no doubled angle is a
quarter turn, and the operator's singular values are exactly
`tan (arcsin aₙ(sin 2Θ))`.  Both are derived from the ordered gap. -/
theorem tanTwoTheta_ambient_unbounded_reducing_sineSequence_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (hBsa : IsSelfAdjoint B) (hV : DavisKahan.ReflectionIntertwines A B V)
    (hBmem : N.Mem B) :
    (∀ n : ℕ, ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection -
        U.starProjection).approximationNumber n < 1) ∧
      (∀ n : ℕ, (absTanTwoAngleOperatorR U V).approximationNumber n =
        Real.tan (Real.arcsin
          (((U.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection -
            U.starProjection).approximationNumber n))) ∧
      N.Mem (absTanTwoAngleOperatorR U V) ∧
      (b - a) * N.gauge (absTanTwoAngleOperatorR U V) ≤ 2 * N.gauge B := by
  obtain ⟨hunit, hmem, hle⟩ :=
    tanTwoTheta_ambient_unbounded_blockRepresentative_reducing_symmetricNorming_real
      hA hred hB (TauCeti.DavisKahanExt.isSelfAdjoint_reflectionOperator V)
      (TauCeti.DavisKahan.reflectionOperator_mul_self_complex V)
      hV.mapsDomain hV.commutes hUa hUb hab N hBsa hBmem
  have hgauge := DavisKahan.extendedGauge_unboundedReflectionTangent_real U V N hunit
  -- the complexified pole exclusion, on the angle spectrum
  have hunitC : IsUnit ((complexifySubmodule U).diagonalPart
      (complexifySubmodule V).reflectionOperator *
      (complexifySubmodule U).diagonalPart
        (complexifySubmodule V).reflectionOperator) := by
    rw [← TauCeti.DavisKahan.complexify_reflectionOperator,
      diagonalPart_complexifySubmodule, ← Foundation.RealComplexification.complexify_mul,
      TauCeti.RealComplexification.isUnit_complexify_iff]
    exact hunit
  have hcos := DavisKahan.cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq
    (complexifySubmodule U) (complexifySubmodule V) hunitC
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_⟩
  · show ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection -
      U.starProjection).approximationNumber n < 1
    rw [show ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection -
        U.starProjection) = realAmbientDoubleSine U V from rfl,
      ← approximationNumber_realAmbientDoubleSine_complexify U V n]
    exact approximationNumber_projectorDifference_lt_one (complexifySubmodule U)
      (complexifySubmodule V) hcos n
  · rw [show ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection -
        U.starProjection) = realAmbientDoubleSine U V from rfl,
      ← approximationNumber_realAmbientDoubleSine_complexify U V n,
      ← approximationNumber_complexify_eq (absTanTwoAngleOperatorR U V) n,
      complexify_absTanTwoAngleOperatorR]
    exact approximationNumber_absTanTwoAngleOperatorC_projectorDifference
      (complexifySubmodule U) (complexifySubmodule V) hcos n
  · unfold SymmetricNormingFunction.Mem at hmem ⊢
    rwa [← hgauge]
  · unfold SymmetricNormingFunction.gauge at hle ⊢
    rwa [← hgauge]

end AmbientReal

end

end DavisKahan1970
end TauCeti
