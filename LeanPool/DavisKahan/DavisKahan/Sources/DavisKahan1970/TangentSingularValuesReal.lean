/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TangentSingularValues
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.AngleFunctionalCalculusReal
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation

/-! # Tangent Singular Values Real -/

open TauCeti.DavisKahan.Angle


/-!
# The single-angle tangent's singular values, over `ℝ`

`TangentSingularValues.lean` proves over `ℂ` that the paper's `tan Θ` carries the
tangents of the principal angles, singular value by singular value.  Everything
in that statement -- the operators, the norm, the approximation numbers -- is
preserved by complexification, so the real statement follows with no new
analysis.

## Main results

* `approximationNumber_tanAngleOperatorR` — `aₙ(tan Θ) = tan (arcsin aₙ(sin Θ))`
  over `ℝ`, with `sin Θ` presented as the projector difference.
* `approximationNumber_projectorDifference_lt_one_real` — the transversality that
  makes each of those a genuine tangent.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 2.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open RealComplexification

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

section SingleAngleReal

variable (U V : Submodule ℝ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- The complexified projector difference is the projector difference of the
complexified subspaces. -/
theorem complexify_projectorDifference :
    complexify (V.starProjection - U.starProjection) =
      (complexifySubmodule V).starProjection -
        (complexifySubmodule U).starProjection := by
  rw [complexify_sub, starProjection_complexifySubmodule,
    starProjection_complexifySubmodule]

/-- Uniform transversality transfers to the complexification. -/
theorem norm_sinAngleOperatorC_complexify_lt_one
    (htr : ‖sinAngleOperatorR U V‖ < 1) :
    ‖sinAngleOperatorC (complexifySubmodule U) (complexifySubmodule V)‖ < 1 := by
  rw [norm_sinAngleOperatorC, subspaceGap_complexifySubmodule U V,
    ← norm_sinAngleOperatorR]
  exact htr

/-- **The real ambient tangent carries the tangents of the principal angles.**

`aₙ(tan Θ) = tan (arcsin aₙ(sin Θ))` over `ℝ`, with `sin Θ` presented as the
projector difference `P_V − P_U`, whose singular values are the sines of the
principal angles with their ambient multiplicity. -/
theorem approximationNumber_tanAngleOperatorR
    (htr : ‖sinAngleOperatorR U V‖ < 1) (n : ℕ) :
    (tanAngleOperatorR U V).approximationNumber n =
      Real.tan (Real.arcsin
        ((V.starProjection - U.starProjection).approximationNumber n)) := by
  have htrC := norm_sinAngleOperatorC_complexify_lt_one U V htr
  have h1 : (tanAngleOperatorR U V).approximationNumber n =
      (tanAngleOperatorC (complexifySubmodule U)
        (complexifySubmodule V)).approximationNumber n := by
    rw [← complexify_tanAngleOperatorR]
    exact (ComplexificationApproximation.approximationSingularValue_complexify
      (tanAngleOperatorR U V) n).symm
  have h2 : (sinAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)).approximationNumber n =
      (V.starProjection - U.starProjection).approximationNumber n := by
    rw [approximationNumber_sinAngleOperatorC, ← complexify_projectorDifference]
    exact ComplexificationApproximation.approximationSingularValue_complexify
      (V.starProjection - U.starProjection) n
  rw [h1, approximationNumber_tanAngleOperatorC _ _ htrC n, h2]

/-- Under uniform transversality no principal angle is a right angle, so each
`tan (arcsin aₙ)` above is a genuine tangent. -/
theorem approximationNumber_projectorDifference_lt_one_real
    (htr : ‖sinAngleOperatorR U V‖ < 1) (n : ℕ) :
    (V.starProjection - U.starProjection).approximationNumber n < 1 := by
  have htrC := norm_sinAngleOperatorC_complexify_lt_one U V htr
  have h2 : (sinAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)).approximationNumber n =
      (V.starProjection - U.starProjection).approximationNumber n := by
    rw [approximationNumber_sinAngleOperatorC, ← complexify_projectorDifference]
    exact ComplexificationApproximation.approximationSingularValue_complexify
      (V.starProjection - U.starProjection) n
  rw [← h2]
  exact lt_of_le_of_lt
    ((sinAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)).approximationNumber_le_norm n) htrC

end SingleAngleReal

end

end DavisKahan1970
end TauCeti
