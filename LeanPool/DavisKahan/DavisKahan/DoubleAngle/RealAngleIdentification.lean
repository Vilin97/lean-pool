/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealUnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.AngleFunctionalCalculusReal
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationReal

/-! # Real Angle Identification -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta

open TauCeti.DavisKahan.Sylvester

/-!
# Reading the real reflected overlap block as the real `sin 2Θ`

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex".  The directed `sin 2Θ` theorem is available over a real Hilbert space
at every Ky-Fan-dominant unitarily invariant ideal gauge
(`DavisKahan/DoubleAngle/RealUnboundedIdeal.lean`), but its conclusion is about
the *canonical reflected overlap block* `sinTwoThetaIdealBlock U V`, not about a
named real angle operator.  Over `ℂ` the two are tied together by
`norm_sinTwoThetaIdealBlock_complex`; that identification is stated for
`directedSinTwoAngleOperatorC`, so nothing carried it to the reals.

This module supplies the missing geometric renaming, and with it the printed
operator-norm conclusion `δ ‖sin 2Θ‖ ≤ 2‖E‖` over a real Hilbert space, for an
unbounded self-adjoint closed operator and its genuine real spectral subspaces.

## The descent

The block is a composition of a projection, a reflection, a complementary
projection and the same reflection — see `sinTwoThetaIdealBlock_eq_comp`, which
is scalar-generic.  Each factor complexifies to its complex counterpart, so the
whole block does (`complexify_sinTwoThetaIdealBlock`).  On the other side
`sinTwoAngleOperatorR` complexifies to `sinTwoAngleOperatorC` by
construction.  What remains is a purely complex fact: the two complex spellings
of `sin 2Θ` have the same norm, because both equal the projection gap between
`U` and its reflection through `V`
(`norm_sinTwoAngleOperatorC_eq_norm_directedSinTwoAngleOperatorC`).

## Main results

* `TauCeti.DavisKahan.norm_sinTwoThetaIdealBlock_real`
* `TauCeti.DavisKahan.sinTwoTheta_reflectionResidual_opNorm_real`
* `TauCeti.DavisKahan.sinTwoTheta_addBounded_opNorm_real`

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: standing assumption 1, the Section
  2 `sin 2Θ` theorem, and equations (7.4)--(7.5).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahanExt




section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The two complex spellings of `sin 2Θ` have the same norm.

`directedSinTwoAngleOperatorC` is the product form `2 sin Θ cos Θ` and
`sinTwoAngleOperatorC` is the functional calculus `sin (2 ·)` of the
operator angle.  Both have the norm of the projection gap between `U` and its
reflection through `V`: the second by the reflection double-angle identity, the
first by `subspaceGap_map_reflection_eq_norm_sinTwoAngle`. -/
theorem norm_sinTwoAngleOperatorC_eq_norm_directedSinTwoAngleOperatorC
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperatorC U V‖ = ‖directedSinTwoAngleOperatorC U V‖ := by
  rw [directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub,
    ContinuousLinearMap.norm_modulus, norm_sub_rev]
  exact DavisKahan.subspaceGap_map_reflection_eq_norm_sinTwoAngle U V

end

end DavisKahanExt

namespace DavisKahan

open TauCeti.DavisKahan
open TauCeti.DavisKahan.RealSpectralRestriction
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

section

universe u v

section ScalarGeneric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The canonical reflected overlap block, written without a `Submodule.map`:
project onto `U`, having reflected the complementary projection through `V`.

This is the shape that transports across complexification, because every factor
is a projection or a reflection. -/
theorem sinTwoThetaIdealBlock_eq_comp
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinTwoThetaIdealBlock U V =
      U.starProjection ∘L V.reflectionOperator ∘L Uᗮ.starProjection ∘L
        V.reflectionOperator := by
  rw [sinTwoThetaIdealBlock, starProjection_map_unitary Uᗮ V.reflection]
  refine ContinuousLinearMap.ext fun x => ?_
  change U.starProjection (V.reflection (Uᗮ.starProjection
      (V.reflection.symm x))) = _
  rw [V.reflection_symm]
  rfl

end ScalarGeneric

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The canonical reflected overlap block of a real pair complexifies to the
complex block of the complexified pair. -/
theorem complexify_sinTwoThetaIdealBlock (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    complexify (sinTwoThetaIdealBlock U V) =
      sinTwoThetaIdealBlock (complexifySubmodule U) (complexifySubmodule V) := by
  rw [sinTwoThetaIdealBlock_eq_comp, sinTwoThetaIdealBlock_eq_comp,
    complexify_comp, complexify_comp, complexify_comp,
    starProjection_complexifySubmodule, complexify_reflectionOperator,
    starProjection_complexifySubmodule_orthogonal]

/-- **The real block-to-angle identification, equations (7.4)--(7.5) over a real
Hilbert space.**  The canonical reflected overlap block has exactly the norm of
the real `sin 2Θ` of the pair.

This is the real counterpart of `norm_sinTwoThetaIdealBlock_complex`, whose statement is
about `directedSinTwoAngleOperatorC` and therefore never left the complex scalars. -/
theorem norm_sinTwoThetaIdealBlock_real (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoThetaIdealBlock U V‖ = ‖sinTwoAngleOperatorR U V‖ := by
  rw [← norm_complexify (sinTwoThetaIdealBlock U V),
    ← norm_complexify (sinTwoAngleOperatorR U V),
    complexify_sinTwoThetaIdealBlock, complexify_sinTwoAngleOperatorR,
    norm_sinTwoThetaIdealBlock_complex,
    norm_sinTwoAngleOperatorC_eq_norm_directedSinTwoAngleOperatorC]

/-! ## The printed operator-norm conclusions over a real Hilbert space

Reading the real Ky-Fan-dominant theorems at the first Ky Fan family — whose
gauge is the operator norm — and renaming the block through
`norm_sinTwoThetaIdealBlock_real` puts the Section 2 `sin 2Θ` theorem over the
reals with a conclusion that names a real angle operator. -/

variable (A : E →ₗ.[ℝ] E)
  (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S)

/-- **Davis--Kahan 1970, `sin 2Θ` theorem over a REAL Hilbert space,
reflection-residual form at the operator norm**: `δ ‖sin 2Θ‖ ≤ ‖R‖`.

`A` is an unbounded self-adjoint closed operator on a real Hilbert space, `U` is
its genuine spectral subspace for the measurable set `S`, `V` is an arbitrary
closed subspace, and `R` is a bounded self-adjoint operator implementing the
mirrored system on the whole domain.  The conclusion names the real operator
`sin 2Θ(U, V)`. -/
theorem sinTwoTheta_reflectionResidual_opNorm_real
    (R : E →L[ℝ] E) (hR : R.IsSymmetric)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA S hS)
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : E) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : E), hJdom x⟩ =
        V.reflectionOperator (A x)) :
    δ * ‖sinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA S hS) V‖ ≤ ‖R‖ := by
  have h := sinTwoTheta_reflectionResidual_gauge_real A hA S hS
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) 1 Nat.one_pos) R hR V hδ hgap
    hJdom hJintertwines
    (KyFanDominantIdealFamily.kyFan_mem 1 Nat.one_pos R)
  rw [KyFanDominantIdealFamily.kyFan_gauge,
    KyFanDominantIdealFamily.kyFan_gauge,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one,
    norm_sinTwoThetaIdealBlock_real] at h
  exact h.2

/-- **Davis--Kahan 1970, `sin 2Θ` theorem over a REAL Hilbert space,
bounded-perturbation form at the operator norm**: `δ ‖sin 2Θ‖ ≤ 2‖E‖`, with the
paper's sharp factor two.

Both subspaces are genuine real spectral subspaces, of the unbounded self-adjoint
closed operator `A` and of its bounded self-adjoint perturbation `A + E`.  There
is no dimension hypothesis. -/
theorem sinTwoTheta_addBounded_opNorm_real
    (Eop : E →L[ℝ] E) (hEop : Eop.IsSymmetric)
    (T : Set ℝ) (hT : MeasurableSet T)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA S hS)
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ) :
    δ * ‖sinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA S hS)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) T hT)‖ ≤ 2 * ‖Eop‖ := by
  have h := sinTwoTheta_addBounded_gauge_real A hA Eop hEop
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) 1 Nat.one_pos) S T hS hT hδ hgap
    (KyFanDominantIdealFamily.kyFan_mem 1 Nat.one_pos Eop)
  rw [KyFanDominantIdealFamily.kyFan_gauge,
    KyFanDominantIdealFamily.kyFan_gauge,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one,
    norm_sinTwoThetaIdealBlock_real] at h
  exact h.2

end Real

end

end DavisKahan
end TauCeti
