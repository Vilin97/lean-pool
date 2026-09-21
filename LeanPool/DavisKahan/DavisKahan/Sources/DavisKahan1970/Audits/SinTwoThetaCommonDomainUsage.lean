/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaCommonDomain

/-!
# Common-domain double-angle usage and signature audit

PENDING: this file has not been compiled in the review environment. It is not
imported by the accepted census or `All`. Build the candidate module first,
then run this file. Inspect the printed types and transitive axioms; in
particular, absence of `sorry` in source is not a substitute for this check.

The two calls below pin the intended clause separation. The directed call has
no global bounded perturbation. The ambient call has no residual, bounded
trial operator, or whole-trial-space domain assumption. Do not repair an
elaboration failure by adding those assumptions.
-/

namespace TauCeti.DavisKahan1970.CommonDomainUsage

open TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester
open scoped TauCeti.CompleteSubspace

noncomputable section
universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
variable (N : NormalizedSymmetricOperatorIdealFamily.{u, v} K)
variable {A T : E →ₗ.[K] E} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
  (hdom : T.domain = A.domain)
variable {P Q : Submodule K E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
  (hP : TauCeti.LinearPMap.ReducesSubspace A P)
  (hQ : TauCeti.LinearPMap.ReducesSubspace T Q)
variable {gap : Real} (hgapPos : 0 < gap)
  (hgap : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction T Q hQ)
    (TauCeti.LinearPMap.reducingRestriction T Q.orthogonal hQ.orthogonal) gap)

/-- Directed use: only the residual is bounded, and its equation is on the domain. -/
example (R : P →L[K] E)
    (hres : forall p : P, forall hp : (p : E) ∈ T.domain,
      T ⟨(p : E), hp⟩ = A ⟨(p : E), by rw [← hdom]; exact hp⟩ + R p)
    (hAngle : N.Mem (Angle.directedSinTwoAngleOperator P Q)) (hR : N.Mem R) :
    gap * N.gaugeReal (Angle.directedSinTwoAngleOperator P Q) ≤ 2 * N.gaugeReal R := by
  exact (sinTwoTheta_commonDomain_whereDefinedUIN_rclike
    N hA hT hdom hP hQ hgapPos hgap).1 R hres hAngle hR

/-- Ambient use: the caller supplies no trial residual or bounded trial operator. -/
example (Hop : E →L[K] E) (hHop : Hop.IsSymmetric)
    (hEq : T = TauCeti.LinearPMap.addBounded A Hop)
    (hAngle : N.Mem (Angle.sinTwoAngleOperator P Q)) (hMem : N.Mem Hop) :
    gap * N.gaugeReal (Angle.sinTwoAngleOperator P Q) ≤ 2 * N.gaugeReal Hop := by
  exact (sinTwoTheta_commonDomain_whereDefinedUIN_rclike
    N hA hT hdom hP hQ hgapPos hgap).2 Hop hHop hEq hAngle hMem

end
end TauCeti.DavisKahan1970.CommonDomainUsage
