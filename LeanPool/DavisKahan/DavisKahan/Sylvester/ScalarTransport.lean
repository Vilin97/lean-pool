/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarGeneric
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-! # Scalar Transport -/

open TauCeti.DavisKahan.Sylvester

/-!
# The unbounded Sylvester Ky Fan estimate at every `RCLike` field

`ExactSinTheta.HasUnboundedSylvesterKyFan` was a hypothesis: the Section 5
estimate quantified uniformly over every pair of Hilbert spaces, with instances at
`ℝ` and at `ℂ` and nothing in between.  Every scalar-generic Section 2 statement
that used it therefore carried it as a binder.

`RCLike` has exactly two models (`RCLike.I_eq_zero_or_im_I_eq_one`), and
`TauCeti.ScalarTransport` carries a Hilbert space to the corresponding real or
complex one without moving a vector, a norm, or a topology.  So the estimate
transports, and the class becomes an instance at every `RCLike` field.

What has to be carried across, and is, in this file:

| object | lemma |
| --- | --- |
| finite Ky Fan gauges | `kyFanApproximationGauge_clm` |
| operator-form semibounds | `semiboundedAbove_pmap_iff`, `semiboundedBelow_pmap_iff` |
| the real resolvent set and spectrum | `realResolventSet_pmap`, `realSpectrum_pmap` |
| the three-constructor separation | `formBoundedSylvesterGap_pmap` |
| the domain-aware Sylvester equation | `sylvesterEquation_pmap` |

Self-adjointness and approximation numbers come from the transport modules
themselves.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Theorem 5.2 and the Section 2
  arbitrary-unitarily-invariant-norm scope.
-/

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti TauCeti.ScalarTransport TauCeti.DavisKahan.ExactSinTheta

universe u w v

namespace TauCeti
namespace ScalarTransport


variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Finite Ky Fan gauges are unchanged by the transport, term by term. -/
theorem kyFanApproximationGauge_clm (k : ℕ) (T : E →L[𝕜] F) :
    kyFanApproximationGauge k (clm (e := e) T) = kyFanApproximationGauge k T := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_congr rfl fun n _ => approximationNumber_clm (e := e) T n

omit [CompleteSpace E] in
/-- An operator-form upper bound transports, and reflects. -/
theorem semiboundedAbove_pmap_iff {A : E →ₗ.[𝕜] E} {c : ℝ} :
    TauCeti.LinearPMap.SemiboundedAbove (pmap (e := e) A) c ↔
      TauCeti.LinearPMap.SemiboundedAbove A c := by
  constructor
  · intro h x
    have h2 : RCLike.re (e (inner 𝕜 (A x) ((x : E)))) ≤ c * ‖(x : E)‖ ^ 2 :=
      h ⟨of (e := e) (x : E), x.2⟩
    rwa [e.re_map] at h2
  · intro h x
    have h2 := h (domainOut (e := e) A x)
    show RCLike.re (e (inner 𝕜 (A (domainOut (e := e) A x))
      ((domainOut (e := e) A x : E)))) ≤ c * ‖(domainOut (e := e) A x : E)‖ ^ 2
    rwa [e.re_map]

omit [CompleteSpace E] in
/-- An operator-form lower bound transports, and reflects. -/
theorem semiboundedBelow_pmap_iff {A : E →ₗ.[𝕜] E} {c : ℝ} :
    TauCeti.LinearPMap.SemiboundedBelow (pmap (e := e) A) c ↔
      TauCeti.LinearPMap.SemiboundedBelow A c := by
  constructor
  · intro h x
    have h2 : c * ‖(x : E)‖ ^ 2 ≤ RCLike.re (e (inner 𝕜 (A x) ((x : E)))) :=
      h ⟨of (e := e) (x : E), x.2⟩
    rwa [e.re_map] at h2
  · intro h x
    have h2 := h (domainOut (e := e) A x)
    show c * ‖(domainOut (e := e) A x : E)‖ ^ 2 ≤
      RCLike.re (e (inner 𝕜 (A (domainOut (e := e) A x)) ((domainOut (e := e) A x : E))))
    rwa [e.re_map]

omit [CompleteSpace E] in
/-- The real resolvent set is unchanged: an inverse on one side is an inverse on the other. -/
theorem realResolventSet_pmap (A : E →ₗ.[𝕜] E) :
    TauCeti.LinearPMap.realResolventSet (pmap (e := e) A) =
      TauCeti.LinearPMap.realResolventSet A := by
  ext lam
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff, TauCeti.LinearPMap.mem_realResolventSet_iff]
  constructor
  · rintro ⟨R, hleft, hright⟩
    refine ⟨(clmEquiv (e := e)).symm R, fun x => ?_, fun y => ?_⟩
    · have h2 := hleft ⟨of (e := e) (x : E), x.2⟩
      rwa [show (((lam : ℝ) : 𝕂)) • (of (e := e) (x : E)) =
        of (e := e) ((((lam : ℝ)) : 𝕜) • (x : E)) from ofReal_smul_of _ _] at h2
    · obtain ⟨h, hh⟩ := hright (of (e := e) y)
      refine ⟨h, ?_⟩
      rwa [show (((lam : ℝ) : 𝕂)) • (R (of (e := e) y)) =
        of (e := e) ((((lam : ℝ)) : 𝕜) • out (R (of (e := e) y))) from
          ofReal_smul_of (e := e) (E := E) lam (out (R (of (e := e) y)))] at hh
  · rintro ⟨R, hleft, hright⟩
    refine ⟨clm (e := e) R, fun x => ?_, fun y => ?_⟩
    · have h2 := hleft (domainOut (e := e) A x)
      rw [show (((lam : ℝ) : 𝕂)) • ((x : ScalarTransport e E)) =
        of (e := e) ((((lam : ℝ)) : 𝕜) • out (x : ScalarTransport e E)) from
          ofReal_smul_of (e := e) (E := E) lam (out (x : ScalarTransport e E))]
      exact congrArg (of (e := e)) h2
    · obtain ⟨h, hh⟩ := hright (out y)
      refine ⟨h, ?_⟩
      rw [show (((lam : ℝ) : 𝕂)) • ((clm (e := e) R) y) =
        of (e := e) ((((lam : ℝ)) : 𝕜) • (R (out y))) from
          ofReal_smul_of (e := e) (E := E) lam (R (out y))]
      exact congrArg (of (e := e)) hh

omit [CompleteSpace E] in
/-- and hence so is the real spectrum. -/
theorem realSpectrum_pmap (A : E →ₗ.[𝕜] E) :
    TauCeti.LinearPMap.realSpectrum (pmap (e := e) A) = TauCeti.LinearPMap.realSpectrum A := by
  unfold TauCeti.LinearPMap.realSpectrum
  rw [realResolventSet_pmap]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The three-constructor separation transports, constructor by constructor. -/
theorem formBoundedSylvesterGap_pmap {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {δ : ℝ}
    (h : FormBoundedSylvesterGap A B δ) :
    FormBoundedSylvesterGap (pmap (e := e) A) (pmap (e := e) B) δ := by
  cases h with
  | intervalExterior hβα hgap =>
      refine FormBoundedSylvesterGap.intervalExterior hβα ?_
      unfold TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap at hgap ⊢
      rwa [realSpectrum_pmap, realSpectrum_pmap]
  | leftAboveRightBelow c hA hB =>
      exact FormBoundedSylvesterGap.leftAboveRightBelow c
        (semiboundedBelow_pmap_iff.mpr hA) (semiboundedAbove_pmap_iff.mpr hB)
  | leftBelowRightAbove c hA hB =>
      exact FormBoundedSylvesterGap.leftBelowRightAbove c
        (semiboundedAbove_pmap_iff.mpr hA) (semiboundedBelow_pmap_iff.mpr hB)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A domain-aware Sylvester equation transports. -/
theorem sylvesterEquation_pmap {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {X C : F →L[𝕜] E}
    (h : TauCeti.LinearPMap.SylvesterEquation A B X C) :
    TauCeti.LinearPMap.SylvesterEquation (pmap (e := e) A) (pmap (e := e) B)
      (clm (e := e) X) (clm (e := e) C) where
  mapsTo_domain x := h.mapsTo_domain (domainOut (e := e) B x)
  equation x := congrArg (of (e := e)) (h.equation (domainOut (e := e) B x))

end ScalarTransport

namespace DavisKahan
namespace Sylvester

open TauCeti.ScalarTransport

/-- The unbounded Sylvester Ky Fan estimate transports along an isomorphism of
`RCLike` fields: every object it mentions -- the two self-adjoint partial maps,
the separation, the Sylvester equation, and the finite Ky Fan gauges -- is
unchanged by the transport. -/
theorem hasUnboundedSylvesterKyFan_of_transport
    {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] (e : RCLikeIso 𝕜 𝕂)
    [HasUnboundedSylvesterKyFan.{w, v} 𝕂] :
    HasUnboundedSylvesterKyFan.{u, v} 𝕜 where
  out := by
    intro E F _ _ _ _ _ _ A B hA hB X C δ hδ hgap hEq k
    have hbound := HasUnboundedSylvesterKyFan.out (𝕜 := 𝕂)
      (A := pmap (e := e) A) (B := pmap (e := e) B)
      ((isSelfAdjoint_pmap_iff e).mpr hA) ((isSelfAdjoint_pmap_iff e).mpr hB)
      (X := clm (e := e) X) (C := clm (e := e) C) hδ
      (formBoundedSylvesterGap_pmap hgap) (sylvesterEquation_pmap hEq) k
    rwa [kyFanApproximationGauge_clm, kyFanApproximationGauge_clm] at hbound

/-- **The unbounded Sylvester Ky Fan estimate holds at every `RCLike` field.**

This discharges the class that every scalar-generic Section 2 statement carried
as a hypothesis; those statements no longer need the binder. -/
instance hasUnboundedSylvesterKyFan (𝕜 : Type u) [RCLike 𝕜] :
    HasUnboundedSylvesterKyFan.{u, v} 𝕜 := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · exact hasUnboundedSylvesterKyFan_of_transport (RCLikeIso.real h)
  · exact hasUnboundedSylvesterKyFan_of_transport (RCLikeIso.complex h)

end Sylvester
end DavisKahan
end TauCeti
