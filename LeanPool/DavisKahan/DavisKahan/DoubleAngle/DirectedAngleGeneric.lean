/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleGeneric
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.AngleTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.DirectedAngleRealTransport
/-! ## The block representation, at every field

`sinTwoThetaIdealBlock U V = P_U ∘ P_{J_V Uᗮ}` is the object the unbounded directed `sin 2Θ`
estimates are actually proved about: a one-sided block, not an angle.  It carries the same
complete approximation-number sequence as the directed `sin 2Θ`, so no unitarily invariant norm
distinguishes them, and a bound proved for the block is a bound for the paper's object.

That correspondence existed over `ℂ`, and over `ℝ` only against the complexified directed angle
(`Real.directedSinTwoAngleOperatorRC`) -- `TangentTransport.lean` says in its own docstring that
a real statement "would need a real directed `sin 2Θ` operator, which would be a second spelling
of an existing concept".  `directedSinTwoAngleOperator` is now that operator at every field, and
it is not a second spelling: it is the one definition, of which the `...C` and `...RC` objects
are the instance and the complexification.
-/

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped InnerProductSpace

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

noncomputable section

universe u w v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

section BlockTransport

variable {𝕂 : Type w} [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}

open TauCeti.ScalarTransport

omit [CompleteSpace E] in
/-- The scalar transport carries the ideal block. -/
@[simp] theorem clm_sinTwoThetaIdealBlock :
    clm (e := e) (sinTwoThetaIdealBlock U V) =
      sinTwoThetaIdealBlock (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  have hmap : ScalarTransport.submodule (e := e)
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)) =
      (ScalarTransport.submodule (e := e) U)ᗮ.map
        (((ScalarTransport.submodule (e := e) V).reflection.toLinearEquiv :
          ScalarTransport e E →ₗ[𝕂] ScalarTransport e E)) := by
    rw [ScalarTransport.submodule_map_reflection, ScalarTransport.submodule_orthogonal]
  change clm (e := e) (U.starProjection ∘L
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection) = _
  change _ = (ScalarTransport.submodule (e := e) U).starProjection ∘L
    ((ScalarTransport.submodule (e := e) U)ᗮ.map
      (((ScalarTransport.submodule (e := e) V).reflection.toLinearEquiv :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e E))).starProjection
  rw [← Submodule.starProjection_congr hmap, ScalarTransport.starProjection_clm,
    ScalarTransport.starProjection_clm]
  rfl

end BlockTransport

/-- **The ideal block and the directed `sin 2Θ` have the same approximation numbers**, at an
arbitrary `RCLike` field.

Proved by transporting both objects to the field's real-like or complex-like model, where the
correspondence is already established: over `ℂ` directly, over `ℝ` through the complexification,
which is where the real development keeps the directed angle. -/
theorem sinTwoThetaIdealBlock_hasSameApproximationNumbers_rclike :
    (sinTwoThetaIdealBlock U V).HasSameApproximationNumbers
      (directedSinTwoAngleOperator U V) := by
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : RCLikeIso 𝕜 𝕂),
      (sinTwoThetaIdealBlock (TauCeti.ScalarTransport.submodule (e := e) U)
          (TauCeti.ScalarTransport.submodule (e := e) V)).HasSameApproximationNumbers
        (directedSinTwoAngleOperator (TauCeti.ScalarTransport.submodule (e := e) U)
          (TauCeti.ScalarTransport.submodule (e := e) V)) →
      (sinTwoThetaIdealBlock U V).HasSameApproximationNumbers
        (directedSinTwoAngleOperator U V) := by
    intro 𝕂 _ e h n
    have hb := TauCeti.ScalarTransport.approximationNumber_clm (e := e)
      (sinTwoThetaIdealBlock U V) n
    have ha := TauCeti.ScalarTransport.approximationNumber_clm (e := e)
      (directedSinTwoAngleOperator U V) n
    rw [clm_sinTwoThetaIdealBlock] at hb
    rw [clm_directedSinTwoAngleOperator] at ha
    rw [← hb, ← ha]
    exact h n
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · refine key (𝕂 := ℝ) (RCLikeIso.real h) fun n => ?_
    show ExactSinTheta.approximationSingularValue n _ =
      ExactSinTheta.approximationSingularValue n _
    rw [approximationSingularValue_sinTwoThetaIdealBlock_real,
      ← ExactSinTheta.ComplexificationApproximation.approximationSingularValue_complexify
        (directedSinTwoAngleOperator _ _) n,
      complexify_directedSinTwoAngleOperator]
  · exact key (𝕂 := ℂ) (RCLikeIso.complex h)
      (sinTwoThetaIdealBlock_hasSameApproximationNumbers _ _)

end

end DavisKahan.Angle
end TauCeti

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The ideal block and the directed `sin 2Θ` have the same gauge in every source unitarily
invariant norm**, at an arbitrary `RCLike` field: a paper norm's extended gauge is determined by
the approximation singular-value sequence, and the two sequences are equal. -/
theorem extendedGauge_sinTwoThetaIdealBlock_rclike (N : SymmetricNormingFunction) :
    N.extendedGauge (sinTwoThetaIdealBlock U V) =
      N.extendedGauge (directedSinTwoAngleOperator U V) :=
  N.gauge_eq_of_sameApproximationSingularValues
    (sinTwoThetaIdealBlock_hasSameApproximationNumbers_rclike U V)

/-- Ideal membership transfers between the block and the directed `sin 2Θ`. -/
theorem mem_directedSinTwoAngleOperator_iff (N : SymmetricNormingFunction) :
    N.Mem (directedSinTwoAngleOperator U V) ↔ N.Mem (sinTwoThetaIdealBlock U V) := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_sinTwoThetaIdealBlock_rclike U V N]

/-- The gauge transfers between the block and the directed `sin 2Θ`. -/
theorem gauge_directedSinTwoAngleOperator (N : SymmetricNormingFunction) :
    N.gauge (directedSinTwoAngleOperator U V) = N.gauge (sinTwoThetaIdealBlock U V) := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_sinTwoThetaIdealBlock_rclike U V N]

/-! ### The trial-side orientation

The estimates are proved about `sinTwoThetaIdealBlock U V` with `U` the reducing subspace
carrying the spectral gap and `V` the trial subspace, and the correspondence above lands on
`directedSinTwoAngleOperator U V`.  Davis and Kahan's `Θ₀` is the **trial-side** angle:
`‖sin Θ₀‖ = ‖Q^⊥ P‖ = ‖Q^⊥ E₀‖` with `P` the trial projector and `Q` the one whose blocks are
separated, so the paper's object is `directedSinTwoAngleOperator V U` -- trial first.

`directedSinTwoAngleOperator_hasSameApproximationNumbers_swap` is what closes that gap, and it
is a theorem, not a renaming: the two ordered directed *sines* have different approximation
numbers in general.  The three lemmas below are the source-facing forms. -/

/-- **The ideal block and the paper's trial-side directed `sin 2Θ₀` have the same approximation
numbers**, at an arbitrary `RCLike` field.

This composes the block correspondence with the order swap, and it is the form a source-facing
directed `sin 2Θ` theorem consumes: the estimate is proved about the block of the pair
(gap-carrying subspace, trial subspace), and the paper's conclusion is about the directed
double-angle sine of the same pair *in the other order*. -/
theorem sinTwoThetaIdealBlock_hasSameApproximationNumbers_trialSide :
    (sinTwoThetaIdealBlock U V).HasSameApproximationNumbers
      (directedSinTwoAngleOperator V U) :=
  (sinTwoThetaIdealBlock_hasSameApproximationNumbers_rclike U V).trans
    (directedSinTwoAngleOperator_hasSameApproximationNumbers_swap U V)

/-- The block and the trial-side directed `sin 2Θ₀` have the same gauge in every source
unitarily invariant norm. -/
theorem extendedGauge_sinTwoThetaIdealBlock_trialSide (N : SymmetricNormingFunction) :
    N.extendedGauge (sinTwoThetaIdealBlock U V) =
      N.extendedGauge (directedSinTwoAngleOperator V U) :=
  N.gauge_eq_of_sameApproximationSingularValues
    (sinTwoThetaIdealBlock_hasSameApproximationNumbers_trialSide U V)

/-- Ideal membership transfers between the block and the trial-side directed `sin 2Θ₀`. -/
theorem mem_directedSinTwoAngleOperator_trialSide_iff (N : SymmetricNormingFunction) :
    N.Mem (directedSinTwoAngleOperator V U) ↔ N.Mem (sinTwoThetaIdealBlock U V) := by
  unfold SymmetricNormingFunction.Mem
  rw [extendedGauge_sinTwoThetaIdealBlock_trialSide U V N]

/-- The gauge transfers between the block and the trial-side directed `sin 2Θ₀`. -/
theorem gauge_directedSinTwoAngleOperator_trialSide (N : SymmetricNormingFunction) :
    N.gauge (directedSinTwoAngleOperator V U) = N.gauge (sinTwoThetaIdealBlock U V) := by
  unfold SymmetricNormingFunction.gauge
  rw [extendedGauge_sinTwoThetaIdealBlock_trialSide U V N]

end

end DavisKahan.Angle
end TauCeti
