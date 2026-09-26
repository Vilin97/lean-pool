/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.AngleTransport
public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealAngleIdentification
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.ComplexificationGauge

/-!
# The real directed `sin 2Θ` and the ideal block

The real counterpart of `DoubleAngle/AngleTransport.lean`: the real `sin 2Θ` block and the
directed double-angle sine of a real pair carry the same complete approximation
singular-value sequence, hence the same membership and gauge in every source unitarily
invariant norm.

These four statements lived in `DoubleAngle/TangentTransport.lean` until 2026-09-04.  Nothing
about them is a tangent fact, and leaving them there made the scalar-generic directed sine
layer (`DoubleAngle/DirectedAngleGeneric.lean`) import the whole source-facing `tan 2Θ` stack
to reach one lemma about `sin 2Θ`.  `TangentTransport.lean` imports this module instead.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan.Angle
open TauCeti.DavisKahanExt TauCeti.ApproximationNumber TauCeti.RealComplexification
  TauCeti.DavisKahan.Foundation.RealComplexification

open scoped InnerProductSpace

noncomputable section

universe v

variable {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er]
  [CompleteSpace Er]

/-- **The real `sin 2Θ` block carries the directed angle's singular data.**

The real counterpart of `sinTwoThetaIdealBlock_hasSameApproximationNumbers`.
`norm_sinTwoThetaIdealBlock_real` gave this at the operator norm only, which is
one number; this gives every approximation singular value, which is what a
symmetric ideal actually reads.

The route is the one the norm identification already used: complexification
preserves approximation singular values, the real block complexifies to the
complex block of the complexified pair, and the complex transport applies there.

The target is `Real.directedSinTwoAngleOperatorRC`, the *directed* double-angle sine of the
real pair read in the complexification, which is where the tree keeps it — there
is no real directed spelling, only the ambient `sinTwoAngleOperatorR`.  As
in the complex case the directed operator is the block's partner: the block is
one-sided and carries each principal angle once, where an ambient angle object
carries it twice.

Superseded 2026-09-04, and the reasoning above no longer applies.  This docstring
said an equality of *real* `SymmetricNormingFunction` gauges "would need a real
directed `sin 2Θ` operator, which would be a second spelling of an existing
concept".  `TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator` is that operator
and is not a second spelling: it is the single definition at every `RCLike` field,
of which `directedSinTwoAngleOperatorC` is the instance at `ℂ` and
`Real.directedSinTwoAngleOperatorRC` the complexification of the instance at `ℝ`.
`DoubleAngle/DirectedAngleGeneric.lean` proves the gauge equality there, at every
field at once. -/
theorem approximationSingularValue_sinTwoThetaIdealBlock_real
    (U V : Submodule ℝ Er) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (n : ℕ) :
    approximationSingularValue n (sinTwoThetaIdealBlock U V)
      = approximationSingularValue n (Real.directedSinTwoAngleOperatorRC U V) := by
  rw [← ExactSinTheta.ComplexificationApproximation.approximationSingularValue_complexify
      (sinTwoThetaIdealBlock U V) n,
    complexify_sinTwoThetaIdealBlock U V]
  exact sinTwoThetaIdealBlock_hasSameApproximationNumbers
    (complexifySubmodule U) (complexifySubmodule V) n

/-- **The real `sin 2Θ` block and the real directed `sin 2Θ` have the same gauge
in every source unitarily invariant norm**, and one lies in the norm's ideal
exactly when the other does.

`approximationSingularValue_sinTwoThetaIdealBlock_real` in gauge form.  The two
operators live over different scalar fields -- the block is a real operator, the
angle is read in the complexification -- so the equality is chained through
`extendedGauge_complexify` rather than through
`gauge_eq_of_sameApproximationSingularValues`, which is same-field. -/
theorem extendedGauge_sinTwoThetaIdealBlock_real
    (U V : Submodule ℝ Er) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (N : ExactSinTheta.SymmetricNormingFunction) :
    N.extendedGauge (sinTwoThetaIdealBlock U V)
      = N.extendedGauge (Real.directedSinTwoAngleOperatorRC U V) := by
  rw [← ExactSinTheta.SymmetricNormingFunction.extendedGauge_complexify N
      (sinTwoThetaIdealBlock U V),
    complexify_sinTwoThetaIdealBlock U V]
  exact extendedGauge_sinTwoThetaIdealBlock_complex (complexifySubmodule U)
    (complexifySubmodule V) N

/-- Ideal membership transfers between the real block and the real directed
`sin 2Θ`. -/
theorem mem_directedSinTwoAngleOperatorRC_iff
    (U V : Submodule ℝ Er) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (N : ExactSinTheta.SymmetricNormingFunction) :
    N.Mem (Real.directedSinTwoAngleOperatorRC U V) ↔ N.Mem (sinTwoThetaIdealBlock U V) := by
  unfold ExactSinTheta.SymmetricNormingFunction.Mem
  rw [extendedGauge_sinTwoThetaIdealBlock_real U V N]

/-- The gauge transfers between the real block and the real directed `sin 2Θ`. -/
theorem gauge_directedSinTwoAngleOperatorRC
    (U V : Submodule ℝ Er) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (N : ExactSinTheta.SymmetricNormingFunction) :
    N.gauge (Real.directedSinTwoAngleOperatorRC U V)
      = N.gauge (sinTwoThetaIdealBlock U V) := by
  unfold ExactSinTheta.SymmetricNormingFunction.gauge
  rw [extendedGauge_sinTwoThetaIdealBlock_real U V N]

end

end DavisKahan
end TauCeti
