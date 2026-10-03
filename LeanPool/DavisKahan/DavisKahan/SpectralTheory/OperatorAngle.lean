/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleReal
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.AngleFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-! # Operator Angle -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Canonical operator-angle compatibility surface

Literal positive angle operators require a complete complex Hilbert space, or
real complexification followed by the established descent bridges.  The former
scalar-generic facade attempted to hide those hypotheses and consequently had
no construction in the pinned foundations.  This module now exposes only the
scalar-generic graph predicates; the actual operators live in the canonical
complex and real-complexified modules imported above.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- An ambient angular operator maps the selected subspace into its orthogonal
complement and vanishes on that complement. -/
def IsAngularOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Prop :=
  X ∘L U.starProjection = X ∧ U.starProjection ∘L X = 0

/-- Maximal angle represented by the projection gap.  This scalar definition
is valid over every `RCLike` field and needs no operator functional calculus. -/
noncomputable def maximalAngle (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  Real.arcsin (U.projectionGap V)

end DavisKahanExt
end TauCeti
