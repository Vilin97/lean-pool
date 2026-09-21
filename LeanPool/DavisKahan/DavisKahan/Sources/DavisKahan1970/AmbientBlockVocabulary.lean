/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.TanAngleFunctionalCalculus

/-!
# Ambient block vocabulary for the Davis--Kahan 1970 whole-space estimates

The paper's ambient single- and double-angle statements are proved through
block representatives built from the projector difference `D = P_V - P_U` and
from totalized secant inverses.  Those three definitions are pure notation: they
carry no spectral hypothesis and no estimate, and both the `tan Theta` and the
`tan 2Theta` whole-space developments consume them.

They live in their own module because a *definition* must be nameable without
importing the *theorems* stated about it.  The comparator challenge surface
states the paper's whole-space theorems in this same namespace, so importing a
theorem module there would clash on the theorem name while importing this one
does not.

The declarations keep their original `TauCeti.DavisKahan1970` names; only the
module boundary moved.
-/

namespace TauCeti
namespace DavisKahan1970



open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The projector difference `D = P_V − P_U`, the operator whose modulus is
`sin Θ`. -/
def projectorDifference : E →L[ℂ] E :=
  V.starProjection - U.starProjection

/-- The ambient `cos²Θ` as an inverse: `(1 − sin²Θ)⁻¹`.  Under uniform
transversality this is the honest inverse; the `Ring.inverse` spelling keeps the
definition total. -/
def secantSquared : E →L[ℂ] E :=
  Ring.inverse (1 - projectorDifference U V * projectorDifference U V)

/-- The ambient `cos 2Θ` as an inverse: `(1 − 2 sin²Θ)⁻¹`.  Under uniform
quarter transversality this is the honest inverse; the `Ring.inverse` spelling
keeps the definition total. -/
def doubleSecant : E →L[ℂ] E :=
  Ring.inverse (1 - 2 * (projectorDifference U V * projectorDifference U V))

end

end DavisKahan1970
end TauCeti
