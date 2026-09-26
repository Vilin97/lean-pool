/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoTheta
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTheta
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoTheta

/-!
# Focused audit for the Section 7 and Theorem 6.3 source surfaces

Dependency audit for the sine-double-angle, generalized-tangent, and
tangent-double-angle source facades.  Every `#print axioms` below must report
only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970

/-! ## Section 7, equations (7.1)--(7.5): sine double angle -/

/-! ## Theorem 6.3: generalized tangent -/

/-! ## Section 7, equation (7.6): tangent double angle -/

end DavisKahan1970
end TauCeti
