/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Erdős 97 convex-octagon formalization: Basic -/

@[expose] public section

namespace Erdos97Octagon

open scoped InnerProductSpace
open Module

/-- The Euclidean plane, represented as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

end Erdos97Octagon
