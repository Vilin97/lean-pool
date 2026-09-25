/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Definitions

/-!
# Connection ranks and minimum colour dimension

The natural-valued connection rank is the dimension of the actual
connection-map range. Under an edge-rank bound this range is finite,
so its natural dimension agrees with its module rank. The minimum
colour dimension is the least total colour bound of a representing
mixed model; it is zero when no representing model exists.
-/

@[expose] public section

namespace RS

/-- The closed fragment of `c` free circles. -/
noncomputable def circlesClosed (c : ℕ) : ClosedFragment :=
  (Fragment.circlesOnly c).relabel
    (_root_.Equiv.equivOfIsEmpty Empty (Fin 0))

/-- The natural dimension of the connection-map range. It agrees
with connection rank whenever the range is finite-dimensional. -/
noncomputable def connectionRank (f : ClosedFragment → ℂ) (t : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (connectionMap f t))

/-- A mixed functional represents the parameter on every closed
fragment, including those with free circles. -/
def MixedFunctional.Represents {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (f : ClosedFragment → ℂ) : Prop :=
  ∀ W, f W = mixedPartition h W

/-- The least total colour bound among representing mixed models,
with value zero when the set of such bounds is empty. -/
noncomputable def minimumColourDimension (f : ClosedFragment → ℂ) : ℕ :=
  sInf {d | IsMixedPartitionFunctionTotalBounded f d}

/-- The rank and free-circle conditions for prescribed even and
odd colour dimensions. -/
structure PrescribedColourBounds (f : ClosedFragment → ℂ)
    (k ℓ : ℕ) : Prop where
  /-- The free-circle value is the prescribed superdimension. -/
  circle_eq : f (circlesClosed 1) = (k : ℂ) - 2 * ℓ
  /-- Every connection rank is bounded by the total colour count. -/
  rank_bounded : EdgeRankBounded f (k + 2 * ℓ)

end RS
