/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisorDegreeIndex
import LeanPool.MarkoffModP.BGS.HasseWeil.ClosedPlaceEulerRecurrence
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaConstantExtensionIdentity

/-!
# Degree support and the constant-extension zeta identity

This file specializes the formal constant-extension identity to the exhaustive
closed-place point-count sequence.  The divisor-degree index itself supplies
the required divisibility support.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The exhaustive closed-place count vanishes outside multiples of the
divisor-degree index. -/
theorem finiteExtensionClosedPlaceExtensionCount_eq_zero_of_not_dvd_index
    (n : ℕ)
    (hn : ¬ finiteExtensionDivisorDegreeIndex K L ∣ n) :
    finiteExtensionClosedPlaceExtensionCount K L n = 0 := by
  classical
  simp only [finiteExtensionClosedPlaceExtensionCount]
  apply Finset.sum_eq_zero
  intro P _
  split_ifs with hdegree
  · exact False.elim (hn
      ((finiteExtensionDivisorDegreeIndex_dvd_placeDegree K L P.1).trans
        hdegree))
  · rfl

/-- Once the geometric constant extension supplies its exact point-count
relation, the corresponding zeta identity follows automatically. -/
theorem finiteExtensionClosedPlaceZeta_hasDegreeExtensionIdentity
    (extendedPointCount : ℕ → ℕ)
    (hcount : ∀ r,
      extendedPointCount r =
        finiteExtensionClosedPlaceExtensionCount K L
          (finiteExtensionDivisorDegreeIndex K L * r)) :
    HasFormalDegreeExtensionZetaIdentity
      (formalPointCountZeta
        (finiteExtensionClosedPlaceExtensionCount K L))
      (formalPointCountZeta extendedPointCount)
      (finiteExtensionDivisorDegreeIndex K L) := by
  exact formalPointCountZeta_hasDegreeExtensionIdentity
    (finiteExtensionClosedPlaceExtensionCount K L)
    extendedPointCount (finiteExtensionDivisorDegreeIndex K L)
    (finiteExtensionDivisorDegreeIndex_pos K L) hcount
    (finiteExtensionClosedPlaceExtensionCount_eq_zero_of_not_dvd_index K L)

end

end BGS.HasseWeil
