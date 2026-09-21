/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ClosedPlaceEulerRecurrence
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceAlgEquiv

/-!
# Closed-place counts across function-field equivalences

The closed-place extension-count sequence is a weighted sum depending only
on absolute place degrees.  Hence the degree-preserving place equivalence
induced by a `K(X)`-algebra equivalence preserves the entire sequence.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K L M : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
  [Field L] [Field M]
  [Algebra (RatFunc K) L] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) M]

/-- Places of degree at most `r` are preserved by a function-field
equivalence. -/
noncomputable def finiteExtensionPlaceDegreeLEEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) (r : ℕ) :
    {P : FiniteExtensionPlace K L //
        finiteExtensionPlaceDegree K L P ≤ r} ≃
      {P : FiniteExtensionPlace K M //
        finiteExtensionPlaceDegree K M P ≤ r} :=
  Equiv.subtypeEquiv (finiteExtensionPlaceEquivOfAlgEquiv K L M e) (by
    intro P
    rw [finiteExtensionPlaceEquivOfAlgEquiv_degree K L M e P])

/-- Within a bounded family, the places whose degrees divide `r` are also
preserved. -/
noncomputable def finiteExtensionPlaceDegreeDvdEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) (r : ℕ) :
    {P : {P : FiniteExtensionPlace K L //
          finiteExtensionPlaceDegree K L P ≤ r} //
        finiteExtensionPlaceDegree K L P.1 ∣ r} ≃
      {P : {P : FiniteExtensionPlace K M //
          finiteExtensionPlaceDegree K M P ≤ r} //
        finiteExtensionPlaceDegree K M P.1 ∣ r} :=
  Equiv.subtypeEquiv
    (finiteExtensionPlaceDegreeLEEquivOfAlgEquiv K L M e r) (by
      intro P
      change finiteExtensionPlaceDegree K L P.1 ∣ r ↔
        finiteExtensionPlaceDegree K M
          (finiteExtensionPlaceEquivOfAlgEquiv K L M e P.1) ∣ r
      rw [finiteExtensionPlaceEquivOfAlgEquiv_degree K L M e P.1])

/-- Every closed-place extension count is invariant under an equivalence of
finite `K(X)`-algebras. -/
theorem finiteExtensionClosedPlaceExtensionCount_eq_of_algEquiv
    (e : L ≃ₐ[RatFunc K] M) (r : ℕ) :
    finiteExtensionClosedPlaceExtensionCount K L r =
      finiteExtensionClosedPlaceExtensionCount K M r := by
  letI := finiteExtensionPlaceDegreeLEFintype K L r
  letI := finiteExtensionPlaceDegreeLEFintype K M r
  rw [finiteExtensionClosedPlaceExtensionCount_eq_sum_degree_dvd,
    finiteExtensionClosedPlaceExtensionCount_eq_sum_degree_dvd]
  apply Fintype.sum_equiv
    (finiteExtensionPlaceDegreeDvdEquivOfAlgEquiv K L M e r)
  intro P
  change finiteExtensionPlaceDegree K L P.1.1 =
    finiteExtensionPlaceDegree K M
      (finiteExtensionPlaceEquivOfAlgEquiv K L M e P.1.1)
  exact (finiteExtensionPlaceEquivOfAlgEquiv_degree K L M e P.1.1).symm

end

end BGS.HasseWeil
