/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisorClassRecurrence

/-!
# Bounding the Riemann--Roch genus from a one-point inequality

Once the uniform Riemann--Roch formula is known, any coarse one-point
Riemann inequality bounds its genus parameter.  This is the bridge that will
turn the existing bidegree monomial budget into a numerator-degree bound.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance genusBoundConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance genusBoundConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A one-point lower Riemann inequality with budget `budget`, together with
the uniform eventual Riemann--Roch formula, forces `genus ≤ budget`. -/
theorem genus_le_budget_of_uniformRiemann_onePoint
    (genus threshold budget : ℕ)
    (P : FiniteExtensionPlace K L)
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hLower : ∀ N : ℕ,
      N * finiteExtensionPlaceDegree K L P + 1 ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P N) + budget) :
    genus ≤ budget := by
  let d := finiteExtensionPlaceDegree K L P
  let D : FiniteExtensionDivisor K L :=
    Finsupp.single P (threshold : ℤ)
  have hd : 0 < d := finiteExtensionPlaceDegree_pos K L P
  have hthreshold : threshold ≤ threshold * d := by
    by_cases ht : threshold = 0
    · simp [ht]
    · exact Nat.le_mul_of_pos_right _ hd
  have hdegree : finiteExtensionDivisorDegree K L D =
      (threshold * d : ℕ) := by
    dsimp only [D, d]
    rw [finiteExtensionDivisorDegree_single]
    norm_num
  have hdata := hRiemann.2 D (threshold * d) hthreshold hdegree
  letI : Module.Finite K (finiteExtensionRiemannSpace K L D) := hdata.1
  have hspace : finiteExtensionRiemannSpace K L D =
      finiteExtensionOnePointRiemannSpace K L P threshold := by
    rfl
  have hrank : Module.finrank K
      (finiteExtensionOnePointRiemannSpace K L P threshold) =
        threshold * d + 1 - genus := by
    rw [← hspace]
    exact hdata.2
  have hlower := hLower threshold
  have hgenusThreshold := hRiemann.1
  have hgenusDegree : genus ≤ threshold * d + 1 := by
    exact hgenusThreshold.trans (by omega)
  have hrankAdd :
      Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P threshold) + genus =
        threshold * d + 1 := by
    rw [hrank, Nat.sub_add_cancel hgenusDegree]
  have hcancel :
      Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P threshold) + genus ≤
        Module.finrank K
          (finiteExtensionOnePointRiemannSpace K L P threshold) + budget := by
    rw [hrankAdd]
    exact hlower
  exact Nat.le_of_add_le_add_left hcancel

end

end BGS.HasseWeil
