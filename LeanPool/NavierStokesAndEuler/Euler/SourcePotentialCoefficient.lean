/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialNormalMap
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The literal vector-potential multiplier inherits the source normal coefficient bounds. -/

@[expose] public section


noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCrossProduct
  EulerSourceNormalCoefficient EulerSourceForwardCoefficient EulerTimeLpGramGevrey EulerGevrey
open scoped BoundedContinuousFunction ContDiff

/-- Normal field: an abbreviation for `Space →ᵇ (Space →L[ℝ] ℝ)`. -/
abbrev NormalField := Space →ᵇ (Space →L[ℝ] ℝ)
/-- Potential field: an abbreviation for `Space →ᵇ (Space →L[ℝ] Space)`. -/
abbrev PotentialField := Space →ᵇ (Space →L[ℝ] Space)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient1 : NormedAddCommGroup NormalField := inferInstance
/-- Cache the standard `NormedSpace ℝ NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient2 : NormedSpace ℝ NormalField := inferInstance
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient3 : NormedAddCommGroup PotentialField := inferInstance
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient4 : NormedSpace ℝ PotentialField := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,NormalField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient5 : NormedAddCommGroup C(K,NormalField) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,NormalField)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient6 : NormedSpace ℝ C(K,NormalField) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient7 : NormedAddCommGroup C(K,PotentialField) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient8 : NormedSpace ℝ C(K,PotentialField) := inferInstance

/-- Potential path map, given by `(normalPotentialMap.compLeftContinuousBounded
Space).compLeftContinuous ℝ K`. -/
def potentialPathMap : C(K,NormalField) →L[ℝ] C(K,PotentialField) :=
  (normalPotentialMap.compLeftContinuousBounded Space).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem potentialPathMap_apply (N : C(K, NormalField)) (t : K) (x : Space) :
    potentialPathMap N t x = normalPotentialMap (N t x) := rfl

theorem potentialPathMap_norm : ‖potentialPathMap (K := K)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro N
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg N)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg N)).mpr
  intro x
  change ‖normalPotentialMap (N t x)‖ ≤ ‖N‖
  exact (normalPotentialMap.le_of_opNorm_le normalPotentialMap_norm (N t x)).trans
    (by simpa only [one_mul] using ((N t).norm_coe_le_norm x).trans (N.norm_coe_le_norm t))

variable (m : SmoothCoefficientPath K Space) (c : ℝ) (hc : 0 < c)
  (hm : ∀ t x, c ≤ ‖m.field t x‖ ^ 2)

/-- Potential coefficient, given by `potentialPathMap (normalFunctional m c hc hm)`. -/
def potentialCoefficient : C(K,PotentialField) :=
  potentialPathMap (normalFunctional m c hc hm)

theorem potentialCoefficient_apply (t : K) (x : Space) :
    potentialCoefficient m c hc hm t x = potentialMultiplier (m.field t x) :=
  normalPotentialMap_eq (m.field t x) (normalFunctional m c hc hm t x)
    (normalFunctional_apply m c hc hm t x)

theorem potentialCoefficient_translated (a : Space) :
    translateCoefficientPath (potentialCoefficient m c hc hm) a =
      potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem potentialCoefficient_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialCoefficient m c hc hm)) := by
  have he : translateCoefficientPath (potentialCoefficient m c hc hm) =
      fun a => potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) :=
    funext (potentialCoefficient_translated m c hc hm)
  rw [he]
  exact potentialPathMap.contDiff.comp (normalFunctional_translation_contDiff m c hc hm)

/-- The source coefficient passes through a linear contraction, with no radius or shift change. -/
theorem potentialCoefficient_translation_bound (Rc C Ri : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRi : 2 * gramCost c C 1 * (Rc + 1) ≤ Ri)
    (hbm : ∀ n t x, ‖iteratedFDeriv ℝ n (m.field t : Space → Space) x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialCoefficient m c hc hm)) a‖ ≤
      (3*Ri*C)*majorant (4*Ri) 0 n := by
  have he : translateCoefficientPath (potentialCoefficient m c hc hm) =
      fun a => potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) :=
    funext (potentialCoefficient_translated m c hc hm)
  rw [he]
  have h := (potentialPathMap (K := K)).norm_iteratedFDeriv_comp_left
    ((normalFunctional_translation_contDiff m c hc hm).contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (potentialPathMap_norm (K := K)) (norm_nonneg _)).trans
    (by
        simpa only [one_mul] using normalFunctional_translation_bound m c hc hm Rc C Ri hRc hC hRi
            hbm n a))

end EulerSourcePotentialCoefficient
