/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourcePotentialTimeCoefficient
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

/-! The potential time coefficient from an actual continuous, translation-smooth normal derivative
path. -/

@[expose] public section


noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerSourceNormalCoefficient
  EulerPacketCrossProduct EulerOperatorGevreyCalculus EulerGevrey EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath1 : NormedAddCommGroup (Space →ᵇ Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimePath2 : NormedSpace ℝ (Space →ᵇ Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath3 : NormedAddCommGroup (ℝ →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (ℝ →L[ℝ] Space)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimePath4 : NormedSpace ℝ (ℝ →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimePath5 : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath6 : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath7 : NormedAddCommGroup C(K,Space →ᵇ Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath8 : NormedSpace ℝ C(K,Space →ᵇ Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimePath9 : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath10 : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath11 : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimePath12 : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
/-- Cache the standard `NormedAddCommGroup NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimePath13 : NormedAddCommGroup NormalField := inferInstance
/-- Cache the standard `NormedSpace ℝ NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimePath14 : NormedSpace ℝ NormalField := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,NormalField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath15 : NormedAddCommGroup C(K,NormalField) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,NormalField)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimePath16 : NormedSpace ℝ C(K,NormalField) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath17 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath18 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath19 : NormedAddCommGroup PotentialField := inferInstance
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimePath20 : NormedSpace ℝ PotentialField := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath21 : NormedAddCommGroup C(K,PotentialField) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimePath22 : NormedSpace ℝ C(K,PotentialField) := inferInstance

/-- Column path, given by `mapCoefficientPath (ContinuousLinearMap.toSpanSingletonLIE ℝ
Space).toLinearIsometry.toContinuousLinearMap`. -/
def columnPath : C(K,Space →ᵇ Space) →L[ℝ] C(K,Space →ᵇ ℝ →L[ℝ] Space) :=
  mapCoefficientPath (ContinuousLinearMap.toSpanSingletonLIE ℝ
      Space).toLinearIsometry.toContinuousLinearMap

theorem columnPath_norm : ‖columnPath (K := K)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).mpr
  intro y
  change ‖(ContinuousLinearMap.toSpanSingletonLIE ℝ Space) (A t y)‖ ≤ ‖A‖
  rw [LinearIsometryEquiv.norm_map]
  exact ((A t).norm_coe_le_norm y).trans (A.norm_coe_le_norm t)

omit [CompactSpace K] in
theorem columnPath_translation (A : C(K, Space →ᵇ Space)) (a : Space) :
    translateCoefficientPath (columnPath A) a = columnPath (translateCoefficientPath A a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

section Coefficient

variable (m : SmoothCoefficientPath K Space) (m₁ : C(K, Space →ᵇ Space))
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)

/-- Potential time path, given by `potentialPathMap (timeNormalPath (normalFunctional m c hc hm)
(columnPath m₁))`. -/
def potentialTimePath : C(K,PotentialField) :=
  potentialPathMap (timeNormalPath (normalFunctional m c hc hm) (columnPath m₁))

theorem potentialTimePath_apply (t : K) (y : Space) :
    potentialTimePath m m₁ c hc hm t y = potentialMultiplierDerivative (m.field t y) (m₁ t y) := by
  have hn : m.field t y ≠ 0 := by
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  exact normalTimeMap_potential (m.field t y) (m₁ t y)
    (normalFunctional m c hc hm t y) hn (normalFunctional_apply m c hc hm t y)

theorem potentialTimePath_translation :
    translateCoefficientPath (potentialTimePath m m₁ c hc hm) = fun a =>
      potentialPathMap (timeNormalPath (translateCoefficientPath (normalFunctional m c hc hm) a)
        (columnPath (translateCoefficientPath m₁ a))) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

theorem potentialTimePath_orbit (h₁ : ContDiff ℝ ∞ (translateCoefficientPath m₁)) :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialTimePath m m₁ c hc hm)) := by
  rw [potentialTimePath_translation]
  have hcol := (columnPath (K := K)).contDiff.comp h₁
  have h := timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm) hcol
  exact (potentialPathMap (K := K)).contDiff.comp h

theorem potentialTimePath_bound (h₁ : ContDiff ℝ ∞ (translateCoefficientPath m₁))
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath (normalFunctional m c hc hm)) a‖ ≤
      C * majorant R 0 n)
    (hb₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath m₁) a‖ ≤ D * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialTimePath m m₁ c hc hm)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  rw [potentialTimePath_translation]
  have hcol := (columnPath (K := K)).contDiff.comp h₁
  have hbcol := contraction_bound (columnPath (K := K)) columnPath_norm
    (translateCoefficientPath m₁) h₁ R D hR hD 0 hb₁
  have h := timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm) hcol
  exact contraction_bound (potentialPathMap (K := K)) potentialPathMap_norm _ h
    R (27*C^2*D) hR (by positivity) 0
    (timeNormalPath_bound _ _ (normalFunctional_translation_contDiff m c hc hm)
      hcol R C D hR hC hD hbN hbcol) n a

end Coefficient

section Time

variable (T : ℝ) (hT : 0 ≤ T) (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (m₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space))
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)
  (hmt : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : Space,
    HasDerivWithinAt (fun r => extendPath T hT m.field r y)
      (extendPath T hT m₁ t y) (Icc (0 : ℝ) T) t)

include hmt in
theorem potentialTimePath_hasDerivWithinAt (t : Icc (0 : ℝ) T) (y : Space) :
    HasDerivWithinAt (fun r => extendPath T hT (potentialCoefficient m c hc hm) r y)
      (potentialTimePath m m₁ c hc hm t y) (Icc (0 : ℝ) T) t := by
  have hn : extendPath T hT m.field t y ≠ 0 := by
    change m.field (projIcc 0 T hT t) y ≠ 0
    rw [projIcc_of_mem hT t.property]
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  have h := potentialMultiplier_hasDerivWithinAt (Icc (0 : ℝ) T) t
    (fun r => extendPath T hT m.field r y) (extendPath T hT m₁ t y) (hmt t t.property y) hn
  convert h using 1 <;> try rfl
  · funext r
    exact potentialCoefficient_apply m c hc hm (projIcc 0 T hT r) y
  · rw [potentialTimePath_apply]
    change potentialMultiplierDerivative (m.field t y) (m₁ t y) =
      potentialMultiplierDerivative (m.field (projIcc 0 T hT t) y) (m₁ (projIcc 0 T hT t) y)
    rw [projIcc_of_mem hT t.property]

end Time
end EulerSourcePotentialCoefficient
