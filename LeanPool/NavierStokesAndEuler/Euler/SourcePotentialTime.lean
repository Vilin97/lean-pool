/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourcePotentialTimeCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTime

@[expose] public section

/-! The source vector potential has its genuine, explicitly constructed time derivative. -/

noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCrossProduct
  EulerVolterraConvolution EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderPotential
open scoped ContDiff BoundedContinuousFunction

variable (T : ℝ) (hT : 0 ≤ T)
  (m m₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖^2)

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

variable (hmt : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : Space,
  HasDerivWithinAt (fun r => extendPath T hT m.field r y)
    (extendPath T hT m₁.field t y) (Icc (0 : ℝ) T) t)

include hmt in
/-- The polynomial coefficient really differentiates the actual source multiplier. -/
theorem potentialCoefficient_hasDerivWithinAt (t : Icc (0 : ℝ) T) (y : Space) :
    HasDerivWithinAt (fun r => extendPath T hT (potentialCoefficient m c hc hm) r y)
      (potentialTimeCoefficient m m₁ c hc hm t y) (Icc (0 : ℝ) T) t := by
  have hn : extendPath T hT m.field t y ≠ 0 := by
    change m.field (projIcc 0 T hT t) y ≠ 0
    rw [projIcc_of_mem hT t.property]
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  have h := potentialMultiplier_hasDerivWithinAt (Icc (0 : ℝ) T) t
    (fun r => extendPath T hT m.field r y) (extendPath T hT m₁.field t y)
    (hmt t t.property y) hn
  convert h using 1 <;> try rfl
  · funext r
    exact potentialCoefficient_apply m c hc hm (projIcc 0 T hT r) y
  · rw [potentialTimeCoefficient_apply]
    change potentialMultiplierDerivative (m.field t y) (m₁.field t y) =
      potentialMultiplierDerivative (m.field (projIcc 0 T hT t) y) (m₁.field (projIcc 0 T hT t) y)
    rw [projIcc_of_mem hT t.property]

variable (P : ℝ) [Fact (0 < P)]
  (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hmt hd in
/-- Q_t is constructed from m, m_t, A and A_t; no regularity of Q is assumed. -/
theorem sourcePotentialPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (potentialPath P (potentialCoefficient m c hc hm) p))
      (potentialDerivative P T (potentialCoefficient m c hc hm)
        (potentialTimeCoefficient m m₁ c hc hm) p f t) (Icc (0 : ℝ) T) t := by
  have hcoeff : ∀ r ∈ Icc (0 : ℝ) T, ∀ y : Space,
      HasDerivWithinAt (fun s => extendPath T hT (potentialCoefficient m c hc hm) s y)
        (extendPath T hT (potentialTimeCoefficient m m₁ c hc hm) r y) (Icc (0 : ℝ) T) r := by
    intro r hr y
    have h := potentialCoefficient_hasDerivWithinAt T hT m m₁ c hc hm hmt ⟨r,hr⟩ y
    exact h.congr_deriv (congrArg (fun z : Icc (0 : ℝ) T =>
      potentialTimeCoefficient m m₁ c hc hm z y) (projIcc_of_mem hT hr).symm)
  have h := potentialPath_hasDerivWithinAt P T hT (potentialCoefficient m c hc hm)
    (potentialTimeCoefficient m m₁ c hc hm) p f hcoeff hd t
  exact h

end EulerSourcePotentialCoefficient
