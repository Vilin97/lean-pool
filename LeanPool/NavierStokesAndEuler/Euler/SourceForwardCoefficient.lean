/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldForwardGenerator

@[expose] public section

/-!
# Actual source forward coefficient and its translated factorial bounds

The input consists of the source frame fields and their genuine uniform jets.
The generator itself is constructed by the bounded-field Gram inverse. Its
spatial translation family is identified pointwise and estimated in the actual
uniform time-space norm.
-/

noncomputable section

namespace EulerSourceForwardCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerBoundedFieldForwardGenerator
  EulerTransverseGramInverse EulerGevrey EulerTimeLpGramGevrey
open scoped BoundedContinuousFunction ContDiff

variable {K U E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (Q Q₁ : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c*‖v‖^2 ≤ ‖Q.field t x v‖^2)

private local instance : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (U →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ U →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ U →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ E →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ E →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ U →L[ℝ] U) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ U →L[ℝ] U) := inferInstance
private local instance : NormedAddCommGroup (C(K,Space →ᵇ U →L[ℝ] E)) := inferInstance
private local instance : NormedSpace ℝ (C(K,Space →ᵇ U →L[ℝ] E)) := inferInstance
private local instance : NormedAddCommGroup (C(K,Space →ᵇ E →L[ℝ] U)) := inferInstance
private local instance : NormedSpace ℝ (C(K,Space →ᵇ E →L[ℝ] U)) := inferInstance
private local instance : NormedAddCommGroup (C(K,Space →ᵇ U →L[ℝ] U)) := inferInstance
private local instance : NormedSpace ℝ (C(K,Space →ᵇ U →L[ℝ] U)) := inferInstance

/-- The actual bounded continuous source generator. -/
def sourceGenerator : C(K,Space →ᵇ U →L[ℝ] U) := generatorPath c hc Q.field Q₁.field hQ

/-- The actual bounded continuous projected-forcing coefficient. -/
def sourceForcing : C(K,Space →ᵇ E →L[ℝ] U) := leftInversePath c hc Q.field hQ

include hQ in
omit [CompleteSpace U] [CompleteSpace E] in
/-- Source lower bounds hold at every translated label. -/
theorem translated_lower (a : Space) (t : K) (x : Space) (v : U) :
    c*‖v‖^2 ≤ ‖translateCoefficientPath Q.field a t x v‖^2 := hQ t (x+a) v

/-- This is an equality of actual fields, not a chosen translated inverse. -/
theorem sourceGenerator_translated (a : Space) :
    generatorPath c hc (translateCoefficientPath Q.field a) (translateCoefficientPath Q₁.field a)
      (translated_lower Q c hQ a) = translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ) a := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem sourceForcing_translated (a : Space) :
    leftInversePath c hc (translateCoefficientPath Q.field a) (translated_lower Q c hQ a) =
      translateCoefficientPath (sourceForcing Q c hc hQ) a := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

/-- The actual generator's translated family is genuinely smooth in the uniform time-space norm. -/
theorem sourceGenerator_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ)) := by
  have he : translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ) =
      fun a => generatorPath c hc (translateCoefficientPath Q.field a) (translateCoefficientPath
        Q₁.field a)
        (translated_lower Q c hQ a) := funext (fun a => (sourceGenerator_translated Q Q₁ c hc hQ
          a).symm)
  rw [he]
  exact generatorPath_contDiff c hc (translateCoefficientPath Q.field) (translateCoefficientPath
    Q₁.field)
    (translated_lower Q c hQ) Q.translation_contDiff Q₁.translation_contDiff

theorem sourceForcing_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (sourceForcing Q c hc hQ)) := by
  have he : translateCoefficientPath (sourceForcing Q c hc hQ) =
      fun a => leftInversePath c hc (translateCoefficientPath Q.field a) (translated_lower Q c hQ
        a) :=
    funext (fun a => (sourceForcing_translated Q c hc hQ a).symm)
  rw [he]
  exact leftInversePath_contDiff c hc (translateCoefficientPath Q.field) (translated_lower Q c hQ)
    Q.translation_contDiff

variable (Rc C₀ C₁ Ri : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
  (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀*majorant Rc 0 n)
  (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁*majorant Rc 0 n)

include hRc hC₀ hC₁ hRi hbQ hbQ₁ in
/-- The constructed source generator has a polynomial shift-zero coefficient bound. -/
theorem sourceGenerator_translation_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ)) a‖ ≤
      (18*Ri*C₀*C₁)*majorant (4*Ri) 0 n := by
  have he : translateCoefficientPath (sourceGenerator Q Q₁ c hc hQ) =
      fun a => generatorPath c hc (translateCoefficientPath Q.field a) (translateCoefficientPath
        Q₁.field a)
        (translated_lower Q c hQ a) := funext (fun a => (sourceGenerator_translated Q Q₁ c hc hQ
          a).symm)
  rw [he]
  exact generatorPath_bound (translateCoefficientPath Q.field) (translateCoefficientPath Q₁.field)
    c hc (translated_lower Q c hQ) Q.translation_contDiff Q₁.translation_contDiff
    Rc C₀ C₁ Ri hRc hC₀ hC₁ hRi
    (fun j x => Q.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0
      j)) (hbQ j) x)
    (fun j x => Q₁.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0
      j)) (hbQ₁ j) x) n a

include hRc hC₀ hRi hbQ in
/-- The actual projected-forcing coefficient has the corresponding polynomial bound. -/
theorem sourceForcing_translation_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (sourceForcing Q c hc hQ)) a‖ ≤
      (3*Ri*C₀)*majorant (4*Ri) 0 n := by
  have he : translateCoefficientPath (sourceForcing Q c hc hQ) =
      fun a => leftInversePath c hc (translateCoefficientPath Q.field a) (translated_lower Q c hQ
        a) :=
    funext (fun a => (sourceForcing_translated Q c hc hQ a).symm)
  rw [he]
  exact leftInversePath_bound (translateCoefficientPath Q.field) c hc (translated_lower Q c hQ)
    Q.translation_contDiff Rc C₀ Ri hRc hC₀ hRi
    (fun j x => Q.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0
      j)) (hbQ j) x) n a

end EulerSourceForwardCoefficient
