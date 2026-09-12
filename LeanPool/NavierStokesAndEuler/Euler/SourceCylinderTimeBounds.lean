/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForcing
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Same-radius bounds for the actual forward time right side

The coordinate and physical right sides are the literal bounded coefficient
expressions in (12) and its physical reconstruction. They preserve the input
external radius and shift. Scalar time weights commute with these expressions;
in particular no derivative of the positive profile is used.
-/

@[expose] public section


noncomputable section

namespace EulerSourceCylinderTimeBounds

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceCylinderForcing EulerSourceForwardCoefficient EulerTransverseForwardCoefficientGevrey
  EulerOperatorGevreyCalculus EulerGevrey EulerParameterWordGevrey EulerTimeLpGramGevrey
  EulerContinuousTimeWeight
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {K U E ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (S : Set Space) (hS : MeasurableSet S)
  (Q Q₁ : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (f : C(K, Supported P E S hS)) (a : C(K, Supported P U S hS))

/-- Coordinate rhs, given by `supportedMultiplierMap P S hS (sourceGenerator Q Q₁ c hc hQ) a +
projectedForcing P S hS Q c hc hQ f`. -/
def coordinateRhs : C(K,Supported P U S hS) :=
  supportedMultiplierMap P S hS (sourceGenerator Q Q₁ c hc hQ) a +
    projectedForcing P S hS Q c hc hQ f

/-- Physical rhs, given by `supportedMultiplierMap P S hS Q₁.field a + supportedMultiplierMap P
S hS Q.field (coordinateRhs P S hS Q Q₁ c hc hQ f a)`. -/
def physicalRhs : C(K,Supported P E S hS) :=
  supportedMultiplierMap P S hS Q₁.field a +
    supportedMultiplierMap P S hS Q.field (coordinateRhs P S hS Q Q₁ c hc hQ f a)

theorem coordinateRhs_contDiff
    (hf : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS f)))
    (ha : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS a))) :
    ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b
      (includePath P S hS (coordinateRhs P S hS Q Q₁ c hc hQ f a))) := by
  have h₁ := supported_product_orbit_contDiff P (sourceGenerator Q Q₁ c hc hQ)
    (sourceGenerator_translation_contDiff Q Q₁ c hc hQ) S hS a ha
  have h₂ := projectedForcing_contDiff P S hS Q c hc hQ f hf
  simpa only [coordinateRhs,map_add] using h₁.add h₂

theorem physicalRhs_contDiff
    (hf : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS f)))
    (ha : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS a))) :
    ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b
      (includePath P S hS (physicalRhs P S hS Q Q₁ c hc hQ f a))) := by
  have h₁ := supported_product_orbit_contDiff P Q₁.field Q₁.translation_contDiff S hS a ha
  have h₂ := supported_product_orbit_contDiff P Q.field Q.translation_contDiff S hS
    (coordinateRhs P S hS Q Q₁ c hc hQ f a) (coordinateRhs_contDiff P S hS Q Q₁ c hc hQ f a hf ha)
  simpa only [physicalRhs,map_add] using h₁.add h₂

/-- Coordinate cost, given by `3*sobolevCoefficientAmplitude ι q (4*Ri) (18*Ri*C₀*C₁)*Da +
3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*C₀)*Df`. -/
def coordinateCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri C₀ C₁ Df Da : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) (18*Ri*C₀*C₁)*Da +
    3*sobolevCoefficientAmplitude ι q (4*Ri) (3*Ri*C₀)*Df

/-- Physical cost, given by `3*sobolevCoefficientAmplitude ι q (4*Ri) C₁*Da +
3*sobolevCoefficientAmplitude ι q (4*Ri) C₀*coordinateCost ι q Ri C₀ C₁ Df Da`. -/
def physicalCost (ι : Type*) [Fintype ι] (q : ℕ) (Ri C₀ C₁ Df Da : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q (4*Ri) C₁*Da +
    3*sobolevCoefficientAmplitude ι q (4*Ri) C₀*coordinateCost ι q Ri C₀ C₁ Df Da

theorem coordinateRhs_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hf : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS f)))
    (ha : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS a)))
    (Rc C₀ C₁ Ri R Df Da : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hDf : 0 ≤ Df) (hDa : 0 ≤ Da) (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
    (hR : sobolevCoefficientRadius ι (4*Ri) ≤ R)
    (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀*majorant Rc 0 n)
    (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁*majorant Rc 0 n)
    (d : ℕ)
    (hbf : ∀ n, block directions q (fun b : LiftTangent => pathTranslate P b (includePath P S hS
        f)) n 0 ≤ Df*majorant R d n)
    (hba : ∀ n, block directions q (fun b : LiftTangent => pathTranslate P b (includePath P S hS
        a)) n 0 ≤ Da*majorant R d n)
    (n : ℕ) :
    block directions q (fun b : LiftTangent => pathTranslate P b
      (includePath P S hS (coordinateRhs P S hS Q Q₁ c hc hQ f a))) n 0 ≤
      coordinateCost ι q Ri C₀ C₁ Df Da*majorant R d n := by
  obtain ⟨hi,-⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  let B := sourceGenerator Q Q₁ c hc hQ
  have hB := sourceGenerator_translation_contDiff Q Q₁ c hc hQ
  have hbB := sourceGenerator_translation_bound Q Q₁ c hc hQ Rc C₀ C₁ Ri hRc hC₀ hC₁ hRi hbQ hbQ₁
  have hfirst := product_orbit_block_bound P B hB directions hd q (includePath P S hS a) ha
    (4*Ri) (18*Ri*C₀*C₁) R Da (by positivity) (by positivity) hDa hR hbB d hba n
  have hsecond := projectedForcing_block_bound P S hS Q c hc hQ directions hd q f hf
    Rc C₀ Ri R Df hRc hC₀ hDf hRi hR hbQ d hbf n
  have hsum := block_add_le directions q
    (fun b : LiftTangent => pathTranslate P b (includePath P S hS
      (supportedMultiplierMap P S hS B a)))
    (fun b : LiftTangent => pathTranslate P b (includePath P S hS
      (projectedForcing P S hS Q c hc hQ f)))
    (supported_product_orbit_contDiff P B hB S hS a ha)
    (projectedForcing_contDiff P S hS Q c hc hQ f hf) n 0
  have hbound := hsum.trans (add_le_add hfirst hsecond)
  simpa only [coordinateRhs,coordinateCost,B,map_add,Pi.add_def,add_mul] using hbound

theorem physicalRhs_block_bound
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hf : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS f)))
    (ha : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (includePath P S hS a)))
    (Rc C₀ C₁ Ri R Df Da : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hDf : 0 ≤ Df) (hDa : 0 ≤ Da) (hRi : 2*gramCost c C₀ 1*(Rc+1) ≤ Ri)
    (hR : sobolevCoefficientRadius ι (4*Ri) ≤ R)
    (hbQ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q.field t : Space → U →L[ℝ] E) x‖ ≤ C₀*majorant Rc 0 n)
    (hbQ₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (Q₁.field t : Space → U →L[ℝ] E) x‖ ≤ C₁*majorant Rc 0 n)
    (d : ℕ)
    (hbf : ∀ n, block directions q (fun b : LiftTangent => pathTranslate P b (includePath P S hS
        f)) n 0 ≤ Df*majorant R d n)
    (hba : ∀ n, block directions q (fun b : LiftTangent => pathTranslate P b (includePath P S hS
        a)) n 0 ≤ Da*majorant R d n)
    (n : ℕ) :
    block directions q (fun b : LiftTangent => pathTranslate P b
      (includePath P S hS (physicalRhs P S hS Q Q₁ c hc hQ f a))) n 0 ≤
      physicalCost ι q Ri C₀ C₁ Df Da*majorant R d n := by
  obtain ⟨hi,hbase⟩ := inverseRadius_bounds c C₀ Rc Ri hc hRc hRi
  have hq (j : ℕ) (b : Space) :
      ‖iteratedFDeriv ℝ j (translateCoefficientPath Q.field) b‖ ≤ C₀*majorant (4*Ri) 0 j :=
    (Q.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0 j)) (hbQ j)
        b).trans
      (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₀)
  have hq₁ (j : ℕ) (b : Space) :
      ‖iteratedFDeriv ℝ j (translateCoefficientPath Q₁.field) b‖ ≤ C₁*majorant (4*Ri) 0 j :=
    (Q₁.norm_iteratedFDeriv_translation_le j _ (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0 j)) (hbQ₁
        j) b).trans
      (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc (4*Ri) hRc hbase 0 j) hC₁)
  have hcost : 0 ≤ coordinateCost ι q Ri C₀ C₁ Df Da := by
    unfold coordinateCost
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num)
        (sobolevCoefficientAmplitude_nonneg q (4*Ri) (18*Ri*C₀*C₁) (by
            positivity) (by positivity))) hDa)
      (mul_nonneg (mul_nonneg (by norm_num)
        (sobolevCoefficientAmplitude_nonneg q (4*Ri) (3*Ri*C₀) (by
            positivity) (by positivity))) hDf)
  have hcoord := coordinateRhs_contDiff P S hS Q Q₁ c hc hQ f a hf ha
  have hbcoord := coordinateRhs_block_bound P S hS Q Q₁ c hc hQ f a directions hd q hf ha
    Rc C₀ C₁ Ri R Df Da hRc hC₀ hC₁ hDf hDa hRi hR hbQ hbQ₁ d hbf hba
  have hfirst := product_orbit_block_bound P Q₁.field Q₁.translation_contDiff directions hd q
    (includePath P S hS a) ha (4*Ri) C₁ R Da (by positivity) hC₁ hDa hR hq₁ d hba n
  have hsecond := product_orbit_block_bound P Q.field Q.translation_contDiff directions hd q
    (includePath P S hS (coordinateRhs P S hS Q Q₁ c hc hQ f a)) hcoord
    (4*Ri) C₀ R (coordinateCost ι q Ri C₀ C₁ Df Da) (by positivity) hC₀ hcost hR hq d hbcoord n
  have hsum := block_add_le directions q
    (fun b : LiftTangent => pathTranslate P b (includePath P S hS (supportedMultiplierMap P S hS
        Q₁.field a)))
    (fun b : LiftTangent => pathTranslate P b (includePath P S hS
      (supportedMultiplierMap P S hS Q.field (coordinateRhs P S hS Q Q₁ c hc hQ f a))))
    (supported_product_orbit_contDiff P Q₁.field Q₁.translation_contDiff S hS a ha)
    (supported_product_orbit_contDiff P Q.field Q.translation_contDiff S hS _ hcoord) n 0
  have hbound := hsum.trans (add_le_add hfirst hsecond)
  simpa only [physicalRhs,physicalCost,map_add,Pi.add_def,add_mul] using hbound

theorem coordinateRhs_weight (g : C(K, ℝ)) :
    coordinateRhs P S hS Q Q₁ c hc hQ (weight g f) (weight g a) =
      weight g (coordinateRhs P S hS Q Q₁ c hc hQ f a) := by
  simp only [coordinateRhs,projectedForcing,supportedMultiplier_weight,map_add]

theorem physicalRhs_weight (g : C(K, ℝ)) :
    physicalRhs P S hS Q Q₁ c hc hQ (weight g f) (weight g a) =
      weight g (physicalRhs P S hS Q Q₁ c hc hQ f a) := by
  simp only [physicalRhs,coordinateRhs_weight,supportedMultiplier_weight,map_add]

end EulerSourceCylinderTimeBounds
