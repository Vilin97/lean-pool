/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedFar
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-!
# Source Morrey Data

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
open CKN.Core.Step3


noncomputable section

namespace CKN.Core.Step4

/-! Product estimates used by the divergence-form sources.  The cutoff
factors are deliberately represented by their finite Morrey norms here; the
smooth compact-support cutoff API supplies those bounds at the point where a
cutoff is chosen. -/

theorem source_product_morrey_bound
    {P P₁ P₂ θ θ₁ θ₂ : ℝ}
    (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂)
    (hrelP : 1 / P = 1 / P₁ + 1 / P₂)
    (hrelθ : 1 / θ = 1 / θ₁ + 1 / θ₂)
    {f g : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (h₁ : morreyNorm P₁ θ₁ f < ∞)
    (h₂ : morreyNorm P₂ θ₂ g < ∞) :
    morreyNorm P θ (fun z => f z * g z) < ∞ ∧
      morreyNorm P θ (fun z => f z * g z) ≤
        morreyNorm P₁ θ₁ f * morreyNorm P₂ θ₂ g := by
  have hbound := morreyNorm_holder hP₁ hP₂ hrelP hrelθ hf hg
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top h₁ h₂), hbound⟩

private theorem heat_integrable_from_morrey
    {F : ParabolicPoint → ℝ} {z : ParabolicPoint}
    {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hP6 : P ≤ 6)
    (hθ2 : 0 < 2 - 5 / θ) (hF : AEMeasurable F volume)
    (hN : morreyNorm P θ F < ∞) (hSupport : HasCompactSupport F) :
    Integrable (fun w => heatPotentialKernel z w * F w) volume := by
  have hsplit := heatPotential_kernel_integrable_on_split
    (F := F) (G := fun _ : Fin 3 => fun _ : ParabolicPoint => (0 : ℝ))
    (z := z) (p := z) (r := (1 : ℝ)) (P := P) (θ₀ := θ) (θ₁ := (6 : ℝ))
    (by norm_num) hP hPθ hP6
    hF (fun _ => aemeasurable_const) hN
    (fun _ => by
      have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
      have hz : morreyNorm P 6 (fun _ : ParabolicPoint => (0 : ℝ)) = 0 := by
        have hzcell : ∀ (z : ParabolicPoint) (r : {r : ℝ // 0 < r}),
            morreyCell P 6 (fun _ : ParabolicPoint => (0 : ℝ)) z r.1 = 0 := by
          intro z r
          unfold morreyCell cylinderPowerIntegral
          have hroot : (∫⁻ w in parabolicCylinder z.1 z.2 r.1,
              ENNReal.ofReal |(0 : ℝ)| ^ P) = 0 := by
            simp only [abs_zero, ENNReal.ofReal_zero]
            rw [ENNReal.zero_rpow_of_pos hPpos]
            simp
          rw [hroot, ENNReal.zero_rpow_of_pos (by positivity : 0 < (1 / P : ℝ))]
          simp
        apply le_antisymm
        · unfold morreyNorm
          refine iSup_le fun z => iSup_le fun r => ?_
          exact (hzcell z r).le
        · exact bot_le
      rw [hz]
      simp)
    hSupport
    (fun _ => HasCompactSupport.zero)
    hθ2 (by norm_num) (by simp)
  have hset := heatPotential_near_far_cover (z := z) (r := (1 : ℝ)) (by norm_num)
  have hOn := hsplit.1
  have hOn' : IntegrableOn (fun w => heatPotentialKernel z w * F w)
      Set.univ volume := by
    rw [hset]
    exact hOn
  simpa only [IntegrableOn, Measure.restrict_univ] using hOn'

private theorem heat_spatial_integrable_from_morrey
    {F : ParabolicPoint → ℝ} {z : ParabolicPoint} {j : Fin 3}
    {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hP6 : P ≤ 6)
    (hθ1 : 0 < 1 - 5 / θ) (hF : AEMeasurable F volume)
    (hN : morreyNorm P θ F < ∞) (hSupport : HasCompactSupport F) :
    Integrable (fun w => heatPotentialSpatialKernel j z w * F w) volume := by
  have hsplit := heatPotential_kernel_integrable_on_split
    (F := fun _ : ParabolicPoint => (0 : ℝ)) (G := fun k =>
      if k = j then F else fun _ : ParabolicPoint => (0 : ℝ))
    (z := z) (p := z) (r := (1 : ℝ)) (P := P) (θ₀ := (6 : ℝ)) (θ₁ := θ)
    (by norm_num) hP hP6 hPθ
    (aemeasurable_const) (by
      intro k
      by_cases hkj : k = j
      · subst k
        simpa using hF
      · simp [hkj]) (by
      have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
      have hz : morreyNorm P 6 (fun _ : ParabolicPoint => (0 : ℝ)) = 0 := by
        have hzcell : ∀ (z : ParabolicPoint) (r : {r : ℝ // 0 < r}),
            morreyCell P 6 (fun _ : ParabolicPoint => (0 : ℝ)) z r.1 = 0 := by
          intro z r
          unfold morreyCell cylinderPowerIntegral
          have hroot : (∫⁻ w in parabolicCylinder z.1 z.2 r.1,
              ENNReal.ofReal |(0 : ℝ)| ^ P) = 0 := by
            simp only [abs_zero, ENNReal.ofReal_zero]
            rw [ENNReal.zero_rpow_of_pos hPpos]
            simp
          rw [hroot, ENNReal.zero_rpow_of_pos (by positivity : 0 < (1 / P : ℝ))]
          simp
        apply le_antisymm
        · unfold morreyNorm
          refine iSup_le fun z => iSup_le fun r => ?_
          exact (hzcell z r).le
        · exact bot_le
      rw [hz]
      simp) (by
      intro k
      by_cases hkj : k = j
      · subst k
        simpa using hN
      · have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
        have hz : morreyNorm P θ (fun _ : ParabolicPoint => (0 : ℝ)) = 0 := by
          have hzcell : ∀ (z : ParabolicPoint) (r : {r : ℝ // 0 < r}),
              morreyCell P θ (fun _ : ParabolicPoint => (0 : ℝ)) z r.1 = 0 := by
            intro z r
            unfold morreyCell cylinderPowerIntegral
            have hroot : (∫⁻ w in parabolicCylinder z.1 z.2 r.1,
                ENNReal.ofReal |(0 : ℝ)| ^ P) = 0 := by
              simp only [abs_zero, ENNReal.ofReal_zero]
              rw [ENNReal.zero_rpow_of_pos hPpos]
              simp
            rw [hroot, ENNReal.zero_rpow_of_pos (by positivity : 0 < (1 / P : ℝ))]
            simp
          apply le_antisymm
          · unfold morreyNorm
            refine iSup_le fun z => iSup_le fun r => ?_
            exact (hzcell z r).le
          · exact bot_le
        simp [hkj, hz]) (by
      exact HasCompactSupport.zero) (by
      intro k
      by_cases hkj : k = j
      · subst k
        simpa using hSupport
      · simp only [hkj, ↓reduceIte]
        exact HasCompactSupport.zero) (by norm_num) hθ1 (by simp)
  have hset := heatPotential_near_far_cover (z := z) (r := (1 : ℝ)) (by norm_num)
  have hOn := hsplit.2 j
  have hOn' : IntegrableOn
      (fun w => heatPotentialSpatialKernel j z w * F w) Set.univ volume := by
    rw [hset]
    simpa using hOn
  simpa only [IntegrableOn, Measure.restrict_univ] using hOn'

/- The two heat-kernel families in the pointwise estimate are therefore
available directly from the source Morrey norms.  The Riesz families are
kept as separate fields in the consumer until the singular-source bridge is
established; this prevents silently replacing that bridge by an L¹ assertion. -/
theorem source_heat_kernel_data_of_morrey
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {P θ₀ θ₁ : ℝ}
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁) (hP6 : P ≤ 6)
    (hδ₀ : 0 < 2 - 5 / θ₀) (hδ₁ : 0 < 1 - 5 / θ₁)
    (hg : ∀ i : Fin 3, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i : Fin 3, AEMeasurable (fun z => h j z i) volume)
    (hNg : ∀ i : Fin 3, morreyNorm P θ₀ (fun z => g z i) < ∞)
    (hNh : ∀ j i : Fin 3, morreyNorm P θ₁ (fun z => h j z i) < ∞)
    (hsg : ∀ i : Fin 3, HasCompactSupport (fun z => g z i))
    (hsh : ∀ j i : Fin 3, HasCompactSupport (fun z => h j z i)) :
    (∀ z i, Integrable (fun w => heatPotentialKernel z w * g w i) volume) ∧
    (∀ z j i, Integrable
      (fun w => heatPotentialSpatialKernel j z w * h j w i) volume) := by
  constructor
  · intro z i
    exact heat_integrable_from_morrey hP hPθ₀ hP6 hδ₀
      (hg i) (hNg i) (hsg i)
  · intro z j i
    exact heat_spatial_integrable_from_morrey hP hPθ₁ hP6 hδ₁ (hh j i)
      (hNh j i) (hsh j i)

end CKN.Core.Step4
