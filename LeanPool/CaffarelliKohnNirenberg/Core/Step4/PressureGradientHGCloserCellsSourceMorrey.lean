/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSourceTensorDef
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.MorreyScaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-! # Morrey membership of the force-free centred tensor source

The convection term uses the product exponents `2` and `3`. The cutoff
term uses two velocity factors. Bounded cutoff coefficients and the
bounded source carrier preserve finiteness at the target exponent.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- An almost-everywhere bounded scalar multiplier preserves finite Morrey
seminorm. -/
theorem pressure_source_bounded_multiplier_morrey_lt_top
    {P κ C : ℝ} (hP : 0 < P) {a g : ParabolicPoint → ℝ}
    (ha : ∀ᵐ z ∂volume, |a z| ≤ |C|) (hg : morreyNorm P κ g < ⊤) :
    morreyNorm P κ (fun z => a z * g z) < ⊤ := by
  have hdom : morreyNorm P κ (fun z => a z * g z) ≤
      morreyNorm P κ (fun z => C * g z) := by
    apply routeA_morreyNorm_mono_ae hP.le
    filter_upwards [ha] with z hz
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  exact (hdom.trans (morreyNorm_const_mul_le hP C g)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg)

/-- Lowering the integrability exponent preserves finite Morrey seminorm. -/
theorem pressure_source_lower_integrability_morrey_lt_top
    {P P₀ κ : ℝ} (hP : 1 ≤ P) (hPP₀ : P ≤ P₀) (hP₀κ : P₀ ≤ κ)
    {g : ParabolicPoint → ℝ} (hg : AEMeasurable g volume)
    (hN : morreyNorm P₀ κ g < ⊤) : morreyNorm P κ g < ⊤ := by
  have hexp : 0 ≤ 1 / P - 1 / P₀ := sub_nonneg.mpr
    (one_div_le_one_div_of_le (zero_lt_one.trans_le hP) hPP₀)
  apply (morreyNorm_lower_p hP hPP₀ hP₀κ hg).trans_lt
  apply ENNReal.mul_lt_top _ hN
  apply ENNReal.rpow_lt_top_of_nonneg hexp
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_ne_top (Integration.volume_vec3Ball_lt_top).ne ENNReal.ofReal_ne_top

/-- Lowering the Morrey exponent on a bounded carrier preserves finiteness. -/
theorem pressure_source_lower_exponent_morrey_lt_top
    {P κ κ₀ R : ℝ} (hP : 1 ≤ P) (hPκ : P ≤ κ) (hκκ₀ : κ ≤ κ₀)
    {g : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} (hR : 0 < R)
    (hsupport : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, g z = 0)
    (hN : morreyNorm P κ₀ g < ⊤) : morreyNorm P κ g < ⊤ := by
  apply (morreyNorm_lower_morrey_exponent hP (hPκ.trans hκκ₀) hPκ hκκ₀ hR hsupport).trans_lt
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top)) hN

/-- The centred force-free source is in the target Morrey class from the
velocity, centred velocity, and weak-gradient Morrey data. -/
theorem pressure_centred_tensor_source_morrey_lt_top
    {τ κ R Cη Cdη : ℝ} (hτ : 25 / 3 ≤ τ)
    (hκ : 6 / 5 ≤ κ) (hκhi : κ ≤ 25 / 9)
    (hκτ : κ ≤ (1 / τ + 8 / 25)⁻¹)
    {S : Set ParabolicPoint} {z₀ : ParabolicPoint} (hR : 0 < R)
    (hS : S ⊆ parabolicCylinder z₀.1 z₀.2 R)
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    (hη : AEMeasurable (fun z : ParabolicPoint => η z.1) volume)
    (hdη : ∀ j, AEMeasurable (fun z : ParabolicPoint => dη j z.1) volume)
    (hηbound : ∀ x, |η x| ≤ |Cη|) (hdηbound : ∀ j x, |dη j x| ≤ |Cdη|)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {c : ℝ → Vec3}
    (hUa : ∀ j, AEMeasurable (S.indicator (fun z => u z j)) volume)
    (hWa : ∀ j, AEMeasurable (S.indicator (fun z => u z j - c z.2 j)) volume)
    (hDa : ∀ i j, AEMeasurable (S.indicator (fun z => Du z i j)) volume)
    (hU : ∀ j, morreyNorm 3 τ (S.indicator (fun z => u z j)) < ⊤)
    (hW : ∀ j, morreyNorm 3 τ (S.indicator (fun z => u z j - c z.2 j)) < ⊤)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ) (S.indicator (fun z => Du z i j)) < ⊤)
    (i : Fin 3) :
    morreyNorm (6 / 5 : ℝ) κ
      (S.indicator (fun z => sourceMorreyCutoffVCentredTensorSpacetime η dη u Du c z i)) < ⊤ := by
  let U : Fin 3 → ParabolicPoint → ℝ := fun j => S.indicator (fun z => u z j)
  let W : Fin 3 → ParabolicPoint → ℝ := fun j => S.indicator (fun z => u z j - c z.2 j)
  let D : Fin 3 → ParabolicPoint → ℝ := fun j => S.indicator (fun z => Du z i j)
  have hDuW : ∀ j, morreyNorm (6 / 5 : ℝ) κ (fun z => D j z * W j z) < ⊤ := by
    intro j
    have hprod := morreyNorm_mul_le (p := (6 / 5 : ℝ))
      (p₁ := 2) (p₂ := 3) (q := (1 / τ + 8 / 25)⁻¹) (q₁ := 25 / 8) (q₂ := τ)
      (by norm_num) (by norm_num) (by norm_num) (by simp only [one_div, inv_inv]; ring) (hDa i j)
        (hWa j)
    apply pressure_source_lower_exponent_morrey_lt_top (by norm_num) hκ hκτ hR
    · intro z hz
      have hzS : z ∉ S := fun h => hz (hS h)
      simp [D, hzS]
    · exact hprod.trans_lt (ENNReal.mul_lt_top (hD i j) (hW j))
  have hUW : ∀ j, morreyNorm (6 / 5 : ℝ) κ (fun z => U i z * W j z) < ⊤ := by
    intro j
    have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
    have hprod := morreyNorm_mul_le (p := (3 / 2 : ℝ))
      (p₁ := 3) (p₂ := 3) (q := τ / 2) (q₁ := τ) (q₂ := τ)
      (by norm_num) (by norm_num) (by norm_num) (by field_simp; ring) (hUa i) (hWa j)
    have hlower := pressure_source_lower_integrability_morrey_lt_top
      (P := (6 / 5 : ℝ)) (by norm_num) (by norm_num : (6 / 5 : ℝ) ≤ 3 / 2)
      (show (3 / 2 : ℝ) ≤ τ / 2 by linarith only [hτ]) ((hUa i).mul (hWa j))
      (hprod.trans_lt (ENNReal.mul_lt_top (hU i) (hW j)))
    apply pressure_source_lower_exponent_morrey_lt_top (by norm_num) hκ
      (show κ ≤ τ / 2 by linarith only [hκhi, hτ]) hR
    · intro z hz
      have hzS : z ∉ S := fun h => hz (hS h)
      simp [U, hzS]
    · exact hlower
  let A : Fin 3 → ParabolicPoint → ℝ := fun j z =>
    η z.1 * (D j z * W j z) + dη j z.1 * (U i z * W j z)
  have hAa : ∀ j, AEMeasurable (A j) volume := fun j =>
    (hη.mul ((hDa i j).mul (hWa j))).add ((hdη j).mul ((hUa i).mul (hWa j)))
  have hAN : ∀ j, morreyNorm (6 / 5 : ℝ) κ (A j) < ⊤ := by
    intro j
    apply (morrey_norm_add_le (by norm_num)
      (hη.mul ((hDa i j).mul (hWa j))) ((hdη j).mul ((hUa i).mul (hWa j)))).trans_lt
    exact ENNReal.add_lt_top.mpr
      ⟨pressure_source_bounded_multiplier_morrey_lt_top (by norm_num)
        (Eventually.of_forall (fun z => hηbound z.1)) (hDuW j),
       pressure_source_bounded_multiplier_morrey_lt_top (by norm_num)
        (Eventually.of_forall (fun z => hdηbound j z.1)) (hUW j)⟩
  have hsum : morreyNorm (6 / 5 : ℝ) κ (fun z => ∑ j, A j z) < ⊤ := by
    have h12 := (morrey_norm_add_le (by norm_num) (hAa 1) (hAa 2)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hAN 1, hAN 2⟩)
    have h012 := (morrey_norm_add_le (by norm_num) (hAa 0) ((hAa 1).add (hAa 2))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hAN 0, h12⟩)
    simpa [Fin.sum_univ_succ] using h012
  have heq : S.indicator (fun z => sourceMorreyCutoffVCentredTensorSpacetime η dη u Du c z i) =
      fun z => ∑ j, A j z := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz, sourceMorreyCutoffVCentredTensorSpacetime,
        sourceMorreyCutoffVCentredTensor, pressureDivergenceCutoffSourceCentredTensor, A, D, U, W]
      apply Finset.sum_congr rfl
      intro j _
      change η z.1 * Du z i j * (u z j - c z.2 j) +
        dη j z.1 * u z i * (u z j - c z.2 j) =
        η z.1 * (Du z i j * (u z j - c z.2 j)) +
          dη j z.1 * (u z i * (u z j - c z.2 j))
      ring
    · simp [hz, A, D, U, W]
  rw [heq]
  exact hsum

end CKN.Core.Step4
