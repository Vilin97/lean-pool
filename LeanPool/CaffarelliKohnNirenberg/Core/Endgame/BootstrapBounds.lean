/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Bootstrap
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.MorreyScaling
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents

/-! # Numerical bounds for the first Morrey improvement

The constants in Adams' estimate and in lowering the integrability exponent
are retained. This gives a bound determined by the source bounds, not by a
new existential constant chosen after the solution.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

noncomputable section
namespace CKN.Core.Endgame

/-- The order-two Adams coefficient after lowering integrability to three. -/
def bootstrapOrderTwoCoefficient : ℝ≥0∞ :=
  volume (parabolicCylinder 0 0 1) ^ (1 / 3 - 5 / 66 : ℝ) *
    parabolicAdamsPotentialConstant 2 (6 / 5) (25 / 11)

/-- The order-one Adams coefficient after lowering integrability to three. -/
def bootstrapOrderOneCoefficient : ℝ≥0∞ :=
  volume (parabolicCylinder 0 0 1) ^ (1 / 3 - 1 / 18 : ℝ) *
    parabolicAdamsPotentialConstant 1 3 (25 / 6)

/-- The numerical velocity bound determined by the two source bounds. -/
def bootstrapSourceMorreyBound (KF KG : ℝ≥0∞) : ℝ≥0∞ :=
  3000 * (bootstrapOrderTwoCoefficient * KF) +
    900000 * (bootstrapOrderOneCoefficient * KG +
      (bootstrapOrderOneCoefficient * KG + bootstrapOrderOneCoefficient * KG))

/-- Both coefficients and hence the resulting bound are finite. -/
theorem bootstrapSourceMorreyBound_lt_top {KF KG : ℝ≥0∞}
    (hKF : KF < ⊤) (hKG : KG < ⊤) : bootstrapSourceMorreyBound KF KG < ⊤ := by
  have h₂ : bootstrapOrderTwoCoefficient < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne)
    (adams_potential_constant_lt_top (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  have h₁ : bootstrapOrderOneCoefficient < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne)
    (adams_potential_constant_lt_top (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  unfold bootstrapSourceMorreyBound
  have hF := ENNReal.mul_lt_top h₂ hKF
  have hG := ENNReal.mul_lt_top h₁ hKG
  finiteness

private theorem order_two_bound {F : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hF : AEMeasurable F volume) (hN : morreyNorm (6 / 5) (25 / 11) F ≤ K) :
    morreyNorm 3 25 (fun z => (parabolicRieszPotential 2 F z).toReal) ≤
      bootstrapOrderTwoCoefficient * K := by
  have hA := riesz_adams_of_aemeasurable (P := 6 / 5) (τ := 25 / 11) (β := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF
  have hA' : morreyNorm (66 / 5) 25
      (fun z => (parabolicRieszPotential 2 F z).toReal) ≤
      parabolicAdamsPotentialConstant 2 (6 / 5) (25 / 11) * K := by
    convert hA.trans (mul_le_mul_of_nonneg_left hN (by positivity)) using 1
    norm_num
  have hlow := morreyNorm_lower_integrability (p' := 3) (p := 66 / 5) (q := 25)
    (by norm_num) (by norm_num) (by norm_num)
    (measurable_riesz_potential_of_aemeasurable 2 hF).ennreal_toReal.aemeasurable
  have hbound := hlow.trans (mul_le_mul_of_nonneg_left hA' (by positivity))
  simpa only [bootstrapOrderTwoCoefficient, mul_assoc,
    show (1 / (66 / 5) : ℝ) = 5 / 66 by norm_num] using hbound

private theorem order_one_bound {F : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hF : AEMeasurable F volume) (hN : morreyNorm 3 (25 / 6) F ≤ K) :
    morreyNorm 3 25 (fun z => (parabolicRieszPotential 1 F z).toReal) ≤
      bootstrapOrderOneCoefficient * K := by
  have hA := riesz_adams_of_aemeasurable (P := 3) (τ := 25 / 6) (β := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF
  have hA' : morreyNorm 18 25
      (fun z => (parabolicRieszPotential 1 F z).toReal) ≤
      parabolicAdamsPotentialConstant 1 3 (25 / 6) * K := by
    convert hA.trans (mul_le_mul_of_nonneg_left hN (by positivity)) using 1
    norm_num
  have hlow := morreyNorm_lower_integrability (p' := 3) (p := 18) (q := 25)
    (by norm_num) (by norm_num) (by norm_num)
    (measurable_riesz_potential_of_aemeasurable 1 hF).ennreal_toReal.aemeasurable
  have hbound := hlow.trans (mul_le_mul_of_nonneg_left hA' (by positivity))
  simpa only [bootstrapOrderOneCoefficient, mul_assoc] using hbound

/-- The potential majorant retains an explicit bound from the source bounds. -/
theorem potential_majorant_morrey_le (KF KG : ℝ≥0∞)
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    (hg : ∀ i, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i, AEMeasurable (fun z => h j z i) volume)
    (hNF : morreyNorm (6 / 5) (25 / 11) (fun z => vec3EuclideanNorm (g z)) ≤ KF)
    (hNG : ∀ j, morreyNorm 3 (25 / 6) (fun z => vec3EuclideanNorm (h j z)) ≤ KG) :
    morreyNorm 3 25 (pointwisePotentialMajorant g h) ≤ bootstrapSourceMorreyBound KF KG := by
  let P₂ := fun z => (parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z).toReal
  let P₁ := fun j z => (parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z).toReal
  have hgN := aemeasurable_euclidean_norm_of_components hg
  have hhN := fun j => aemeasurable_euclidean_norm_of_components (hh j)
  have hM₂ : AEMeasurable P₂ volume :=
    (measurable_riesz_potential_of_aemeasurable 2 hgN).ennreal_toReal.aemeasurable
  have hM₁ : ∀ j, AEMeasurable (P₁ j) volume := fun j =>
    (measurable_riesz_potential_of_aemeasurable 1 (hhN j)).ennreal_toReal.aemeasurable
  have hP₂ := order_two_bound hgN hNF
  have hP₁ := fun j => order_one_bound (hhN j) (hNG j)
  have hsum12 := (routeA_morreyNorm_add_le (hM₁ 1) (hM₁ 2)).trans
    (add_le_add (hP₁ 1) (hP₁ 2))
  have hsum := (routeA_morreyNorm_add_le (hM₁ 0) ((hM₁ 1).add (hM₁ 2))).trans
    (add_le_add (hP₁ 0) hsum12)
  have hs₂ := (morreyNorm_const_mul_le (τ := 25) (by norm_num : (0 : ℝ) < 3) 3000 P₂).trans
    (mul_le_mul_of_nonneg_left hP₂ (by positivity))
  have hs₁ := (morreyNorm_const_mul_le (τ := 25) (by norm_num : (0 : ℝ) < 3) 900000
    (fun z => P₁ 0 z + (P₁ 1 z + P₁ 2 z))).trans
      (mul_le_mul_of_nonneg_left hsum (by positivity))
  have htotal := (routeA_morreyNorm_add_le (hM₂.const_mul (3000 : ℝ))
    (((hM₁ 0).add ((hM₁ 1).add (hM₁ 2))).const_mul (900000 : ℝ))).trans
      (add_le_add hs₂ hs₁)
  change morreyNorm 3 25 (fun z => 3000 * P₂ z + 900000 * ∑ j, P₁ j z) ≤ _
  simpa [bootstrapSourceMorreyBound, Fin.sum_univ_succ] using htotal

/-- The first Morrey improvement has a source-uniform numerical bound.
Actual kernel finiteness is derived before applying the real majorant. -/
theorem bootstrap_morrey_le_of_sources (KF KG : ℝ≥0∞) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hg : ∀ i, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i, AEMeasurable (fun z => h j z i) volume)
    (hNF : morreyNorm (6 / 5) (25 / 11) (fun z => vec3EuclideanNorm (g z)) ≤ KF)
    (hNG : ∀ j, morreyNorm 3 (25 / 6) (fun z => vec3EuclideanNorm (h j z)) ≤ KG)
    (hgsupp : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, g z = 0)
    (hhsupp : ∀ j z, z ∉ parabolicCylinder z₀.1 z₀.2 R → h j z = 0)
    (hrep : v =ᵐ[volume] duhamelPotential g h) :
    morreyNorm 3 25 (fun z => vec3EuclideanNorm (v z)) ≤ bootstrapSourceMorreyBound KF KG := by
  have hpoint := pointwisePotentialBound_ae_of_bootstrap_sources hR hg hh
    (aemeasurable_euclidean_norm_of_components hg)
    (fun j => aemeasurable_euclidean_norm_of_components (hh j))
    (hNF.trans_lt hKF) (fun j => (hNG j).trans_lt hKG) hgsupp hhsupp hrep
  apply le_trans _ (potential_majorant_morrey_le KF KG hg hh hNF hNG)
  apply routeA_morreyNorm_mono_ae (by norm_num)
  filter_upwards [hpoint] with z hz
  have hnonneg : 0 ≤ pointwisePotentialMajorant g h z := by
    unfold pointwisePotentialMajorant
    positivity
  simpa only [abs_of_nonneg (vec3EuclideanNorm_nonneg _), abs_of_nonneg hnonneg] using hz

/-- Componentwise source bounds supply the numerical bootstrap bound with
the explicit three-coordinate aggregation factor. -/
theorem bootstrap_morrey_le_of_component_sources
    (KF KG : ℝ≥0∞) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hg : ∀ i, AEMeasurable (fun z => g z i) volume)
    (hh : ∀ j i, AEMeasurable (fun z => h j z i) volume)
    (hNF : ∀ i, morreyNorm (6 / 5) (25 / 11) (fun z => g z i) ≤ KF)
    (hNG : ∀ j i, morreyNorm 3 (25 / 6) (fun z => h j z i) ≤ KG)
    (hgsupp : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, g z = 0)
    (hhsupp : ∀ j z, z ∉ parabolicCylinder z₀.1 z₀.2 R → h j z = 0)
    (hrep : v =ᵐ[volume] duhamelPotential g h) :
    morreyNorm 3 25 (fun z => vec3EuclideanNorm (v z)) ≤
      bootstrapSourceMorreyBound (3 * KF) (3 * KG) := by
  have hgN : morreyNorm (6 / 5) (25 / 11) (fun z => vec3EuclideanNorm (g z)) ≤ 3 * KF := by
    have hbound := (morrey_norm_euclidean_le_sum_components
      (P := 6 / 5) (τ := 25 / 11) (by norm_num) hg).trans
      (Finset.sum_le_sum (fun i _ => hNF i))
    simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hbound
  have hhN : ∀ j, morreyNorm 3 (25 / 6) (fun z => vec3EuclideanNorm (h j z)) ≤ 3 * KG := by
    intro j
    have hbound := (morrey_norm_euclidean_le_sum_components
      (P := 3) (τ := 25 / 6) (by norm_num) (hh j)).trans
      (Finset.sum_le_sum (fun i _ => hNG j i))
    simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using hbound
  exact bootstrap_morrey_le_of_sources (3 * KF) (3 * KG)
    (ENNReal.mul_lt_top (by norm_num) hKF) (ENNReal.mul_lt_top (by norm_num) hKG)
    hR hg hh hgN hhN hgsupp hhsupp hrep

end CKN.Core.Endgame
