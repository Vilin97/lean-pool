/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSourceBounds

/-!
# Pressure Gradient Source Morrey

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

private theorem morrey_norm_neg {P τ : ℝ} (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun z => -f z) = morreyNorm P τ f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

private theorem morrey_norm_sub_le {P τ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    morreyNorm P τ (fun z => f z - g z) ≤
      morreyNorm P τ f + morreyNorm P τ g := by
  have h := CKN.Core.Endgame.morrey_norm_add_le (τ := τ) hP hf hg.neg
  change morreyNorm P τ (fun z => f z + -g z) ≤
    morreyNorm P τ f + morreyNorm P τ (fun z => -g z) at h
  rw [morrey_norm_neg] at h
  simpa only [sub_eq_add_neg] using h


/-! The source estimate on a spacetime carrier.  The two product exponents
combine to `(1 / τ + 8 / 25)⁻¹`; the force is lowered from its q-Morrey
exponent only after the common target exponent has been selected. -/

private theorem source_morrey_base_ge
    {τ : ℝ} (hτ : 25 / 3 ≤ τ) :
    6 / 5 ≤ (1 / τ + 8 / 25)⁻¹ := by
  have hτpos : 0 < τ := by linarith only [hτ]
  have hsum : 0 < 1 / τ + 8 / 25 := by positivity
  have hinv : 1 / τ ≤ 3 / 25 := by
    have htmp := one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 25 / 3) hτ
    norm_num at htmp
    simpa only [one_div] using htmp
  have hsumle : 1 / τ + 8 / 25 ≤ 5 / 6 := by
    linarith only [hinv]
  have hrecip := (one_div_le_one_div
    (by norm_num : (0 : ℝ) < 5 / 6) hsum).mpr hsumle
  norm_num at hrecip
  simpa only [one_div] using hrecip

private theorem source_morrey_product_le
    {S : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {i j : Fin 3}
    {KU KD : ℝ≥0∞} {τr κr R : ℝ}
    {z₀ : ParabolicPoint}
    (hτ : 25 / 3 ≤ τr) (hκ : 6 / 5 ≤ κr)
    (hκτ : κr ≤ (1 / τr + 8 / 25)⁻¹)
    (hR : 0 < R) (hRle : R ≤ 1)
    (hSsupport : S ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hU : morreyNorm 3 τr (S.indicator (fun z => u z j)) ≤ KU)
    (hD : morreyNorm 2 (25 / 8 : ℝ)
      (S.indicator (fun z => Du z i j)) ≤ KD)
    (hUmeas : AEMeasurable (S.indicator (fun z => u z j)) volume)
    (hDmeas : AEMeasurable (S.indicator (fun z => Du z i j)) volume) :
    morreyNorm (6 / 5 : ℝ) κr
      (fun z => S.indicator (fun v => Du v i j) z *
        S.indicator (fun v => u v j) z) ≤ KU * KD := by
  have hbase := source_morrey_base_ge hτ
  have hRbase : ENNReal.ofReal R ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hRle
  have hκpos : 0 < κr := lt_of_lt_of_le (by norm_num) hκ
  have hrelp : 1 / (6 / 5 : ℝ) = 1 / 2 + 1 / 3 := by norm_num
  have hrelq : 1 / ((1 / τr + 8 / 25 : ℝ)⁻¹) =
      1 / (25 / 8 : ℝ) + 1 / τr := by
    simp only [one_div, inv_inv]
    ring
  have hbaseprod := morreyNorm_holder (p := (6 / 5 : ℝ))
    (p₁ := 2) (p₂ := 3) (q := (1 / τr + 8 / 25)⁻¹)
    (q₁ := (25 / 8 : ℝ)) (q₂ := τr) (by norm_num) (by norm_num)
    hrelp hrelq hDmeas hUmeas
  have hbaseprod' := hbaseprod.trans (mul_le_mul hD hU
    (by positivity) (by positivity))
  have hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R,
      (fun z => S.indicator (fun v => Du v i j) z *
        S.indicator (fun v => u v j) z) w = 0 := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact False.elim (hw (hSsupport hwS))
    · simp only [indicator_of_notMem hwS, zero_mul]
  have hlower := morreyNorm_lower_morrey_exponent
    (p := (6 / 5 : ℝ)) (q := (1 / τr + 8 / 25)⁻¹) (q' := κr)
    (f := fun z => S.indicator (fun v => Du v i j) z *
      S.indicator (fun v => u v j) z)
    (by norm_num) hbase hκ hκτ hR hsupp
  have hexp : 0 ≤ 5 * (1 / κr -
      1 / (1 / τr + 8 / 25)⁻¹) := by
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_div_le_one_div_of_le hκpos hκτ))
  have hfactor : (ENNReal.ofReal R) ^
      (5 * (1 / κr - 1 / (1 / τr + 8 / 25)⁻¹)) ≤ 1 := by
    exact (ENNReal.rpow_le_rpow hRbase hexp).trans_eq (by simp)
  calc
    _ ≤ (ENNReal.ofReal R) ^
        (5 * (1 / κr - 1 / (1 / τr + 8 / 25)⁻¹)) *
          morreyNorm (6 / 5 : ℝ) ((1 / τr + 8 / 25)⁻¹)
            (fun z => S.indicator (fun v => Du v i j) z *
              S.indicator (fun v => u v j) z) := hlower
    _ ≤ morreyNorm (6 / 5 : ℝ) ((1 / τr + 8 / 25)⁻¹)
        (fun z => S.indicator (fun v => Du v i j) z *
          S.indicator (fun v => u v j) z) := by
      calc
        _ ≤ 1 * morreyNorm (6 / 5 : ℝ) ((1 / τr + 8 / 25)⁻¹)
            (fun z => S.indicator (fun v => Du v i j) z *
              S.indicator (fun v => u v j) z) :=
          mul_le_mul_of_nonneg_right hfactor bot_le
        _ = _ := one_mul _
    _ ≤ KU * KD := by simpa only [mul_comm] using hbaseprod'

private theorem source_morrey_force_le
    {S : Set ParabolicPoint} {f : ParabolicPoint → Vec3} {i : Fin 3}
    {KF : ℝ≥0∞} {qr κr R : ℝ} {z₀ : ParabolicPoint}
    (hq : 5 / 2 < qr) (hκ : 6 / 5 ≤ κr) (hκq : κr ≤ qr)
    (hR : 0 < R) (hRle : R ≤ 1)
    (hSsupport : S ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hF : morreyNorm (6 / 5 : ℝ) qr
      (S.indicator (fun z => f z i)) ≤ KF)
    (_ : AEMeasurable (S.indicator (fun z => f z i)) volume) :
    morreyNorm (6 / 5 : ℝ) κr (S.indicator (fun z => f z i)) ≤ KF := by
  have hRbase : ENNReal.ofReal R ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hRle
  have hκpos : 0 < κr := lt_of_lt_of_le (by norm_num) hκ
  have hqκ : 6 / 5 ≤ qr := by linarith only [hq]
  have hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R,
      S.indicator (fun z => f z i) w = 0 := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact False.elim (hw (hSsupport hwS))
    · rw [indicator_of_notMem hwS]
  have hlower := morreyNorm_lower_morrey_exponent
    (p := (6 / 5 : ℝ)) (q := qr) (q' := κr)
    (f := S.indicator (fun z => f z i)) (by norm_num) hqκ hκ hκq hR hsupp
  have hexp : 0 ≤ 5 * (1 / κr - 1 / qr) := by
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_div_le_one_div_of_le hκpos hκq))
  have hfactor : (ENNReal.ofReal R) ^ (5 * (1 / κr - 1 / qr)) ≤ 1 := by
    exact (ENNReal.rpow_le_rpow hRbase hexp).trans_eq (by simp)
  calc
    _ ≤ (ENNReal.ofReal R) ^ (5 * (1 / κr - 1 / qr)) *
        morreyNorm (6 / 5 : ℝ) qr (S.indicator (fun z => f z i)) := hlower
    _ ≤ morreyNorm (6 / 5 : ℝ) qr (S.indicator (fun z => f z i)) := by
      calc
        _ ≤ 1 * morreyNorm (6 / 5 : ℝ) qr
            (S.indicator (fun z => f z i)) :=
          mul_le_mul_of_nonneg_right hfactor bot_le
        _ = _ := one_mul _
    _ ≤ KF := hF

theorem pressure_divergence_source_morrey_component_le
    {S : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {f : ParabolicPoint → Vec3}
    {i : Fin 3} {τ q κ : ℝ} {KU KD KF : ℝ≥0∞}
    {z₀ : ParabolicPoint} {R : ℝ}
    (hτ : 25 / 3 ≤ τ) (hq : 5 / 2 < q)
    (hκ : 6 / 5 ≤ κ)
    (hκτ : κ ≤ (1 / τ + 8 / 25)⁻¹) (hκq : κ ≤ q)
    (hR : 0 < R) (hRle : R ≤ 1)
    (hSsupport : S ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hU : ∀ j : Fin 3,
      morreyNorm 3 τ (S.indicator (fun z => u z j)) ≤ KU)
    (hD : ∀ j : Fin 3,
      morreyNorm 2 (25 / 8 : ℝ)
        (S.indicator (fun z => Du z i j)) ≤ KD)
    (hF : morreyNorm (6 / 5 : ℝ) q
      (S.indicator (fun z => f z i)) ≤ KF)
    (hUmeas : ∀ j : Fin 3,
      AEMeasurable (S.indicator (fun z => u z j)) volume)
    (hDmeas : ∀ j : Fin 3,
      AEMeasurable (S.indicator (fun z => Du z i j)) volume)
    (hFmeas : AEMeasurable
      (S.indicator (fun z => f z i)) volume) :
    morreyNorm (6 / 5 : ℝ) κ
      (S.indicator (fun z => ∑ j, Du z i j * u z j - f z i)) ≤
      3 * KU * KD + KF := by
  have hprod : ∀ j : Fin 3,
      morreyNorm (6 / 5 : ℝ) κ
        (fun z => S.indicator (fun v => Du v i j) z *
          S.indicator (fun v => u v j) z) ≤ KU * KD := by
    intro j
    exact source_morrey_product_le hτ hκ hκτ hR hRle hSsupport
      (hU j) (hD j) (hUmeas j) (hDmeas j)
  have hforce := source_morrey_force_le hq hκ hκq hR hRle hSsupport
    hF hFmeas
  have hprodMeas : ∀ j : Fin 3,
      AEMeasurable (fun z => S.indicator (fun v => Du v i j) z *
        S.indicator (fun v => u v j) z) volume := fun j =>
    (hDmeas j).mul (hUmeas j)
  have hsumMeas : AEMeasurable (fun z => ∑ j,
      S.indicator (fun v => Du v i j) z * S.indicator (fun v => u v j) z) volume := by
    simpa [Fin.sum_univ_succ, Pi.add_def] using
      (hprodMeas 0).add ((hprodMeas 1).add (hprodMeas 2))
  have hsum12 := (CKN.Core.Endgame.morrey_norm_add_le
      (τ := κ) (by norm_num) (hprodMeas 1) (hprodMeas 2)).trans
    (add_le_add (hprod 1) (hprod 2))
  have hsum := (CKN.Core.Endgame.morrey_norm_add_le
      (τ := κ) (by norm_num) (hprodMeas 0)
      ((hprodMeas 1).add (hprodMeas 2))).trans
    (add_le_add (hprod 0) hsum12)
  have hsumBound : morreyNorm (6 / 5 : ℝ) κ (fun z => ∑ j,
      S.indicator (fun v => Du v i j) z * S.indicator (fun v => u v j) z) ≤
      3 * KU * KD := by
    have heq : (fun z => ∑ j,
        S.indicator (fun v => Du v i j) z * S.indicator (fun v => u v j) z) =
        (fun z => S.indicator (fun v => Du v i 0) z * S.indicator (fun v => u v 0) z +
          (S.indicator (fun v => Du v i 1) z * S.indicator (fun v => u v 1) z +
            S.indicator (fun v => Du v i 2) z * S.indicator (fun v => u v 2) z)) := by
      funext z
      simp [Fin.sum_univ_succ]
    rw [heq]
    convert hsum using 1
    · ring
  have hsourceEq : S.indicator (fun z => ∑ j, Du z i j * u z j - f z i) =
      (fun z => ∑ j, S.indicator (fun v => Du v i j) z *
        S.indicator (fun v => u v j) z) - S.indicator (fun z => f z i) := by
    funext z
    by_cases hz : z ∈ S
    · simp [hz]
    · simp [hz]
  rw [hsourceEq]
  exact (morrey_norm_sub_le (τ := κ) (by norm_num) hsumMeas hFmeas).trans
    (add_le_add hsumBound hforce)

theorem pressure_divergence_source_morrey_le
    {S : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {f : ParabolicPoint → Vec3}
    {τ q κ : ℝ} {KU KD KF : ℝ≥0∞} {z₀ : ParabolicPoint} {R : ℝ}
    (hτ : 25 / 3 ≤ τ) (hq : 5 / 2 < q)
    (hκ : 6 / 5 ≤ κ) (hκτ : κ ≤ (1 / τ + 8 / 25)⁻¹) (hκq : κ ≤ q)
    (hR : 0 < R) (hRle : R ≤ 1)
    (hSsupport : S ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hU : ∀ j, morreyNorm 3 τ (S.indicator (fun z => u z j)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      (S.indicator (fun z => Du z i j)) ≤ KD)
    (hF : ∀ i, morreyNorm (6 / 5 : ℝ) q
      (S.indicator (fun z => f z i)) ≤ KF)
    (hUmeas : ∀ j, AEMeasurable (S.indicator (fun z => u z j)) volume)
    (hDmeas : ∀ i j, AEMeasurable
      (S.indicator (fun z => Du z i j)) volume)
    (hFmeas : ∀ i, AEMeasurable
      (S.indicator (fun z => f z i)) volume) :
    morreyNorm (6 / 5 : ℝ) κ (fun z => vec3EuclideanNorm
      (S.indicator (fun w => fun i => ∑ j, Du w i j * u w j - f w i) z)) ≤
      3 * (3 * KU * KD + KF) := by
  let G : ParabolicPoint → Vec3 := fun z =>
    S.indicator (fun w => fun i => ∑ j, Du w i j * u w j - f w i) z
  have hGmeas : ∀ i, AEMeasurable (fun z => G z i) volume := by
    intro i
    have hsrc : AEMeasurable (S.indicator (fun z =>
        ∑ j, Du z i j * u z j - f z i)) volume := by
      have hsumMeas : AEMeasurable (fun z => ∑ j,
          S.indicator (fun v => Du v i j) z *
            S.indicator (fun v => u v j) z) volume := by
        simpa [Fin.sum_univ_succ, Pi.add_def] using
          (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
            (fun j _ => (hDmeas i j).mul (hUmeas j)))
      have heq : (fun z => ∑ j,
          S.indicator (fun v => Du v i j) z *
            S.indicator (fun v => u v j) z) -
          S.indicator (fun z => f z i) = S.indicator (fun z =>
            ∑ j, Du z i j * u z j - f z i) := by
        funext z
        by_cases hz : z ∈ S
        · simp [hz]
        · simp [hz]
      rw [← heq]
      exact hsumMeas.sub (hFmeas i)
    have heqG : (fun z => G z i) = S.indicator (fun z =>
        ∑ j, Du z i j * u z j - f z i) := by
      funext z
      by_cases hz : z ∈ S <;> simp [G, hz]
    rw [heqG]
    exact hsrc
  have hcomp : ∀ i, morreyNorm (6 / 5 : ℝ) κ (fun z => G z i) ≤
      3 * KU * KD + KF := by
    intro i
    have heqG : (fun z => G z i) = S.indicator (fun z =>
        ∑ j, Du z i j * u z j - f z i) := by
      funext z
      by_cases hz : z ∈ S <;> simp [G, hz]
    rw [heqG]
    exact pressure_divergence_source_morrey_component_le
      (i := i) hτ hq hκ hκτ hκq hR hRle hSsupport (hU) (hD i)
        (hF i) (hUmeas) (hDmeas i) (hFmeas i)
  have hsum := CKN.Core.Endgame.morrey_norm_euclidean_le_sum_components
    (τ := κ) (by norm_num : (1 : ℝ) ≤ 6 / 5) hGmeas
  change morreyNorm (6 / 5 : ℝ) κ (fun z => vec3EuclideanNorm (G z)) ≤ _
  calc
    _ ≤ ∑ i, morreyNorm (6 / 5 : ℝ) κ (fun z => G z i) := hsum
    _ ≤ 3 * (3 * KU * KD + KF) := by
      calc
        _ = morreyNorm (6 / 5 : ℝ) κ (fun z => G z 0) +
            (morreyNorm (6 / 5 : ℝ) κ (fun z => G z 1) +
              morreyNorm (6 / 5 : ℝ) κ (fun z => G z 2)) := by
          simp [Fin.sum_univ_succ]
        _ ≤ (3 * KU * KD + KF) +
            ((3 * KU * KD + KF) + (3 * KU * KD + KF)) :=
          add_le_add (hcomp 0) (add_le_add (hcomp 1) (hcomp 2))
        _ = 3 * (3 * KU * KD + KF) := by ring

end CKN.Core.Step4
