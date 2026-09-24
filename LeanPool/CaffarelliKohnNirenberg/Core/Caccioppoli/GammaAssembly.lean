/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.GammaTerms
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI3Bound
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI4

/-!
# Gamma Assembly

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! This adapter assembles the four raw terms in the `gamma` form of
`lem:caccioppoli-gamma`.  The lower energy certificate remains explicit until
the unconditional Caccioppoli producer supplies it. -/

/-- Assemble the gamma form from the two gamma replacements and the raw
pressure and force estimates. -/
theorem caccioppoli_gamma_of_raw_bounds
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ r ε C₂₅ C₂₆ : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r)
    (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆)
    (hK₁ : 6000 * ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
      ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
        6 * cutoffGradientConstant * 5000000)) ≤ C₂₅ ^ 2)
    (hK₂ : 6000 * (3 * (1500 * cutoffGradientConstant + 900000)) ≤ C₂₅ ^ 2)
    (hK₃ : 6000 * (3000 * cutoffGradientConstant + 1800000) ≤ C₂₅ ^ 2)
    (hK₄ : 6000 * (2000 * (4 * Real.pi / 3) ^
      (1 / (q / (q - 1)) - 1 / 3 : ℝ)) ≤ C₂₆ ^ 2)
    {c : ParabolicPoint → ℝ}
    (hc : ∀ w, 0 ≤ c w)
    (hcm : AEMeasurable c
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hA₁ : AEMeasurable (fun w =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hmean : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3))
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    {I₁ I₂ I₃ I₄ : ℝ}
    (hLower : (alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r) ^ 2 ≤
      6000 * (I₁ + I₂ + I₃ + I₄))
    (hI₁ : I₁ = caccioppoli_I1_heat_cutoff_raw
      (u := u) (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε)
    (hI₂ : I₂ = caccioppoli_I2_heat_cutoff_raw
      (u := u) (c := c) (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
      hρ hε)
    (hI₃ : I₃ = caccioppoli_I3_heat_cutoff_raw
      (p := p) (v := u) (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
      hρ hε)
    (hI₄ : I₄ = caccioppoli_I4_heat_cutoff_raw
      (u := u) (f := f) (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
      hρ hε) :
    alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r ≤
      C₂₅ * ((r / ρ) * gamma u (x₀, t₀) ρ +
        (r / ρ) ^ (-1 : ℝ) * gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ) +
        (r / ρ) ^ (-1 : ℝ) * delta p (x₀, t₀) ρ *
          gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ)) +
      C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u (x₀, t₀) ρ ^
        (1 / 2 : ℝ) * lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ) := by
  have hs : 0 < Real.sqrt (6000 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt (6000 : ℝ)) ^ 2 = 6000 := by
    rw [Real.sq_sqrt]
    norm_num
  have hscale₂₅ (a : ℝ) :
      6000 * (C₂₅ / Real.sqrt (6000 : ℝ) * a) ^ 2 = (C₂₅ * a) ^ 2 := by
    calc
      6000 * (C₂₅ / Real.sqrt (6000 : ℝ) * a) ^ 2 =
          6000 * (C₂₅ / Real.sqrt (6000 : ℝ)) ^ 2 * a ^ 2 := by ring
      _ = C₂₅ ^ 2 * a ^ 2 := by
        rw [div_pow, hs2]
        field_simp [ne_of_gt hs]
      _ = _ := by ring
  have hscale₂₆ (a : ℝ) :
      6000 * (C₂₆ / Real.sqrt (6000 : ℝ) * a) ^ 2 = (C₂₆ * a) ^ 2 := by
    calc
      6000 * (C₂₆ / Real.sqrt (6000 : ℝ) * a) ^ 2 =
          6000 * (C₂₆ / Real.sqrt (6000 : ℝ)) ^ 2 * a ^ 2 := by ring
      _ = C₂₆ ^ 2 * a ^ 2 := by
        rw [div_pow, hs2]
        field_simp [ne_of_gt hs]
      _ = _ := by ring
  have hC₂₅' : 0 ≤ C₂₅ / Real.sqrt (6000 : ℝ) :=
    div_nonneg hC₂₅ (Real.sqrt_nonneg _)
  have hC₂₆' : 0 ≤ C₂₆ / Real.sqrt (6000 : ℝ) :=
    div_nonneg hC₂₆ (Real.sqrt_nonneg _)
  have hK₁' : (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
      ((32 + 3 * cutoffSecondDerivativeConstant) * 8000000 +
        6 * cutoffGradientConstant * 5000000) ≤
      (C₂₅ / Real.sqrt (6000 : ℝ)) ^ 2 := by
    rw [div_pow, hs2]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6000)).2
    nlinarith only [hK₁]
  have hK₂' : 3 * (1500 * cutoffGradientConstant + 900000) ≤
      (C₂₅ / Real.sqrt (6000 : ℝ)) ^ 2 := by
    rw [div_pow, hs2]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6000)).2
    nlinarith only [hK₂]
  have hK₃' : 3000 * cutoffGradientConstant + 1800000 ≤
      (C₂₅ / Real.sqrt (6000 : ℝ)) ^ 2 := by
    rw [div_pow, hs2]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6000)).2
    nlinarith only [hK₃]
  have hK₄' : 2000 * (4 * Real.pi / 3) ^
      (1 / (q / (q - 1)) - 1 / 3 : ℝ) ≤
      (C₂₆ / Real.sqrt (6000 : ℝ)) ^ 2 := by
    rw [div_pow, hs2]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6000)).2
    nlinarith only [hK₄]
  have hI₁b := caccioppoli_I1_gamma_normalized
    (C₂₅ := C₂₅ / Real.sqrt (6000 : ℝ)) hρ hε hr hscale hεr
    hvelocity hA₁ hK₁'
  have hI₂raw := caccioppoli_I2_gamma_heat_cutoff_raw_bound hsol hρ hε hr
    hscale hsub hc hcm hmean hvelocity
  have hγ : 0 ≤ gamma u (x₀, t₀) ρ := by
    unfold gamma
    positivity
  have hκ : 0 < r / ρ := div_pos hr hρ
  have hri : (r / ρ) ^ (-1 : ℝ) = (r / ρ)⁻¹ := by
    rw [Real.rpow_neg hκ.le, Real.rpow_one]
  have hratio : ρ ^ 2 / r ^ 2 =
      ((r / ρ) ^ (-1 : ℝ)) ^ (2 : ℕ) := by
    rw [hri]
    field_simp [hρ.ne', hr.ne']
  have hγpow : (gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ)) ^ (2 : ℕ) =
      gamma u (x₀, t₀) ρ ^ (3 : ℕ) := by
    calc
      _ = (gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = gamma u (x₀, t₀) ρ ^ ((3 / 2 : ℝ) * 2) := by
        rw [← Real.rpow_mul hγ]
      _ = _ := by norm_num
  have hI₂b : I₂ ≤
      ((C₂₅ / Real.sqrt (6000 : ℝ)) * (r / ρ) ^ (-1 : ℝ) *
        gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ)) ^ 2 := by
    rw [hI₂]
    have hfactor : 0 ≤ ((r / ρ) ^ (-1 : ℝ)) ^ (2 : ℕ) *
        gamma u (x₀, t₀) ρ ^ (3 : ℕ) := by positivity
    calc
      _ ≤ 3 * (1500 * cutoffGradientConstant + 900000) *
          ((r / ρ) ^ (-1 : ℝ)) ^ (2 : ℕ) *
          gamma u (x₀, t₀) ρ ^ (3 : ℕ) := by
        rw [← hratio]
        exact hI₂raw
      _ ≤ (C₂₅ / Real.sqrt (6000 : ℝ)) ^ 2 *
          ((r / ρ) ^ (-1 : ℝ)) ^ (2 : ℕ) *
          gamma u (x₀, t₀) ρ ^ (3 : ℕ) := by
        calc
          _ = (3 * (1500 * cutoffGradientConstant + 900000)) *
              (((r / ρ) ^ (-1 : ℝ)) ^ (2 : ℕ) *
                gamma u (x₀, t₀) ρ ^ (3 : ℕ)) := by ring
          _ ≤ (C₂₅ / Real.sqrt (6000 : ℝ)) ^ 2 *
              (((r / ρ) ^ (-1 : ℝ)) ^ (2 : ℕ) *
              gamma u (x₀, t₀) ρ ^ (3 : ℕ)) :=
            mul_le_mul_of_nonneg_right hK₂' hfactor
          _ = _ := by ring
      _ = _ := by
        calc
          _ = (C₂₅ / Real.sqrt (6000 : ℝ)) ^ 2 *
              ((r / ρ) ^ (-1 : ℝ)) ^ 2 *
              (gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ)) ^ 2 := by
            rw [← hγpow]
          _ = _ := by ring
  have hI₃b := caccioppoli_I3_heat_cutoff_raw_normalized hsol hρ hε hr
    (C₂₅ := C₂₅ / Real.sqrt (6000 : ℝ)) hscale hsub hvelocity hK₃'
  have hI₄b := caccioppoli_I4_heat_cutoff_raw_normalized hsol hρ hε hr
    (C₂₆ := C₂₆ / Real.sqrt (6000 : ℝ)) hεr hsub hvelocity hK₄'
  have hq : 0 < q := lt_trans (by norm_num) hsol.2.2.2.1
  have hI₃b' := hI₃b
  rw [← hri] at hI₃b'
  have hI₁' : 6000 * I₁ ≤
      (C₂₅ * (r / ρ) * gamma u (x₀, t₀) ρ) ^ 2 := by
    rw [hI₁]
    calc
      6000 * caccioppoli_I1_heat_cutoff_raw (u := u) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
          6000 * (C₂₅ / Real.sqrt (6000 : ℝ) * (r / ρ) *
            gamma u (x₀, t₀) ρ) ^ 2 :=
        mul_le_mul_of_nonneg_left hI₁b (by norm_num)
      _ = _ := by
        simpa only [mul_assoc] using
          hscale₂₅ ((r / ρ) * gamma u (x₀, t₀) ρ)
  have hI₂' : 6000 * I₂ ≤
      (C₂₅ * (r / ρ) ^ (-1 : ℝ) *
        gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ)) ^ 2 := by
    calc
      6000 * I₂ ≤ 6000 *
          ((C₂₅ / Real.sqrt (6000 : ℝ)) * (r / ρ) ^ (-1 : ℝ) *
            gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hI₂b (by norm_num)
      _ = _ := by
        simpa only [mul_assoc] using
          hscale₂₅ ((r / ρ) ^ (-1 : ℝ) *
            gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ))
  have hI₃' : 6000 * I₃ ≤
      (C₂₅ * (r / ρ) ^ (-1 : ℝ) * delta p (x₀, t₀) ρ *
        gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [hI₃]
    calc
      6000 * caccioppoli_I3_heat_cutoff_raw (p := p) (v := u)
          (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
          6000 * (C₂₅ / Real.sqrt (6000 : ℝ) * (r / ρ) ^ (-1 : ℝ) *
            delta p (x₀, t₀) ρ * gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hI₃b' (by norm_num)
      _ = _ := by
        simpa only [mul_assoc] using
          hscale₂₅ ((r / ρ) ^ (-1 : ℝ) * delta p (x₀, t₀) ρ *
            gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ))
  have hI₄' : 6000 * I₄ ≤
      (C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) *
        gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
        lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [hI₄]
    calc
      6000 * caccioppoli_I4_heat_cutoff_raw (u := u) (f := f)
          (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
          6000 * (C₂₆ / Real.sqrt (6000 : ℝ) * (r / ρ) ^ (-1 / 2 : ℝ) *
            gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
              lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hI₄b (by norm_num)
      _ = _ := by
        simpa only [mul_assoc] using
          hscale₂₆ ((r / ρ) ^ (-1 / 2 : ℝ) *
            gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
            lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ))
  have hδ : 0 ≤ delta p (x₀, t₀) ρ := by unfold delta; positivity
  have hLambda : 0 ≤ lambda q f (x₀, t₀) ρ := by unfold lambda; positivity
  have hγ32 : 0 ≤ gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hγ _
  have hγ12 : 0 ≤ gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hγ _
  have hκm1 : 0 ≤ (r / ρ) ^ (-1 : ℝ) :=
    Real.rpow_nonneg hκ.le _
  have hκm12 : 0 ≤ (r / ρ) ^ (-1 / 2 : ℝ) :=
    Real.rpow_nonneg hκ.le _
  have hy₁ : 0 ≤ C₂₅ * (r / ρ) * gamma u (x₀, t₀) ρ := by
    positivity
  have hy₂ : 0 ≤ C₂₅ * (r / ρ) ^ (-1 : ℝ) *
      gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ) := by
    positivity
  have hy₃ : 0 ≤ C₂₅ * (r / ρ) ^ (-1 : ℝ) *
      delta p (x₀, t₀) ρ * gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) := by
    positivity
  have hy₄ : 0 ≤ C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) *
      gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
      lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ) := by
    have hLambda12 : 0 ≤ lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ) := by
      exact Real.rpow_nonneg hLambda _
    positivity
  have hsum := caccioppoli_square_sum_le_square_sum
    (x₁ := 6000 * I₁) (x₂ := 6000 * I₂) (x₃ := 6000 * I₃) (x₄ := 6000 * I₄)
    (y₁ := C₂₅ * (r / ρ) * gamma u (x₀, t₀) ρ)
    (y₂ := C₂₅ * (r / ρ) ^ (-1 : ℝ) *
      gamma u (x₀, t₀) ρ ^ (3 / 2 : ℝ))
    (y₃ := C₂₅ * (r / ρ) ^ (-1 : ℝ) * delta p (x₀, t₀) ρ *
      gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ))
    (y₄ := C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) *
      gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
      lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ))
    hy₁ hy₂ hy₃ hy₄ hI₁' hI₂' hI₃' hI₄'
  have hsum' : 6000 * (I₁ + I₂ + I₃ + I₄) ≤
      (C₂₅ * (r / ρ) * gamma u (x₀, t₀) ρ +
        C₂₅ * (r / ρ) ^ (-1 : ℝ) * gamma u (x₀, t₀) ρ ^
          (3 / 2 : ℝ) +
        C₂₅ * (r / ρ) ^ (-1 : ℝ) * delta p (x₀, t₀) ρ *
          gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u (x₀, t₀) ρ ^
          (1 / 2 : ℝ) * lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 := by
    convert hsum using 1
    ring
  have hmain := hLower.trans hsum'
  have hα : 0 ≤ alpha u (x₀, t₀) r := by unfold alpha; positivity
  have hβ : 0 ≤ beta u Du (x₀, t₀) r := by unfold beta; positivity
  have hroot : alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r ≤
      C₂₅ * (r / ρ) * gamma u (x₀, t₀) ρ +
        C₂₅ * (r / ρ) ^ (-1 : ℝ) * gamma u (x₀, t₀) ρ ^
          (3 / 2 : ℝ) +
        C₂₅ * (r / ρ) ^ (-1 : ℝ) * delta p (x₀, t₀) ρ *
          gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u (x₀, t₀) ρ ^
          (1 / 2 : ℝ) * lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ) := by
    have hright : 0 ≤
        C₂₅ * (r / ρ) * gamma u (x₀, t₀) ρ +
          C₂₅ * (r / ρ) ^ (-1 : ℝ) * gamma u (x₀, t₀) ρ ^
            (3 / 2 : ℝ) +
          C₂₅ * (r / ρ) ^ (-1 : ℝ) * delta p (x₀, t₀) ρ *
            gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) +
          C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u (x₀, t₀) ρ ^
            (1 / 2 : ℝ) * lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ) := by
      exact add_nonneg (add_nonneg (add_nonneg hy₁ hy₂) hy₃) hy₄
    nlinarith only [hmain, hα, hβ, hright]
  convert hroot using 1
  ring

end CKN
