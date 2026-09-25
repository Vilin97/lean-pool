/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSided
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBudget
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.OneSidedMorreyMonotone

/-!
# Pressure Gradient One Sided KP

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-!
# Enlarged one-sided pressure-gradient majorant

This file preserves `oneSidedPressureGradientKP` and introduces a larger
majorant with an additive `6/5`-power term in its small-cell budget and the
clipped-scale inflation in its whole-carrier budget.

## Main results
- `oneSidedPressureGradientKP_le_oneSidedPressureGradientKP'`: the old
  majorant is bounded by the enlarged one without parameter assumptions.
- `clipped_clause_le_oneSidedPressureGradientKP'`: the original raw budget
  certificates imply the clipped-scale conclusion throughout `0 < R₁ < 3/4`.
- `oneSidedPressureGradientQuantitative_to_KP'`: transports the explicit AE
  binder with the old majorant to the binder with the enlarged majorant.

The adapter direction is from the AE producer stated with `KP` to the larger
`KP'` bound; a closer consuming the enlarged binder should use this direction.
-/

/-- The enlarged pressure-gradient majorant. Its A budget adds the raised
`6/5` power to the old A budget, and its B budget absorbs the clipped-scale
inflation, floored at one. -/
def oneSidedPressureGradientKP'
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) : ℝ≥0∞ :=
  let κ := min ((1 / τ + 8 / 25)⁻¹) q
  let c := ENNReal.ofReal (|C_CZ| + 1)
  let X := 3 * KU * KD + forceSourceMorreyBound q ε
  let θ := 5 * (1 - (6 / 5 : ℝ) / κ)
  let A := c * (3 * X) + (c * (3 * X)) ^ (6 / 5 : ℝ)
  let B := (c * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
    ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^ θ))
  oneSidedMorreyBound (6 / 5) κ R₁ A B

/-- The enlarged majorant is finite for finite velocity and gradient budgets
and an admissible force exponent. -/
theorem oneSidedPressureGradientKP'_lt_top
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hKU : KU < ⊤) (hKD : KD < ⊤) :
    oneSidedPressureGradientKP' q τ C_CZ R₀ R₁ ε KU KD < ⊤ := by
  have hforce : forceSourceMorreyBound q ε < ⊤ :=
    forceSourceMorreyBound_lt_top q ε hq
  have hc : ENNReal.ofReal (|C_CZ| + 1) < ⊤ := ENNReal.ofReal_lt_top
  have hAlinear :
      ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) < ⊤ := by
    apply ENNReal.mul_lt_top hc
    apply ENNReal.mul_lt_top (by simp)
    apply ENNReal.add_lt_top.mpr
    constructor
    · apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top (by simp) hKU
      · exact hKD
    · exact hforce
  have hApower :
      (ENNReal.ofReal (|C_CZ| + 1) *
        (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) ^ (6 / 5 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hAlinear.ne
  have hA :
      ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) +
        (ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) ^ (6 / 5 : ℝ) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hAlinear, hApower⟩
  have hBbase :
      ENNReal.ofReal (|C_CZ| + 1) *
        ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) < ⊤ :=
    ENNReal.mul_lt_top hc ENNReal.ofReal_lt_top
  have hBfactor :
      ENNReal.ofReal
        (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) : ℝ) < ⊤ :=
    ENNReal.ofReal_lt_top
  have hB :
      (ENNReal.ofReal (|C_CZ| + 1) *
        ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal
          (max 1 ((2 * R₁ / (1 - R₁)) ^
            (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) : ℝ) < ⊤ :=
    ENNReal.mul_lt_top hBbase hBfactor
  dsimp [oneSidedPressureGradientKP']
  exact oneSidedMorreyBound_lt_top (by norm_num) hA hB

/-- The original one-sided pressure-gradient majorant is pointwise bounded
by the enlarged majorant. -/
theorem oneSidedPressureGradientKP_le_oneSidedPressureGradientKP'
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞) :
    oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD ≤
      oneSidedPressureGradientKP' q τ C_CZ R₀ R₁ ε KU KD := by
  have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (|C_CZ| + 1) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith only [abs_nonneg C_CZ])
  have hA :
      ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) ≤
        ENNReal.ofReal (|C_CZ| + 1) *
            (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) +
          (ENNReal.ofReal (|C_CZ| + 1) *
            (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) ^ (6 / 5 : ℝ) := by
    exact le_add_of_nonneg_right bot_le
  have hfactor :
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal
        (max 1 ((2 * R₁ / (1 - R₁)) ^
          (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) : ℝ) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hB :
      ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) ≤
        (ENNReal.ofReal (|C_CZ| + 1) *
          ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
          ENNReal.ofReal
            (max 1 ((2 * R₁ / (1 - R₁)) ^
              (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) : ℝ) := by
    calc
      _ = _ * 1 := (mul_one _).symm
      _ ≤ _ * _ := mul_le_mul' le_rfl hfactor
  dsimp [oneSidedPressureGradientKP, oneSidedPressureGradientKP']
  exact oneSidedMorreyBound_mono (by norm_num) hA hB

/-- Raw A and B budget certificates imply the clipped-scale estimate against
the enlarged majorant for every `0 < R₁ < 3/4`; the clipped-scale inflation is
absorbed into its B slot. -/
theorem clipped_clause_le_oneSidedPressureGradientKP'
    {q τ C_CZ R₀ R₁ ε : ℝ} {KU KD A B : ℝ≥0∞}
    (hR₁ : 0 < R₁) (hR₁' : R₁ < 3 / 4)
    (hA : A ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε))
    (hB : B ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) :
    oneSidedMorreyBound (6 / 5) (min ((1 / τ + 8 / 25)⁻¹) q)
        ((1 - R₁) / 2) A B ≤
      oneSidedPressureGradientKP' q τ C_CZ R₀ R₁ ε KU KD := by
  have hR₁lt : R₁ < 1 := lt_trans hR₁' (by norm_num)
  have hρ₀ : 0 < (1 - R₁) / 2 := clipped_scale_pos hR₁lt
  have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (|C_CZ| + 1) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith only [abs_nonneg C_CZ])
  have hA' :
      A ≤ ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) +
        (ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε))) ^ (6 / 5 : ℝ) := by
    calc
      A ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε) := hA
      _ = 1 * (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (|C_CZ| + 1) *
          (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) :=
        mul_le_mul' hc le_rfl
      _ ≤ _ + _ := le_add_of_nonneg_right bot_le
  have hfactor :
      ENNReal.ofReal
          ((R₁ / ((1 - R₁) / 2)) ^
            (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) : ℝ) ≤
        ENNReal.ofReal
          (max 1 ((2 * R₁ / (1 - R₁)) ^
            (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) : ℝ)) := by
    have hden : (1 : ℝ) - R₁ ≠ 0 :=
      ne_of_gt (by linarith only [hR₁lt])
    have hratio : R₁ / ((1 - R₁) / 2) = 2 * R₁ / (1 - R₁) := by
      field_simp
    rw [hratio]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hB' :
      B * ENNReal.ofReal
          ((R₁ / ((1 - R₁) / 2)) ^
            (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) : ℝ) ≤
        (ENNReal.ofReal (|C_CZ| + 1) *
          ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
          ENNReal.ofReal
            (max 1 ((2 * R₁ / (1 - R₁)) ^
              (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)) : ℝ)) := by
    have hBbase : B ≤ ENNReal.ofReal (|C_CZ| + 1) *
        ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := by
      calc
        B ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := hB
        _ = 1 * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul' hc le_rfl
    calc
      _ ≤ (ENNReal.ofReal (|C_CZ| + 1) *
          ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
            ENNReal.ofReal
              ((R₁ / ((1 - R₁) / 2)) ^
                (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) :=
        mul_le_mul' hBbase le_rfl
      _ ≤ _ := mul_le_mul' le_rfl hfactor
  rw [oneSidedMorreyBound_scale_eq (P := 6 / 5)
    (τ := min ((1 / τ + 8 / 25)⁻¹) q) (ρ₀ := (1 - R₁) / 2) (ρ₁ := R₁)
    (A := A) (B := B) (by norm_num) hρ₀ hR₁]
  dsimp [oneSidedPressureGradientKP']
  exact oneSidedMorreyBound_mono (by norm_num) hA' hB'

/-- Convert the explicit AE binder with the original majorant to the same
quantitative binder with the enlarged majorant. This is the direction needed
when the closer consumes `KP'`: each old output estimate is transported upward
using `oneSidedPressureGradientKP_le_oneSidedPressureGradientKP'`. -/
theorem oneSidedPressureGradientQuantitative_to_KP'
    (hGA : oneSidedPressureGradientQuantitative) :
    ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ⊤ → KD < ⊤ →
    oneSidedPressureGradientKP' q τ C_CZ R₀ R₁ ε KU KD < ⊤ ∧
    ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
            (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i)
              (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ)
              (min ((1 / τ + 8 / 25)⁻¹) q)
              ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
                (fun z => Dp z i)) ≤
            oneSidedPressureGradientKP' q τ C_CZ R₀ R₁ ε KU KD) := by
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  obtain ⟨_hKPfinite, hout⟩ :=
    hGA q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  refine ⟨oneSidedPressureGradientKP'_lt_top q τ C_CZ R₀ R₁ ε KU KD hq hKU hKD,
    ?_⟩
  intro Ω I u Du p f hsol hdom hU hD hsmall
  obtain ⟨Dp, hAE, hInt, hweak, hMorrey⟩ := hout hsol hdom hU hD hsmall
  exact ⟨Dp, hAE, hInt, hweak, fun i =>
    (hMorrey i).trans
      (oneSidedPressureGradientKP_le_oneSidedPressureGradientKP'
        q τ C_CZ R₀ R₁ ε KU KD)⟩

end CKN.Core.Step4

end
