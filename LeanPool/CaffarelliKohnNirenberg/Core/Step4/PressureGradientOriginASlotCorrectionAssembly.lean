/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotThinCells
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremAClosersInstances
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTMeasurableFourTermAssembly

/-! # The A slot from its homogeneous centred-source correction

The other three terms, their measurable envelopes, and the finite-cell
transfer are supplied internally. Only the displayed correction estimate
remains as the analytic input of this reduction.
-/

public section

section

/-! # The instance A-slot interface with exponent-dependent thresholds

The base threshold may depend on the force exponent alone.
The analytic estimate is restricted to the common half-collar radius.
The finite cover restores the exact cell range of the pressure adapter.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- Thin-cell bounds at the two prescribed triples imply the full A-slot
integral estimate with one absolute increase of the coefficient. -/
theorem theoremA_aSlot_integral_instances_of_thin_cells_q
    (Cbase : ℝ → ℝ) (hCbase : ∀ q, 0 ≤ Cbase q)
    (hmargin :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → Cbase q ≤ C_CZ →
    ((τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32)) →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
      ∀ i : Fin 3, ∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
        ∀ r : ℝ, 0 < r → r ≤ 1 / 256 →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ →
    originASlotThinCellThreshold (Cbase q) ≤ C_CZ →
    ((τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32)) →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
      ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτhi hC hthreshold hinstances hR₁ hR₁R₀ hR₀ hε hKU hKD Ω I u
    Du p f
    hsol hdom hU hDu hsize Dp hDp hweak i z _hz r hr _hrR₁
  exact originASlot_clipped_cell_of_thin_cells hq hτ hτhi hR₁
    (lt_trans hR₁R₀ hR₀) hthreshold hDp i
    (fun w hw ρ hρ hρle =>
      hmargin q τ (Cbase q) R₀ R₁ ε KU KD hq hτ hτhi (hCbase q) le_rfl hinstances hR₁ hR₁R₀ hR₀ hε
        hKU hKD
        hsol hdom hU hDu hsize Dp hDp hweak i w hw ρ hρ hρle)
    z hr

end CKN.Core.Step4
end

end

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat CKN.Foundation.Euclidean CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- The common component coefficient, depending only on the force exponent
when the correction coefficient has that dependence. -/
def originASlotComponentThreshold (CM2 : ℝ → ℝ) (q : ℝ) : ℝ :=
  max 0 (max rieszSourceThresholdA
    (max gapHarmonicEnvelopeThreshold (max originASlotForceIncrementThreshold (CM2 q))))

/-- The triangle cost followed by one finite-cover cost. -/
def originASlotCorrectionThreshold (CM2 : ℝ → ℝ) (q : ℝ) : ℝ :=
  originASlotThinCellThreshold (fourTermAffineThreshold (originASlotComponentThreshold CM2 q))

/-- The homogeneous correction bound on the common half-collar scale
implies the exact exponent-dependent A-slot integral binder. -/
theorem theoremA_aSlot_integral_of_source_correction
    (CM2 : ℝ → ℝ)
    (hM2 :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → CM2 q ≤ C_CZ →
    ∀ hinstances : (τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32),
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ i : Fin 3, ∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
        ∀ r : ℝ, 0 < r → r ≤ 1 / 256 →
        let hρ : 0 < (R₀-R₁)/2 := by
          rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
        let η := mollifiedBallCutoff z.1 hρ
        let c := sourceSliceCentredMean z.1 ((R₀-R₁)/2) u
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun x => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
            (rieszSecondL2_weak_type j i)
            (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η (spatialDeriv η)
              (fun y => u (y,s)) (fun y => f (y,s)) (fun y => Du (y,s)) (c s) j) x)
                (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q)))) :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ →
    originASlotCorrectionThreshold CM2 q ≤ C_CZ →
    ((τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32)) →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
      ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        ∀ r : ℝ, 0 < r → r ≤ R₁ →
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
  apply theoremA_aSlot_integral_instances_of_thin_cells_q
    (fun q => fourTermAffineThreshold (originASlotComponentThreshold CM2 q))
    (fun q => by unfold fourTermAffineThreshold; positivity)
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτhi _hC hthreshold hinstances hR₁ hgap hR₀ hε hKU hKD
    Ω I u Du p f hsol hdom hU hD hsize Dp _hDp hweak i z hz r hr hcell
  have hnonneg : 0 ≤ originASlotComponentThreshold CM2 q := le_max_left _ _
  have hriesz : rieszSourceThresholdA ≤ originASlotComponentThreshold CM2 q :=
    le_max_of_le_right (le_max_left _ _)
  have hharmonic : gapHarmonicEnvelopeThreshold ≤ originASlotComponentThreshold CM2 q :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hforce : originASlotForceIncrementThreshold ≤ originASlotComponentThreshold CM2 q :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hcorrection : CM2 q ≤ originASlotComponentThreshold CM2 q :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  apply actual_pressure_four_term_affine_of_sws q ε C_CZ τ R₀ R₁ r
    (originASlotComponentThreshold CM2) KU KD hthreshold hriesz hforce hharmonic
    hinstances hKU hKD hU hD hsol hdom hsize hweak z hz hr hcell i
  exact hM2 q τ (originASlotComponentThreshold CM2 q) R₀ R₁ ε KU KD hq hτ hτhi
    hnonneg hcorrection hinstances hR₁ hgap hR₀ hε hKU hKD hsol hdom hU hD hsize i z hz r hr hcell

end CKN.Core.Step4
