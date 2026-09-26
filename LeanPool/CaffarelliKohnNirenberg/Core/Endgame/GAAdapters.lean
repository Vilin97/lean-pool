/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSided

/-! # The one-sided pressure-gradient boundary in its three consumed shapes

The small-data theorem `thm:A` of `paper/ckn.tex` uses the one-sided
pressure-gradient estimate of `prop:bootstrap` in three different spellings.
The estimate itself is recorded by `oneSidedPressureGradientQuantitative`,
whose majorant is the explicit formula `oneSidedPressureGradientKP`.  The
small-data statement instead asks only for *some* finite majorant, uniformly
in the velocity exponent `τ ∈ [25/3, 25]` and in the two radii.  The uniform
bootstrap round and the closed half-cylinder estimate ask for the two
numerical instantiations `(τ, R₀, R₁) = (25/3, 11/16, 43/64)` and
`(25, 5/8, 19/32)`, with the solution fields explicit, the hypotheses in the
order `hsol → hdom → hsmall → hU → hD`, and the measurability carrier written
as `spaceTimeSet (vec3Ball 0 R₁) I`.

The three theorems below are the translations between those spellings.  The
exponent normalizations are exact: at `τ = 25/3` the Morrey exponent
`min ((1/τ + 8/25)⁻¹) q` equals `25/11`, because `25/11 < 5/2 < q`, while at
`τ = 25` it equals `min q (25/9)` and the minimum genuinely survives, since
`q` is only known to exceed `5/2 = 22.5/9`.  Nothing in this translation is
special to either numerical instantiation: the majorant formula, its
finiteness, and the estimate are all uniform in `τ`.

The hypothesis named `hGA` throughout the assembly of `thm:A` is
`lem:pressure-gradient-morrey`. These theorems only rewrite it between
spellings: existential majorant against explicit majorant, free centre
against origin carrier, and the two orders in which the solution hypotheses
are presented. No estimate is strengthened or weakened here.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Endgame

/-- The explicit majorant of `prop:bootstrap` witnesses the existential
majorant that the small-data statement asks for, at every admissible velocity
exponent and radius pair.  No numerical instantiation is involved. -/
theorem pressure_gradient_existential_of_quantitative
    (hGA : oneSidedPressureGradientQuantitative) :
    ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
    ∃ KP : ℝ≥0∞, KP < ∞ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
            ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤ KP) := by
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  obtain ⟨hKP, hout⟩ :=
    hGA q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  exact ⟨_, hKP, hout⟩

/-- The existential form at `(τ, R₀, R₁) = (25/3, 11/16, 43/64)`, in the exact
shape the uniform bootstrap round consumes: explicit solution fields, the
hypothesis order `hsol → hdom → hsmall → hU → hD`, the measurability carrier
written as a space-time set, and the Morrey exponent already normalized to
`25/11`. -/
theorem initial_pressure_output_of_existential
    (hGA : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
    ∃ KP : ℝ≥0∞, KP < ∞ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
            ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤ KP))
    (q C_CZ ε₀ : ℝ) (KUinitial KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hC : 0 ≤ C_CZ)
    (hε₀ : 0 ≤ ε₀) (hKUinitial : KUinitial < ⊤) (hKD : KD < ⊤) :
    ∃ KP : ℝ≥0∞, KP < ⊤ ∧
        ∀ (Ω : Set Vec3) (I : Set ℝ)
          (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
          (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        (∀ i, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
          (fun z => u z i)) ≤ KUinitial) →
        (∀ i j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
          (fun z => Du z i j)) ≤ KD) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) (43 / 64)) I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball (0 : Vec3) (43 / 64) →
            ∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
          (∀ (i : Fin 3) (ψ : Vec3 × ℝ → ℝ),
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball (0 : Vec3) (43 / 64) ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          ∀ i, morreyNorm (6 / 5) (25 / 11 : ℝ)
            ((parabolicCylinder (0 : Vec3) 0 (43 / 64)).indicator (fun z => Dp z i)) ≤ KP := by
  obtain ⟨KP, hKP, houtput⟩ := hGA q (25 / 3) C_CZ (11 / 16) (43 / 64)
    ε₀ KUinitial KD hq (by norm_num) (by norm_num) hC
      (by norm_num) (by norm_num) (by norm_num) hε₀ hKUinitial hKD
  refine ⟨KP, hKP, ?_⟩
  intro Ω I u f Du p hsol hdom hsmall hU hD
  obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := houtput hsol hdom hU hD hsmall
  refine ⟨Dp, ?_, hInt, hweak, ?_⟩
  · simpa only [spaceTimeSet] using hAE
  · intro i
    have hmin : min (((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹) q = 25 / 11 := by
      rw [show ((1 / (25 / 3 : ℝ)) + 8 / 25)⁻¹ = 25 / 11 by norm_num]
      exact min_eq_left (by linarith only [hq])
    simpa only [hmin] using hN i

/-- The existential form at `(τ, R₀, R₁) = (25, 5/8, 19/32)`, in the exact
shape the closed half-cylinder estimate consumes.  Here the Morrey exponent
stays a minimum: `q` is only known to exceed `5/2`, so `min q (25/9)` cannot
be simplified further. -/
theorem final_pressure_output_of_existential
    (hGA : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
    ∃ KP : ℝ≥0∞, KP < ∞ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∀ i, morreyNorm 3 τ
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
          ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
        ((∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (vec3Ball 0 R₁ ×ˢ I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball 0 R₁ → ∀ i : Fin 3,
            Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
          (∀ i, ∀ ψ : Vec3 × ℝ → ℝ,
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball 0 R₁ ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          (∀ i, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
            ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤ KP))
    (q C_CZ ε₀ : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hC : 0 ≤ C_CZ)
    (hε₀ : 0 ≤ ε₀) (hKU : KU < ⊤) (hKD : KD < ⊤) :
    ∃ KP : ℝ≥0∞, KP < ⊤ ∧
        ∀ (Ω : Set Vec3) (I : Set ℝ)
          (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
          (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        (∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
          (fun z => u z i)) ≤ KU) →
        (∀ i j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
          (fun z => Du z i j)) ≤ KD) →
        ∃ Dp : ParabolicPoint → Vec3,
          (∀ i, AEMeasurable (fun z => Dp z i)
            (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) (19 / 32)) I))) ∧
          (∀ (U : Set Vec3) (J : Set ℝ), localBox Ω I U J →
            U ⊆ vec3Ball (0 : Vec3) (19 / 32) →
            ∀ i, Integrable (fun z => Dp z i) (volume.restrict (spaceTimeSet U J))) ∧
          (∀ (i : Fin 3) (ψ : Vec3 × ℝ → ℝ),
            ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
            tsupport ψ ⊆ vec3Ball (0 : Vec3) (19 / 32) ×ˢ I →
            (∫ z : ParabolicPoint, p z * spatialPartial ψ i z) =
              -(∫ z : ParabolicPoint, Dp z i * ψ z)) ∧
          ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
            ((parabolicCylinder (0 : Vec3) 0 (19 / 32)).indicator (fun z => Dp z i)) ≤ KP := by
  obtain ⟨KP, hKP, houtput⟩ := hGA q 25 C_CZ (5 / 8) (19 / 32)
    ε₀ KU KD hq (by norm_num) (by norm_num) hC
      (by norm_num) (by norm_num) (by norm_num) hε₀ hKU hKD
  refine ⟨KP, hKP, ?_⟩
  intro Ω I u f Du p hsol hdom hsmall hU hD
  obtain ⟨Dp, hAE, hInt, hweak, hN⟩ := houtput hsol hdom hU hD hsmall
  refine ⟨Dp, ?_, hInt, hweak, ?_⟩
  · simpa only [spaceTimeSet] using hAE
  · intro i
    have hexp : ((1 / (25 : ℝ)) + 8 / 25)⁻¹ = 25 / 9 := by norm_num
    simpa only [hexp, min_comm] using hN i

end CKN.Core.Endgame
