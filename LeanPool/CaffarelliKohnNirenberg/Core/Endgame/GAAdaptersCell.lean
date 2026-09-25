/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.GAAdapters
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSidedCell

/-! # The pressure-gradient boundary from a cell estimate on the origin cell

`prop:bootstrap` is proved by a finite spatial cover, a slice-wise estimate,
and a passage through Fubini, all of which produce a bound on every Morrey
cell of the gradient rather than on the Morrey seminorm directly.  The
seminorm is the supremum of those cells, so the two forms differ only by one
supremum.

This module records that last step: from a cell estimate carried by the
one-sided cylinder `parabolicCylinder 0 0 R₁`, with the three regularity
conjuncts of the selected gradient field, the explicit-majorant statement
`oneSidedPressureGradientQuantitative` follows, and with it the existential
form the small-data statement consumes.  The hypothesis is stated with the
same numerical binders, the same domain hypothesis
`closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I`, and the same
majorant formula as its conclusion, so nothing is strengthened on the way.

The last four theorems record why the carrier of that hypothesis has to be
the one-sided cylinder.  A symmetric parabolic ball around a point always
contains times strictly after that point, and the closed backward cylinder
around the same point contains none.  Since the closed unit backward cylinder
is itself a space-time product set, the domain hypothesis of `thm:A` does not
imply the corresponding inclusion for any symmetric ball about the origin.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Endgame

/-- The explicit-majorant form of `prop:bootstrap` from a cell estimate on the
origin cell.  Only the Morrey supremum is taken here; the three regularity
conjuncts of the selected gradient field pass through unchanged. -/
theorem pressure_gradient_quantitative_of_origin_cell_producer
    (hcell : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
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
          oneSidedPressureGradientOriginCellOutput R₁
            (min ((1 / τ + 8 / 25)⁻¹) q)
            (oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD) Dp) :
    oneSidedPressureGradientQuantitative := by
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
  refine ⟨oneSidedPressureGradientKP_lt_top q τ C_CZ R₀ R₁ ε KU KD
    hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD, ?_⟩
  intro Ω I u Du p f hsol hdom hU hD hsmall
  obtain ⟨Dp, hAE, hInt, hweak, hcellDp⟩ :=
    hcell q τ C_CZ R₀ R₁ ε KU KD hq hτ hτupper hC hR₁ hR₁R₀ hR₀ hε hKU hKD
      hsol hdom hU hD hsmall
  exact ⟨Dp, hAE, hInt, hweak,
    fun i => pressure_gradient_morrey_bound (fun z r => hcellDp i z r)⟩

/-- The existential form consumed by `thm:A`, from the same cell estimate. -/
theorem pressure_gradient_existential_of_origin_cell_producer
    (hcell : ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 →
    0 ≤ C_CZ →
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε →
    KU < ∞ → KD < ∞ →
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
          oneSidedPressureGradientOriginCellOutput R₁
            (min ((1 / τ + 8 / 25)⁻¹) q)
            (oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD) Dp) :
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
            ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Dp z i)) ≤ KP) :=
  pressure_gradient_existential_of_quantitative
    (pressure_gradient_quantitative_of_origin_cell_producer hcell)

/-- Display `eq:parabolic-ball`: the point advanced in time by half the
squared radius lies in the symmetric parabolic ball of that radius. -/
theorem forwardTime_mem_metricBall (z₀ : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ) :
    ((z₀.1, z₀.2 + ρ ^ 2 / 2) : ParabolicPoint) ∈ Metric.ball z₀ ρ := by
  rw [metricBall_eq_parabolicBall]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hρ
  · linarith only [sq_pos_of_pos hρ]
  · linarith only [sq_pos_of_pos hρ]

/-- A consequence of the cylinder definition `eq:cylinder`: its closure at a
positive radius is the space-time product of a closed spatial ball with a
closed time interval. -/
theorem closure_parabolicCylinder_eq_spaceTimeSet (x : Vec3) (t : ℝ) {r : ℝ}
    (hr : 0 < r) :
    closure (parabolicCylinder x t r) =
      spaceTimeSet {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} (Icc (t - r ^ 2) t) := by
  rw [closure_parabolicCylinder hr]
  rfl

/-- A symmetric parabolic ball is never contained in the closed backward
cylinder about its own centre, at any pair of positive radii. -/
theorem metricBall_not_subset_closure_parabolicCylinder (z₀ : ParabolicPoint)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    ¬ Metric.ball z₀ ρ ⊆ closure (parabolicCylinder z₀.1 z₀.2 r) := by
  intro hsub
  have hmem := hsub (forwardTime_mem_metricBall z₀ hρ)
  rw [closure_parabolicCylinder hr] at hmem
  have hupper : z₀.2 + ρ ^ 2 / 2 ≤ z₀.2 := hmem.2.2
  linarith only [sq_pos_of_pos hρ, hupper]

/-- The domain hypothesis of `thm:A` does not imply the same inclusion for a
symmetric parabolic ball about the origin: the closed unit backward cylinder
is itself an admissible space-time set, and no symmetric ball fits inside it.
This is why the cell estimate consumed above carries its own domain
hypothesis on the one-sided cylinder. -/
theorem exists_spaceTimeSet_without_symmetric_ball {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (Ω : Set Vec3) (I : Set ℝ),
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I ∧
      ¬ Metric.ball oneSidedPressureGradientOrigin ρ ⊆ spaceTimeSet Ω I := by
  refine ⟨_, _,
    (closure_parabolicCylinder_eq_spaceTimeSet (0 : Vec3) 0 (r := 1) one_pos).subset, ?_⟩
  rw [← closure_parabolicCylinder_eq_spaceTimeSet (0 : Vec3) 0 (r := 1) one_pos]
  exact metricBall_not_subset_closure_parabolicCylinder
    oneSidedPressureGradientOrigin hρ one_pos

end CKN.Core.Endgame
