/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSidedCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradient

/-!
# Pressure Gradient One Sided Origin

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-! The origin carrier is the backward cylinder.  The slice estimate used by
the pressure construction is therefore consumed directly on that carrier;
there is no symmetric time window in this interface. -/

/-- Existence interface for a measurable weak pressure gradient with normalized-cylinder cell
bounds. -/
def oneSidedPressureGradientOriginCellProducer : Prop :=
  ∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
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
            (oneSidedPressureGradientKP q τ C_CZ R₀ R₁ ε KU KD) Dp

theorem oneSidedPressureGradientOriginScalarSlice_of_vector_slice
    {R₀ : ℝ} {p : ParabolicPoint → ℝ} {K : ℝ → ℝ≥0∞}
    (hD : ∀ᵐ s ∂(volume.restrict (Ioc (-R₀ ^ 2) 0)),
      ∃ D : Vec3 → Vec3,
        (∀ j : Fin 3, LocallyIntegrableOn (fun x => D x j)
          (euclideanBall (0 : Vec3) (R₀ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) (R₀ / 2))) ∧
        (∀ j : Fin 3, HasWeakPartialDerivOn
          (euclideanBall (0 : Vec3) (R₀ / 2)) j
          (fun x => p (x, s)) (fun x => D x j)) ∧
        (∀ j : Fin 3, eLpNorm (fun x => D x j)
          (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) (R₀ / 2))) ≤ K s)) :
    ∀ j : Fin 3, ∀ᵐ s ∂(volume.restrict (Ioc (-R₀ ^ 2) 0)),
      ∃ g : Vec3 → ℝ,
        LocallyIntegrableOn g (euclideanBall (0 : Vec3) (R₀ / 2)) volume ∧
        HasWeakPartialDerivOn (euclideanBall (0 : Vec3) (R₀ / 2)) j
          (fun x => p (x, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) (R₀ / 2))) ≤ K s := by
  intro j
  exact exists_scalar_slice_gradient_of_vector_slice j hD

private theorem origin_kappa_lower_bound
    {q τ : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    6 / 5 ≤ min ((1 / τ + 8 / 25)⁻¹) q := by
  apply le_min
  · have hτpos : 0 < τ := by linarith only [hτ]
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
    convert hrecip using 1 <;> norm_num
  · linarith only [hq]

theorem oneSidedPressureGradientOriginCellOutput_of_past_slice_bounds
    {R₁ κ : ℝ} {A B : ℝ≥0∞} {Dp : ParabolicPoint → Vec3}
    (hR₁ : 0 < R₁) (hR₁quarter : R₁ < 3 / 4)
    (hκ : 6 / 5 ≤ κ)
    (hsmall : ∀ i : Fin 3, ∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
      ∀ r : ℝ, 0 < r → r ≤ R₁ →
      cylinderPowerIntegral (6 / 5 : ℝ) (fun w => Dp w i) z r ≤
        A * ENNReal.ofReal
          (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))))
    (hglobal : ∀ i : Fin 3,
      (∫⁻ w in parabolicCylinder (0 : Vec3) 0 R₁,
        ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤ B) :
    oneSidedPressureGradientOriginCellOutput R₁ κ
      (oneSidedMorreyBound (6 / 5) κ R₁
        A B) Dp := by
  intro i z r
  have hnorm := morreyNorm_one_sided_indicator_le_on_cylinder
    R₁ (6 / 5) κ R₁ A B
    hR₁ hR₁quarter (by norm_num) hκ hR₁ (fun w => Dp w i)
    (hsmall i) (hglobal i)
  have hcell : morreyCell (6 / 5 : ℝ) κ
      ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
        (fun w => Dp w i)) z r.1 ≤
      morreyNorm (6 / 5 : ℝ) κ
        ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
          (fun w => Dp w i)) := by
    unfold morreyNorm
    exact le_iSup_of_le z (le_iSup_of_le r le_rfl)
  exact hcell.trans hnorm

end CKN.Core.Step4
