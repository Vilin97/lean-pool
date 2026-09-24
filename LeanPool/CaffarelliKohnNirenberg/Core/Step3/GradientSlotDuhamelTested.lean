/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.GradientSlotDuhamelAtoms
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.GradientSlotDuhamelTransfers
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.GradientSlotDuhamelSplit
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationConvectionTransfer

/-!
# Gradient Slot Duhamel Tested

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Core.Step4


noncomputable section

namespace CKN.Core.Step3

/-!
# Trading the divergence-form pressure slot for the gradient slot

Paper label `lem:local-equation`. The cutoff-tested identity for the localized
velocity is first obtained with the pressure sitting in the divergence-form
slot, as `p ∂ᵢφ` together with the diagonal entry `δᵢⱼ p φ`.  The estimates of
Step 4 instead need the pressure as `φ Dp` in the heat slot, the convection in
the form `φ (u · ∇) u`, and the second cutoff derivative `Δφ u` explicit.  The
theorem below performs that exchange once and for all at the level of the
tested identity: the divergence-form right-hand side and the gradient-slot
right-hand side agree for every space-time test function.  The three inputs are
the convection transfer (`∑ⱼ ∫ uᵢuⱼ ∂ⱼ(φψ) = −∫ φψ (u · ∇)uᵢ`), the diffusion
transfer (one integration by parts in `∂ⱼφ ψ`) and the weak pressure gradient
tested against the product cutoff `φψ`.
-/

/-- An integrable factor times a continuous compactly supported factor is
integrable. -/
private lemma integrable_mul_of_compact_continuous
    {a : ParabolicPoint → ℝ} (ha : Integrable a volume)
    {b : Vec3 × ℝ → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun z : ParabolicPoint => a z * b z) volume := by
  obtain ⟨C, hC⟩ := hbc.exists_bound_of_continuous hb
  exact ha.mul_bdd hb.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hC z)

/-- The divergence-form and gradient-slot right-hand sides of the tested local
equation agree, for every space-time test function `ψ`.  Paper label
`lem:local-equation`: this is the passage from the raw tested identity to the
displayed equation `eq:local-equation`, in which the pressure enters through
its weak gradient `Dp`. -/
theorem gradientSlot_tested_transfer_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {Dp : ParabolicPoint → Vec3}
    (hDpInt : ∀ i : Fin 3, Integrable (fun z => Dp z i)
      (volume.restrict (spaceTimeSet Ω' J)))
    (hDpweak : ∀ i : Fin 3, ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      tsupport χ ⊆ Ω' ×ˢ J →
      (∫ z : ParabolicPoint, p z * spatialPartial χ i z) =
        -(∫ z : ParabolicPoint, Dp z i * χ z))
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    (i : Fin 3) :
    (∫ z : ParabolicPoint, localizedDivergenceG φ u Du p f z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          localizedDivergenceH φ u p j z i * spatialPartial ψ j z =
      (∫ z : ParabolicPoint, localizedGradientSourceG φ u Du f Dp z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9⟩ :=
    gradientSlot_tested_integrable_of_sws hsol hφ hbox hφbox hDpInt hψ i
  obtain ⟨-, hGInt, hHInt, -, -, -⟩ :=
    localized_divergence_source_data_of_sws hsol hφ hbox hφbox
  obtain ⟨hGradInt, hGradHInt, -, -⟩ :=
    localized_gradient_source_data_of_sws hsol hφ hbox hφbox hDpInt
  have hφd : ContDiff ℝ (⊤ : ℕ∞) φ := hφ.1
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := hψ.1
  have hψc : HasCompactSupport ψ := hψ.2.1
  have hψsp (j : Fin 3) : Continuous
      (fun z : Vec3 × ℝ => spatialPartial ψ j z) :=
    (spatialPartial_contDiff hψd j).continuous
  have hψspc (j : Fin 3) : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial ψ j z) := by
    apply HasCompactSupport.of_support_subset_isCompact hψc.isCompact
    intro z hz
    by_contra hnot
    exact hz (spatialPartial_zero_of_not_mem_tsupport_public hψd hnot j)
  have hGdivψ : Integrable (fun z : ParabolicPoint =>
      localizedDivergenceG φ u Du p f z i * ψ z) volume :=
    integrable_mul_of_compact_continuous (hGInt i) hψd.continuous hψc
  have hHdivψ (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      localizedDivergenceH φ u p j z i * spatialPartial ψ j z) volume :=
    integrable_mul_of_compact_continuous (hHInt j i) (hψsp j) (hψspc j)
  have hGgradψ : Integrable (fun z : ParabolicPoint =>
      localizedGradientSourceG φ u Du f Dp z i * ψ z) volume :=
    integrable_mul_of_compact_continuous (hGradInt i) hψd.continuous hψc
  have hHgradψ (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z) volume :=
    integrable_mul_of_compact_continuous (hGradHInt j i) (hψsp j) (hψspc j)
  have hAint : Integrable (fun z : ParabolicPoint =>
      u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) volume :=
    hA1.add hA2
  have hBint : Integrable (fun z : ParabolicPoint =>
      ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) volume :=
    integrable_finsetSum _ (fun j _ => hA3 j)
  have hnegD (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      -(Du z i j * (spatialPartial φ j z * ψ z))) volume := (hA4 j).neg
  have hA5two (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    (hA5 j).const_mul 2
  have hCjint (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      -(Du z i j * (spatialPartial φ j z * ψ z)) +
        u z i * (spatialPartial φ j z * spatialPartial ψ j z)) volume :=
    (hnegD j).add (hA5 j)
  have hCint : Integrable (fun z : ParabolicPoint =>
      ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
        u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    integrable_finsetSum _ (fun j _ => hCjint j)
  have hB'int : Integrable (fun z : ParabolicPoint =>
      -((φ z * ψ z) * localizedConvection u Du z i)) volume := hA9.neg
  have hC'jint (j : Fin 3) : Integrable (fun z : ParabolicPoint =>
      u z i * (spatialSecondPartial φ j j z * ψ z) +
        2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    (hA6 j).add (hA5two j)
  have hC'int : Integrable (fun z : ParabolicPoint =>
      ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
        2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) volume :=
    integrable_finsetSum _ (fun j _ => hC'jint j)
  have hD'int : Integrable (fun z : ParabolicPoint =>
      -(Dp z i * (φ z * ψ z))) volume := hA8.neg
  have hABint : Integrable (fun z : ParabolicPoint =>
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) volume :=
    hAint.add hBint
  have hABCint : Integrable (fun z : ParabolicPoint =>
      ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
          ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
        ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
          u z i * (spatialPartial φ j z * spatialPartial ψ j z))) volume :=
    hABint.add hCint
  have hAB'int : Integrable (fun z : ParabolicPoint =>
      (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
        -((φ z * ψ z) * localizedConvection u Du z i)) volume :=
    hAint.add hB'int
  have hAB'C'int : Integrable (fun z : ParabolicPoint =>
      ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
          -((φ z * ψ z) * localizedConvection u Du z i)) +
        ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
          2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) volume :=
    hAB'int.add hC'int
  have hHdivψsum : Integrable (fun z : ParabolicPoint =>
      ∑ j, localizedDivergenceH φ u p j z i * spatialPartial ψ j z) volume :=
    integrable_finsetSum _ (fun j _ => hHdivψ j)
  have hHgradψsum : Integrable (fun z : ParabolicPoint =>
      ∑ j, (-localizedGradientSourceH φ u j z i) *
        spatialPartial ψ j z) volume :=
    integrable_finsetSum _ (fun j _ => hHgradψ j)
  have hBeq : (∫ z : ParabolicPoint,
      ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) =
      ∫ z : ParabolicPoint, -((φ z * ψ z) * localizedConvection u Du z i) := by
    rw [integral_finsetSum _ (fun j _ => hA3 j), integral_neg]
    exact localized_convection_transfer_no_trace hsol hφ hbox hφbox hψ i
  have hCeq : (∫ z : ParabolicPoint,
      ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
        u z i * (spatialPartial φ j z * spatialPartial ψ j z))) =
      ∫ z : ParabolicPoint,
        ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
          2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z))) := by
    rw [integral_finsetSum _ (fun j _ => hCjint j),
      integral_finsetSum _ (fun j _ => hC'jint j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_add (hnegD j) (hA5 j), integral_neg,
      integral_add (hA6 j) (hA5two j), integral_const_mul]
    exact gradientSlot_diffusion_transfer_of_sws hsol hφ hbox hφbox hψ i j
  have hDeq : (∫ z : ParabolicPoint,
      p z * spatialPartial (fun w => φ w * ψ w) i z) =
      ∫ z : ParabolicPoint, -(Dp z i * (φ z * ψ z)) := by
    rw [integral_neg]
    exact gradientSlot_pressure_transfer hφd hφbox hψ hDpweak i
  calc
    (∫ z : ParabolicPoint, localizedDivergenceG φ u Du p f z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          localizedDivergenceH φ u p j z i * spatialPartial ψ j z =
        ∫ z : ParabolicPoint,
          (localizedDivergenceG φ u Du p f z i * ψ z +
            ∑ j, localizedDivergenceH φ u p j z i * spatialPartial ψ j z) := by
      rw [← integral_finsetSum _ (fun j _ => hHdivψ j),
        ← integral_add hGdivψ hHdivψsum]
    _ = ∫ z : ParabolicPoint,
          ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
            (∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
            (∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
              u z i * (spatialPartial φ j z * spatialPartial ψ j z))) +
            p z * spatialPartial (fun w => φ w * ψ w) i z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      exact gradientSlot_divergence_integrand hφd hψd i z
    _ = ((∫ z : ParabolicPoint,
            (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z))) +
          (∫ z : ParabolicPoint,
            ∑ j, u z i * u z j * spatialPartial (fun w => φ w * ψ w) j z) +
          (∫ z : ParabolicPoint,
            ∑ j, (-(Du z i j * (spatialPartial φ j z * ψ z)) +
              u z i * (spatialPartial φ j z * spatialPartial ψ j z))) +
          (∫ z : ParabolicPoint,
            p z * spatialPartial (fun w => φ w * ψ w) i z)) := by
      rw [integral_add hABCint hA7, integral_add hABint hCint,
        integral_add hAint hBint]
    _ = ((∫ z : ParabolicPoint,
            (u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z))) +
          (∫ z : ParabolicPoint,
            -((φ z * ψ z) * localizedConvection u Du z i)) +
          (∫ z : ParabolicPoint,
            ∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
              2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) +
          (∫ z : ParabolicPoint, -(Dp z i * (φ z * ψ z)))) := by
      rw [hBeq, hCeq, hDeq]
    _ = ∫ z : ParabolicPoint,
          ((u z i * (timePartial φ z * ψ z) + f z i * (φ z * ψ z)) +
            (-((φ z * ψ z) * localizedConvection u Du z i)) +
            (∑ j, (u z i * (spatialSecondPartial φ j j z * ψ z) +
              2 * (u z i * (spatialPartial φ j z * spatialPartial ψ j z)))) +
            (-(Dp z i * (φ z * ψ z)))) := by
      rw [integral_add hAB'C'int hD'int, integral_add hAB'int hC'int,
        integral_add hAint hB'int]
    _ = ∫ z : ParabolicPoint,
          (localizedGradientSourceG φ u Du f Dp z i * ψ z +
            ∑ j, (-localizedGradientSourceH φ u j z i) *
              spatialPartial ψ j z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      exact (gradientSlot_gradient_integrand i z).symm
    _ = (∫ z : ParabolicPoint,
          localizedGradientSourceG φ u Du f Dp z i * ψ z) +
        ∑ j, ∫ z : ParabolicPoint,
          (-localizedGradientSourceH φ u j z i) * spatialPartial ψ j z := by
      rw [integral_add hGgradψ hHgradψsum,
        integral_finsetSum _ (fun j _ => hHgradψ j)]

end CKN.Core.Step3
