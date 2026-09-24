/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient

/-! # Past-time invariance of the localized gradient-slot sources

The admissible cutoff and the fixed cutoff agree as germs at nonpositive
times. Their actual truncated equation sources therefore agree, including
the pressure gradient in the order-two slot. This is an identity of formulas;
it does not assert the still-needed localized representation theorem.
-/

@[expose] public section

open Set Filter
open scoped Topology
open CKN.Foundation.Parabolic CKN.Core.Step3
open CKN.Core.Step4

noncomputable section
namespace CKN.Core.Endgame

/-- The actual past-time order-two source with the pressure gradient. -/
def causalGradientSourceComponent (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f Dp : ParabolicPoint → Vec3) (i : Fin 3) : ParabolicPoint → ℝ :=
  {z : ParabolicPoint | z.2 ≤ 0}.indicator
    (fun z => localizedGradientSourceG φ u Du f Dp z i)

/-- All coefficients of a smooth cutoff vanish in the past outside its
prescribed intermediate-cylinder support. -/
theorem cutoff_coefficients_zero_on_past_outside_intermediate
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    {z : ParabolicPoint} (ht : z.2 ≤ 0)
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) :
    φ z = 0 ∧ timePartial φ z = 0 ∧
      (∀ j, spatialPartial φ j z = 0) ∧
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
  have hraw : (z.1, z.2) ∉ tsupport φ := fun hmem => hz (hsupp _ hmem ht)
  have hvalue : φ (z.1, z.2) = 0 := image_eq_zero_of_notMem_tsupport hraw
  refine ⟨hvalue,
    timePartial_zero_of_not_mem_tsupport_public hφ hraw,
    fun j => spatialPartial_zero_of_not_mem_tsupport_public hφ hraw j, ?_⟩
  change (∑ j, spatialSecondPartial φ j j z) = 0
  exact Finset.sum_eq_zero fun j _ =>
    spatialSecondPartial_zero_of_not_mem_tsupport_public hφ hraw j j

/-- The actual causal gradient-slot source vanishes outside the intermediate
cylinder, regardless of the fields outside it. -/
theorem causalGradientSourceComponent_zero_outside_intermediate
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f Dp : ParabolicPoint → Vec3) (i : Fin 3) {z : ParabolicPoint}
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) :
    causalGradientSourceComponent φ u Du f Dp i z = 0 := by
  by_cases ht : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
  · obtain ⟨hv, htime, _, hlap⟩ :=
      cutoff_coefficients_zero_on_past_outside_intermediate hφ hsupp ht hz
    simp only [causalGradientSourceComponent, indicator_of_mem ht, localizedGradientSourceG, localizedEquationG,
      hv, htime, hlap, zero_mul, add_zero, sub_zero]
  · exact indicator_of_notMem ht _



end CKN.Core.Endgame
