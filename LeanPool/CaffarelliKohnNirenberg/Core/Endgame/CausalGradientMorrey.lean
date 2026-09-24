/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalSources
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalLinearSources
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalConvection
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalForceSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability

/-! # Quantitative bounds for the actual gradient-slot source

The five terms of the localized equation are estimated from the improved
velocity norm, the initial gradient norm, the supplied pressure-gradient
norm, and the original force smallness. The formula includes the pressure
gradient in the order-two slot. No potential or Hölder estimate is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- The numerical bound for a component of the final order-two source. -/
def causalGradientMorreyBound (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    3 * KU * KD + forceSourceMorreyBound q ε₀ + KP

/-- Finite input bounds give a finite numerical source bound. -/
theorem causalGradientMorreyBound_lt_top
    (q ε₀ C : ℝ) {KU KD KP : ℝ≥0∞} (hq : 5 / 2 < q)
    (hKU : KU < ⊤) (hKD : KD < ⊤) (hKP : KP < ⊤) :
    causalGradientMorreyBound q ε₀ C KU KD KP < ⊤ := by
  have hvol : volume (parabolicCylinder (0 : Vec3) 0 1) ^ (5 / 6 - 1 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne
  have hforce := forceSourceMorreyBound_lt_top q ε₀ hq
  unfold causalGradientMorreyBound
  finiteness

private theorem norm_neg {P τ : ℝ} (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun z => -f z) = morreyNorm P τ f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

private theorem norm_sub_le {P τ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    morreyNorm P τ (fun z => f z - g z) ≤ morreyNorm P τ f + morreyNorm P τ g := by
  have h := morrey_norm_add_le (τ := τ) hP hf hg.neg
  change morreyNorm P τ (fun z => f z + -g z) ≤
    morreyNorm P τ f + morreyNorm P τ (fun z => -g z) at h
  rw [norm_neg] at h
  simpa only [sub_eq_add_neg] using h

/-- The concrete past gradient-slot source has the paper exponent and an
explicit uniform bound. The pressure-gradient field must be supplied with
its indicated component norms; its weak-gradient characterization is needed
separately in the representation theorem, not in this algebraic estimate. -/
theorem causal_gradient_source_of_suitableWeakSolution
    (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞) (hq : 5 / 2 < q) (hC : 0 ≤ C)
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ}
    {u f Dp : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hφrange : ∀ z : Vec3 × ℝ, 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (hder : ∀ z : Vec3 × ℝ, z.2 ≤ 0 →
      |timePartial φ z| ≤ C ∧ |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C)
    (hU : ∀ i, morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => Du z i j)) ≤ KD)
    (hDp : ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => Dp z i)) volume)
    (hP : ∀ i, morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => Dp z i)) ≤ KP)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) :
    ∀ i, AEMeasurable (causalGradientSourceComponent φ u Du f Dp i) volume ∧
      morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
        (causalGradientSourceComponent φ u Du f Dp i) ≤
          causalGradientMorreyBound q ε₀ C KU KD KP := by
  obtain ⟨hu, hDu, _, _⟩ := one_sided_indicated_components_aemeasurable hsol hdom
  have hφmeas : AEMeasurable (φ : ParabolicPoint → ℝ) volume :=
    hφ.1.continuous.measurable.aemeasurable
  have htmeas : AEMeasurable (fun z : ParabolicPoint => timePartial φ z) volume :=
    ((timePartial_contDiff_full hφ.1).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hlapcont : Continuous
      (fun z : Vec3 × ℝ => spatialLaplacian (fun x => φ (x, z.2)) z.1) := by
    change Continuous (fun z : Vec3 × ℝ => ∑ j, spatialSecondPartial φ j j z)
    exact continuous_finsetSum _ fun j _ =>
      (spatialSecondPartial_contDiff_full hφ.1 j j).continuous
  have hlapmeas : AEMeasurable
      (fun z : ParabolicPoint => spatialLaplacian (fun x => φ (x, z.2)) z.1) volume :=
    (hlapcont.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hzero := fun z ht hz =>
    cutoff_coefficients_zero_on_past_outside_intermediate hφ.1 hsupp (z := z) ht hz
  have hφzero : ∀ z : ParabolicPoint, z.2 ≤ 0 →
      z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → φ z = 0 := fun z ht hz => (hzero z ht hz).1
  have hφone : ∀ z : ParabolicPoint, z.2 ≤ 0 → |φ z| ≤ 1 := by
    intro z _
    rw [abs_of_nonneg (hφrange z).1]
    exact (hφrange z).2
  have hφunit : ∀ z : ParabolicPoint, z.2 ≤ 0 →
      z ∉ parabolicCylinder (0 : Vec3) 0 1 → φ z = 0 := by
    intro z ht hz
    apply hφzero z ht
    exact fun hm => hz (parabolicCylinder_mono (by norm_num) (by norm_num) hm)
  intro i
  let A := pastMultiplierSource (fun z => timePartial φ z) (fun z => u z i)
  let B := pastMultiplierSource (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1)
    (fun z => u z i)
  let N := {z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => φ z * localizedConvection u Du z i)
  let F := causalForceComponent φ f i
  let P := pastMultiplierSource φ (fun z => Dp z i)
  obtain ⟨hA, hAN⟩ := causal_linear_velocity_source_morrey_le q C KU hq hC
    (fun z => timePartial φ z) (fun z => u z i) htmeas (hu i)
    (fun z ht => (hder z ht).1) (fun z ht hz => (hzero z ht hz).2.1) (hU i)
  obtain ⟨hB, hBN⟩ := causal_linear_velocity_source_morrey_le q C KU hq hC
    (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1) (fun z => u z i) hlapmeas (hu i)
    (fun z ht => (hder z ht).2) (fun z ht hz => (hzero z ht hz).2.2.2) (hU i)
  obtain ⟨hN, hNN⟩ := past_convection_source_morrey_le q KU KD hq φ u Du i
    hφmeas hφone hφzero hu (hDu i) hU (hD i)
  obtain ⟨hF, hFN⟩ := causal_force_source_of_suitableWeakSolution q ε₀ hq hsol hdom
    hφmeas (fun z _ => hφrange z) hφunit hsmall i
  obtain ⟨hP', hPN⟩ := causal_linear_pressure_source_morrey_le q KP φ (fun z => Dp z i)
    hφmeas (hDp i) hφone hφzero (hP i)
  have heq : causalGradientSourceComponent φ u Du f Dp i =
      fun z => A z + B z - N z + F z - P z := by
    funext z
    by_cases ht : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · simp only [causalGradientSourceComponent, A, B, N, F, P,
        pastMultiplierSource, causalForceComponent, indicator_of_mem ht,
        CKN.Core.Step4.localizedGradientSourceG, localizedEquationG]
    · simp only [causalGradientSourceComponent, A, B, N, F, P,
        pastMultiplierSource, causalForceComponent, indicator_of_notMem ht, add_zero, sub_zero]
  rw [heq]
  refine ⟨(((hA.add hB).sub hN).add hF).sub hP', ?_⟩
  have hAB := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6 / 5) hA hB).trans
    (add_le_add hAN hBN)
  have hABN := (norm_sub_le (by norm_num : (1 : ℝ) ≤ 6 / 5) (hA.add hB) hN).trans
    (add_le_add hAB hNN)
  have hABNF := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
    ((hA.add hB).sub hN) hF).trans (add_le_add hABN hFN)
  exact (norm_sub_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (((hA.add hB).sub hN).add hF) hP').trans (add_le_add hABNF hPN)

end CKN.Core.Endgame
