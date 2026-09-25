/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalEquationRepresentation
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalSources
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalLinearSources
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapLinearSources
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalForceSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability

/-! # Quantitative bounds for the actual gradient-slot source

The five terms of the localized equation are estimated from the improved
velocity norm, the initial gradient norm, the supplied pressure-gradient
norm, and the original force smallness. The formula includes the pressure
gradient in the order-two slot. No potential or Hölder estimate is assumed.
-/

@[expose] public section

section

/-! # The past-time convective heat source

The initial velocity exponent and initial gradient exponent give the
convective source estimate by scalar Morrey Hölder and the finite-sum
triangle inequality. Only the cutoff's nonpositive-time values are used.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- Component source bounds give the actual past convection source's
measurability and quantitative paper-exponent Morrey bound. -/
theorem bootstrap_past_convection_source_morrey_le (KU KD : ℝ≥0∞)
    (φ : ParabolicPoint → ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (i : Fin 3)
    (hφ : AEMeasurable φ volume)
    (hφbound : ∀ z : ParabolicPoint, z.2 ≤ 0 → |φ z| ≤ 1)
    (hφsupp : ∀ z : ParabolicPoint, z.2 ≤ 0 →
      z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16) → φ z = 0)
    (hu : ∀ j, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z j)) volume)
    (hDu : ∀ j, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Du z i j)) volume)
    (hUN : ∀ j, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z j)) ≤ KU)
    (hDN : ∀ j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Du z i j)) ≤ KD) :
    AEMeasurable ({z : ParabolicPoint | z.2 ≤ 0}.indicator
      (fun z => φ z * localizedConvection u Du z i)) volume ∧
    morreyNorm (6 / 5) ((25 / 11))
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => φ z * localizedConvection u Du z i)) ≤ 3 * KU * KD := by
  let S := parabolicCylinder (0 : Vec3) 0 (11 / 16)
  let U : Fin 3 → ParabolicPoint → ℝ := fun j => S.indicator (fun z => u z j)
  let D : Fin 3 → ParabolicPoint → ℝ := fun j => S.indicator (fun z => Du z i j)
  let B : ParabolicPoint → ℝ := fun z => ∑ j, U j z * D j z
  let a : ParabolicPoint → ℝ := {z : ParabolicPoint | z.2 ≤ 0}.indicator φ
  have hterm : ∀ j, AEMeasurable (fun z => U j z * D j z) volume :=
    fun j => (hu j).mul (hDu j)
  have hB : AEMeasurable B volume := by
    simpa [B, Fin.sum_univ_succ, Pi.add_def] using (hterm 0).add ((hterm 1).add (hterm 2))
  have ha : AEMeasurable a volume :=
    hφ.indicator (measurableSet_le measurable_snd measurable_const)
  have haone : ∀ z, |a z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · simpa only [a, indicator_of_mem hz] using hφbound z hz
    · simp only [a, indicator_of_notMem hz, abs_zero, zero_le_one]
  have heq : {z : ParabolicPoint | z.2 ≤ 0}.indicator
      (fun z => φ z * localizedConvection u Du z i) = (fun z => a z * B z) := by
    funext z
    by_cases hz : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · by_cases hzS : z ∈ S
      · simp only [a, B, U, D, indicator_of_mem hz, indicator_of_mem hzS, localizedConvection]
      · simp only [a, indicator_of_mem hz, hφsupp z hz hzS, zero_mul]
    · simp only [a, indicator_of_notMem hz, zero_mul]
  have hprod : ∀ j, morreyNorm (6 / 5) (25 / 11) (fun z => U j z * D j z) ≤ KU * KD := by
    intro j
    have h := morreyNorm_holder (p := 6 / 5) (p₁ := 3) (p₂ := 2)
      (q := 25 / 11) (q₁ := 25 / 3) (q₂ := 25 / 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (hu j) (hDu j)
    exact h.trans (mul_le_mul (hUN j) (hDN j) (by positivity) (by positivity))
  have h12 := (morrey_norm_add_le (τ := 25 / 11) (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (hterm 1) (hterm 2)).trans (add_le_add (hprod 1) (hprod 2))
  have hsum := (morrey_norm_add_le (τ := 25 / 11) (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (hterm 0) ((hterm 1).add (hterm 2))).trans (add_le_add (hprod 0) h12)
  have hBN : morreyNorm (6 / 5) (25 / 11) B ≤ 3 * KU * KD := by
    have hthree : KU * KD + (KU * KD + KU * KD) = 3 * KU * KD := by ring
    simpa [B, Fin.sum_univ_succ, hthree] using hsum
  have hmul : morreyNorm (6 / 5) (25 / 11) (fun z => a z * B z) ≤
      morreyNorm (6 / 5) (25 / 11) B := by
    apply morreyNorm_mono (by norm_num)
    intro z
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (haone z) (abs_nonneg (B z))
  rw [heq]
  exact ⟨ha.mul hB, hmul.trans hBN⟩

end CKN.Core.Endgame
end

end

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- Every component of the velocity, weak gradient, pressure, and force,
indicated to the intermediate one-sided cylinder, is globally a.e.
measurable. All measurability is supplied by the local solution clauses. -/
theorem bootstrap_indicated_components_aemeasurable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hunit : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I) :
    (∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z i)) volume) ∧
    (∀ i j, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Du z i j)) volume) ∧
    AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator p) volume ∧
    ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => f z i)) volume := by
  obtain ⟨Ω', J, hbox, _hJopen, hunitbox⟩ :=
    exists_localBox_around_closed_unit hsol.1 hsol.2.1 hunit
  have hsub : parabolicCylinder (0 : Vec3) 0 (11 / 16) ⊆ spaceTimeSet Ω' J :=
    (parabolicCylinder_mono (by norm_num : (0 : ℝ) ≤ 11 / 16)
      (by norm_num : (11 / 16 : ℝ) ≤ 1)).trans (subset_closure.trans hunitbox)
  have hmeasure := Measure.restrict_mono (μ := volume) hsub le_rfl
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hu := hdata.1.aemeasurable.mono_measure hmeasure
  have hDu := hdata.2.1.aemeasurable.mono_measure hmeasure
  have hp := hdata.2.2.1.aemeasurable.mono_measure hmeasure
  have hf := hdata.2.2.2.1.aemeasurable.mono_measure hmeasure
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (11 / 16)) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  refine ⟨?_, ?_, (aemeasurable_indicator_iff hS).mpr hp, ?_⟩
  · intro i
    exact (aemeasurable_indicator_iff hS).mpr (aemeasurable_pi_iff.mp hu i)
  · intro i j
    exact (aemeasurable_indicator_iff hS).mpr
      (aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hDu i) j)
  · intro i
    exact (aemeasurable_indicator_iff hS).mpr (aemeasurable_pi_iff.mp hf i)


/-- Past cutoff coefficients vanish outside the larger initial cylinder. -/
theorem bootstrap_cutoff_coefficients_zero
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (11 / 16))
    {z : ParabolicPoint} (ht : z.2 ≤ 0)
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16)) :
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


/-- Both literal source slots vanish outside any cylinder containing the
cutoff's past support. This statement also applies to the smaller support
cylinder used inside the initial norm carrier. -/
theorem bootstrap_literal_sources_zero_on_past
    {R : ℝ} {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 R)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f Dp : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (ht : z.2 ≤ 0) (hz : z ∉ parabolicCylinder (0 : Vec3) 0 R) :
    CKN.Core.Step4.localizedGradientSourceG φ u Du f Dp z = 0 ∧
      ∀ j, CKN.Core.Step4.localizedGradientSourceH φ u j z = 0 := by
  have hraw : (z.1, z.2) ∉ tsupport φ := fun hm => hz (hsupp _ hm ht)
  have hv : φ (z.1, z.2) = 0 := image_eq_zero_of_notMem_tsupport hraw
  have ht' : timePartial φ z = 0 := timePartial_zero_of_not_mem_tsupport_public hφ hraw
  have hx : ∀ j, spatialPartial φ j z = 0 :=
    fun j => spatialPartial_zero_of_not_mem_tsupport_public hφ hraw j
  have hlap : spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    change (∑ j, spatialSecondPartial φ j j z) = 0
    exact Finset.sum_eq_zero fun j _ =>
      spatialSecondPartial_zero_of_not_mem_tsupport_public hφ hraw j j
  constructor
  · funext i
    change timePartial φ z * u z i +
      spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i -
      φ z * localizedConvection u Du z i + φ z * f z i - φ z * Dp z i = 0
    change φ z = 0 at hv
    simp only [ht', hlap, hv, zero_mul, add_zero, sub_zero]
  · intro j
    funext i
    change (-2 * spatialPartial φ j z) * u z i = 0
    rw [hx j, mul_zero, zero_mul]

/-- The numerical bound for a component of the first order-two source. -/
def bootstrapGradientMorreyBound (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    ENNReal.ofReal C * (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) +
    3 * KU * KD + forceSourceMorreyBound q ε₀ + KP

/-- Finite input bounds give a finite numerical source bound. -/
theorem bootstrapGradientMorreyBound_lt_top
    (q ε₀ C : ℝ) {KU KD KP : ℝ≥0∞} (hq : 5 / 2 < q)
    (hKU : KU < ⊤) (hKD : KD < ⊤) (hKP : KP < ⊤) :
    bootstrapGradientMorreyBound q ε₀ C KU KD KP < ⊤ := by
  have hvol : volume (parabolicCylinder (0 : Vec3) 0 1) ^ (5 / 6 - 1 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne
  have hforce := forceSourceMorreyBound_lt_top q ε₀ hq
  unfold bootstrapGradientMorreyBound
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
theorem bootstrap_gradient_source_of_suitableWeakSolution
    (q ε₀ C : ℝ) (KU KD KP : ℝ≥0∞) (hq : 5 / 2 < q) (hC : 0 ≤ C)
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 × ℝ → ℝ}
    {u f Dp : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hφrange : ∀ z : Vec3 × ℝ, 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (11 / 16))
    (hder : ∀ z : Vec3 × ℝ, z.2 ≤ 0 →
      |timePartial φ z| ≤ C ∧ |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C)
    (hU : ∀ i, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => Du z i j)) ≤ KD)
    (hDp : ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Dp z i)) volume)
    (hP : ∀ i, morreyNorm (6 / 5) ((25 / 11 : ℝ))
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => Dp z i)) ≤ KP)
    (hsmall : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) :
    ∀ i, AEMeasurable (causalGradientSourceComponent φ u Du f Dp i) volume ∧
      morreyNorm (6 / 5) ((25 / 11 : ℝ))
        (causalGradientSourceComponent φ u Du f Dp i) ≤
          bootstrapGradientMorreyBound q ε₀ C KU KD KP := by
  obtain ⟨hu, hDu, _, _⟩ := bootstrap_indicated_components_aemeasurable hsol hdom
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
    bootstrap_cutoff_coefficients_zero hφ.1 hsupp (z := z) ht hz
  have hφzero : ∀ z : ParabolicPoint, z.2 ≤ 0 →
      z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16) → φ z = 0 := fun z ht hz => (hzero z ht hz).1
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
  obtain ⟨hA, hAN⟩ := bootstrap_causal_linear_velocity_source_morrey_le C KU hC
    (fun z => timePartial φ z) (fun z => u z i) htmeas (hu i)
    (fun z ht => (hder z ht).1) (fun z ht hz => (hzero z ht hz).2.1) (hU i)
  obtain ⟨hB, hBN⟩ := bootstrap_causal_linear_velocity_source_morrey_le C KU hC
    (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1) (fun z => u z i) hlapmeas (hu i)
    (fun z ht => (hder z ht).2) (fun z ht hz => (hzero z ht hz).2.2.2) (hU i)
  obtain ⟨hN, hNN⟩ := bootstrap_past_convection_source_morrey_le KU KD φ u Du i
    hφmeas hφone hφzero hu (hDu i) hU (hD i)
  obtain ⟨hF, hFN⟩ := causal_force_source_of_suitableWeakSolution q ε₀ hq hsol hdom
    hφmeas (fun z _ => hφrange z) hφunit hsmall i
  have hFlow := morreyNorm_lower_morrey_exponent (p := (6 / 5 : ℝ))
    (f := causalForceComponent φ f i)
    (q := min q (25 / 9 : ℝ)) (q' := (25 / 11 : ℝ))
    (by norm_num) (le_min (by linarith only [hq]) (by norm_num))
    (by norm_num) (le_min (by linarith only [hq]) (by norm_num))
    (z₀ := ((0, 0) : ParabolicPoint)) one_pos
    (fun z hz => causalForceComponent_zero_outside_unit (f := f) hφunit i hz)
  simp only [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] at hFlow
  have hFN' := hFlow.trans hFN
  obtain ⟨hP', hPN⟩ := bootstrap_causal_linear_pressure_source_morrey_le KP φ (fun z => Dp z i)
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
    ((hA.add hB).sub hN) hF).trans (add_le_add hABN hFN')
  exact (norm_sub_le (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (((hA.add hB).sub hN).add hF) hP').trans (add_le_add hABNF hPN)

end CKN.Core.Endgame
