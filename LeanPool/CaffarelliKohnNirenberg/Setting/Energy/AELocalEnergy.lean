/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Integrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.TimeCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Real

/-!
# AELocal Energy

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private theorem oneSidedAverage_norm_sub
    {Λ : ℝ → ℝ} (hΛ : LocallyIntegrable Λ volume) :
    ∀ᵐ t ∂volume, Tendsto
      (fun h : ℝ => ⨍ s in Icc (t - h) t, |Λ s - Λ t|)
      (𝓝[>] 0) (𝓝 0) := by
  have hLDT := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (volume : Measure ℝ) hΛ 1
  filter_upwards [hLDT] with t ht
  have hδ : Tendsto (fun h : ℝ => h / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hid : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds
      simpa only [id_eq, zero_div] using hid.div_const (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact half_pos (by simpa only [mem_Ioi] using hh)
  have hball := ht (w := fun h : ℝ => t - h / 2)
    (δ := fun h => h / 2) hδ
    (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : 0 ≤ h / 2 := le_of_lt
        (half_pos (by simpa only [mem_Ioi] using hh))
      rw [Metric.mem_closedBall]
      simpa only [one_mul, Real.dist_eq, sub_sub_cancel, abs_of_nonneg hh'] using
        (le_refl (h / 2)))
  have heq : ∀ h : ℝ, Metric.closedBall (t - h / 2) (h / 2) = Icc (t - h) t := by
    intro h
    ext s
    rw [Metric.mem_closedBall, mem_Icc]
    constructor
    · intro hs
      have hs' := (abs_le.mp (by simpa [Real.dist_eq] using hs))
      constructor <;> linarith only [hs'.1, hs'.2]
    · rintro ⟨hs₁, hs₂⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith only [hs₁, hs₂]
  have hball' := hball.congr' (Eventually.of_forall (fun h => by rw [heq h]))
  change Tendsto (fun h : ℝ => ⨍ s in Icc (t - h) t, |Λ s - Λ t|)
    (𝓝[>] 0) (𝓝 0) at hball'
  exact hball'

private lemma weighted_cutoff_limit
    {Λ : ℝ → ℝ} (hΛ : LocallyIntegrable Λ volume) :
    ∀ᵐ t ∂volume, Tendsto
      (fun h : ℝ => ∫ s, (-deriv (backwardTimeCutoff t h) s) • Λ s)
      (𝓝[>] 0) (𝓝 (Λ t)) := by
  filter_upwards [oneSidedAverage_norm_sub hΛ] with t ht
  apply tendsto_integral_smul_of_tendsto_average_norm_sub 16 ht
  · filter_upwards [] with h
    exact hΛ.integrableOn_isCompact isCompact_Icc
  · apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] 0) (𝓝 1)).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    exact (backwardTimeCutoff_kernel_integral (t := t) (h := h) hh').symm
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact backwardTimeCutoff_kernel_support (by simpa only [mem_Ioi] using hh)
  · filter_upwards [self_mem_nhdsWithin] with h hh s
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    have hvol : volume.real (Icc (t - h) t) = h := by
      rw [measureReal_def, Real.volume_Icc]
      convert ENNReal.toReal_ofReal (le_of_lt hh') using 1
      ring_nf
    rw [hvol]
    simpa only [abs_neg] using
      (backwardTimeCutoff_abs_deriv_le (t := t) (h := h) (s := s) hh')

private lemma cutoff_tendsto_one_or_zero {t s : ℝ} :
    Tendsto (fun h : ℝ => backwardTimeCutoff t h s) (𝓝[>] 0)
      (𝓝 ((Iio t).indicator (fun _ : ℝ => (1 : ℝ)) s)) := by
  by_cases hs : s < t
  · have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < t - s :=
      (eventually_lt_nhds (sub_pos.mpr hs)).filter_mono nhdsWithin_le_nhds
    have htarget : (Iio t).indicator (fun _ : ℝ => (1 : ℝ)) s = 1 := by
      simp [hs]
    rw [htarget]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] 0) (𝓝 1)).congr'
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hsmall' hh
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    exact (backwardTimeCutoff_eq_one_of_le (t := t) (h := h) (s := s) hh'
      (by linarith only [hsmall'])).symm
  · have hs' : t ≤ s := le_of_not_gt hs
    have htarget : (Iio t).indicator (fun _ : ℝ => (1 : ℝ)) s = 0 := by
      simp [hs]
    rw [htarget]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] 0) (𝓝 0)).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (backwardTimeCutoff_eq_zero_of_ge
      (by simpa only [mem_Ioi] using hh) hs').symm

private lemma cutoff_integral_tendsto
    {g : Vec3 × ℝ → ℝ} (hg : Integrable g volume) (t : ℝ) :
    Tendsto
      (fun h : ℝ => ∫ z, g z * backwardTimeCutoff t h z.2)
      (𝓝[>] 0)
      (𝓝 (∫ z : Vec3 × ℝ in (Set.univ ×ˢ Iio t), g z)) := by
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (F := fun h z => g z * backwardTimeCutoff t h z.2)
    (f := fun z => if z.2 < t then g z else 0)
    (μ := (volume : Measure (Vec3 × ℝ)))
    (fun z => ‖g z‖)
    (by
      filter_upwards [] with h
      exact hg.aestronglyMeasurable.mul
        ((backwardTimeCutoff_smooth (t := t) (h := h)).continuous.measurable.comp
          measurable_snd).aestronglyMeasurable)
    (by
      filter_upwards [] with h
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (backwardTimeCutoff_nonneg (t := t) (h := h) (s := z.2))]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (backwardTimeCutoff_le_one (t := t) (h := h) (s := z.2)))
      hg.norm
    (by
      classical
      filter_upwards [] with z
      have hcut := cutoff_tendsto_one_or_zero (t := t) (s := z.2)
      by_cases hz : z.2 < t
      · have hmem : z ∈ (Set.univ ×ˢ Iio t : Set (Vec3 × ℝ)) := by
          change z.1 ∈ (Set.univ : Set Vec3) ∧ z.2 ∈ Iio t
          simp [hz]
        have hcut' : Tendsto (fun h : ℝ => backwardTimeCutoff t h z.2)
            (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
          simpa [hz] using hcut
        simpa [hz] using hcut'.const_mul (g z)
      · have hmem : z ∉ (Set.univ ×ˢ Iio t : Set (Vec3 × ℝ)) := by
          intro hmem
          exact hz hmem.2
        have hcut' : Tendsto (fun h : ℝ => backwardTimeCutoff t h z.2)
            (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
          simpa [hz] using hcut
        simpa [hz] using hcut'.const_mul (g z))
  have hset : MeasurableSet (Set.univ ×ˢ Iio t : Set (Vec3 × ℝ)) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Iio
  have hind : (∫ z : Vec3 × ℝ, if z.2 < t then g z else 0) =
      ∫ z : Vec3 × ℝ in (Set.univ ×ˢ Iio t), g z := by
    rw [← integral_indicator hset]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z.2 < t
    · have hmem : z ∈ (Set.univ ×ˢ Iio t : Set (Vec3 × ℝ)) := by
        change z.1 ∈ (Set.univ : Set Vec3) ∧ z.2 ∈ Iio t
        simp [hz]
      simp [hmem, hz]
    · have hmem : z ∉ (Set.univ ×ˢ Iio t : Set (Vec3 × ℝ)) := by
        intro hmem
        exact hz hmem.2
      simp [hmem, hz]
  rw [hind] at hDCT
  change Tendsto (fun h : ℝ => ∫ z : Vec3 × ℝ,
      g z * backwardTimeCutoff t h z.2) (𝓝[>] 0)
      (𝓝 (∫ z : Vec3 × ℝ in (Set.univ ×ˢ Iio t), g z))
  exact hDCT

private lemma spatialPartial_eq_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i : Fin 3) :
    spatialPartialProd ψ i z = 0 := by
  change (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec i) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev : (fun x : Vec3 => ψ (x, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with x hx
    by_contra hne
    exact hx (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private lemma timePartial_eq_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    timePartialProd ψ z = 0 := by
  change (fderiv ℝ (fun s : ℝ => ψ (z.1, s)) z.2) 1 = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
    Continuous.prodMk continuous_const continuous_id
  have hev : (fun s : ℝ => ψ (z.1, s)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with s hs
    by_contra hne
    exact hs (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private lemma spatialSecondPartial_eq_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i j : Fin 3) :
    spatialSecondPartialProd ψ i j z = 0 := by
  change spatialPartialProd (fun w => spatialPartialProd ψ i w) j z = 0
  change (fderiv ℝ (fun x : Vec3 => spatialPartialProd ψ i (x, z.2)) z.1)
      (basisVec j) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hzero :
      (fun w : Vec3 × ℝ => spatialPartialProd ψ i w) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen] with w hw
    exact spatialPartial_eq_zero_of_not_mem_tsupport hψ hw i
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev :
      (fun x : Vec3 => spatialPartialProd ψ i (x, z.2)) =ᶠ[𝓝 z.1]
        (fun _ => (0 : ℝ)) := hmap.continuousAt.preimage_mem_nhds hzero
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private theorem tsupport_parabolic_eq_energy (g : ParabolicPoint → ℝ) :
    tsupport g = parabolicHomeomorph ⁻¹' (tsupport fun q : Vec3 × ℝ => g q) := by
  have hsupp : Function.support g =
      parabolicHomeomorph ⁻¹' (Function.support fun q : Vec3 × ℝ => g q) := by
    ext z
    rw [Set.mem_preimage, Function.mem_support, Function.mem_support]
    rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure]

private lemma localEnergyRhs_eq_zero_of_not_mem_tsupport
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {f : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) : localEnergyRhs u p f ψ z = 0 := by
  have hψ0 : ψ z = 0 := by
    by_contra hne
    exact hz (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  have ht : timePartialProd ψ z = 0 := timePartial_eq_zero_of_not_mem_tsupport hψ hz
  have hs : ∀ i : Fin 3, spatialPartialProd ψ i z = 0 := fun i =>
    spatialPartial_eq_zero_of_not_mem_tsupport hψ hz i
  have hss : ∀ i : Fin 3, spatialSecondPartialProd ψ i i z = 0 := fun i =>
    spatialSecondPartial_eq_zero_of_not_mem_tsupport hψ hz i i
  simp [localEnergyRhs, hψ0, ht, hs, hss]

theorem localEnergyRhs_eq_zero_of_not_mem_tsupport_public
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {f : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) : localEnergyRhs u p f ψ z = 0 :=
  localEnergyRhs_eq_zero_of_not_mem_tsupport hψ hz

private lemma localEnergyRhs_eq_zero_of_not_mem_parabolic_tsupport
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {f : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : ParabolicPoint}
    (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
    localEnergyRhs u p f ψ z = 0 := by
  have hz' : (show Vec3 × ℝ from z) ∉ tsupport ψ := by
    intro hmem
    apply hz
    rw [tsupport_parabolic_eq_energy (show ParabolicPoint → ℝ from ψ)]
    exact hmem
  exact localEnergyRhs_eq_zero_of_not_mem_tsupport hψ hz'

private lemma setIntegral_univ_Iio
    {g : Vec3 × ℝ → ℝ} {t : ℝ}
    (hg : IntegrableOn g (Set.univ ×ˢ Iio t) volume) :
    ∫ z : Vec3 × ℝ in (Set.univ ×ˢ Iio t), g z =
      ∫ s in Iio t, ∫ x, g (x, s) := by
  have hgs : IntegrableOn (fun z : ℝ × Vec3 => g z.swap)
      (Iio t ×ˢ Set.univ) ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    exact hg.swap
  calc
    ∫ z in (Set.univ ×ˢ Iio t), g z ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ)) =
        ∫ z in (Iio t ×ˢ Set.univ), g z.swap ∂
          ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
      exact (setIntegral_prod_swap (μ := (volume : Measure Vec3))
        (ν := (volume : Measure ℝ)) Set.univ (Iio t) g).symm
    _ = ∫ s in Iio t, ∫ x, g (x, s) := by
      rw [setIntegral_prod _ hgs]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [setIntegral_univ]
      rfl

private lemma diss_integrable_and_rhs_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    Integrable (fun z => spatialGradientSq u Du z * ψ z) volume ∧
      Integrable (fun z => localEnergyRhs u p f ψ z) volume ∧
      Integrable (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume := by
  have he : Integrable (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume :=
    u_sq_mul_test_integrable hsol hψ
  rcases hsol with ⟨_, _, _, _, _, _, _, _, henergy⟩
  obtain ⟨hdiss, hrhs, -⟩ := henergy ψ hψ hψ_nonneg
  have hdiss_support : Function.support
      (fun z : ParabolicPoint => spatialGradientSq u Du z * ψ z) ⊆
        tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro z hz
    by_contra hnot
    apply hz
    simp only [mul_eq_zero]
    right
    exact not_not.mp (fun hne => hnot (subset_tsupport
      (f := (show ParabolicPoint → ℝ from ψ)) (Function.mem_support.mpr hne)))
  have hrhs_support : Function.support
      (fun z : ParabolicPoint => localEnergyRhs u p f ψ z) ⊆
        tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro z hz
    by_contra hnot
    apply hz
    exact localEnergyRhs_eq_zero_of_not_mem_parabolic_tsupport
      hψ.1 hnot
  have hdiss' : IntegrableOn
      (fun z : ParabolicPoint => spatialGradientSq u Du z * ψ z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := hdiss
  have hrhs' : IntegrableOn
      (fun z : ParabolicPoint => localEnergyRhs u p f ψ z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := by
    simpa only [localEnergyRhs, timePartialProd, spatialSecondPartialProd,
      spatialPartialProd] using hrhs
  refine ⟨(integrableOn_iff_integrable_of_support_subset hdiss_support).mp hdiss',
    (integrableOn_iff_integrable_of_support_subset hrhs_support).mp hrhs', ?_⟩
  exact he

theorem suitableWeakSolution_energy_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    Integrable (fun z => spatialGradientSq u Du z * ψ z) volume ∧
      Integrable (fun z => localEnergyRhs u p f ψ z) volume ∧
      Integrable (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume :=
  diss_integrable_and_rhs_integrable hsol hψ hψ_nonneg

private lemma derivative_cutoff_tendsto
    {e : Vec3 × ℝ → ℝ} (he : Integrable e volume) :
    ∀ᵐ t ∂volume, Tendsto
      (fun h : ℝ => ∫ z, e z * deriv (backwardTimeCutoff t h) z.2)
      (𝓝[>] 0) (𝓝 (-∫ x, e (x, t))) := by
  have hΛ : Integrable (fun s => ∫ x, e (x, s)) volume := he.integral_prod_right
  filter_upwards [weighted_cutoff_limit (Λ := fun s => ∫ x, e (x, s)) hΛ.locallyIntegrable]
    with t ht
  have heq : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (∫ z, e z * deriv (backwardTimeCutoff t h) z.2) =
        -(∫ s, (-deriv (backwardTimeCutoff t h) s) • (∫ x, e (x, s))) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    have hk_meas : AEStronglyMeasurable
        (fun z : Vec3 × ℝ => -deriv (backwardTimeCutoff t h) z.2) volume := by
      exact (((backwardTimeCutoff_smooth (t := t) (h := h)).continuous_deriv
        (by simp)).neg.measurable.comp measurable_snd).aestronglyMeasurable
    have hk_bound : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
        ‖-deriv (backwardTimeCutoff t h) z.2‖ ≤ 16 / h := by
      filter_upwards [] with z
      simpa only [Real.norm_eq_abs, abs_neg] using
        (backwardTimeCutoff_abs_deriv_le (t := t) (h := h) (s := z.2) hh')
    have hke : Integrable
        (fun z : Vec3 × ℝ => (-deriv (backwardTimeCutoff t h) z.2) * e z) volume :=
      he.bdd_mul hk_meas hk_bound
    have hfub := integral_prod_symm
      (fun z : Vec3 × ℝ => (-deriv (backwardTimeCutoff t h) z.2) * e z) hke
    calc
      ∫ z, e z * deriv (backwardTimeCutoff t h) z.2 =
          -∫ z, (-deriv (backwardTimeCutoff t h) z.2) * e z := by
            rw [← integral_neg]
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = -∫ s, ∫ x, (-deriv (backwardTimeCutoff t h) s) * e (x, s) := by
            congr 1
      _ = -∫ s, (-deriv (backwardTimeCutoff t h) s) * (∫ x, e (x, s)) := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with s
            rw [integral_const_mul]
      _ = -(∫ s, (-deriv (backwardTimeCutoff t h) s) • (∫ x, e (x, s))) := by
            congr 1
  exact ht.neg.congr' (heq.mono fun h hh => hh.symm)

private lemma suitableWeakSolution_localEnergyInequality_ae_hfinal_global_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {ψ : Vec3 × ℝ → ℝ},
          Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I) ψ →
            (∀ (z : Vec3 × ℝ), 0 ≤ ψ z) →
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (z : Vec3 × ℝ) => spatialGradientSq u Du z * ψ z) volume →
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (z : Vec3 × ℝ) => localEnergyRhs u p f ψ z) volume →
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (z : Vec3 × ℝ) => vec3EuclideanNorm (u z) ^ 2 * ψ z) volume →
                    (∀ z ∉ spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z = 0) →
                      (∀ z ∉ spaceTimeSet Ω I, vec3EuclideanNorm (u z) ^ 2 * ψ z = 0) →
                        (∀ z ∉ spaceTimeSet Ω I, localEnergyRhs u p f ψ z = 0) →
                          (∀ᵐ (t : ℝ),
                              Tendsto (β := ℝ)
                                (fun h =>
                                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                    fun (z : Vec3 × ℝ) =>
                                    vec3EuclideanNorm (u z) ^ 2 * ψ z *
                                      deriv (backwardTimeCutoff t h) z.2)
                                (𝓝[>] 0)
                                (𝓝
                                  (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                      fun (x : Vec3) =>
                                      vec3EuclideanNorm (u (x, t)) ^ 2 * ψ (x, t)))) →
                            ∀ᵐ (t : ℝ),
                              ((@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                    fun (x : Vec3) =>
                                    vec3EuclideanNorm (u (x, t)) ^ 2 * ψ (x, t)) +
                                  2 *
                                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                      (Measure.restrict volume
                                        (SProd.sprod (α := Set Vec3) univ (Iio t)))
                                      fun z => spatialGradientSq u Du z * ψ z) ≤
                                @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                  (Measure.restrict volume
                                    (SProd.sprod (α := Set Vec3) univ (Iio t)))
                                  fun z => localEnergyRhs u p f ψ z
    := by
  intro Ω I q u Du p f hsol ψ hψ hψ_nonneg hD' hR' hE' hD_zero hE_zero hR_zero hE_lim
  filter_upwards [hE_lim] with t ht
  have hD_t := cutoff_integral_tendsto hD' t
  have hR_t := cutoff_integral_tendsto hR' t
  have hlim_left := hD_t.const_mul (2 : ℝ)
  have hlim_right := hR_t.add ht
  have hineq_t : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      2 * ∫ z : Vec3 × ℝ, spatialGradientSq u Du z * ψ z *
          backwardTimeCutoff t h z.2 ≤
        (∫ z : Vec3 × ℝ, localEnergyRhs u p f ψ z * backwardTimeCutoff t h z.2)
          + (∫ z : Vec3 × ℝ, (vec3EuclideanNorm (u z)) ^ 2 * ψ z *
              deriv (backwardTimeCutoff t h) z.2) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    have hχ : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => backwardTimeCutoff t h z.2) := by
      exact (backwardTimeCutoff_smooth (t := t) (h := h)).comp contDiff_snd
    have htest := spaceTimeTestFunction_mul_smooth hψ
      hχ
    have htest_nonneg : ∀ z, 0 ≤ ψ z * backwardTimeCutoff t h z.2 := by
      intro z
      exact mul_nonneg (hψ_nonneg z)
        (backwardTimeCutoff_nonneg (t := t) (h := h) (s := z.2))
    have hineq := suitableWeakSolution_energyInequality hsol htest htest_nonneg
    have hineq' :
        2 * ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
            spatialGradientSq u Du z * ψ z * backwardTimeCutoff t h z.2 ≤
          ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
            localEnergyRhs u p f (fun w => ψ w * backwardTimeCutoff t h w.2) z := by
      change 2 * ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
          spatialGradientSq u Du z * (ψ z * backwardTimeCutoff t h z.2) ≤
        ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
          localEnergyRhs u p f (fun w => ψ w * backwardTimeCutoff t h w.2) z at hineq
      simpa only [mul_assoc] using hineq
    have hDzero : ∀ z : Vec3 × ℝ, z ∉ (Ω ×ˢ I) →
        spatialGradientSq u Du z * ψ z * backwardTimeCutoff t h z.2 = 0 := by
      intro z hz
      have hz' : (show ParabolicPoint from z) ∉ spaceTimeSet Ω I := by
        intro hz'
        exact hz ⟨hz'.1, hz'.2⟩
      simp [hD_zero z hz']
    have hRzero : ∀ z : Vec3 × ℝ, z ∉ (Ω ×ˢ I) →
        localEnergyRhs u p f ψ z * backwardTimeCutoff t h z.2 = 0 := by
      intro z hz
      have hz' : (show ParabolicPoint from z) ∉ spaceTimeSet Ω I := by
        intro hz'
        exact hz ⟨hz'.1, hz'.2⟩
      simp [hR_zero z hz']
    have hEzero : ∀ z : Vec3 × ℝ, z ∉ (Ω ×ˢ I) →
        (vec3EuclideanNorm (u z)) ^ 2 * ψ z *
            deriv (backwardTimeCutoff t h) z.2 = 0 := by
      intro z hz
      have hz' : (show ParabolicPoint from z) ∉ spaceTimeSet Ω I := by
        intro hz'
        exact hz ⟨hz'.1, hz'.2⟩
      simp [hE_zero z hz']
    have hsplit : ∫ z : Vec3 × ℝ in (Ω ×ˢ I), localEnergyRhs u p f
        (fun w => ψ w * backwardTimeCutoff t h w.2) z =
        ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
          (localEnergyRhs u p f ψ z * backwardTimeCutoff t h z.2
            + (vec3EuclideanNorm (u z)) ^ 2 * ψ z *
              deriv (backwardTimeCutoff t h) z.2) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact localEnergyRhs_mul_time hψ.1
        (backwardTimeCutoff_smooth (t := t) (h := h)) (z := z)
    have hDset := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure (Vec3 × ℝ))) hDzero
    have hRset := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure (Vec3 × ℝ))) hRzero
    have hEset := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure (Vec3 × ℝ))) hEzero
    have hR_int : Integrable
        (fun z : Vec3 × ℝ => localEnergyRhs u p f ψ z *
          backwardTimeCutoff t h z.2) volume := by
      apply hR'.mul_bdd
      · exact ((backwardTimeCutoff_smooth (t := t) (h := h)).continuous.comp
          continuous_snd).measurable.aestronglyMeasurable
      · filter_upwards [] with z
        rw [Real.norm_eq_abs, abs_of_nonneg
          (backwardTimeCutoff_nonneg (t := t) (h := h) (s := z.2))]
        exact backwardTimeCutoff_le_one (t := t) (h := h) (s := z.2)
    have hE_int : Integrable
        (fun z : Vec3 × ℝ => (vec3EuclideanNorm (u z)) ^ 2 * ψ z *
          deriv (backwardTimeCutoff t h) z.2) volume := by
      apply hE'.mul_bdd
      · exact (((backwardTimeCutoff_smooth (t := t) (h := h)).continuous_deriv
          (by simp)).comp continuous_snd).measurable.aestronglyMeasurable
      · filter_upwards [] with z
        have hbound := backwardTimeCutoff_abs_deriv_le
          (t := t) (h := h) (s := z.2) hh'
        simpa only [Real.norm_eq_abs] using hbound
    calc
      2 * ∫ z : Vec3 × ℝ,
          spatialGradientSq u Du z * ψ z * backwardTimeCutoff t h z.2 =
          2 * ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
            spatialGradientSq u Du z * ψ z * backwardTimeCutoff t h z.2 := by
              rw [hDset]
      _ ≤ ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
          localEnergyRhs u p f (fun w => ψ w * backwardTimeCutoff t h w.2) z := hineq'
      _ = ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
          (localEnergyRhs u p f ψ z * backwardTimeCutoff t h z.2
            + (vec3EuclideanNorm (u z)) ^ 2 * ψ z *
              deriv (backwardTimeCutoff t h) z.2) := hsplit
      _ = (∫ z : Vec3 × ℝ in (Ω ×ˢ I),
            localEnergyRhs u p f ψ z * backwardTimeCutoff t h z.2)
          + ∫ z : Vec3 × ℝ in (Ω ×ˢ I),
            (vec3EuclideanNorm (u z)) ^ 2 * ψ z *
              deriv (backwardTimeCutoff t h) z.2 := by
            simpa only [Pi.add_apply] using
              (integral_add' hR_int.integrableOn hE_int.integrableOn)
      _ = (∫ z : Vec3 × ℝ,
            localEnergyRhs u p f ψ z * backwardTimeCutoff t h z.2)
          + ∫ z : Vec3 × ℝ,
            (vec3EuclideanNorm (u z)) ^ 2 * ψ z *
              deriv (backwardTimeCutoff t h) z.2 := by
            rw [hRset, hEset]
  have hlim := tendsto_le_of_eventuallyLE hlim_left hlim_right hineq_t
  linarith only [hlim]

/-- The local energy inequality for almost every time slice. -/
theorem suitableWeakSolution_localEnergyInequality_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    ∀ᵐ t ∂(volume.restrict I),
      (∫ x in Ω, (vec3EuclideanNorm (u (x, t))) ^ 2 * ψ (x, t))
        + 2 * ∫ s in Iio t, ∫ x in Ω,
            spatialGradientSq u Du (x, s) * ψ (x, s)
        ≤ ∫ s in Iio t, ∫ x in Ω, localEnergyRhs u p f ψ (x, s) := by
  obtain ⟨hD, hR, hE⟩ := diss_integrable_and_rhs_integrable hsol hψ hψ_nonneg
  have hD' : Integrable
      (fun z : Vec3 × ℝ => spatialGradientSq u Du z * ψ z) volume := hD
  have hR' : Integrable
      (fun z : Vec3 × ℝ => localEnergyRhs u p f ψ z) volume := hR
  have hE' : Integrable
      (fun z : Vec3 × ℝ => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume := hE
  have hψ_zero : ∀ z : ParabolicPoint, z ∉ spaceTimeSet Ω I → ψ z = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hne' : ψ (show Vec3 × ℝ from z) ≠ 0 := hne
    exact hψ.2.2 (subset_tsupport (f := ψ) (Function.mem_support.mpr hne'))
  have hD_zero : ∀ z : ParabolicPoint, z ∉ spaceTimeSet Ω I →
      spatialGradientSq u Du z * ψ z = 0 := by
    intro z hz
    simp [hψ_zero z hz]
  have hE_zero : ∀ z : ParabolicPoint, z ∉ spaceTimeSet Ω I →
      (vec3EuclideanNorm (u z)) ^ 2 * ψ z = 0 := by
    intro z hz
    simp [hψ_zero z hz]
  have hR_zero : ∀ z : ParabolicPoint, z ∉ spaceTimeSet Ω I →
      localEnergyRhs u p f ψ z = 0 := by
    intro z hz
    rcases z with ⟨x, s⟩
    apply localEnergyRhs_eq_zero_of_not_mem_parabolic_tsupport hψ.1
    intro hmem
    have hmem' : (x, s) ∈ tsupport ψ := by
      have hmem'' := hmem
      rw [tsupport_parabolic_eq_energy] at hmem''
      exact hmem''
    exact hz (hψ.2.2 hmem')
  have hE_lim := derivative_cutoff_tendsto hE'
  have hfinal_global := @suitableWeakSolution_localEnergyInequality_ae_hfinal_global_1 Ω I q u Du
    p f hsol ψ hψ hψ_nonneg hD' hR' hE' hD_zero hE_zero hR_zero hE_lim
  have hfinal_restrict : ∀ᵐ t ∂(volume.restrict I),
      (∫ x, (vec3EuclideanNorm (u (x, t))) ^ 2 * ψ (x, t))
        + 2 * ∫ z in (Set.univ ×ˢ Iio t), spatialGradientSq u Du z * ψ z
        ≤ ∫ z in (Set.univ ×ˢ Iio t), localEnergyRhs u p f ψ z :=
    ae_restrict_of_ae hfinal_global
  filter_upwards [hfinal_restrict] with t ht
  have hD_slice : ∀ s, ∫ x, spatialGradientSq u Du (x, s) * ψ (x, s) =
      ∫ x in Ω, spatialGradientSq u Du (x, s) * ψ (x, s) := by
    intro s
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : (show ParabolicPoint from (x, s)) ∉ spaceTimeSet Ω I := by
      intro hmem
      exact hx hmem.1
    simp [hψ_zero (show ParabolicPoint from (x, s)) hz]
  have hR_slice : ∀ s, ∫ x, localEnergyRhs u p f ψ (x, s) =
      ∫ x in Ω, localEnergyRhs u p f ψ (x, s) := by
    intro s
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply localEnergyRhs_eq_zero_of_not_mem_tsupport hψ.1
    intro hmem
    exact hx (hψ.2.2 hmem).1
  have hE_slice : ∀ s, ∫ x, (vec3EuclideanNorm (u (x, s))) ^ 2 * ψ (x, s) =
      ∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * ψ (x, s) := by
    intro s
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : (show ParabolicPoint from (x, s)) ∉ spaceTimeSet Ω I := by
      intro hmem
      exact hx hmem.1
    simp [hψ_zero (show ParabolicPoint from (x, s)) hz]
  rw [setIntegral_univ_Iio (hD'.integrableOn.mono_set (Set.subset_univ _)),
    setIntegral_univ_Iio (hR'.integrableOn.mono_set (Set.subset_univ _))] at ht
  have hDtime : ∫ s in Iio t, ∫ x in Ω,
        spatialGradientSq u Du (x, s) * ψ (x, s) =
      ∫ s in Iio t, ∫ x,
        spatialGradientSq u Du (x, s) * ψ (x, s) := by
    apply integral_congr_ae
    filter_upwards [] with s
    exact (hD_slice s).symm
  have hRtime : ∫ s in Iio t, ∫ x,
        localEnergyRhs u p f ψ (x, s) =
      ∫ s in Iio t, ∫ x in Ω,
        localEnergyRhs u p f ψ (x, s) := by
    apply integral_congr_ae
    filter_upwards [] with s
    exact hR_slice s
  rw [hDtime, ← hE_slice t, ← hRtime]
  exact ht

end CKN
