/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TwoPointMixture
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# A measurable kernel of mean-one two-point laws

This file supplies the measurable-kernel interface needed to condition on
the latent two-point parameters in the proof of Theorem 2.1.
-/

open MeasureTheory ProbabilityTheory Set

namespace Feige

noncomputable section

/-- Evaluation of the two-point law on a Borel set is measurable in both
support points. -/
theorem measurable_twoPointMeasure_apply {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun p : ℝ × ℝ ↦ twoPointMeasure p.1 p.2 B) := by
  simp only [twoPointMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hB]
  unfold twoPointLowerWeight twoPointUpperWeight
  fun_prop

/-- Admissible parameters `x ≤ 1 ≤ y`, with distinct support points. -/
def TwoPointParams :=
  {p : ℝ × ℝ // p.1 ≤ 1 ∧ 1 ≤ p.2 ∧ p.1 < p.2}

instance : MeasurableSpace TwoPointParams :=
  MeasurableSpace.comap Subtype.val inferInstance

/-- The Markov kernel sending `(x,y)` to the mean-one two-point law
`Q_{x,y}`. -/
noncomputable def twoPointKernel : Kernel TwoPointParams ℝ where
  toFun p := twoPointMeasure p.1.1 p.1.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    exact (measurable_twoPointMeasure_apply hB).comp measurable_subtype_coe

@[simp] theorem twoPointKernel_apply (p : TwoPointParams) :
    twoPointKernel p = twoPointMeasure p.1.1 p.1.2 :=
  rfl

instance : IsMarkovKernel twoPointKernel where
  isProbabilityMeasure p :=
    twoPointMeasure_isProbability p.2.1 p.2.2.1 p.2.2.2

theorem twoPointKernel_mean (p : TwoPointParams) :
    (∫ z : ℝ, z ∂(twoPointKernel p)) = 1 := by
  rw [twoPointKernel_apply]
  exact twoPointMeasure_mean p.2.1 p.2.2.1 p.2.2.2

theorem twoPointKernel_nonnegative_support (p : TwoPointParams)
    (hx : 0 ≤ p.1.1) :
    twoPointKernel p (Iio 0) = 0 := by
  rw [twoPointKernel_apply, twoPointMeasure]
  simp only [Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iio]
  have hy : 0 ≤ p.1.2 := le_trans (by norm_num) p.2.2.1
  simp [not_lt_of_ge hx, not_lt_of_ge hy]

/-- The genuine measure obtained by sampling latent two-point parameters and
then sampling from their two-point law. -/
noncomputable def kernelTwoPointMixture (ν : Measure TwoPointParams) : Measure ℝ :=
  twoPointKernel ∘ₘ ν

instance (ν : Measure TwoPointParams) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (kernelTwoPointMixture ν) := by
  unfold kernelTwoPointMixture
  infer_instance

/-- The `Measure.bind` formula for the two-point mixture. -/
theorem kernelTwoPointMixture_apply (ν : Measure TwoPointParams)
    {B : Set ℝ} (hB : MeasurableSet B) :
    kernelTwoPointMixture ν B =
      ∫⁻ p, twoPointMeasure p.1.1 p.1.2 B ∂ν := by
  rw [kernelTwoPointMixture, Measure.bind_apply hB twoPointKernel.aemeasurable]
  rfl

/-- Averaging a pointwise probability bound over latent parameters. -/
theorem kernelTwoPointMixture_apply_le
    (ν : Measure TwoPointParams) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) {c : ENNReal}
    (hc : ∀ p : TwoPointParams, twoPointMeasure p.1.1 p.1.2 B ≤ c) :
    kernelTwoPointMixture ν B ≤ c := by
  rw [kernelTwoPointMixture_apply ν hB]
  calc
    (∫⁻ p, twoPointMeasure p.1.1 p.1.2 B ∂ν) ≤ ∫⁻ _p, c ∂ν :=
      lintegral_mono fun p ↦ hc p
    _ = c := by simp

/-- The strict below-above region used for the nondegenerate latent pair. -/
def strictPairSet : Set (ℝ × ℝ) :=
  {p | p.1 < 1 ∧ 1 < p.2}

theorem measurableSet_strictPairSet : MeasurableSet strictPairSet := by
  exact (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_snd)

/-- Every strict below-above pair is an admissible two-point parameter. -/
theorem strictPairSet_admissible {p : ℝ × ℝ} (hp : p ∈ strictPairSet) :
    p.1 ≤ 1 ∧ 1 ≤ p.2 ∧ p.1 < p.2 :=
  ⟨hp.1.le, hp.2.le, hp.1.trans hp.2⟩

/-- Classical decidability for membership in the strict parameter region. -/
local instance : DecidablePred (· ∈ strictPairSet) :=
  Classical.decPred _

/-- A total measurable map into `TwoPointParams`; outside the strict region
we use the harmless default pair `(0,2)`.  The weighted latent measure below
is supported on the strict region. -/
noncomputable def pairToParams (p : ℝ × ℝ) : TwoPointParams :=
  if hp : p ∈ strictPairSet then ⟨p, strictPairSet_admissible hp⟩
  else ⟨(0, 2), by norm_num⟩

theorem measurable_pairToParams : Measurable pairToParams := by
  let f : ℝ × ℝ → ℝ × ℝ :=
    fun p ↦ if p ∈ strictPairSet then p else (0, 2)
  have hf : Measurable f :=
    Measurable.ite measurableSet_strictPairSet measurable_id measurable_const
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap pairToParams
      (MeasurableSpace.comap (fun p : TwoPointParams ↦ p.val)
        (inferInstance : MeasurableSpace (ℝ × ℝ))) ≤
    (inferInstance : MeasurableSpace (ℝ × ℝ))
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun p ↦ (pairToParams p).val)
      (inferInstance : MeasurableSpace (ℝ × ℝ)) ≤
    (inferInstance : MeasurableSpace (ℝ × ℝ))
  rw [show (fun p ↦ (pairToParams p).val) = f by
    funext p
    by_cases hp : p ∈ strictPairSet <;> simp [pairToParams, f, hp]]
  exact hf.comap_le

/-- The unnormalized product law on a strict below point and a strict above
point. -/
noncomputable def belowAboveProduct (μ : Measure ℝ) : Measure (ℝ × ℝ) :=
  (μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))

/-- The density `(y-x)/M` of the latent below/above pair, written in
`ℝ≥0∞`. -/
noncomputable def latentPairDensity (M : ℝ) (p : ℝ × ℝ) : ENNReal :=
  (ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)

theorem measurable_latentPairDensity (M : ℝ) :
    Measurable (latentPairDensity M) := by
  unfold latentPairDensity
  fun_prop

/-- The concrete weighted below×above latent measure. -/
noncomputable def latentPairMeasure (μ : Measure ℝ) (M : ℝ) :
    Measure (ℝ × ℝ) :=
  (belowAboveProduct μ).withDensity (latentPairDensity M)

theorem strictPairSet_eq_prod :
    strictPairSet = Iio (1 : ℝ) ×ˢ Ioi (1 : ℝ) := by
  ext p
  rfl

theorem belowAboveProduct_compl_strictPairSet (μ : Measure ℝ) [SFinite μ] :
    belowAboveProduct μ strictPairSetᶜ = 0 := by
  rw [belowAboveProduct, Measure.prod_restrict,
    strictPairSet_eq_prod,
    Measure.restrict_apply (measurableSet_Iio.prod measurableSet_Ioi).compl]
  simp

/-- The weighted latent pair measure has no mass outside the strict
below×above parameter region. -/
theorem latentPairMeasure_compl_strictPairSet (μ : Measure ℝ) [SFinite μ] (M : ℝ) :
    latentPairMeasure μ M strictPairSetᶜ = 0 := by
  rw [latentPairMeasure, withDensity_apply _ measurableSet_strictPairSet.compl]
  exact setLIntegral_measure_zero strictPairSetᶜ (latentPairDensity M)
    (belowAboveProduct_compl_strictPairSet μ)

instance (μ : Measure ℝ) [SFinite μ] (M : ℝ) :
    SFinite (latentPairMeasure μ M) := by
  unfold latentPairMeasure belowAboveProduct
  infer_instance

/-- The weighted pair measure, transported to the admissible parameter
subtype on which `twoPointKernel` is Markov. -/
noncomputable def latentParamsMeasure (μ : Measure ℝ) (M : ℝ) :
    Measure TwoPointParams :=
  (latentPairMeasure μ M).map pairToParams

theorem latentParamsMeasure_apply (μ : Measure ℝ) (M : ℝ)
    {A : Set TwoPointParams} (hA : MeasurableSet A) :
    latentParamsMeasure μ M A =
      latentPairMeasure μ M (pairToParams ⁻¹' A) := by
  rw [latentParamsMeasure, Measure.map_apply measurable_pairToParams hA]

/-- The resulting genuine kernel mixture of the nondegenerate latent
component. -/
noncomputable def nondegenerateKernelMixture (μ : Measure ℝ) (M : ℝ) :
    Measure ℝ :=
  kernelTwoPointMixture (latentParamsMeasure μ M)

/-- The absolute-value definition of the lower moment is the usual
restricted first moment below one. -/
theorem belowMoment_eq_integral_Iio (μ : Measure ℝ) :
    belowMoment μ = ∫ x in Iio (1 : ℝ), 1 - x ∂μ := by
  rw [← integral_indicator measurableSet_Iio]
  unfold belowMoment
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x < 1
  · have hxmem : x ∈ Iio (1 : ℝ) := hx
    rw [Set.indicator_of_mem hxmem]
    rw [abs_of_neg (sub_neg.mpr hx)]
    ring
  · have hxmem : x ∉ Iio (1 : ℝ) := hx
    rw [Set.indicator_of_notMem hxmem]
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx))]
    ring

/-- The absolute-value definition of the upper moment is the usual
restricted first moment above one. -/
theorem aboveMoment_eq_integral_Ioi (μ : Measure ℝ) :
    aboveMoment μ = ∫ y in Ioi (1 : ℝ), y - 1 ∂μ := by
  rw [← integral_indicator measurableSet_Ioi]
  unfold aboveMoment
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : 1 < y
  · have hymem : y ∈ Ioi (1 : ℝ) := hy
    rw [Set.indicator_of_mem hymem]
    rw [abs_of_pos (sub_pos.mpr hy)]
    ring
  · have hymem : y ∉ Ioi (1 : ℝ) := hy
    rw [Set.indicator_of_notMem hymem]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt hy))]
    ring

theorem ofReal_belowMoment_eq_lintegral_Iio
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    ENNReal.ofReal (belowMoment μ) =
      ∫⁻ x in Iio (1 : ℝ), ENNReal.ofReal (1 - x) ∂μ := by
  rw [belowMoment_eq_integral_Iio]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact ((integrable_const 1).sub hμ).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact sub_nonneg.mpr hx.le

theorem ofReal_aboveMoment_eq_lintegral_Ioi
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    ENNReal.ofReal (aboveMoment μ) =
      ∫⁻ y in Ioi (1 : ℝ), ENNReal.ofReal (y - 1) ∂μ := by
  rw [aboveMoment_eq_integral_Ioi]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (hμ.sub (integrable_const 1)).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact sub_nonneg.mpr hy.le

/-- Tonelli expansion of the total mass of the nondegenerate latent pair
measure. -/
theorem latentPairMeasure_univ
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (M : ℝ) :
    latentPairMeasure μ M Set.univ =
      (ENNReal.ofReal M)⁻¹ *
        (μ (Iio 1) * ENNReal.ofReal (aboveMoment μ) +
          ENNReal.ofReal (belowMoment μ) * μ (Ioi 1)) := by
  rw [latentPairMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  unfold latentPairDensity belowAboveProduct
  rw [lintegral_const_mul]
  · have hae :
        (fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 - p.1)) =ᵐ[
          (μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))]
        (fun p ↦ ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)) := by
      have hf : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 - p.1)) := by
        fun_prop
      have hg : Measurable (fun p : ℝ × ℝ ↦
          ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)) := by
        fun_prop
      have heqmeas : MeasurableSet {p : ℝ × ℝ |
          ENNReal.ofReal (p.2 - p.1) =
            ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)} := by
        rw [show {p : ℝ × ℝ |
            ENNReal.ofReal (p.2 - p.1) =
              ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)} =
            {p | ENNReal.ofReal (p.2 - p.1) ≤
              ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)} ∩
            {p | ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1) ≤
              ENNReal.ofReal (p.2 - p.1)} by
                ext p
                simp only [mem_ofPred_eq, mem_inter_iff]
                constructor
                · intro h
                  exact ⟨h.le, h.ge⟩
                · rintro ⟨h₁, h₂⟩
                  exact le_antisymm h₁ h₂]
        exact (measurableSet_le hf hg).inter (measurableSet_le hg hf)
      apply (Measure.ae_prod_iff_ae_ae heqmeas).2
      filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hy.le)
        (sub_nonneg.mpr hx.le)]
      congr 1
      ring
    rw [lintegral_congr_ae hae]
    rw [lintegral_add_left (by fun_prop)]
    have hfirst :
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (p.2 - 1)
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        (∫⁻ _x : ℝ, (1 : ENNReal) ∂μ.restrict (Iio 1)) *
          ∫⁻ y : ℝ, ENNReal.ofReal (y - 1) ∂μ.restrict (Ioi 1) := by
      simpa using
        (lintegral_prod_mul (μ := μ.restrict (Iio 1))
          (ν := μ.restrict (Ioi 1))
          (f := fun _x : ℝ ↦ (1 : ENNReal))
          (g := fun y : ℝ ↦ ENNReal.ofReal (y - 1))
          (by fun_prop) (by fun_prop))
    have hsecond :
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (1 - p.1)
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        (∫⁻ x : ℝ, ENNReal.ofReal (1 - x) ∂μ.restrict (Iio 1)) *
          ∫⁻ _y : ℝ, (1 : ENNReal) ∂μ.restrict (Ioi 1) := by
      simpa using
        (lintegral_prod_mul (μ := μ.restrict (Iio 1))
          (ν := μ.restrict (Ioi 1))
          (f := fun x : ℝ ↦ ENNReal.ofReal (1 - x))
          (g := fun _y : ℝ ↦ (1 : ENNReal))
          (by fun_prop) (by fun_prop))
    rw [hfirst, hsecond]
    simp only [lintegral_one, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    rw [← ofReal_aboveMoment_eq_lintegral_Ioi hμ,
      ← ofReal_belowMoment_eq_lintegral_Iio hμ]
  · fun_prop

theorem mass_below_add_above
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ (Iio 1) + μ (Ioi 1) = 1 - μ {1} := by
  have hparts := congrArg (fun ν : Measure ℝ ↦ ν Set.univ)
    (restrict_below_add_atom_add_above μ)
  simp only [Measure.add_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.smul_apply, measure_univ,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem
      (Set.mem_univ (1 : ℝ)), Pi.one_apply, smul_eq_mul, mul_one] at hparts
  apply ENNReal.eq_sub_of_add_eq' (by simp)
  calc
    μ (Iio 1) + μ (Ioi 1) + μ {1} =
        μ (Iio 1) + μ {1} + μ (Ioi 1) := by ac_rfl
    _ = 1 := hparts

/-- In the mean-one positive-moment branch, the nondegenerate latent
component has precisely the mass outside the atom at one. -/
theorem latentPairMeasure_univ_meanOne
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    latentPairMeasure μ (belowMoment μ) Set.univ = 1 - μ {1} := by
  rw [latentPairMeasure_univ hμ]
  rw [← belowMoment_eq_aboveMoment hμ hmean]
  let a : ENNReal := ENNReal.ofReal (belowMoment μ)
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hM)
  have hatop : a ≠ ⊤ := by simp [a]
  change a⁻¹ * (μ (Iio 1) * a + a * μ (Ioi 1)) = 1 - μ {1}
  calc
    a⁻¹ * (μ (Iio 1) * a + a * μ (Ioi 1)) =
        a⁻¹ * (a * (μ (Iio 1) + μ (Ioi 1))) := by
          congr 1
          rw [mul_comm (μ (Iio 1)) a, mul_add]
    _ = μ (Iio 1) + μ (Ioi 1) :=
      ENNReal.inv_mul_cancel_left ha0 hatop
    _ = 1 - μ {1} := mass_below_add_above μ

/-- The full kernel mixture: the atom at one plus the nondegenerate latent
two-point component. -/
noncomputable def fullKernelMixture (μ : Measure ℝ) (M : ℝ) : Measure ℝ :=
  μ {1} • Measure.dirac 1 + nondegenerateKernelMixture μ M

theorem nondegenerateKernelMixture_univ
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    nondegenerateKernelMixture μ (belowMoment μ) Set.univ =
      1 - μ {1} := by
  rw [nondegenerateKernelMixture, kernelTwoPointMixture_apply _
    MeasurableSet.univ]
  have hmap :
      latentParamsMeasure μ (belowMoment μ) Set.univ =
        latentPairMeasure μ (belowMoment μ) Set.univ := by
    rw [latentParamsMeasure, Measure.map_apply measurable_pairToParams
      MeasurableSet.univ]
    simp
  rw [show (∫⁻ p : TwoPointParams,
      twoPointMeasure p.1.1 p.1.2 Set.univ
        ∂latentParamsMeasure μ (belowMoment μ)) =
      latentParamsMeasure μ (belowMoment μ) Set.univ by
        rw [← lintegral_one]
        apply lintegral_congr
        intro p
        let := twoPointMeasure_isProbability p.2.1 p.2.2.1 p.2.2.2
        exact measure_univ]
  rw [hmap, latentPairMeasure_univ_meanOne hμ hmean hM]

theorem fullKernelMixture_isProbability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    IsProbabilityMeasure (fullKernelMixture μ (belowMoment μ)) := by
  constructor
  rw [fullKernelMixture, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ (1 : ℝ)), Pi.one_apply,
    smul_eq_mul, mul_one,
    nondegenerateKernelMixture_univ hμ hmean hM]
  apply add_tsub_cancel_of_le
  calc
    μ ({1} : Set ℝ) ≤ μ Set.univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

/-- Pull the nondegenerate kernel mixture back from the parameter subtype to
the original weighted pair measure.  This is the change-of-variables layer
in the Borel-set verification of the two-point mixture formula. -/
theorem nondegenerateKernelMixture_apply_pair
    (μ : Measure ℝ) (M : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    nondegenerateKernelMixture μ M B =
      ∫⁻ p : ℝ × ℝ,
        twoPointMeasure (pairToParams p).1.1 (pairToParams p).1.2 B
          ∂latentPairMeasure μ M := by
  rw [nondegenerateKernelMixture, kernelTwoPointMixture_apply _ hB]
  rw [latentParamsMeasure]
  have hf : Measurable (fun q : TwoPointParams ↦
      twoPointMeasure q.1.1 q.1.2 B) := by
    exact (measurable_twoPointMeasure_apply hB).comp measurable_subtype_coe
  rw [lintegral_map hf measurable_pairToParams]

theorem nondegenerateKernelMixture_apply_strict
    (μ : Measure ℝ) [SFinite μ] (M : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    nondegenerateKernelMixture μ M B =
      ∫⁻ p : ℝ × ℝ, twoPointMeasure p.1 p.2 B
        ∂latentPairMeasure μ M := by
  rw [nondegenerateKernelMixture_apply_pair μ M hB]
  apply lintegral_congr_ae
  filter_upwards [compl_mem_ae_iff.2
    (latentPairMeasure_compl_strictPairSet μ M)] with p hp
  have hps : p ∈ strictPairSet := by simpa only [compl_compl] using hp
  simp [pairToParams, hps]

theorem nondegenerateKernelMixture_apply_expanded
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (M : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    nondegenerateKernelMixture μ M B =
      (ENNReal.ofReal M)⁻¹ *
        (ENNReal.ofReal (aboveMoment μ) * μ.restrict (Iio 1) B +
          ENNReal.ofReal (belowMoment μ) * μ.restrict (Ioi 1) B) := by
  have hdirac : Measurable (fun x : ℝ ↦ Measure.dirac x B) := by
    simp only [Measure.dirac_apply' _ hB]
    exact measurable_const.indicator hB
  rw [nondegenerateKernelMixture_apply_strict μ M hB]
  rw [latentPairMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_latentPairDensity M)
    (measurable_twoPointMeasure_apply hB)]
  unfold latentPairDensity belowAboveProduct
  have hae :
      (fun p : ℝ × ℝ ↦
        ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
          twoPointMeasure p.1 p.2 B) =ᵐ[
        (μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))]
      (fun p ↦ (ENNReal.ofReal M)⁻¹ *
        (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
          ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) := by
    apply (Measure.ae_prod_iff_ae_ae (by
      have hf : Measurable (fun p : ℝ × ℝ ↦
          ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
            twoPointMeasure p.1 p.2 B) := by
        exact (measurable_const.mul
          ((measurable_snd.sub measurable_fst).ennreal_ofReal)).mul
            (measurable_twoPointMeasure_apply hB)
      have hg : Measurable (fun p : ℝ × ℝ ↦ (ENNReal.ofReal M)⁻¹ *
          (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
            ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) := by
        exact measurable_const.mul
          (((measurable_snd.sub measurable_const).ennreal_ofReal.mul
              (hdirac.comp measurable_fst)).add
            ((measurable_const.sub measurable_fst).ennreal_ofReal.mul
              (hdirac.comp measurable_snd)))
      rw [show {p | (fun p : ℝ × ℝ ↦
          ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
            twoPointMeasure p.1 p.2 B) p =
          (fun p ↦ (ENNReal.ofReal M)⁻¹ *
            (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
              ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) p} =
          {p | (fun p : ℝ × ℝ ↦
            ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
              twoPointMeasure p.1 p.2 B) p ≤
            (fun p ↦ (ENNReal.ofReal M)⁻¹ *
              (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
                ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) p} ∩
          {p | (fun p : ℝ × ℝ ↦ (ENNReal.ofReal M)⁻¹ *
              (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
                ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) p ≤
            (fun p ↦
              ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
                twoPointMeasure p.1 p.2 B) p} by
            ext p
            simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_antisymm_iff]]
      exact (measurableSet_le hf hg).inter (measurableSet_le hg hf))).2
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hs := twoPointMeasure_scaled_apply hx.le hy.le (hx.trans hy) B
    calc
      ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (y - x)) *
          twoPointMeasure x y B =
        (ENNReal.ofReal M)⁻¹ *
          (ENNReal.ofReal (y - x) * twoPointMeasure x y B) := by ac_rfl
      _ = _ := by rw [hs]
  change (∫⁻ p : ℝ × ℝ,
      ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
        twoPointMeasure p.1 p.2 B
      ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) = _
  rw [lintegral_congr_ae hae]
  have hterm1 : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B) :=
    (measurable_snd.sub measurable_const).ennreal_ofReal.mul
      (hdirac.comp measurable_fst)
  have hterm2 : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B) :=
    (measurable_const.sub measurable_fst).ennreal_ofReal.mul
      (hdirac.comp measurable_snd)
  rw [lintegral_const_mul]
  case hf => exact hterm1.add hterm2
  rw [lintegral_add_left hterm1]
  have hfirst :
      (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        μ.restrict (Iio 1) B * ENNReal.ofReal (aboveMoment μ) := by
    rw [show (fun p : ℝ × ℝ ↦
        ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B) =
      fun p ↦ Measure.dirac p.1 B * ENNReal.ofReal (p.2 - 1) by
        funext p; ac_rfl]
    rw [lintegral_prod_mul
      (μ := μ.restrict (Iio 1)) (ν := μ.restrict (Ioi 1))
      (f := fun x ↦ Measure.dirac x B)
      (g := fun y ↦ ENNReal.ofReal (y - 1))
      hdirac.aemeasurable (by fun_prop)]
    rw [show (∫⁻ x, Measure.dirac x B ∂μ.restrict (Iio 1)) =
        μ.restrict (Iio 1) B by
          simp only [Measure.dirac_apply' _ hB]
          rw [← lintegral_indicator_one hB]]
    rw [← ofReal_aboveMoment_eq_lintegral_Ioi hμ]
  have hsecond :
      (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        ENNReal.ofReal (belowMoment μ) * μ.restrict (Ioi 1) B := by
    rw [lintegral_prod_mul
      (μ := μ.restrict (Iio 1)) (ν := μ.restrict (Ioi 1))
      (f := fun x ↦ ENNReal.ofReal (1 - x))
      (g := fun y ↦ Measure.dirac y B)
      (by fun_prop) hdirac.aemeasurable]
    rw [show (∫⁻ y, Measure.dirac y B ∂μ.restrict (Ioi 1)) =
        μ.restrict (Ioi 1) B by
          simp only [Measure.dirac_apply' _ hB]
          rw [← lintegral_indicator_one hB]]
    rw [← ofReal_belowMoment_eq_lintegral_Iio hμ]
  rw [hfirst, hsecond, mul_comm (μ.restrict (Iio 1) B)]

/-- The measurable-kernel construction agrees with the direct expansion of
the two-point mixture formula. -/
theorem fullKernelMixture_eq_expanded
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (M : ℝ) :
    fullKernelMixture μ M = expandedTwoPointMixture μ M := by
  ext B hB
  rw [fullKernelMixture, expandedTwoPointMixture, Measure.add_apply,
    Measure.add_apply, nondegenerateKernelMixture_apply_expanded hμ M hB]
  simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]

/-- For a mean-one probability law with a nonzero lower moment, sampling the
latent pair and then the corresponding two-point law reconstructs the
original law. -/
theorem fullKernelMixture_eq
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    fullKernelMixture μ (belowMoment μ) = μ := by
  rw [fullKernelMixture_eq_expanded hμ,
    expandedTwoPointMixture_eq hμ hmean hM]

end

end Feige
