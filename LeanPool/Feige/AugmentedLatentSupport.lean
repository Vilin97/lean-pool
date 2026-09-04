/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.MeanOneAugmentedMixture

/-!
# Support of the augmented latent parameterization
-/

open Set MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- The nonnegativity condition on an augmented two-point parameter. -/
def AugmentedParamNonnegative (p : AugmentedTwoPointParams) : Prop :=
  match p with
  | Sum.inl _ => True
  | Sum.inr q => 0 ≤ q.1.1 ∧ 1 < q.1.2

theorem measurableSet_augmentedParamNonnegative :
    MeasurableSet {p : AugmentedTwoPointParams |
      AugmentedParamNonnegative p} := by
  rw [measurableSet_sum_iff]
  constructor
  · simp
  · change MeasurableSet {q : TwoPointParams |
      0 ≤ q.1.1 ∧ 1 < q.1.2}
    exact (measurableSet_le measurable_const
      (measurable_fst.comp measurable_subtype_coe)).inter
      (measurableSet_lt measurable_const
        (measurable_snd.comp measurable_subtype_coe))

theorem augmentedParamsNonnegative_iff {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) :
    AugmentedParamsNonnegative p ↔
      ∀ i, AugmentedParamNonnegative (p i) := by
  rfl

theorem measurableSet_augmentedParamsNonnegative (n : ℕ) :
    MeasurableSet {p : Fin n → AugmentedTwoPointParams |
      AugmentedParamsNonnegative p} := by
  rw [show {p : Fin n → AugmentedTwoPointParams |
      AugmentedParamsNonnegative p} =
      ⋂ i, (fun p : Fin n → AugmentedTwoPointParams => p i) ⁻¹'
        {q | AugmentedParamNonnegative q} by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_preimage]
    rfl]
  exact MeasurableSet.iInter fun i =>
    measurableSet_augmentedParamNonnegative.preimage
      (measurable_pi_apply i)

theorem ae_latentPair_first_nonnegative
    {μ : Measure ℝ} [SFinite μ] (hsupport : μ (Iio 0) = 0)
    (M : ℝ) :
    ∀ᵐ p ∂latentPairMeasure μ M, 0 ≤ p.1 := by
  have hx : ∀ᵐ x ∂μ.restrict (Iio 1), 0 ≤ x := by
    rw [ae_iff]
    rw [show {a : ℝ | ¬0 ≤ a} = Iio 0 by ext; simp]
    rw [Measure.restrict_apply measurableSet_Iio]
    simpa [inter_eq_left.2 (Iio_subset_Iio (by norm_num : (0 : ℝ) ≤ 1))]
      using hsupport
  have hprod :
      ∀ᵐ p ∂belowAboveProduct μ, 0 ≤ p.1 := by
    unfold belowAboveProduct
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_fst)]
    filter_upwards [hx] with x hx
    exact Filter.Eventually.of_forall fun _ => hx
  exact hprod.filter_mono
    (withDensity_absolutelyContinuous
      (belowAboveProduct μ) (latentPairDensity M)).ae_le

theorem ae_latentParams_nonnegative
    {μ : Measure ℝ} [SFinite μ] (hsupport : μ (Iio 0) = 0)
    (M : ℝ) :
    ∀ᵐ q ∂latentParamsMeasure μ M,
      0 ≤ q.1.1 ∧ 1 < q.1.2 := by
  unfold latentParamsMeasure
  rw [ae_map_iff measurable_pairToParams.aemeasurable
    (by
      exact (measurableSet_le measurable_const
        (measurable_fst.comp measurable_subtype_coe)).inter
        (measurableSet_lt measurable_const
          (measurable_snd.comp measurable_subtype_coe)))]
  filter_upwards
    [ae_latentPair_first_nonnegative hsupport M,
      (show ∀ᵐ p ∂latentPairMeasure μ M,
          p ∈ strictPairSet by
        rw [ae_iff]
        change latentPairMeasure μ M strictPairSetᶜ = 0
        exact latentPairMeasure_compl_strictPairSet μ M)]
    with p hp0 hpstrict
  simp [pairToParams, hpstrict, hp0, hpstrict.2]

theorem ae_augmentedLatent_nonnegative
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (_hμ : Integrable (fun x : ℝ ↦ x) μ)
    (_hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hsupport : μ (Iio 0) = 0) :
    ∀ᵐ p ∂meanOneAugmentedLatent μ,
      AugmentedParamNonnegative p := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, ite_eq_left hM]
    rw [ae_dirac_iff measurableSet_augmentedParamNonnegative]
    simp [AugmentedParamNonnegative]
  · rw [meanOneAugmentedLatent, ite_eq_right hM,
      augmentedLatentMeasure, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure
        (by
          rw [ae_dirac_iff measurableSet_augmentedParamNonnegative]
          simp [AugmentedParamNonnegative]) _
    · rw [ae_map_iff measurable_inr.aemeasurable
        measurableSet_augmentedParamNonnegative]
      exact ae_latentParams_nonnegative hsupport (belowMoment μ)

theorem ae_recursiveAugmentedLatent_nonnegative
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1)
    (hsupport : ∀ i, μ i (Iio 0) = 0) :
    ∀ᵐ p ∂recursiveAugmentedLatent n
        (fun i ↦ meanOneAugmentedLatent (μ i)),
      AugmentedParamsNonnegative p := by
  induction n with
  | zero =>
      unfold recursiveAugmentedLatent
      simp [AugmentedParamsNonnegative]
  | succ n ih =>
      let latent := fun i : Fin (n + 1) =>
        meanOneAugmentedLatent (μ i)
      let tail := recursiveAugmentedLatent n
        (fun i => meanOneAugmentedLatent (μ (Fin.succ i)))
      let : ∀ i, IsProbabilityMeasure (latent i) :=
        fun i => meanOneAugmentedLatent_isProbability
          (hμ i) (hmean i) (hsupport i)
      have hhead :
          ∀ᵐ p ∂latent 0, AugmentedParamNonnegative p :=
        ae_augmentedLatent_nonnegative
          (hμ 0) (hmean 0) (hsupport 0)
      have htail :
          ∀ᵐ p ∂tail, AugmentedParamsNonnegative p :=
        ih (fun i => μ (Fin.succ i))
          (fun i => hμ (Fin.succ i))
          (fun i => hmean (Fin.succ i))
          (fun i => hsupport (Fin.succ i))
      unfold recursiveAugmentedLatent
      rw [ae_map_iff
        (finHeadTailEquiv AugmentedTwoPointParams n).symm.measurable.aemeasurable
          (measurableSet_augmentedParamsNonnegative (n + 1))]
      rw [Measure.ae_prod_iff_ae_ae
        (by
          exact (measurableSet_augmentedParamsNonnegative (n + 1)).preimage
            (finHeadTailEquiv AugmentedTwoPointParams n).symm.measurable)]
      filter_upwards [hhead] with head hhead
      filter_upwards [htail] with tail htail
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change AugmentedParamNonnegative head
        exact hhead
      · change AugmentedParamNonnegative (tail j)
        exact htail j

end

end Feige
