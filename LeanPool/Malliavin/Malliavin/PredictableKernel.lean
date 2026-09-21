/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# A finite-horizon kernel for the predictable projection

Mathlib's conditional-expectation kernel is available for finite measures.  The product of
Lebesgue measure on all of `ℝ≥0` with the probability measure `P` is not finite, so it cannot be
used directly.  This file restricts time to `Set.Iic T`, identifies the resulting finite product
measure with the corresponding restriction of the global measure, and applies the kernel theorem
there.

The resulting kernel is conditioned on the predictable σ-algebra of the *product* space.  We prove
that it is almost surely supported on points with the same time coordinate, and hence obtain a
same-time integral formula for the product-`L²` projection.  This file does not identify the
kernel's sample-space marginal with the fixed-time kernel `condExpKernel P (𝓕 t)`; for the
natural Brownian filtration that identification — almost every time, almost every sample, as
measures — is `predictableSectionKernel_ae_eq_condExpKernel` in `KernelIdentification.lean`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

/-- Lebesgue measure restricted to the finite time interval `Set.Iic T`. -/
noncomputable def finiteHorizonTimeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  nonnegativeLebesgueMeasure.restrict (Set.Iic T)

instance (T : ℝ≥0) : IsFiniteMeasure (finiteHorizonTimeMeasure T) :=
  isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Iic_ne_top T)

/-- Almost every time in a finite horizon is strictly positive; the omitted endpoint `0` is a
Lebesgue-null singleton. -/
theorem ae_pos_finiteHorizonTimeMeasure (T : ℝ≥0) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t := by
  have hne : ∀ᵐ t ∂finiteHorizonTimeMeasure T, t ≠ 0 := by
    exact ae_restrict_of_ae (nonnegativeLebesgueMeasure.ae_ne 0)
  filter_upwards [hne] with t ht
  exact pos_iff_ne_zero.mpr ht

/-- The finite measure obtained by restricting the time coordinate of the product measure. -/
noncomputable def finiteHorizonProductMeasure (P : Measure W) (T : ℝ≥0) :
    Measure (ℝ≥0 × W) :=
  (finiteHorizonTimeMeasure T).prod P

instance (P : Measure W) [IsFiniteMeasure P] (T : ℝ≥0) :
    IsFiniteMeasure (finiteHorizonProductMeasure P T) := by
  unfold finiteHorizonProductMeasure
  infer_instance

omit [CompleteSpace W] [BorelSpace W] in
/-- Restricting the time measure before taking the product is the same as restricting the product
measure to `Set.Iic T ×ˢ Set.univ`. -/
theorem finiteHorizonProductMeasure_eq_restrict (T : ℝ≥0) :
    finiteHorizonProductMeasure P T =
      (nonnegativeLebesgueMeasure.prod P).restrict (Set.Iic T ×ˢ Set.univ) := by
  simpa only [finiteHorizonProductMeasure, finiteHorizonTimeMeasure] using
    Measure.restrict_prod_eq_prod_univ (μ := nonnegativeLebesgueMeasure)
      (ν := P) (Set.Iic T)

section SameTime

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

/-- A conditional-expectation kernel onto the predictable σ-algebra preserves the observed time:
conditionally, the output time is almost surely the input time. -/
theorem condExpKernel_predictable_ae_same_time
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ 𝓕.predictable p, q.1 = p.1 := by
  let mΩ : MeasurableSpace (ℝ≥0 × S) := inferInstance
  have hm : 𝓕.predictable ≤ mΩ := predictable_le_prod 𝓕
  have hdiag_meas : @Measurable (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      mΩ (𝓕.predictable.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hsame_time_meas : @MeasurableSet ((ℝ≥0 × S) × (ℝ≥0 × S))
      (𝓕.predictable.prod mΩ) {z | z.2.1 = z.1.1} := by
    apply measurableSet_eq_fun
    · exact measurable_fst.comp measurable_snd
    · exact (measurable_fst_predictable 𝓕).comp measurable_fst
  have hdiag_ae : @AEMeasurable (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      (𝓕.predictable.prod mΩ) mΩ Function.diag μ :=
    @Measurable.aemeasurable (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      mΩ (𝓕.predictable.prod mΩ) Function.diag μ hdiag_meas
  have hbad_time_meas : @MeasurableSet ((ℝ≥0 × S) × (ℝ≥0 × S))
      (𝓕.predictable.prod mΩ) {z | ¬z.2.1 = z.1.1} := hsame_time_meas.compl
  have hdiag : ∀ᵐ z ∂(@Measure.map (ℝ≥0 × S) ((ℝ≥0 × S) × (ℝ≥0 × S))
      mΩ (𝓕.predictable.prod mΩ) Function.diag μ), z.2.1 = z.1.1 := by
    rw [ae_iff]
    rw [@Measure.map_apply_of_aemeasurable (ℝ≥0 × S)
      ((ℝ≥0 × S) × (ℝ≥0 × S)) mΩ (𝓕.predictable.prod mΩ)
      μ Function.diag hdiag_ae _ hbad_time_meas]
    simp only [Set.preimage_ofPred_eq, Function.diag, not_true_eq_false, Set.ofPred_false,
      measure_empty]
  rw [← compProd_trim_condExpKernel hm] at hdiag
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hdiag)

/-- Kernel-valued form of `condExpKernel_predictable_ae_same_time`: pushing the predictable
conditional kernel forward by the time coordinate gives the Dirac kernel at the observed time. -/
theorem condExpKernel_predictable_map_fst_ae
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    (condExpKernel μ 𝓕.predictable).map Prod.fst =ᵐ[μ]
      Kernel.deterministic Prod.fst (measurable_fst_predictable 𝓕) := by
  filter_upwards [condExpKernel_predictable_ae_same_time μ 𝓕] with p hp
  rw [Kernel.map_apply _ measurable_fst, Kernel.deterministic_apply]
  exact (hasLaw_dirac_of_ae_eq hp).map_eq

/-- The sample-space marginal of the product conditional kernel for the predictable σ-algebra.

This is a jointly predictable kernel indexed by `(t, ω)`.  It is not definitionally the varying
fixed-time kernel `condExpKernel P (𝓕 t)`. -/
noncomputable def predictableSectionKernel
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    @Kernel (ℝ≥0 × S) S 𝓕.predictable inferInstance :=
  (condExpKernel μ 𝓕.predictable).map Prod.snd

/-- The predictable-section kernel is Markov: it is the measurable pushforward of a conditional
expectation kernel by the sample-coordinate projection. -/
instance instIsMarkovKernelPredictableSectionKernel
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    IsMarkovKernel (predictableSectionKernel μ 𝓕) := by
  unfold predictableSectionKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ measurable_snd

end SameTime

/-- On a finite time horizon, the global predictable `L²` projection is represented pointwise by
Mathlib's conditional-expectation kernel for the predictable σ-algebra on the product space.

The integration variable `q` still ranges over `ℝ≥0 × W`; this theorem deliberately makes no
claim that the kernel is the fixed-time kernel `condExpKernel P (𝓕 p.1)`. -/
theorem predictableProjection_ae_eq_integral_condExpKernel_Iic
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ q, U q
          ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let S : Set (ℝ≥0 × W) := Set.Iic T ×ˢ Set.univ
  let μT := finiteHorizonProductMeasure P T
  have hμT : μT = μ.restrict S := by
    simpa only [μT, μ, S] using finiteHorizonProductMeasure_eq_restrict (P := P) T
  have hS : MeasurableSet[𝓕.predictable] S := by
    have hpre : MeasurableSet[𝓕.predictable]
        (Prod.fst ⁻¹' Set.Iic T : Set (ℝ≥0 × W)) :=
      (measurable_fst_predictable 𝓕) measurableSet_Iic
    rw [show S = Prod.fst ⁻¹' Set.Iic T by
      ext p
      simp only [S, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true,
        Set.mem_preimage]]
    exact hpre
  have hμT_le : μT ≤ μ := by
    rw [hμT]
    exact Measure.restrict_le_self
  have hU_mem : MemLp (U : ℝ≥0 × W → ℝ) 2 μT :=
    (Lp.memLp U).mono_measure hμT_le
  have hU_int : Integrable (U : ℝ≥0 × W → ℝ) μT :=
    hU_mem.integrable fact_one_le_two_ennreal.elim
  let Q := predictableProjection 𝓕 U
  have hQ_mem : MemLp (Q : ℝ≥0 × W → ℝ) 2 μT :=
    (Lp.memLp (Q : TimeProcessL2 P)).mono_measure hμT_le
  have hQ_int : Integrable (Q : ℝ≥0 × W → ℝ) μT :=
    hQ_mem.integrable fact_one_le_two_ennreal.elim
  have hQ_meas : AEStronglyMeasurable[𝓕.predictable]
      (Q : ℝ≥0 × W → ℝ) μT :=
    (lpMeas.aestronglyMeasurable Q).mono_measure hμT_le
  have hQ_cond : (Q : ℝ≥0 × W → ℝ) =ᵐ[μT]
      μT[(U : ℝ≥0 × W → ℝ) | 𝓕.predictable] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (predictable_le_prod 𝓕) hU_int
    · intro s _ _
      exact hQ_int.integrableOn
    · intro s hs _
      have hsS : MeasurableSet[𝓕.predictable] (s ∩ S) := hs.inter hS
      have hμsS : μ (s ∩ S) ≠ ∞ := by
        apply ne_top_of_le_ne_top
          (show μ S ≠ ∞ from ?_)
          (measure_mono Set.inter_subset_right)
        change (nonnegativeLebesgueMeasure.prod P)
          (Set.Iic T ×ˢ Set.univ) ≠ ∞
        rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top (nonnegativeLebesgueMeasure_Iic_ne_top T)
          (measure_ne_top P Set.univ)
      change ∫ x, (Q : ℝ≥0 × W → ℝ) x ∂μT.restrict s =
        ∫ x, (U : ℝ≥0 × W → ℝ) x ∂μT.restrict s
      rw [hμT, Measure.restrict_restrict ((predictable_le_prod 𝓕) s hs)]
      simpa only [Q, predictableProjection] using
        integral_condExpL2_eq (predictable_le_prod 𝓕) U hsS hμsS
    · exact hQ_meas
  exact hQ_cond.trans
    (condExp_ae_eq_integral_condExpKernel (predictable_le_prod 𝓕) hU_int)

/-- Same-time form of `predictableProjection_ae_eq_integral_condExpKernel_Iic`: the conditional
kernel can be used after replacing the input time by the observed time `p.1`. -/
theorem predictableProjection_ae_eq_sameTimeCondExpKernel_Iic
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ q, U (p.1, q.2)
          ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p := by
  refine (predictableProjection_ae_eq_integral_condExpKernel_Iic 𝓕 U T).trans ?_
  filter_upwards [condExpKernel_predictable_ae_same_time
    (finiteHorizonProductMeasure P T) 𝓕] with p hp
  exact integral_congr_ae (hp.mono fun q hq ↦ by
    congr 1
    exact Prod.ext hq rfl)

/-- On a finite horizon, the predictable projection is a pointwise integral of the same-time
section `U (p.1, ·)` against the jointly predictable sample-space kernel
`predictableSectionKernel`. -/
theorem predictableProjection_ae_eq_integral_predictableSectionKernel_Iic
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ w, U (p.1, w)
          ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p := by
  refine (predictableProjection_ae_eq_sameTimeCondExpKernel_Iic 𝓕 U T).trans ?_
  apply Filter.Eventually.of_forall
  intro p
  change (∫ q, U (p.1, q.2)
      ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p) =
    ∫ w, U (p.1, w)
      ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p
  rw [predictableSectionKernel, Kernel.map_apply _ measurable_snd]
  exact (integral_map measurable_snd.aemeasurable
    ((Lp.stronglyMeasurable U).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).symm

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
