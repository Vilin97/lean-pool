/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue

/-!
# Probability lemmas for Grünbaum's inequality
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace Grunbaum

section Projection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] in
private lemma exists_apply_ne (L : E →L[ℝ] ℝ) (hL : L ≠ 0) (t : ℝ) :
    ∃ x, L x ≠ t := by
  by_cases ht : t = 0
  · subst t
    by_contra! h
    apply hL
    ext x
    simpa using h x
  · exact ⟨0, by simpa using Ne.symm ht⟩

lemma volume_preimage_singleton_eq_zero (L : E →L[ℝ] ℝ) (hL : L ≠ 0) (t : ℝ) :
    volume (L ⁻¹' ({t} : Set ℝ)) = 0 := by
  let A : AffineSubspace ℝ E :=
    (affineSpan ℝ ({t} : Set ℝ)).comap L.toLinearMap.toAffineMap
  have hA_coe : (A : Set E) = L ⁻¹' ({t} : Set ℝ) := by
    ext x
    simp [A]
  have hA_ne_top : A ≠ ⊤ := by
    obtain ⟨x, hx⟩ := exists_apply_ne L hL t
    intro hA
    have hxA : x ∈ A := by rw [hA]; simp
    exact hx (by simpa [A] using hxA)
  rw [← hA_coe]
  exact Measure.addHaar_affineSubspace volume A hA_ne_top

lemma nullSingletonClass_map_uniform
    (K : Set E) (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    NullSingletonClass (((volume K)⁻¹ • volume.restrict K).map L) := by
  constructor
  intro t
  have hm : MeasurableSet (L ⁻¹' ({t} : Set ℝ)) :=
    (measurableSet_singleton t).preimage L.measurable
  have hzero : volume ((L ⁻¹' ({t} : Set ℝ)) ∩ K) = 0 :=
    measure_mono_null inter_subset_left (volume_preimage_singleton_eq_zero L hL t)
  rw [Measure.map_apply L.measurable (measurableSet_singleton t), Measure.smul_apply,
    Measure.restrict_apply hm, hzero, smul_zero]

end Projection

section CDF

lemma continuous_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  apply le_antisymm
  · exact (monotone_cdf μ).leftLim_le le_rfl
  · have hzero : (cdf μ).measure {x} = 0 := by
      rw [measure_cdf μ]
      exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at hzero
    exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hzero)

lemma measure_cdf_preimage_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    μ ((cdf μ) ⁻¹' Iic u) = ENNReal.ofReal u := by
  let F : ℝ → ℝ := cdf μ
  let S : Set ℝ := F ⁻¹' Iic u
  have hF_cont : Continuous F := by
    simpa [F] using continuous_cdf_of_noAtoms μ
  have hF_mono : Monotone F := by
    simpa [F] using monotone_cdf μ
  have hS_closed : IsClosed S := isClosed_Iic.preimage hF_cont
  obtain ⟨b, hb⟩ :=
    eventually_atTop.1 ((tendsto_cdf_atTop μ).eventually_const_lt hu1)
  have hS_bdd : BddAbove S := by
    refine ⟨b, ?_⟩
    intro x hx
    change F x ≤ u at hx
    apply le_of_not_gt
    intro hbx
    exact (not_lt_of_ge hx) (hb x hbx.le)
  by_cases hS_nonempty : S.Nonempty
  · let q := sSup S
    have hq : IsGreatest S q :=
      hS_closed.isGreatest_csSup hS_nonempty hS_bdd
    have hFq_le : F q ≤ u := hq.1
    have hFq : F q = u := by
      apply le_antisymm hFq_le
      rcases eq_or_lt_of_le hu0 with hu | hu
      · subst u
        simpa [F] using cdf_nonneg μ q
      · obtain ⟨y, hy⟩ : ∃ y, F y = u :=
          mem_range_of_exists_le_of_exists_ge hF_cont
            ⟨q, hFq_le⟩ ⟨b, (hb b le_rfl).le⟩
        have hyS : y ∈ S := by
          change F y ≤ u
          exact hy.le
        calc
          u = F y := hy.symm
          _ ≤ F q := hF_mono (hq.2 hyS)
    have hS : S = Iic q := by
      apply Subset.antisymm
      · exact hq.2
      · intro x hx
        change F x ≤ u
        exact (hF_mono hx).trans hFq_le
    change μ S = ENNReal.ofReal u
    rw [hS, ← ofReal_cdf μ q]
    simpa [F] using congrArg ENNReal.ofReal hFq
  · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS_nonempty
    have hu_not_pos : ¬ 0 < u := by
      intro hu
      have heventually : ∀ᶠ x in atBot, F x < u := by
        simpa [F] using (tendsto_cdf_atBot μ).eventually_lt_const hu
      obtain ⟨x, hx⟩ := heventually.exists
      apply hS_nonempty
      refine ⟨x, ?_⟩
      change F x ≤ u
      exact hx.le
    have hu : u = 0 := le_antisymm (not_lt.mp hu_not_pos) hu0
    change μ S = ENNReal.ofReal u
    simp [hS_empty, hu]

open unitInterval in
/-- The cumulative distribution function regarded as a map into `[0,1]`. -/
def cdfToUnitInterval (μ : Measure ℝ) (x : ℝ) : I :=
  ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩

open unitInterval in
lemma measurable_cdfToUnitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Measurable (cdfToUnitInterval μ) :=
  (continuous_cdf_of_noAtoms μ).measurable.subtype_mk

open unitInterval in
theorem map_cdfToUnitInterval_apply_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (u : I) :
    μ.map (cdfToUnitInterval μ) (Iic u) = ENNReal.ofReal (u : ℝ) := by
  rw [Measure.map_apply (measurable_cdfToUnitInterval μ) measurableSet_Iic]
  by_cases hu : (u : ℝ) = 1
  · have hpre : cdfToUnitInterval μ ⁻¹' Iic u = Set.univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      change cdf μ x ≤ (u : ℝ)
      simpa [hu] using cdf_le_one μ x
    simp [hpre, hu]
  · have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hu
    have hpre :
        cdfToUnitInterval μ ⁻¹' Iic u = (cdf μ) ⁻¹' Iic (u : ℝ) := by
      ext x
      rfl
    rw [hpre]
    exact measure_cdf_preimage_Iic μ (u : ℝ) u.2.1 hu1

end CDF

section LayerCake

lemma Integrable.integral_eq_integral_Ioc_meas_lt'
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {M : ℝ}
    (f_intble : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f)
    (f_bdd : f ≤ᵐ[μ] fun _ ↦ M) :
    ∫ ω, f ω ∂μ = ∫ t in Ioc 0 M, μ.real {a : α | t < f a} := by
  rw [f_intble.integral_eq_integral_meas_lt f_nn]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    nullMeasurableSet_Ioi Ioc_subset_Ioi_self ?_]
  apply Eventually.of_forall
  intro t ht
  have htM : M < t := by
    simp_all only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le]
  have obs : μ {a | M < f a} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [f_bdd] with a ha using not_lt.mpr ha
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  exact Or.inl <| measure_mono_null (fun a ha ↦ htM.trans ha) obs

theorem integral_cdf_rpow_inv_natCast (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {n : ℕ} (hn : n ≠ 0) :
    (∫ x, (cdf μ x) ^ ((n : ℝ)⁻¹) ∂μ) = (n : ℝ) / (n + 1) := by
  let F : ℝ → ℝ := cdf μ
  let G : ℝ → ℝ := fun x ↦ F x ^ ((n : ℝ)⁻¹)
  have hp : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hF_cont : Continuous F := by
    simpa [F] using continuous_cdf_of_noAtoms μ
  have hG_cont : Continuous G :=
    (Real.continuous_rpow_const hp).comp hF_cont
  have hG_nonneg (x : ℝ) : 0 ≤ G x :=
    Real.rpow_nonneg (by simpa [F] using cdf_nonneg μ x) _
  have hG_le_one (x : ℝ) : G x ≤ 1 :=
    Real.rpow_le_one (by simpa [F] using cdf_nonneg μ x)
      (by simpa [F] using cdf_le_one μ x) hp
  have hG_int : Integrable G μ :=
    Integrable.of_bound hG_cont.aestronglyMeasurable 1 <|
      Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg x)]
        exact hG_le_one x
  change (∫ x, G x ∂μ) = _
  rw [Grunbaum.Integrable.integral_eq_integral_Ioc_meas_lt' hG_int
    (Eventually.of_forall hG_nonneg) (Eventually.of_forall hG_le_one)]
  calc
    (∫ t in Ioc (0 : ℝ) 1, μ.real {x | t < G x}) =
        ∫ t in Ioc (0 : ℝ) 1, (1 - t ^ n) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · have hempty : {x | (1 : ℝ) < G x} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact (not_lt_of_ge (hG_le_one x)) hx
        simp [hempty]
      · have ht0 : 0 ≤ t := ht.1.le
        have hu0 : 0 ≤ t ^ n := pow_nonneg ht0 n
        have hu1 : t ^ n < 1 := pow_lt_one₀ ht0 ht1 hn
        have hsub :
            μ {x | F x ≤ t ^ n} = ENNReal.ofReal (t ^ n) := by
          change μ (F ⁻¹' Iic (t ^ n)) = ENNReal.ofReal (t ^ n)
          simpa [F] using measure_cdf_preimage_Iic μ (t ^ n) hu0 hu1
        have hsub_meas : MeasurableSet {x | F x ≤ t ^ n} :=
          measurableSet_Iic.preimage hF_cont.measurable
        have htail : {x | t < G x} = {x | F x ≤ t ^ n}ᶜ := by
          ext x
          simp only [mem_ofPred_eq, mem_compl_iff]
          rw [← pow_lt_pow_iff_left₀ ht0 (hG_nonneg x) hn,
            Real.rpow_inv_natCast_pow (by simpa [F] using cdf_nonneg μ x) hn]
          simp
        have hsub_real : μ.real {x | F x ≤ t ^ n} = t ^ n := by
          rw [measureReal_def, hsub, ENNReal.toReal_ofReal hu0]
        change μ.real {x | t < G x} = 1 - t ^ n
        rw [htail, probReal_compl_eq_one_sub hsub_meas, hsub_real]
    _ = ∫ t in (0 : ℝ)..1, (1 - t ^ n) :=
      (intervalIntegral.integral_of_le zero_le_one).symm
    _ = (n : ℝ) / (n + 1) := by
      have hlin :
          (∫ t : ℝ in (0 : ℝ)..1, (1 - t ^ n)) =
            (∫ _t : ℝ in (0 : ℝ)..1, (1 : ℝ)) -
              ∫ t : ℝ in (0 : ℝ)..1, t ^ n := by
        simpa only using
          (intervalIntegral.integral_sub
            (f := fun _ : ℝ ↦ 1) (g := fun t : ℝ ↦ t ^ n)
            intervalIntegrable_const
            ((continuous_id.pow n).intervalIntegrable 0 1))
      rw [hlin,
        integral_one, integral_pow]
      (norm_num [Nat.cast_add];
        field_simp [show (n : ℝ) + 1 ≠ 0 by positivity];
        ring)

end LayerCake

section Jensen

theorem cdf_rpow_inv_natCast_le_at_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {n : ℕ} (hn : n ≠ 0) (m : ℝ)
    (hconc : ConcaveOn ℝ (Ici m)
      (fun x ↦ (cdf μ x) ^ ((n : ℝ)⁻¹)))
    (hsupport : ∀ᵐ x ∂μ, x ∈ Ici m)
    (hid : Integrable (fun x : ℝ ↦ x) μ) :
    (n : ℝ) / (n + 1) ≤
      (cdf μ (∫ x : ℝ, x ∂μ)) ^ ((n : ℝ)⁻¹) := by
  let G : ℝ → ℝ := fun x ↦ (cdf μ x) ^ ((n : ℝ)⁻¹)
  have hp : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hG_cont : Continuous G :=
    (Real.continuous_rpow_const hp).comp (continuous_cdf_of_noAtoms μ)
  have hG_nonneg (x : ℝ) : 0 ≤ G x :=
    Real.rpow_nonneg (cdf_nonneg μ x) _
  have hG_le_one (x : ℝ) : G x ≤ 1 :=
    Real.rpow_le_one (cdf_nonneg μ x) (cdf_le_one μ x) hp
  have hG_int : Integrable G μ :=
    Integrable.of_bound hG_cont.aestronglyMeasurable 1 <|
      Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg x)]
        exact hG_le_one x
  calc
    (n : ℝ) / (n + 1) = ∫ x, G x ∂μ := by
      simpa [G] using (integral_cdf_rpow_inv_natCast μ hn).symm
    _ ≤ G (∫ x : ℝ, x ∂μ) := by
      simpa [G, Function.comp_def] using
        hconc.le_map_integral hG_cont.continuousOn isClosed_Ici
          hsupport hid hG_int

end Jensen

section UniformCentroid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Lebesgue volume restricted to `K` and normalized to total mass one. -/
def uniformVolume (K : Set E) : Measure E :=
  (volume K)⁻¹ • volume.restrict K

/-- The centroid of `K` defined by its set average. -/
def volumeCentroid (K : Set E) : E :=
  ⨍ x in K, x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma isProbabilityMeasure_uniformVolume (K : Set E)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ∞) :
    IsProbabilityMeasure (uniformVolume K) := by
  constructor
  simp only [uniformVolume, Measure.smul_apply,
    Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hK0 hKtop

omit [FiniteDimensional ℝ E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma volumeCentroid_eq_integral_uniformVolume (K : Set E) :
    volumeCentroid K = ∫ x, x ∂uniformVolume K := by
  simpa [volumeCentroid, uniformVolume] using
    (setAverage_eq' (μ := volume) (fun x : E ↦ x) K)

lemma integral_id_map_uniformVolume_eq_centroid_projection
    (K : Set E) (hK : IsCompact K) (L : E →L[ℝ] ℝ) :
    (∫ t : ℝ, t ∂(uniformVolume K).map L) = L (volumeCentroid K) := by
  have hid_restrict : Integrable (fun x : E ↦ x) (volume.restrict K) :=
    continuous_id.continuousOn.integrableOn_compact hK
  have hid_uniform : Integrable (fun x : E ↦ x) (uniformVolume K) := by
    simpa [uniformVolume, Measure.restrict_apply_univ] using
      hid_restrict.to_average
  calc
    (∫ t : ℝ, t ∂(uniformVolume K).map L) =
        ∫ x : E, L x ∂uniformVolume K :=
      integral_map L.measurable.aemeasurable continuous_id.aestronglyMeasurable
    _ = L (∫ x : E, x ∂uniformVolume K) :=
      L.integral_comp_comm hid_uniform
    _ = L (volumeCentroid K) := by
      rw [volumeCentroid_eq_integral_uniformVolume]

end UniformCentroid

section Average

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma ContinuousLinearMap.map_setAverage (L : E →L[ℝ] F)
    (μ : Measure α) (s : Set α) (f : α → E) (hf : IntegrableOn f s μ) :
    L (⨍ x in s, f x ∂μ) = ⨍ x in s, L (f x) ∂μ := by
  simp only [setAverage_eq, map_smul]
  rw [← L.integral_comp_comm hf]

end Average

end Grunbaum
