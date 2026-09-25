/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Localized Equation Duhamel Kernels

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section

namespace CKN.Core.Step3

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

private lemma kernel_sub_measurePreserving (y : ParabolicPoint) :
    MeasurePreserving (fun x : ParabolicPoint => pointSub x y)
      (volume : Measure ParabolicPoint) volume := by
  have h := (measurePreserving_add_right (volume : Measure Vec3) (-y.1)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-y.2))
  rw [Integration.volume_parabolicPoint_eq_prod]
  change MeasurePreserving (fun x : Vec3 × ℝ =>
    (x.1 + -y.1, x.2 + -y.2)) (volume.prod volume) (volume.prod volume)
  convert h using 1
  rfl

private lemma kernel_integrableOn_shift
    {k : ParabolicPoint → ℝ} (hk : LocallyIntegrable k volume)
    {K : Set ParabolicPoint} (hK : IsCompact K) (y : ParabolicPoint) :
    IntegrableOn (fun x : ParabolicPoint => k (pointSub x y)) K volume := by
  let S : Set ParabolicPoint := (fun x : ParabolicPoint => pointSub x y) '' K
  have hS : IsCompact S := by
    apply hK.image
    change Continuous (fun x : ParabolicPoint =>
      parabolicHomeomorph.symm (x.1 - y.1, x.2 - y.2))
    apply parabolicHomeomorph.continuous_symm.comp
    exact ((continuous_fst_parabolicPoint : Continuous (fun x : ParabolicPoint => x.1)).sub
      (continuous_const : Continuous (fun _ : ParabolicPoint => y.1))).prodMk
      ((continuous_snd_parabolicPoint : Continuous (fun x : ParabolicPoint => x.2)).sub
        (continuous_const : Continuous (fun _ : ParabolicPoint => y.2)))
  have hInd := (hk.integrableOn_isCompact hS).integrable_indicator hS.measurableSet
  have hcomp := (kernel_sub_measurePreserving y).integrable_comp
    hInd.aestronglyMeasurable |>.mpr hInd
  have heq : (fun x : ParabolicPoint => S.indicator k (pointSub x y)) =
      (fun x : ParabolicPoint => K.indicator
        (fun z : ParabolicPoint => k (pointSub z y)) x) := by
    funext x
    by_cases hx : x ∈ K
    · have hxy : pointSub x y ∈ S := ⟨x, hx, rfl⟩
      simp only [Set.indicator_of_mem hxy, Set.indicator_of_mem hx]
    · have hxy : pointSub x y ∉ S := by
        rintro ⟨z, hz, hzx⟩
        have hzx' : z = x := by
          apply Prod.ext
          · exact sub_left_injective (b := y.1)
              (by simpa [pointSub] using congrArg Prod.fst hzx)
          · exact sub_left_injective (b := y.2)
              (by simpa [pointSub] using congrArg Prod.snd hzx)
        exact hx (by simpa only [hzx'] using hz)
      simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy]
  have hcomp' : Integrable (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) volume := by
    change Integrable (fun x : ParabolicPoint =>
      S.indicator k (pointSub x y)) volume at hcomp
    exact hcomp
  rw [heq] at hcomp'
  exact (integrable_indicator_iff hK.measurableSet).mp hcomp'

private lemma kernel_setIntegral_norm_shift_le
    {k : ParabolicPoint → ℝ} (hk : LocallyIntegrable k volume)
    {K L : Set ParabolicPoint} (hK : IsCompact K) (hL : IsCompact L)
    (y : ParabolicPoint)
    (hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L) :
    (∫ x in K, ‖k (pointSub x y)‖) ≤ ∫ z in L, ‖k z‖ := by
  have hkn : LocallyIntegrable (fun z : ParabolicPoint => ‖k z‖) volume := by
    exact (locallyIntegrableOn_univ.mp
      (locallyIntegrableOn_univ.mpr hk).norm)
  have hshift := kernel_integrableOn_shift hkn hK y
  have hleft := hshift.integrable_indicator hK.measurableSet
  have hright := (hkn.integrableOn_isCompact hL).integrable_indicator hL.measurableSet
  have hcomp := (kernel_sub_measurePreserving y).integrable_comp
    hright.aestronglyMeasurable |>.mpr hright
  have hle : ∀ᵐ x : ParabolicPoint, K.indicator
      (fun z => ‖k (pointSub z y)‖) x ≤
      L.indicator (fun z => ‖k z‖) (pointSub x y) := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub ⟨x, hx, rfl⟩)]
    · rw [Set.indicator_of_notMem hx]
      by_cases hLx : pointSub x y ∈ L
      · rw [Set.indicator_of_mem hLx]
        exact norm_nonneg _
      · rw [Set.indicator_of_notMem hLx]
  have hint := integral_mono_ae hleft hcomp hle
  rw [integral_indicator hK.measurableSet] at hint
  change (∫ x : ParabolicPoint in K, ‖k (pointSub x y)‖) ≤
      ∫ x : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖)
        (pointSub x y) at hint
  let e := (Homeomorph.subRight y.1).prodCongr (Homeomorph.subRight y.2)
  have htrans := (kernel_sub_measurePreserving y).integral_comp
    e.measurableEmbedding (L.indicator (fun z : ParabolicPoint => ‖k z‖))
  have htrans' : (∫ x : ParabolicPoint,
      L.indicator (fun z : ParabolicPoint => ‖k z‖) (pointSub x y)) =
      ∫ z : ParabolicPoint, L.indicator (fun z : ParabolicPoint => ‖k z‖) z := by
    simpa [e, pointSub] using htrans
  rw [htrans', integral_indicator hL.measurableSet] at hint
  exact hint

theorem duhamel_kernel_test_integrable_of_compact_support
    {k F : ParabolicPoint → ℝ} {ζ : Vec3 × ℝ → ℝ}
    (hk : LocallyIntegrable k volume) (hkm : Measurable k)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hF : Integrable F volume) (hFc : HasCompactSupport F) :
    Integrable (fun q : ParabolicPoint × ParabolicPoint =>
      k (pointSub q.1 q.2) * ζ q.1 * F q.2)
      ((volume : Measure ParabolicPoint).prod volume) := by
  let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹' tsupport ζ
  let S : Set ParabolicPoint := tsupport F
  let L : Set ParabolicPoint :=
    (fun z : ParabolicPoint × ParabolicPoint => pointSub z.1 z.2) '' (K ×ˢ S)
  have hK : IsCompact K := parabolicHomeomorph.isCompact_preimage.2 hζc.isCompact
  have hS : IsCompact S := hFc.isCompact
  have hL : IsCompact L := by
    apply (hK.prod hS).image
    change Continuous (fun z : ParabolicPoint × ParabolicPoint =>
      parabolicHomeomorph.symm (z.1.1 - z.2.1, z.1.2 - z.2.2))
    apply parabolicHomeomorph.continuous_symm.comp
    have h11 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.1.1) :=
      continuous_fst_parabolicPoint.comp continuous_fst
    have h21 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.2.1) :=
      continuous_fst_parabolicPoint.comp continuous_snd
    have h12 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.1.2) :=
      continuous_snd_parabolicPoint.comp continuous_fst
    have h22 : Continuous (fun z : ParabolicPoint × ParabolicPoint => z.2.2) :=
      continuous_snd_parabolicPoint.comp continuous_snd
    exact (h11.sub h21).prodMk (h12.sub h22)
  have hbase : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
      k (pointSub q.1 q.2) * F q.2)
      ((volume.restrict K).prod volume) := by
    let μ : Measure ParabolicPoint := volume.restrict K
    let B : ParabolicPoint × ParabolicPoint → ℝ :=
      fun q => k (pointSub q.1 q.2) * F q.2
    have hBm : AEStronglyMeasurable B (μ.prod volume) := by
      have hkm' : Measurable (fun q : ParabolicPoint × ParabolicPoint =>
          k (pointSub q.1 q.2)) := by
        apply hkm.comp
        exact (measurable_fst.fst.sub measurable_snd.fst).prodMk
          (measurable_fst.snd.sub measurable_snd.snd)
      exact hkm'.aestronglyMeasurable.mul hF.aestronglyMeasurable.comp_snd
    apply (integrable_prod_iff' hBm).2
    constructor
    · filter_upwards [] with y
      have hs := kernel_integrableOn_shift hk hK y
      simpa [B, μ, mul_comm] using hs.integrable.const_mul (F y)
    · have hm := hBm.prod_swap.norm.integral_prod_right'
      have hmajor : Integrable (fun y =>
          (∫ z in L, ‖k z‖) * ‖F y‖) volume := hF.norm.const_mul _
      apply hmajor.mono hm
      filter_upwards [] with y
      by_cases hy : y ∈ S
      · have hsub : (fun x : ParabolicPoint => pointSub x y) '' K ⊆ L := by
          rintro z ⟨x, hx, rfl⟩
          exact ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
        have hb := kernel_setIntegral_norm_shift_le hk hK hL y hsub
        dsimp [B, μ]
        rw [abs_of_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _))]
        rw [abs_of_nonneg (mul_nonneg (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)) (abs_nonneg _))]
        simp_rw [abs_mul, mul_comm]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      · simp [B, image_eq_zero_of_notMem_tsupport hy]
  have hbound : ∃ C : ℝ, ∀ z, ‖ζ z‖ ≤ C := by
    rcases hζ.continuous.norm.bddAbove_range_of_hasCompactSupport hζc.norm with ⟨C, hC⟩
    exact ⟨C, fun z => hC ⟨z, rfl⟩⟩
  rcases hbound with ⟨C, hC⟩
  have hζP : Continuous (fun z : ParabolicPoint => ζ (z.1, z.2)) :=
    hζ.continuous.comp continuous_parabolicPoint_to_prod
  have hζm : AEStronglyMeasurable
      (fun q : ParabolicPoint × ParabolicPoint => ζ (q.1.1, q.1.2))
      ((volume.restrict K).prod volume) :=
    (hζP.measurable.comp measurable_fst).aestronglyMeasurable
  have hmul := hbase.bdd_mul hζm
    (Filter.Eventually.of_forall (fun q => hC q.1))
  have hmul' : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
      k (pointSub q.1 q.2) * ζ q.1 * F q.2)
      ((volume.prod volume).restrict (K ×ˢ (Set.univ : Set ParabolicPoint))) := by
    rw [← Measure.prod_restrict]
    have hmul0 : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
        ζ (q.1.1, q.1.2) *
          (k (pointSub q.1 q.2) * F q.2))
        ((volume.restrict K).prod volume) := hmul
    have hmul1 := hmul0.congr (Filter.Eventually.of_forall (fun q => by
      change ζ (q.1.1, q.1.2) *
          (k (pointSub q.1 q.2) * F q.2) =
        k (pointSub q.1 q.2) * ζ (q.1.1, q.1.2) * F q.2
      ring))
    simp only [Measure.restrict_univ]
    change Integrable (fun q : ParabolicPoint × ParabolicPoint =>
        k (pointSub q.1 q.2) * ζ (q.1.1, q.1.2) * F q.2)
      ((volume.restrict K).prod volume)
    exact hmul1
  change IntegrableOn (fun q : ParabolicPoint × ParabolicPoint =>
      k (pointSub q.1 q.2) * ζ q.1 * F q.2)
      (K ×ˢ (Set.univ : Set ParabolicPoint)) (volume.prod volume) at hmul'
  apply hmul'.integrable_of_forall_notMem_eq_zero
  intro q hq
  have hq1 : q.1 ∉ K := by
    intro hqK
    exact hq ⟨hqK, Set.mem_univ _⟩
  have hq1' : (q.1.1, q.1.2) ∉ tsupport ζ := by
    simpa only [K, Set.mem_preimage, parabolicHomeomorph_apply] using hq1
  have hz : ζ (q.1.1, q.1.2) = 0 := image_eq_zero_of_notMem_tsupport hq1'
  have hz' : ζ q.1 = 0 := by
    change ζ (q.1.1, q.1.2) = 0
    exact hz
  simp [hz']

end CKN.Core.Step3
