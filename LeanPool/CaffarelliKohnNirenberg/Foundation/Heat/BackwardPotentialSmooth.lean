/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialPairing

/-!
# Backward Potential Smooth

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology Convolution

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

private lemma heatKernel_neg (y : Vec3) (s : ℝ) : heatKernel (-y) s = heatKernel y s := by
  by_cases hs : 0 < s
  · rw [heatKernel_eq_formula_sum hs, heatKernel_eq_formula_sum hs]
    congr 2
    simp only [Pi.neg_apply, neg_sq]
  · rw [heatKernel_eq_zero_of_nonpos (le_of_not_gt hs),
      heatKernel_eq_zero_of_nonpos (le_of_not_gt hs)]

lemma backwardTestPotential_future_integral
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x : Vec3) (t : ℝ) :
    backwardTestPotential ζ (x, t) =
      ∫ s : ℝ in Ioi 0, heatConv s (fun y : Vec3 => ζ (y, t + s)) x := by
  let v : Vec3 × ℝ := (x, t)
  let _ : backwardProductVolume.IsAddLeftInvariant := by
    dsimp [backwardProductVolume]
    infer_instance
  let _ : SFinite backwardProductVolume := by
    dsimp [backwardProductVolume]
    exact Measure.prod.instSFinite
  let hconv := hζc.convolutionExists_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
    hζ.continuous
  have hbase : Integrable (fun p : Vec3 × ℝ =>
      backwardTestKernel p * ζ (v - p)) backwardProductVolume := by
    change Integrable (fun p : Vec3 × ℝ =>
      ContinuousLinearMap.lsmul ℝ ℝ (backwardTestKernel p) (ζ (v - p)))
      backwardProductVolume
    exact (hconv v).integrable
  have hneg : MeasurePreserving (MeasurableEquiv.neg (Vec3 × ℝ) :
      Vec3 × ℝ → Vec3 × ℝ) backwardProductVolume backwardProductVolume := by
    dsimp [backwardProductVolume]
    exact (Measure.measurePreserving_neg (volume : Measure Vec3)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hplus : Integrable (fun q : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from q) * ζ (v + q)) backwardProductVolume := by
    have hcomp := hneg.integrable_comp
      (show AEStronglyMeasurable (fun p : Vec3 × ℝ =>
        backwardTestKernel p * ζ (v - p)) backwardProductVolume from
        hbase.aestronglyMeasurable)
    have hi := hcomp.mpr hbase
    convert hi using 1
    funext q
    change heatKernelPlus (show ParabolicPoint from q) * ζ (v + q) =
      backwardTestKernel (-q) * ζ (v - -q)
    simp only [backwardTestKernel]
    congr 1
    · change heatKernelPlus (show ParabolicPoint from q) =
        heatKernelPlus (show ParabolicPoint from -(-q))
      simp
    · simp [sub_eq_add_neg]
  have hpotential : backwardTestPotential ζ v =
      ∫ q : Vec3 × ℝ, heatKernelPlus (show ParabolicPoint from q) * ζ (v + q)
        ∂backwardProductVolume := by
    rw [backwardTestPotential_eq_backwardHeatPotential ζ v]
    unfold backwardHeatPotential backwardHeatKernel
    let hadd0 := measurePreserving_add_left backwardProductVolume v
    let hadd : MeasurePreserving (MeasurableEquiv.addLeft v :
        Vec3 × ℝ → Vec3 × ℝ) backwardProductVolume backwardProductVolume := by
      convert hadd0 using 1
      funext q
      rfl
    change (∫ z : Vec3 × ℝ,
        heatKernelPlus (show ParabolicPoint from (z - v)) * ζ z
          ∂backwardProductVolume) = _
    have h := hadd.integral_comp'
      (fun z : Vec3 × ℝ => heatKernelPlus (show ParabolicPoint from (z - v)) * ζ z)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h.symm
  change backwardTestPotential ζ v = _
  rw [hpotential]
  let F : Vec3 × ℝ → ℝ := fun q =>
    heatKernelPlus (show ParabolicPoint from q) * ζ ((x, t) + q)
  have hzero : ∀ᵐ q : Vec3 × ℝ ∂backwardProductVolume,
      F q = (Set.univ ×ˢ Ioi 0).indicator F q := by
    filter_upwards [] with q
    by_cases hq : 0 < q.2
    · simp [Set.indicator_of_mem, hq]
    · have hq0 : heatKernelPlus (show ParabolicPoint from q) = 0 :=
        heatKernelPlus_eq_zero_of_nonpos (le_of_not_gt hq)
      simp only [Set.indicator_apply, mem_prod, mem_univ, true_and]
      simp [hq, hq0, F]
  change (∫ q : Vec3 × ℝ, F q ∂backwardProductVolume) = _
  have hset : MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ)) :=
    MeasurableSet.prod (show MeasurableSet (Set.univ : Set Vec3) from MeasurableSet.univ)
      measurableSet_Ioi
  rw [integral_congr_ae hzero, integral_indicator hset]
  have hmeasure :
      (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) =
        backwardProductVolume.restrict (Set.univ ×ˢ Ioi (0 : ℝ)) := by
    rw [backwardProductVolume, ← Measure.prod_restrict]
    simp
  have hprod : Integrable F
      ((volume : Measure Vec3).prod (volume.restrict (Ioi 0))) := by
    rw [hmeasure]
    simpa [F, v] using hplus.restrict
  have hswap : ∫ q : Vec3 × ℝ, F q ∂
      ((volume : Measure Vec3).prod (volume.restrict (Ioi 0))) =
      ∫ s : ℝ in Ioi 0, ∫ y : Vec3, F (y, s) := by
    have hs := integral_prod_swap
      (μ := (volume : Measure Vec3)) (ν := volume.restrict (Ioi (0 : ℝ))) F
    have hp := integral_prod (fun q : ℝ × Vec3 => F q.swap) hprod.swap
    calc
      ∫ q : Vec3 × ℝ, F q ∂
          ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) =
          ∫ q : ℝ × Vec3, F q.swap ∂
            ((volume.restrict (Ioi (0 : ℝ))).prod volume) := hs.symm
      _ = ∫ s : ℝ in Ioi 0, ∫ y : Vec3, F (y, s) := by
        simpa only [Prod.swap_prod_mk] using hp
  change (∫ q : Vec3 × ℝ, F q ∂
      (backwardProductVolume.restrict (Set.univ ×ˢ Ioi (0 : ℝ)))) = _
  rw [← hmeasure, hswap]
  apply integral_congr_ae
  filter_upwards [] with s
  change (∫ y : Vec3, heatKernelPlus (show ParabolicPoint from (y, s)) *
      ζ (x + y, t + s)) = heatConv s (fun y : Vec3 => ζ (y, t + s)) x
  rw [show (fun y : Vec3 => heatKernelPlus (show ParabolicPoint from (y, s)) *
      ζ (x + y, t + s)) =
      fun y : Vec3 => heatKernel y s * ζ (x + y, t + s) by
    funext y
    rw [heatKernelPlus_eq_heatKernel]]
  rw [heatConv_eq_integral]
  let hneg3 : MeasurePreserving (MeasurableEquiv.neg Vec3 : Vec3 → Vec3)
      volume volume := Measure.measurePreserving_neg volume
  have hi := hneg3.integral_comp'
    (fun y : Vec3 => heatKernel y s * ζ (x + y, t + s))
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with y
  change heatKernel (-y) s * ζ (x + (-y), t + s) =
    heatKernel y s * ζ (x - y, t + s)
  rw [heatKernel_neg]
  simp [sub_eq_add_neg]

lemma backwardTestPotential_future_integrable
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x : Vec3) (t : ℝ) :
    IntegrableOn (fun s : ℝ =>
      heatConv s (fun y : Vec3 => ζ (y, t + s)) x) (Ioi 0) volume := by
  let v : Vec3 × ℝ := (x, t)
  let _ : backwardProductVolume.IsAddLeftInvariant := by
    dsimp [backwardProductVolume]
    infer_instance
  let _ : SFinite backwardProductVolume := by
    dsimp [backwardProductVolume]
    exact Measure.prod.instSFinite
  have hconv := hζc.convolutionExists_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) backwardTestKernel_locallyIntegrable
    hζ.continuous
  have hbase : Integrable (fun p : Vec3 × ℝ =>
      backwardTestKernel p * ζ (v - p)) backwardProductVolume := by
    change Integrable (fun p : Vec3 × ℝ =>
      ContinuousLinearMap.lsmul ℝ ℝ (backwardTestKernel p) (ζ (v - p)))
      backwardProductVolume
    exact (hconv v).integrable
  have hneg : MeasurePreserving (MeasurableEquiv.neg (Vec3 × ℝ) :
      Vec3 × ℝ → Vec3 × ℝ) backwardProductVolume backwardProductVolume := by
    dsimp [backwardProductVolume]
    exact (Measure.measurePreserving_neg (volume : Measure Vec3)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hplus : Integrable (fun q : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from q) * ζ (v + q)) backwardProductVolume := by
    have hcomp := hneg.integrable_comp
      (show AEStronglyMeasurable (fun p : Vec3 × ℝ =>
        backwardTestKernel p * ζ (v - p)) backwardProductVolume from
        hbase.aestronglyMeasurable)
    have hi := hcomp.mpr hbase
    convert hi using 1
    funext q
    change heatKernelPlus (show ParabolicPoint from q) * ζ (v + q) =
      backwardTestKernel (-q) * ζ (v - -q)
    simp only [backwardTestKernel]
    congr 1
    · change heatKernelPlus (show ParabolicPoint from q) =
        heatKernelPlus (show ParabolicPoint from -(-q))
      simp
    · simp [sub_eq_add_neg]
  have hmeasure : (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) =
      backwardProductVolume.restrict (Set.univ ×ˢ Ioi (0 : ℝ)) := by
    rw [backwardProductVolume, ← Measure.prod_restrict]
    simp
  have hprod : Integrable (fun q : Vec3 × ℝ =>
      heatKernelPlus (show ParabolicPoint from q) * ζ (v + q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioi 0))) := by
    rw [hmeasure]
    simpa using hplus.restrict
  have htime := hprod.integral_prod_right
  change Integrable (fun s : ℝ =>
      heatConv s (fun y : Vec3 => ζ (y, t + s)) x)
      (volume.restrict (Ioi 0))
  apply htime.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hneg3 : MeasurePreserving (MeasurableEquiv.neg Vec3 : Vec3 → Vec3)
      volume volume := Measure.measurePreserving_neg volume
  have hi := hneg3.integral_comp'
    (fun y : Vec3 => heatKernel y s * ζ (x + y, t + s))
  calc
    (∫ y : Vec3, heatKernelPlus (show ParabolicPoint from (y, s)) *
        ζ (v + (y, s))) =
        ∫ y : Vec3, heatKernel y s * ζ (x + y, t + s) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [heatKernelPlus_eq_heatKernel]
      rfl
    _ = ∫ y : Vec3, heatKernel y s * ζ (x - y, t + s) := by
      rw [← hi]
      apply integral_congr_ae
      filter_upwards [] with y
      change heatKernel (-y) s * ζ (x + (-y), t + s) =
        heatKernel y s * ζ (x - y, t + s)
      rw [heatKernel_neg]
      simp [sub_eq_add_neg]
    _ = heatConv s (fun y : Vec3 => ζ (y, t + s)) x := by
      rw [heatConv_eq_integral]

lemma backwardTestPotential_future_truncated_tendsto
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (x : Vec3) (t : ℝ) :
    Tendsto (fun ε : ℝ => ∫ s : ℝ in Ioi ε,
      heatConv s (fun y : Vec3 => ζ (y, t + s)) x) (𝓝[>] 0)
      (𝓝 (backwardTestPotential ζ (x, t))) := by
  let f : ℝ → ℝ := fun s => heatConv s (fun y : Vec3 => ζ (y, t + s)) x
  have hf : IntegrableOn f (Ioi 0) volume := by
    exact backwardTestPotential_future_integrable hζ hζc x t
  have hf₀ : Integrable ((Ioi (0 : ℝ)).indicator f) volume :=
    hf.integrable_indicator measurableSet_Ioi
  have hmeasure : Tendsto (fun ε : ℝ =>
      (volume : Measure ℝ) (Ioc 0 ε)) (𝓝[>] 0) (𝓝 0) := by
    rw [show (fun ε : ℝ => (volume : Measure ℝ) (Ioc 0 ε)) =
        (fun ε : ℝ => ENNReal.ofReal ε) by
      funext ε
      rw [Real.volume_Ioc]
      simp]
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.tendsto_ofReal
        (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from
          (tendsto_id : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝[>] 0)).mono_right
            nhdsWithin_le_nhds))
  have hsmall : Tendsto (fun ε : ℝ =>
      ∫ s : ℝ in Ioc 0 ε, (Ioi (0 : ℝ)).indicator f s)
      (𝓝[>] 0) (𝓝 0) := hf₀.tendsto_setIntegral_nhds_zero hmeasure
  have hfull : (∫ s : ℝ in Ioi 0, (Ioi (0 : ℝ)).indicator f s) =
      ∫ s : ℝ in Ioi 0, f s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp [hs]
  have htrunc : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ s : ℝ in Ioc 0 ε, (Ioi (0 : ℝ)).indicator f s) +
          ∫ s : ℝ in Ioi ε, (Ioi (0 : ℝ)).indicator f s =
        ∫ s : ℝ in Ioi 0, (Ioi (0 : ℝ)).indicator f s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← intervalIntegral.integral_of_le hε.le]
    exact intervalIntegral.integral_interval_add_Ioi
      hf₀.integrableOn hf₀.integrableOn
  have hdiff : Tendsto (fun ε : ℝ =>
      ∫ s : ℝ in Ioi ε, (Ioi (0 : ℝ)).indicator f s)
      (𝓝[>] 0) (𝓝 (∫ s : ℝ in Ioi 0, (Ioi (0 : ℝ)).indicator f s)) := by
    have hsub : Tendsto (fun ε : ℝ =>
        (∫ s : ℝ in Ioi 0, (Ioi (0 : ℝ)).indicator f s) -
          ∫ s : ℝ in Ioc 0 ε, (Ioi (0 : ℝ)).indicator f s)
        (𝓝[>] 0) (𝓝 (∫ s : ℝ in Ioi 0, (Ioi (0 : ℝ)).indicator f s)) := by
      simpa using (tendsto_const_nhds.sub hsmall)
    apply hsub.congr'
    filter_upwards [htrunc] with ε hε
    linarith only [hε]
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ s : ℝ in Ioi ε, (Ioi (0 : ℝ)).indicator f s) =
        ∫ s : ℝ in Ioi ε, f s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hε hs
    simp [hs0]
  have hdiff' : Tendsto (fun ε : ℝ => ∫ s : ℝ in Ioi ε, f s)
      (𝓝[>] 0) (𝓝 (∫ s : ℝ in Ioi 0, f s)) := by
    simpa only [hfull] using hdiff.congr' heq
  simpa only [f, backwardTestPotential_future_integral hζ hζc x t] using hdiff'


end CKN.Foundation.Heat
