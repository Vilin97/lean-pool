/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientTopSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TensorNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SeedMultiplierSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceSmallnessThreshold
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FiniteSpatialWordBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmBounds

/-! Adapter to the actual spatial divergence-gradient tensor.
Import this module directly: HmBounds already imports the AmnrBounds facade. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The two integration measures in the Amnr and Hm APIs coincide. -/
theorem amnr_product_measure_eq_timeCube :
    (volume.restrict (uIoc (0 : ℝ) 1)).prod
      (volume.restrict AVenhance.unitCube) = volume.restrict AVenhance.timeCube := by
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), ← restrict_Ioo_eq_restrict_Ioc,
    Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
  rfl

/-- Two spatial letters fit the source budget at every Hm summation level. -/
theorem amnr_hm_second_derivative_budget {β : ℝ} {r : ℕ}
    (hr : r ∈ Finset.range (AVenhance.Jcut β)) :
    2 ≤ AVenhance.Nstar β - 2 * r := by
  have hr' := Finset.mem_range.mp hr
  unfold AVenhance.Jcut at hr'
  omega

/-- Actual iterate solutions give the finite joint regularity required by
spatial slicing; no mixed estimate is assumed here. -/
theorem amnr_actual_contDiffOn {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1)))
      κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (n r a : ℕ) (hbudget : a + r ≤ AVenhance.Nstar β) (i j k : Fin 2) :
    ContDiffOn ℝ a
      (fun z : AmnrSpace => I.Amnr hΦ m κm n (T (AVenhance.Nstar β)) r z.1 z.2 i j k)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))) := by
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ univ
  let b := fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hbInf : ContDiff ℝ (⊤ : ℕ∞) b :=
    contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ hm N)
  have hb : ContDiffOn ℝ (AVenhance.Nstar β) b U :=
    (hbInf.of_le (by simp)).contDiffOn
  have hB (i p : Fin 2) : ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrVelocityGradient b i p) U :=
    (amnrVelocityGradient_contDiffOn_infty hU hbInf.contDiffOn i p).of_le (by simp)
  obtain ⟨Ffinal, hfinal⟩ := amnr_tIterates_classical_family I hΦ hθprev hT
    (AVenhance.Nstar β) le_rfl
  have hg (p : Fin 2) : ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrTGradient (T (AVenhance.Nstar β)) p) U :=
    amnr_classical_gradient_smooth hfinal p _
  have hf (i p : Fin 2) : ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrSeedMultiplier I hΦ m κm n j k i p) U :=
    (amnr_seedMultiplier_contDiff I hΦ hm hκm n _ le_rfl j k i p).contDiffOn
  exact Amnr_contDiffOn_of_factors I hΦ hm κm n (T (AVenhance.Nstar β))
    hU j k hb hB hf hg hbudget i

/-- Finite actual joint regularity supplies the Hessian entry measurability
argument required by the Hm consumer, on its exact physical cell. -/
theorem amnr_hm_hessian_entry_measurable_of_contDiff {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n r : ℕ)
    (hreg : ∀ i j k : Fin 2, ContDiffOn ℝ 2
      (fun z : AmnrSpace => I.Amnr hΦ m κ n T r z.1 z.2 i j k)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2)))) :
    ∀ i j k p : Fin 2, AEStronglyMeasurable
      (fun z => amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p)
      (volume.restrict AVenhance.timeCube) := by
  let μ := volume.restrict AVenhance.timeCube
  have hslice (i j k p : Fin 2) (z : AmnrSpace) (hz : z ∈ AVenhance.timeCube) :
      amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord [p, i] 0)
        (fun y => I.Amnr hΦ m κ n T r y.1 y.2 i j k) z =
      amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p := by
    have ht : 0 < z.1 := hz.1.1
    have hh := amnrWord_spatial_slice_on_vertical_domain_finite
      (isOpen_Ioi.prod isOpen_univ) (hreg i j k)
      (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) [p, i]
      (by norm_num) z.1 (fun _ => ⟨ht, mem_univ _⟩) z.2
    simpa only [amnrMixedWord, List.replicate_zero, List.append_nil,
      amnrSpaceWord, AVenhance.spaceGrad, amnrSpatialDivergenceGradientTensor] using hh
  have hmeas (i j k p : Fin 2) : AEStronglyMeasurable
      (fun z => amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p) μ := by
    have hh := amnrWord_contDiffOn (isOpen_Ioi.prod isOpen_univ)
      (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : AmnrSpace => (0 : Vec 2))
        (Ioi (0 : ℝ) ×ˢ univ)) (hreg i j k) [some p, some i]
      (n := 0) (by norm_num)
    have heq := amnrWord_spatial_independent
      (fun _ => (0 : Vec 2))
      (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) [p, i]
      (fun y => I.Amnr hΦ m κ n T r y.1 y.2 i j k)
    have hh' := hh.continuousOn.mono
      (show AVenhance.timeCube ⊆ Ioi (0 : ℝ) ×ˢ univ from
        fun z hz => ⟨hz.1.1, mem_univ _⟩)
    have hm := hh'.aestronglyMeasurable (μ := volume) amnr_timeCube_isOpen.measurableSet
    apply hm.congr
    filter_upwards [ae_restrict_mem amnr_timeCube_isOpen.measurableSet] with z hz
    rw [show [some p, some i] = [p, i].map some from rfl, heq]
    exact hslice i j k p z hz
  exact hmeas

/-- A spatial specialization of the mixed tensor bound supplies the
`hAmnrHess` input of `hm_bounds_of_flowFTC_and_pAmnr`, with its exact
four-index carrier. Joint C² regularity is a primitive slicing condition;
`amnr_actual_contDiffOn` proves it for the actual iterates. -/
theorem amnr_hm_hessian_of_mixed_bound {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n r : ℕ)
    {B : ℝ}
    (hreg : ∀ i j k : Fin 2, ContDiffOn ℝ 2
      (fun z : AmnrSpace => I.Amnr hΦ m κ n T r z.1 z.2 i j k)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))))
    (hBound : ∀ p i : Fin 2,
      eLpNorm (fun z : AmnrSpace => fun a j k : Fin 2 =>
        amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
          (amnrMixedWord [p, i] 0)
          (fun y => I.Amnr hΦ m κ n T r y.1 y.2 a j k) z) 2
        ((volume.restrict (uIoc 0 1)).prod (volume.restrict AVenhance.unitCube)) ≤
          ENNReal.ofReal B) :
    eLpNorm (amnrSpatialDivergenceGradientTensor I hΦ m κ T n r) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal (16 * B) := by
  let μ := volume.restrict AVenhance.timeCube
  have hslice (i j k p : Fin 2) (z : AmnrSpace) (hz : z ∈ AVenhance.timeCube) :
      amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord [p, i] 0)
        (fun y => I.Amnr hΦ m κ n T r y.1 y.2 i j k) z =
      amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p := by
    have ht : 0 < z.1 := hz.1.1
    have hh := amnrWord_spatial_slice_on_vertical_domain_finite
      (isOpen_Ioi.prod isOpen_univ) (hreg i j k)
      (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) [p, i]
      (by norm_num) z.1 (fun _ => ⟨ht, mem_univ _⟩) z.2
    simpa only [amnrMixedWord, List.replicate_zero, List.append_nil,
      amnrSpaceWord, AVenhance.spaceGrad, amnrSpatialDivergenceGradientTensor] using hh
  have hmeas := amnr_hm_hessian_entry_measurable_of_contDiff I hΦ m κ T n r hreg
  have hcoord (i j k p : Fin 2) :
      eLpNorm (fun z => amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i j k p) 2 μ ≤
        ENNReal.ofReal B := by
    have hb := hBound p i
    rw [amnr_product_measure_eq_timeCube] at hb
    refine (eLpNorm_mono_ae (hmeas i j k p) ?_).trans hb
    filter_upwards [ae_restrict_mem amnr_timeCube_isOpen.measurableSet] with z hz
    rw [← hslice i j k p z hz]
    let F : Fin 2 → Fin 2 → Fin 2 → ℝ := fun a j k =>
      amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord [p, i] 0)
        (fun y => I.Amnr hΦ m κ n T r y.1 y.2 a j k) z
    exact (norm_le_pi_norm (F i j) k).trans
      ((norm_le_pi_norm (F i) j).trans (norm_le_pi_norm F i))
  have hAll : AEStronglyMeasurable
      (amnrSpatialDivergenceGradientTensor I hΦ m κ T n r) μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      aemeasurable_pi_iff.mpr fun k => aemeasurable_pi_iff.mpr fun p =>
        (hmeas i j k p).aemeasurable
  have h3 (i : Fin 2) : eLpNorm
      (fun z => amnrSpatialDivergenceGradientTensor I hΦ m κ T n r z i) 2 μ ≤
        ENNReal.ofReal (8 * B) :=
    amnr_tensor_L2_le_eight ((continuous_apply i).comp_aestronglyMeasurable hAll) (hcoord i)
  convert amnr_pi_L2_le_card hAll h3 using 1
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  congr 1
  ring

end AVenhance.Infra.Section4
