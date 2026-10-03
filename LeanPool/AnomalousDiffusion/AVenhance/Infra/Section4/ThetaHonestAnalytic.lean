/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaCommutatorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergyLevels
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaFluxEstimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences

/-! Honest analytic estimates for the classical theta solution. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem theta_analytic_funList_sum_apply {α : Type*}
    (L : List (α → ℝ)) (x : α) :
    L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

theorem ThetaHonestAnalytic.theta_word_spatial_energy_range_bddAbove
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol b κ (fun _ _ => 0) θ₀ θ)
    (w : List (Fin 2)) :
    BddAbove (Set.range fun t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} =>
      thetaWordSpatialEnergy θ w t.1) := by
  let u : ℝ → Vec 2 → ℝ := fun t x => classicalWordDerivative w (θ t) x
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => classicalWordDerivative w (θ p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)
    exact theta_classical_word_joint_contDiffOn_nonneg hsol.1 w
  have hcont := theta_energy_continuousOn hu (by norm_num : (0 : ℝ) ≤ 1)
  have hcont' : ContinuousOn (fun t => thetaWordSpatialEnergy θ w t)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [thetaWordSpatialEnergy, u] using hcont
  have hcompact : BddAbove
      (thetaWordSpatialEnergy θ w '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hcont'
  apply hcompact.mono
  rintro y ⟨t, rfl⟩
  exact ⟨t.1, t.2, rfl⟩

theorem ThetaHonestAnalytic.theta_word_spatial_energy_nonneg
    (θ : ℝ → Vec 2 → ℝ) (w : List (Fin 2)) (t : ℝ) :
    0 ≤ thetaWordSpatialEnergy θ w t := by
  simp only [thetaWordSpatialEnergy]
  apply setIntegral_nonneg thetaTime_measurableSet_unitCube
  intro x hx
  exact sq_nonneg _

/-- Closed time-space unit cell for the analytic induction estimates. -/
def ThetaHonestAnalytic.thetaHonestClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ
    (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem ThetaHonestAnalytic.thetaHonestClosedCell_compact :
    IsCompact ThetaHonestAnalytic.thetaHonestClosedCell := by
  apply IsCompact.prod isCompact_Icc
  simpa [ThetaHonestAnalytic.thetaHonestClosedCell] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem ThetaHonestAnalytic.thetaHonestTimeCube_subset_closedCell :
    AVenhance.timeCube ⊆ ThetaHonestAnalytic.thetaHonestClosedCell := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
  change ∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1
  intro i hi
  exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩

/-- The gradient energy of one ordered derivative over the initial time
interval `[0,T]`. -/
noncomputable def thetaIntervalWordGradientEnergy
    (θ : ℝ → Vec 2 → ℝ) (T : ℝ) (w : List (Fin 2)) : ℝ :=
  ∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
    vecNormSq (spaceGrad (classicalWordDerivative w (θ t)) x)

theorem theta_interval_word_l2_le_gradient
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {i : Fin 2} (word right : List (Fin 2))
    (hperm : word.Perm (i :: right)) :
    (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      (thetaWordExtension θ word p) ^ 2) ≤
      thetaWordSpaceTimeGradientEnergy θ right := by
  have hsub : Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube ⊆
      AVenhance.timeCube := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, ht.2.trans_le hT.2⟩, hx⟩
  have hf : Continuous (thetaWordExtension θ word) :=
    thetaWordExtension_continuous hθ
  have hInt : IntegrableOn (fun p => (thetaWordExtension θ word p) ^ 2)
      AVenhance.timeCube := by
    exact (hf.pow 2).continuousOn.integrableOn_compact
      ThetaHonestAnalytic.thetaHonestClosedCell_compact |>.mono_set
          ThetaHonestAnalytic.thetaHonestTimeCube_subset_closedCell
  have hnonneg : 0 ≤ᵐ[volume.restrict AVenhance.timeCube]
      (fun p => (thetaWordExtension θ word p) ^ 2) :=
    ae_of_all _ (fun _ => sq_nonneg _)
  have hmono := MeasureTheory.setIntegral_mono_set hInt hnonneg
    (Filter.Eventually.of_forall hsub)
  exact hmono.trans <|
    theta_word_derivative_energy_le_gradient hθ hperm

theorem theta_intervalCube_integral_eq_interval_integral
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {f : ℝ × Vec 2 → ℝ} (hf : Continuous f) :
    (∫ p in (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube), f p) =
      ∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube, f (t, x) := by
  by_cases hT0 : T = 0
  · subst T
    simp
  · have hTpos : 0 < T := lt_of_le_of_ne hT.1 (Ne.symm hT0)
    let μ : Measure ℝ := volume
    let ν : Measure (Vec 2) := volume
    have htime : Set.Ioo (0 : ℝ) T =ᵐ[μ] Set.Ioc 0 T := by
      have hdiff₁ : Set.Ioo (0 : ℝ) T \ Set.Ioc 0 T = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact ht.2 ⟨ht.1.1, ht.1.2.le⟩
      have hdiff₂ : Set.Ioc 0 T \ Set.Ioo 0 T = {T} := by
        ext t
        simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Ioo,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨ht0, htT⟩, hnot⟩
          have hnot' : ¬ (0 < t ∧ t < T) := hnot
          have : t = T := by
            rcases lt_or_eq_of_le htT with hlt | heq
            · exact (hnot' ⟨ht0, hlt⟩).elim
            · exact heq
          exact this
        · intro ht
          subst t
          exact ⟨⟨hTpos, le_rfl⟩, by simp⟩
      rw [MeasureTheory.ae_eq_set]
      constructor
      · rw [hdiff₁]
        simp
      · rw [hdiff₂]
        simp [measure_singleton]
    have htimeMeasure : μ.restrict (Set.Ioo (0 : ℝ) T) =
        μ.restrict (Set.Ioc 0 T) :=
      MeasureTheory.Measure.restrict_congr_set htime
    have hproductMeasure :
        (μ.restrict (Set.Ioo (0 : ℝ) T)).prod
            (ν.restrict AVenhance.unitCube) =
          (volume : Measure (ℝ × Vec 2)).restrict
            (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube) := by
      rw [MeasureTheory.Measure.prod_restrict]
      rw [← MeasureTheory.Measure.volume_eq_prod ℝ (Vec 2)]
    let closedCell : Set (Vec 2) :=
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
    have hclosed : IsCompact closedCell := by
      simpa [closedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
    let K : Set (ℝ × Vec 2) := Set.Icc (0 : ℝ) T ×ˢ closedCell
    have hK : IsCompact K := IsCompact.prod isCompact_Icc hclosed
    have hsub : Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube ⊆ K := by
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      refine ⟨⟨le_of_lt ht.1, ht.2.le⟩, ?_⟩
      change ∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1
      intro i hi
      exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩
    have hfInt : IntegrableOn f
        (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube) :=
      (hf.continuousOn.integrableOn_compact hK).mono_set hsub
    have hfProd : Integrable f
        ((μ.restrict (Set.Ioo (0 : ℝ) T)).prod
          (ν.restrict AVenhance.unitCube)) := by
      rw [hproductMeasure]
      exact hfInt
    have hprod := MeasureTheory.integral_prod f hfProd
    rw [intervalIntegral.integral_of_le hT.1]
    calc
      (∫ p in (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube), f p) =
          ∫ t in Set.Ioo (0 : ℝ) T,
            ∫ x in AVenhance.unitCube, f (t, x) := by
        rw [← hproductMeasure]
        exact hprod
      _ = ∫ t in Set.Ioc 0 T,
            ∫ x in AVenhance.unitCube, f (t, x) := by
        change (∫ t, (∫ x in AVenhance.unitCube, f (t, x)) ∂
          (μ.restrict (Set.Ioo (0 : ℝ) T))) = _
        rw [htimeMeasure]

/-- On a partial time interval, a coordinate derivative is controlled by
the gradient energy of the complementary word on that same interval. -/
theorem theta_interval_word_l2_le_partial_gradient
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {i : Fin 2} (word right : List (Fin 2))
    (hperm : word.Perm (i :: right)) :
    (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      (thetaWordExtension θ word p) ^ 2) ≤
      thetaIntervalWordGradientEnergy θ T right := by
  let S : Set (ℝ × Vec 2) := Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube
  let f : ℝ × Vec 2 → ℝ := fun p => (thetaWordExtension θ word p) ^ 2
  let g : ℝ × Vec 2 → ℝ := fun p =>
    vecNormSq (thetaWordGradientExtension θ right p)
  have hsub : S ⊆ ThetaHonestAnalytic.thetaHonestClosedCell := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨⟨le_of_lt ht.1, ht.2.le.trans hT.2⟩, ?_⟩
    change ∀ j ∈ Set.univ, x j ∈ Set.Icc (0 : ℝ) 1
    intro j hj
    exact ⟨le_of_lt (hx j hj).1, le_of_lt (hx j hj).2⟩
  have hpoint (p : ℝ × Vec 2) (hp : p ∈ S) : f p ≤ g p := by
    have ht : 0 < p.1 := hp.1.1
    have hslice := theta_classical_word_slice_contDiff_nonneg hθ [] p.1 ht.le
    have hslice' : ContDiff ℝ (⊤ : ℕ∞) (θ p.1) := by
      simpa [classicalWordDerivative,
        Classical.classicalWordDerivative] using hslice
    change (thetaWordExtension θ word p) ^ 2 ≤
      vecNormSq (thetaWordGradientExtension θ right p)
    rw [thetaWordExtension_eq_slice p.1 ht p.2]
    calc
      classicalWordDerivative word (θ p.1) p.2 ^ 2 ≤
          vecNormSq (spaceGrad (classicalWordDerivative right (θ p.1)) p.2) :=
        classicalWordDerivative_sq_le_gradient_of_perm
          word right i (θ p.1) hslice' p.2 hperm
      _ = vecNormSq (thetaWordGradientExtension θ right p) := by
        rw [thetaWordGradientExtension_eq_slice
          (u := θ) (w := right) p.1 ht p.2]
  have hfcont : Continuous f := (thetaWordExtension_continuous hθ).pow 2
  have hgcont : Continuous g := by
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension θ right p j * thetaWordGradientExtension θ right p j)
    have hgrad := thetaWordGradientExtension_continuous (u := θ) (w := right) hθ
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hgrad).mul
      ((continuous_apply j).comp hgrad)
  have hIf : IntegrableOn f S :=
    (hfcont.continuousOn.integrableOn_compact ThetaHonestAnalytic.thetaHonestClosedCell_compact)
      |>.mono_set hsub
  have hIg : IntegrableOn g S :=
    (hgcont.continuousOn.integrableOn_compact ThetaHonestAnalytic.thetaHonestClosedCell_compact)
      |>.mono_set hsub
  have hmono := MeasureTheory.setIntegral_mono_on hIf hIg
    (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube) hpoint
  have hcube := theta_intervalCube_integral_eq_interval_integral hT hgcont
  have hslice : (∫ p in S, g p) = thetaIntervalWordGradientEnergy θ T right := by
    rw [hcube]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) T := by
      simpa only [Set.uIoc_of_le hT.1] using ht
    apply integral_congr_ae
    filter_upwards with x
    dsimp [g, thetaIntervalWordGradientEnergy]
    rw [thetaWordGradientExtension_eq_slice
      (u := θ) (w := right) t ht'.1 x]
  simpa [S, f] using hmono.trans_eq hslice

theorem ThetaHonestAnalytic.theta_intervalCube_integral_rescale_eq
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {f : ℝ × Vec 2 → ℝ} (hf : Continuous f) :
    (∫ p in (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube), f p) =
      T * (∫ p in AVenhance.timeCube, f (T * p.1, p.2)) := by
  by_cases hT0 : T = 0
  · subst T
    simp
  · have hTne : T ≠ 0 := hT0
    let F : ℝ → ℝ := fun t => ∫ x in AVenhance.unitCube, f (t, x)
    have hFpartial :=
      theta_intervalCube_integral_eq_interval_integral hT hf
    have hscaleT : Continuous (fun p : ℝ × Vec 2 => T * p.1) :=
      continuous_const.mul continuous_fst
    have hmap : Continuous (fun p : ℝ × Vec 2 => (T * p.1, p.2)) :=
      hscaleT.prodMk continuous_snd
    have hFscaled := theta_timeCube_integral_eq_interval_integral
      (f := fun p => f (T * p.1, p.2)) (hf.comp hmap)
    have hchange := intervalIntegral.integral_comp_mul_left
      (f := F) (a := (0 : ℝ)) (b := 1) (c := T) hTne
    have hchange' : (∫ s in (0 : ℝ)..1, F (T * s)) =
        T⁻¹ * (∫ t in (0 : ℝ)..T, F t) := by
      simpa [F, smul_eq_mul] using hchange
    have hscale : (∫ t in (0 : ℝ)..T, F t) =
        T * (∫ s in (0 : ℝ)..1, F (T * s)) := by
      have hcancel : T * T⁻¹ = 1 := by field_simp
      calc
        (∫ t in (0 : ℝ)..T, F t) =
            (T * T⁻¹) * (∫ t in (0 : ℝ)..T, F t) := by rw [hcancel, one_mul]
        _ = T * (T⁻¹ * (∫ t in (0 : ℝ)..T, F t)) := by ring
        _ = T * (∫ s in (0 : ℝ)..1, F (T * s)) := by rw [← hchange']
    rw [hFpartial, hFscaled]
    exact hscale

theorem theta_intervalCube_integral_mul_bounded_le
    {T M : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {f g a : ℝ × Vec 2 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (ha : Continuous a)
    (hM : 0 ≤ M)
    (haM : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      |a p| ≤ M) :
    |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
        f p * (a p * g p)| ≤
      M * Real.sqrt
          (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p ^ 2) *
        Real.sqrt
          (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, g p ^ 2) := by
  by_cases hT0 : T = 0
  · subst T
    simp
  · have hTpos : 0 < T := lt_of_le_of_ne hT.1 (Ne.symm hT0)
    let rescale : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (T * p.1, p.2)
    let fT := fun p => f (rescale p)
    let gT := fun p => g (rescale p)
    let aT := fun p => a (rescale p)
    have hmap : Continuous rescale :=
      (continuous_const.mul continuous_fst).prodMk continuous_snd
    have hfT : Continuous fT := hf.comp hmap
    have hgT : Continuous gT := hg.comp hmap
    have haT : Continuous aT := ha.comp hmap
    have hcoefT : ∀ p ∈ AVenhance.timeCube, |aT p| ≤ M := by
      intro p hp
      have hpt : (T * p.1, p.2) ∈
          Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube := by
        refine ⟨⟨mul_pos hTpos hp.1.1, ?_⟩, hp.2⟩
        nlinarith [mul_lt_mul_of_pos_left hp.1.2 hTpos]
      exact haM (T * p.1, p.2) hpt
    have hfull := theta_timeCube_integral_mul_bounded_le hfT hgT haT hM hcoefT
    have hprod := ThetaHonestAnalytic.theta_intervalCube_integral_rescale_eq hT
      (hf.mul (ha.mul hg))
    have hfsq := ThetaHonestAnalytic.theta_intervalCube_integral_rescale_eq hT (hf.pow 2)
    have hgsq := ThetaHonestAnalytic.theta_intervalCube_integral_rescale_eq hT (hg.pow 2)
    have hIprod :
        (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          f p * (a p * g p)) =
          T * (∫ p in AVenhance.timeCube, fT p * (aT p * gT p)) := by
      simpa [fT, aT, gT, rescale] using hprod
    have hIf : 0 ≤ ∫ p in AVenhance.timeCube, fT p ^ 2 :=
      setIntegral_nonneg
        (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube)
        (fun p hp => sq_nonneg _)
    have hIg : 0 ≤ ∫ p in AVenhance.timeCube, gT p ^ 2 :=
      setIntegral_nonneg
        (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube)
        (fun p hp => sq_nonneg _)
    have hrootf :
        Real.sqrt (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p ^ 2) =
          Real.sqrt T * Real.sqrt (∫ p in AVenhance.timeCube, fT p ^ 2) := by
      rw [show (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p ^ 2) =
          T * (∫ p in AVenhance.timeCube, fT p ^ 2) by
            simpa [fT, rescale] using hfsq]
      exact Real.sqrt_mul hT.1 _
    have hrootg :
        Real.sqrt (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, g p ^ 2) =
          Real.sqrt T * Real.sqrt (∫ p in AVenhance.timeCube, gT p ^ 2) := by
      rw [show (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, g p ^ 2) =
          T * (∫ p in AVenhance.timeCube, gT p ^ 2) by
            simpa [gT, rescale] using hgsq]
      exact Real.sqrt_mul hT.1 _
    rw [hIprod, hrootf, hrootg]
    have hrootT : Real.sqrt T * Real.sqrt T = T := by
      calc
        Real.sqrt T * Real.sqrt T = Real.sqrt T ^ 2 := by ring
        _ = T := Real.sq_sqrt hT.1
    calc
      |T * ∫ p in AVenhance.timeCube, fT p * (aT p * gT p)| =
          T * |∫ p in AVenhance.timeCube, fT p * (aT p * gT p)| := by
            rw [abs_mul, abs_of_nonneg hT.1]
      _ ≤ T * (M * Real.sqrt (∫ p in AVenhance.timeCube, fT p ^ 2) *
            Real.sqrt (∫ p in AVenhance.timeCube, gT p ^ 2)) :=
          mul_le_mul_of_nonneg_left hfull hT.1
      _ = M * (Real.sqrt T * Real.sqrt (∫ p in AVenhance.timeCube, fT p ^ 2)) *
            (Real.sqrt T * Real.sqrt (∫ p in AVenhance.timeCube, gT p ^ 2)) := by
          calc
            T * (M * Real.sqrt (∫ p in AVenhance.timeCube, fT p ^ 2) *
                Real.sqrt (∫ p in AVenhance.timeCube, gT p ^ 2)) =
                (Real.sqrt T * Real.sqrt T) *
                  (M * Real.sqrt (∫ p in AVenhance.timeCube, fT p ^ 2) *
                    Real.sqrt (∫ p in AVenhance.timeCube, gT p ^ 2)) := by
                      rw [hrootT]
            _ = _ := by ring

theorem theta_word_spatial_energy_le_sup_of_classical
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol b κ (fun _ _ => 0) θ₀ θ)
    (w : List (Fin 2)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    thetaWordSpatialEnergy θ w t ≤ thetaWordSpatialEnergySup θ w := by
  exact thetaWordSpatialEnergy_le_sup θ w ht
    (ThetaHonestAnalytic.theta_word_spatial_energy_range_bddAbove hsol w)

theorem theta_word_spacetime_l2_le_spatial_sup
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol b κ (fun _ _ => 0) θ₀ θ)
    (w : List (Fin 2)) :
    (∫ p in AVenhance.timeCube,
      (thetaWordExtension θ w p) ^ 2) ≤ thetaWordSpatialEnergySup θ w := by
  let f : ℝ × Vec 2 → ℝ := thetaWordExtension θ w
  have hf : Continuous f := thetaWordExtension_continuous hsol.1
  have hFubini := theta_timeCube_integral_eq_interval_integral
    (f := fun p => (f p) ^ 2) (hf.pow 2)
  have hcontEnergy := theta_energy_continuousOn
    (u := fun t x => classicalWordDerivative w (θ t) x)
    (by
      change ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => classicalWordDerivative w (θ p.1) p.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)
      exact theta_classical_word_joint_contDiffOn_nonneg hsol.1 w)
    (by norm_num : (0 : ℝ) ≤ 1)
  have hinterval : IntervalIntegrable
      (fun t => thetaWordSpatialEnergy θ w t) volume 0 1 := by
    have hc : ContinuousOn (fun t => thetaWordSpatialEnergy θ w t)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), thetaWordSpatialEnergy]
        using hcontEnergy
    exact hc.intervalIntegrable
  have hconst : IntervalIntegrable
      (fun _ : ℝ => thetaWordSpatialEnergySup θ w) volume 0 1 :=
    intervalIntegrable_const
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      thetaWordSpatialEnergy θ w t ≤ thetaWordSpatialEnergySup θ w := by
    intro t ht
    exact theta_word_spatial_energy_le_sup_of_classical hsol w ht
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) hinterval hconst hbound
  have hinner :
      (∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube, (f (t, x)) ^ 2) =
      ∫ t in (0 : ℝ)..1, thetaWordSpatialEnergy θ w t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have ht0 : 0 ≤ t := ht'.1
    have hfeq : (fun x => f (t, x)) = classicalWordDerivative w (θ t) := by
      funext x
      simp [f, thetaWordExtension, max_eq_left ht0]
    change (∫ x in AVenhance.unitCube, (f (t, x)) ^ 2) = _
    have hsq : (fun x => (f (t, x)) ^ 2) =
        fun x => (classicalWordDerivative w (θ t) x) ^ 2 := by
      funext x
      simp [f, thetaWordExtension, max_eq_left ht0]
    rw [hsq]
    rfl
  rw [hFubini, hinner]
  calc
    (∫ t in (0 : ℝ)..1, thetaWordSpatialEnergy θ w t) ≤
        ∫ t in (0 : ℝ)..1, thetaWordSpatialEnergySup θ w := hmono
    _ = thetaWordSpatialEnergySup θ w := by simp

/-- Partial-time L² control of an order-`n` derivative by its uniform-time
spatial energy. -/
theorem theta_interval_word_l2_le_spatial_sup
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol b κ (fun _ _ => 0) θ₀ θ)
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1) (w : List (Fin 2)) :
    (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      (thetaWordExtension θ w p) ^ 2) ≤
      thetaWordSpatialEnergySup θ w := by
  have hsub : Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube ⊆
      AVenhance.timeCube := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, ht.2.trans_le hT.2⟩, hx⟩
  have hf : Continuous (thetaWordExtension θ w) :=
    thetaWordExtension_continuous hsol.1
  have hInt : IntegrableOn (fun p => (thetaWordExtension θ w p) ^ 2)
      AVenhance.timeCube := by
    exact (hf.pow 2).continuousOn.integrableOn_compact
      ThetaHonestAnalytic.thetaHonestClosedCell_compact |>.mono_set
          ThetaHonestAnalytic.thetaHonestTimeCube_subset_closedCell
  have hnonneg : 0 ≤ᵐ[volume.restrict AVenhance.timeCube]
      (fun p => (thetaWordExtension θ w p) ^ 2) :=
    ae_of_all _ (fun _ => sq_nonneg _)
  have hmono := MeasureTheory.setIntegral_mono_set hInt hnonneg
    (Filter.Eventually.of_forall hsub)
  exact hmono.trans <| theta_word_spacetime_l2_le_spatial_sup hsol w

theorem ThetaHonestAnalytic.theta_const_time_gradient_energy
    {u : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (w : List (Fin 2)) :
    thetaWordSpaceTimeGradientEnergy (fun _ => u) w =
      ∫ x in AVenhance.unitCube,
        vecNormSq (spaceGrad (classicalWordDerivative w u) x) := by
  let v : ℝ → Vec 2 → ℝ := fun _ => u
  have hvJ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry v)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => u p.2) :=
      hu.comp contDiff_snd
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => u p.2) _
    exact hc.contDiffOn
  have hgrad : Continuous (thetaWordGradientExtension v w) :=
    thetaWordGradientExtension_continuous hvJ
  have hf : Continuous (fun p : ℝ × Vec 2 =>
      vecNormSq (thetaWordGradientExtension v w p)) := by
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension v w p j * thetaWordGradientExtension v w p j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hgrad).mul ((continuous_apply j).comp hgrad)
  have hF := theta_timeCube_integral_eq_interval_integral
    (f := fun p : ℝ × Vec 2 =>
      vecNormSq (thetaWordGradientExtension v w p)) hf
  have hrewrite :
      (fun p : ℝ × Vec 2 =>
        vecNormSq (spaceGrad (classicalWordDerivative w (v p.1)) p.2)) =
        fun p => vecNormSq (thetaWordGradientExtension v w p) := by
    funext p
    rfl
  unfold thetaWordSpaceTimeGradientEnergy
  rw [hrewrite, hF]
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Vec 2) :
      vecNormSq (thetaWordGradientExtension v w (t, x)) =
        vecNormSq (spaceGrad (classicalWordDerivative w u) x) := by
    have hvec : thetaWordGradientExtension v w (t, x) =
        spaceGrad (classicalWordDerivative w u) x := by
      funext j
      change thetaWordExtension v (j :: w) (t, x) = _
      simp [thetaWordExtension, v, max_eq_left ht.1, classicalWordDerivative,
        Classical.classicalWordDerivative]
    rw [hvec]
  have hinner : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x in AVenhance.unitCube,
        vecNormSq (thetaWordGradientExtension v w (t, x))) =
      ∫ x in AVenhance.unitCube,
        vecNormSq (spaceGrad (classicalWordDerivative w u) x) := by
    intro t ht
    apply integral_congr_ae
    filter_upwards with x
    exact hpoint t ht x
  calc
    (∫ t in (0 : ℝ)..1,
      ∫ x in AVenhance.unitCube,
        vecNormSq (thetaWordGradientExtension v w (t, x))) =
      ∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          vecNormSq (spaceGrad (classicalWordDerivative w u) x) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      exact hinner t ht'
    _ = ∫ x in AVenhance.unitCube,
          vecNormSq (spaceGrad (classicalWordDerivative w u) x) := by simp

theorem theta_vecDot_list_sum
    (v : Vec 2) (L : List (Vec 2)) :
    vecDot v L.sum = (L.map fun z => vecDot v z).sum := by
  induction L with
  | nil => simp [vecDot]
  | cons a L ih =>
      have ih' : v 0 * L.sum 0 + v 1 * L.sum 1 =
          (L.map fun z => vecDot v z).sum := by
        simpa [vecDot, Fin.sum_univ_two] using ih
      calc
        vecDot v (a + L.sum) =
            (v 0 * a 0 + v 1 * a 1) +
              (v 0 * L.sum 0 + v 1 * L.sum 1) := by
          simp [vecDot, Fin.sum_univ_two]
          ring
        _ = (L.map fun z => vecDot v z).sum +
              (v 0 * a 0 + v 1 * a 1) := by rw [ih']; ring
        _ = (List.map (fun z => vecDot v z) (a :: L)).sum := by
          simp [vecDot, Fin.sum_univ_two, add_comm]

theorem ThetaHonestAnalytic.theta_list_vec_sum_apply (L : List (Vec 2)) (j : Fin 2) :
    L.sum j = (L.map fun v => v j).sum := by
  induction L with
  | nil => rfl
  | cons v L ih => simp [ih]

theorem ThetaHonestAnalytic.theta_commutator_split_count
    (w : List (Fin 2)) (q : ℕ) :
    List.count q ((classicalWordCommutatorSplits w).map fun p => p.1.length) =
      if q = 0 then 0 else w.length.choose q := by
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  change (classicalWordCommutatorSplits w |>.filter
    (fun p => decide (p.1.length = q))).length = _
  exact classicalWordCommutatorSplits_leftLength_count w q

theorem theta_commutator_split_weighted_sum
    (w : List (Fin 2)) (F : ℕ → ℝ) :
    ((classicalWordCommutatorSplits w).map fun p => F p.1.length).sum =
      ∑ q ∈ Finset.range (w.length + 1),
        ((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) * F q := by
  let L := (classicalWordCommutatorSplits w).map fun p => p.1.length
  have hsum := Finset.sum_list_map_count L F
  have hLsubset : L.toFinset ⊆ Finset.range (w.length + 1) := by
    intro q hq
    have hqL : q ∈ L := List.mem_toFinset.mp hq
    obtain ⟨p, hp, hqp⟩ := List.mem_map.mp hqL
    have hlen := classicalWordCommutatorSplits_length w hp
    have hle : p.1.length ≤ w.length := by omega
    rw [← hqp, Finset.mem_range]
    exact Nat.lt_succ_of_le hle
  have hsumrange :
      (∑ q ∈ L.toFinset, ((List.count q L : ℕ) : ℝ) * F q) =
        ∑ q ∈ Finset.range (w.length + 1),
          ((List.count q L : ℕ) : ℝ) * F q := by
    apply Finset.sum_subset hLsubset
    intro q hq hnot
    have hcount : List.count q L = 0 := by
      apply List.count_eq_zero.mpr
      intro hmem
      exact hnot (List.mem_toFinset.mpr hmem)
    simp [hcount]
  have hsum' :
      ((classicalWordCommutatorSplits w).map fun p => F p.1.length).sum =
        ∑ q ∈ L.toFinset, ((List.count q L : ℕ) : ℝ) * F q := by
    simpa [L, nsmul_eq_mul, List.map_map, Function.comp_def] using hsum
  rw [hsum', hsumrange]
  apply Finset.sum_congr rfl
  intro q hq
  rw [ThetaHonestAnalytic.theta_commutator_split_count w q]

theorem theta_intervalCube_list_sum_continuous
    (L : List (ℝ × Vec 2 → ℝ)) (hcont : ∀ f ∈ L, Continuous f) :
    Continuous (fun p => (L.map fun f => f p).sum) := by
  induction L with
  | nil =>
      change Continuous (fun _ : ℝ × Vec 2 => (0 : ℝ))
      exact continuous_const
  | cons f L ih =>
      have htail : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hcont g (by simp [hg])
      change Continuous (fun p => f p + (L.map fun g => g p).sum)
      exact (hcont f (by simp)).add (ih htail)

theorem theta_intervalCube_integral_list_sum
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    (L : List (ℝ × Vec 2 → ℝ))
    (hcont : ∀ f ∈ L, Continuous f) :
    (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      (L.map fun f => f p).sum) =
      (L.map fun f => ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
        f p).sum := by
  induction L with
  | nil => simp
  | cons f L ih =>
      have htail : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hcont g (by simp [hg])
      have hfint : IntegrableOn f
          (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube) := by
        have hsub : Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube ⊆
            ThetaHonestAnalytic.thetaHonestClosedCell := by
          rintro ⟨t, x⟩ ⟨ht, hx⟩
          refine ⟨⟨le_of_lt ht.1, ht.2.le.trans hT.2⟩, ?_⟩
          change ∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1
          intro i hi
          exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩
        exact (hcont f (by simp)).continuousOn.integrableOn_compact
          ThetaHonestAnalytic.thetaHonestClosedCell_compact |>.mono_set hsub
      have htailcont := theta_intervalCube_list_sum_continuous L htail
      have htailint : IntegrableOn (fun p => (L.map fun g => g p).sum)
          (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube) := by
        have hsub : Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube ⊆
            ThetaHonestAnalytic.thetaHonestClosedCell := by
          rintro ⟨t, x⟩ ⟨ht, hx⟩
          refine ⟨⟨le_of_lt ht.1, ht.2.le.trans hT.2⟩, ?_⟩
          change ∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1
          intro i hi
          exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩
        exact htailcont.continuousOn.integrableOn_compact
          ThetaHonestAnalytic.thetaHonestClosedCell_compact |>.mono_set hsub
      simp only [List.map_cons, List.sum_cons]
      change (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          f p + (L.map fun g => g p).sum) =
        (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p) +
          (L.map fun g => ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
            g p).sum
      rw [integral_add hfint htailint, ih htail]

theorem ThetaHonestAnalytic.theta_list_eval_sum_continuous
    (L : List (Vec 2 → ℝ)) (hcont : ∀ f ∈ L, Continuous f) :
    Continuous (fun x => (L.map fun f => f x).sum) := by
  induction L with
  | nil =>
      change Continuous (fun _ : Vec 2 => (0 : ℝ))
      exact continuous_const
  | cons f L ih =>
      have htail : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hcont g (by simp [hg])
      change Continuous (fun x => f x + (L.map fun g => g x).sum)
      exact (hcont f (by simp)).add (ih htail)

theorem ThetaHonestAnalytic.theta_integral_list_sum
    (L : List (Vec 2 → ℝ))
    (hcont : ∀ f ∈ L, Continuous f) :
    (∫ x in AVenhance.unitCube, (L.map fun f => f x).sum) =
      (L.map fun f => ∫ x in AVenhance.unitCube, f x).sum := by
  induction L with
  | nil => simp
  | cons f L ih =>
      have htail : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hcont g (by simp [hg])
      have hfint : IntegrableOn f AVenhance.unitCube :=
        thetaTime_integrableOn_unitCube (hcont f (by simp))
      have htailcont := ThetaHonestAnalytic.theta_list_eval_sum_continuous L htail
      have htailint : IntegrableOn (fun x => (L.map fun g => g x).sum)
          AVenhance.unitCube := thetaTime_integrableOn_unitCube htailcont
      simp only [List.map_cons, List.sum_cons]
      change (∫ x in AVenhance.unitCube,
          f x + (L.map fun g => g x).sum) =
        (∫ x in AVenhance.unitCube, f x) +
          (L.map fun g => ∫ x in AVenhance.unitCube, g x).sum
      rw [integral_add hfint htailint, ih htail]

/-- A single stream-form Leibniz split on an arbitrary initial time interval.
The coefficient bound is only needed on the open interval of integration. -/
theorem theta_interval_stream_split_pairing_abs_le
    {u φ : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T M : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    (split : List (Fin 2) × List (Fin 2))
    (hM : 0 ≤ M)
    (hcoef : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      |thetaWordExtension φ split.1 p| ≤ M) :
    |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      vecDot (thetaWordGradientExtension u w p)
        (fun j => thetaWordExtension φ split.1 p *
          thetaStreamWordExtension u split.2 p j)| ≤
      2 * M * Real.sqrt (thetaIntervalWordGradientEnergy u T w) *
        Real.sqrt (thetaIntervalWordGradientEnergy u T split.2) := by
  let F : Fin 2 → ℝ × Vec 2 → ℝ := fun j p =>
    thetaWordExtension u (j :: w) p
  let G : Fin 2 → ℝ × Vec 2 → ℝ := fun j p =>
    thetaStreamWordExtension u split.2 p j
  let A : ℝ × Vec 2 → ℝ := thetaWordExtension φ split.1
  let S : Set (ℝ × Vec 2) := Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube
  have hF (j : Fin 2) : Continuous (F j) := thetaWordExtension_continuous hu
  have hG (j : Fin 2) : Continuous (G j) :=
    (continuous_apply j).comp (thetaStreamWordExtension_continuous hu)
  have hA : Continuous A := thetaWordExtension_continuous hφ
  have hterm (j : Fin 2) :
      |∫ p in S, F j p * (A p * G j p)| ≤
        M * Real.sqrt (∫ p in S, (F j p) ^ 2) *
          Real.sqrt (∫ p in S, (G j p) ^ 2) := by
    exact theta_intervalCube_integral_mul_bounded_le hT (hF j) (hG j) hA hM
      (by simpa [S, A] using hcoef)
  have hFenergy (j : Fin 2) :
      (∫ p in S, (F j p) ^ 2) ≤
        thetaIntervalWordGradientEnergy u T w := by
    exact theta_interval_word_l2_le_partial_gradient hu hT (i := j) (j :: w) w
      (List.Perm.refl _)
  have hGenergy (j : Fin 2) :
      (∫ p in S, (G j p) ^ 2) ≤
        thetaIntervalWordGradientEnergy u T split.2 := by
    fin_cases j
    · have hword := theta_interval_word_l2_le_partial_gradient hu hT
        (1 :: split.2) split.2
        (List.Perm.refl _)
      simpa [G, thetaStreamWordExtension] using hword
    · have hword := theta_interval_word_l2_le_partial_gradient hu hT
        (0 :: split.2) split.2
        (List.Perm.refl _)
      simpa [G, thetaStreamWordExtension] using hword
  have hterm' (j : Fin 2) :
      |∫ p in S, F j p * (A p * G j p)| ≤
        M * Real.sqrt (thetaIntervalWordGradientEnergy u T w) *
          Real.sqrt (thetaIntervalWordGradientEnergy u T split.2) := by
    have hFsqrt := Real.sqrt_le_sqrt (hFenergy j)
    have hGsqrt := Real.sqrt_le_sqrt (hGenergy j)
    have hmul := mul_le_mul hFsqrt hGsqrt (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    calc
      _ ≤ M * Real.sqrt (∫ p in S, (F j p) ^ 2) *
          Real.sqrt (∫ p in S, (G j p) ^ 2) := hterm j
      _ = M * (Real.sqrt (∫ p in S, (F j p) ^ 2) *
          Real.sqrt (∫ p in S, (G j p) ^ 2)) := by ring
      _ ≤ M * (Real.sqrt (thetaIntervalWordGradientEnergy u T w) *
          Real.sqrt (thetaIntervalWordGradientEnergy u T split.2)) :=
            mul_le_mul_of_nonneg_left hmul hM
      _ = _ := by ring
  have hsumInt :
      (∫ p in S, vecDot (thetaWordGradientExtension u w p)
        (fun j => A p * G j p)) =
        ∑ j : Fin 2, ∫ p in S, F j p * (A p * G j p) := by
    have hpoint (p : ℝ × Vec 2) :
        vecDot (thetaWordGradientExtension u w p) (fun j => A p * G j p) =
          ∑ j : Fin 2, F j p * (A p * G j p) := by
      simp [vecDot, F, thetaWordGradientExtension, G, Fin.sum_univ_two]
    calc
      _ = ∫ p in S, ∑ j : Fin 2, F j p * (A p * G j p) := by
        apply setIntegral_congr_fun
          (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube)
        intro p hp
        exact hpoint p
      _ = ∑ j : Fin 2, ∫ p in S, F j p * (A p * G j p) := by
        rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
          (f := fun j p => F j p * (A p * G j p)) (by
            intro j hj
            have hprodcont : Continuous
                (fun p => F j p * (A p * G j p)) :=
              (hF j).mul (hA.mul (hG j))
            have hsub : S ⊆ ThetaHonestAnalytic.thetaHonestClosedCell := by
              intro p hp
              rcases hp with ⟨ht, hx⟩
              refine ⟨⟨le_of_lt ht.1, ht.2.le.trans hT.2⟩, ?_⟩
              change ∀ i ∈ Set.univ, p.2 i ∈ Set.Icc (0 : ℝ) 1
              intro i hi
              exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩
            exact (hprodcont.continuousOn.integrableOn_compact
              ThetaHonestAnalytic.thetaHonestClosedCell_compact).mono_set hsub)]
  rw [hsumInt]
  have hsumabs :
      |∑ j : Fin 2, ∫ p in S, F j p * (A p * G j p)| ≤
        ∑ j : Fin 2, |∫ p in S, F j p * (A p * G j p)| :=
    Finset.abs_sum_le_sum_abs _ _
  calc
      |∑ j : Fin 2, ∫ p in S, F j p * (A p * G j p)| ≤
        ∑ j : Fin 2, |∫ p in S, F j p * (A p * G j p)| :=
      hsumabs
    _ ≤ ∑ j : Fin 2,
        M * Real.sqrt (thetaIntervalWordGradientEnergy u T w) *
          Real.sqrt (thetaIntervalWordGradientEnergy u T split.2) :=
      by exact Finset.sum_le_sum (by intro j hj; exact hterm' j)
    _ = 2 * M * Real.sqrt (thetaIntervalWordGradientEnergy u T w) *
        Real.sqrt (thetaIntervalWordGradientEnergy u T split.2) := by
      simp only [Fin.sum_univ_two]
      ring

private theorem first_order_stream_pairing_bound :
  ∀ {β κ : ℝ} {m : ℕ} (I : Ingredients β) (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ), IsStreamSeq I Φ → (2 :
    ℕ) ≤ m → (∀ (j : ℕ), (1 : ℕ) ≤ j → ∀ (t : ℝ) (n : ℕ), (2 : ℕ) ≤ n → barNorm n ((2 : ℝ) ^ (8
    : ℕ) * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤ ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ) * AVenhance.a β I.Λ
    j * epsilon β I.Λ j ^ (2 : ℕ) * (((↑n : ℝ) + (2 : ℝ)) ^ (2 : ℕ) / ((↑n : ℝ) + (1 : ℝ)) ^ (3
    : ℕ)))) → ∀ {θ₀ : Vec (2 : ℕ) → ℝ} {θ : ℝ → Vec (2 : ℕ) → ℝ}, IsClassicalSol (streamVel fun
    (t : ℝ) => Φ (m - (1 : ℕ)) t) κ (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) θ₀ θ → ∀ {T :
    ℝ} {w : List (Fin (2 : ℕ))}, ∀ split ∈ classicalWordCommutatorSplits w, split.1.length = (1
    : ℕ) →
  let φ : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) => Φ (m - (1 : ℕ)) t;
  let F : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => vecDot (thetaWordGradientExtension
    θ w p) fun (j : Fin (2 : ℕ)) => thetaWordExtension φ split.1 p * thetaStreamWordExtension θ
    split.2 p j;
  let H : ℝ × Vec (2 : ℕ) → ℝ := fun (p : ℝ × Vec (2 : ℕ)) => vecNormSq
    (thetaWordGradientExtension θ split.2 p);
  let P : ℝ → ℝ := fun (t : ℝ) => ∫ (x : Vec (2 : ℕ)) in unitCube, F (t, x);
  let Q : ℝ → ℝ := fun (t : ℝ) => ∫ (x : Vec (2 : ℕ)) in unitCube, H (t, x);
  let M : ℝ := (2 : ℝ) ^ (5 : ℕ) * a β I.Λ (m - (1 : ℕ)) * epsilon β I.Λ (m - (1 : ℕ)) ^ (2 : ℕ)
    * (↑(Nat.factorial (2 : ℕ)) : ℝ) * ((2 : ℝ) ^ (8 : ℕ) * (epsilon β I.Λ (m - (1 : ℕ)))⁻¹) ^
    (2 : ℕ);
  IsAdmissibleStream φ → ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry φ) (Set.Ici (0
    : ℝ) ×ˢ Set.univ) → ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry θ) (Set.Ici (0 :
    ℝ) ×ˢ Set.univ) → (0 : ℝ) ≤ M → ∀ t ∈ Set.Ioo (0 : ℝ) T, |P t| ≤ (2 : ℝ) * M * Q t
    := by
  intro β κ m I Φ hΦ hm hA3 θ₀ θ hsol T w split hsplit hlen φ F H P Q M hφadm hφ hθ hMnonneg t ht
  have hts : 0 < t := ht.1
  have hφt : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have hmapp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => (t, x)) Set.univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmem : ∀ x ∈ (Set.univ : Set (Vec 2)),
        (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
      intro x hx
      exact ⟨hts.le, Set.mem_univ _⟩
    have hcomp := hφ.comp hmapp hmem
    exact contDiffOn_univ.mp (by
      simpa [φ, Function.uncurry, Function.comp_def] using hcomp)
  have hθt : ContDiff ℝ (⊤ : ℕ∞) (θ t) := by
    have hmapp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => (t, x)) Set.univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmem : ∀ x ∈ (Set.univ : Set (Vec 2)),
        (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
      intro x hx
      exact ⟨hts.le, Set.mem_univ _⟩
    have hcomp := hθ.comp hmapp hmem
    exact contDiffOn_univ.mp (by
      simpa [Function.uncurry, Function.comp_def] using hcomp)
  have hgradPoint (x : Vec 2) (j : Fin 2) :
      |AVenhance.spaceGrad (classicalWordDerivative split.1 (φ t)) x j| ≤ M := by
    have hlen2 : 2 ≤ (j :: split.1).length := by simp [hlen]
    have hA3point := theta_prev_potential_word_abs_le_of_A3
      I Φ hΦ hm hA3 (t := t) (j :: split.1) hlen2 x
    have hlen' : (j :: split.1).length = 2 := by simp [hlen]
    rw [hlen'] at hA3point
    simpa [M, φ, classicalWordDerivative,
      Classical.classicalWordDerivative] using hA3point
  have hcompPoint (x : Vec 2) :
      classicalWordDerivative w (θ t) x ^ 2 ≤
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x) :=
    classicalWordDerivative_sq_le_gradient_of_first_order_split
      w split (θ t) hθt x hsplit hlen
  have hperφ : AVenhance.IsZ2Periodic (φ t) := by
    intro k x
    simpa [φ] using hφadm.2 0 k t x
  have hperθ : AVenhance.IsZ2Periodic (θ t) := hsol.2.1 t hts.le
  have hgper := classicalWordDerivative_periodic split.1 hφt hperφ
  have hhper := classicalWordDerivative_periodic split.2 hθt hperθ
  have huper := classicalWordDerivative_periodic w hθt hperθ
  have hspatial := theta_first_order_flux_pairing_abs_le
    (g := classicalWordDerivative split.1 (φ t))
    (h := classicalWordDerivative split.2 (θ t))
    (u := classicalWordDerivative w (θ t))
    (M := M)
    (classicalWordDerivative_contDiff split.1 (φ t) hφt)
    (classicalWordDerivative_contDiff split.2 (θ t) hθt)
    (classicalWordDerivative_contDiff w (θ t) hθt)
    hgper hhper huper hMnonneg hcompPoint hgradPoint
  have hPslice : P t =
      ∫ x in AVenhance.unitCube,
        vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
          (thetaStreamCommutatorProductTerm split (φ t) (θ t) x) := by
    apply integral_congr_ae
    filter_upwards with x
    have hgradSlice := thetaWordGradientExtension_eq_slice
      (u := θ) (w := w) t hts x
    have hcoefSlice := thetaWordExtension_eq_slice
      (u := φ) (w := split.1) t hts x
    have hstreamSlice := thetaStreamWordExtension_eq_slice
      (u := θ) (w := split.2) t hts x
    change vecDot (thetaWordGradientExtension θ w (t, x))
        (fun j => thetaWordExtension φ split.1 (t, x) *
          thetaStreamWordExtension θ split.2 (t, x) j) = _
    rw [hgradSlice, hcoefSlice, hstreamSlice]
    rfl
  have hQslice : Q t =
      ∫ x in AVenhance.unitCube,
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x) := by
    apply integral_congr_ae
    filter_upwards with x
    change Homogenization.vecNormSq
      (thetaWordGradientExtension θ split.2 (t, x)) = _
    rw [thetaWordGradientExtension_eq_slice
      (u := θ) (w := split.2) t hts x]
  rw [hPslice, hQslice]
  change |∫ x in AVenhance.unitCube,
    vecDot (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)
      (fun j => classicalWordDerivative split.1 (φ t) x *
        AVenhance.streamVel
          (fun _ => classicalWordDerivative split.2 (θ t)) 0 x j)| ≤
    2 * M * ∫ x in AVenhance.unitCube,
      Homogenization.vecNormSq
        (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x)
  exact hspatial

/-- The one-derivative stream-flux term admits the sharper energy bound after
periodic integration by parts.  The derivative on the top word is a
coordinate derivative of the complementary word, so the resulting square is
controlled by the lower-order gradient energy. -/
theorem theta_first_order_stream_split_pairing_time_abs_le_of_A3
    {β κ : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t)) κ
      (fun _ _ => 0) θ₀ θ)
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {w : List (Fin 2)} (split : List (Fin 2) × List (Fin 2))
    (hsplit : split ∈ classicalWordCommutatorSplits w)
    (hlen : split.1.length = 1) :
    |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      vecDot (thetaWordGradientExtension θ w p)
        (fun j => thetaWordExtension (fun t => Φ (m - 1) t) split.1 p *
          thetaStreamWordExtension θ split.2 p j)| ≤
      2 * (2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
        ((2 : ℕ).factorial : ℝ) *
        (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ 2) *
        (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x)) := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let F : ℝ × Vec 2 → ℝ := fun p =>
    vecDot (thetaWordGradientExtension θ w p)
      (fun j => thetaWordExtension φ split.1 p *
        thetaStreamWordExtension θ split.2 p j)
  let H : ℝ × Vec 2 → ℝ := fun p =>
    vecNormSq (thetaWordGradientExtension θ split.2 p)
  let P : ℝ → ℝ := fun t => ∫ x in AVenhance.unitCube, F (t, x)
  let Q : ℝ → ℝ := fun t => ∫ x in AVenhance.unitCube, H (t, x)
  let M : ℝ := 2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
    AVenhance.epsilon β I.Λ (m - 1) ^ 2 * ((2 : ℕ).factorial : ℝ) *
      (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ 2
  have hφadm : AVenhance.IsAdmissibleStream φ :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    exact hφadm.1.contDiffOn.mono (by intro p hp; exact Set.mem_univ p)
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hsol.1
  have hgrad : Continuous (thetaWordGradientExtension θ w) :=
    thetaWordGradientExtension_continuous hθ
  have hcoef : Continuous (thetaWordExtension φ split.1) :=
    thetaWordExtension_continuous hφ
  have hstream : Continuous (thetaStreamWordExtension θ split.2) :=
    thetaStreamWordExtension_continuous hθ
  have hterm : Continuous (fun p : ℝ × Vec 2 =>
      fun j => thetaWordExtension φ split.1 p *
        thetaStreamWordExtension θ split.2 p j) := by
    apply continuous_pi
    intro j
    exact hcoef.mul ((continuous_apply j).comp hstream)
  have hF : Continuous F := by
    dsimp [F]
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension θ w p j *
        (thetaWordExtension φ split.1 p *
          thetaStreamWordExtension θ split.2 p j))
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hgrad).mul
      ((continuous_apply j).comp hterm)
  have hH : Continuous H := by
    dsimp [H]
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension θ split.2 p j *
        thetaWordGradientExtension θ split.2 p j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp
      (thetaWordGradientExtension_continuous hθ)).mul
      ((continuous_apply j).comp
        (thetaWordGradientExtension_continuous hθ))
  have hP : ContinuousOn P (Set.Ici (0 : ℝ)) := by
    exact theta_time_parametric_integral_continuousOn hF.continuousOn
  have hQ : ContinuousOn Q (Set.Ici (0 : ℝ)) := by
    exact theta_time_parametric_integral_continuousOn hH.continuousOn
  have hPI : IntervalIntegrable P volume 0 T := by
    exact (hP.mono (by intro t ht; exact ht.1)).intervalIntegrable_of_Icc hT.1
  have hQI : IntervalIntegrable Q volume 0 T := by
    exact (hQ.mono (by intro t ht; exact ht.1)).intervalIntegrable_of_Icc hT.1
  have hQnonneg (t : ℝ) : 0 ≤ Q t := by
    dsimp [Q, H]
    exact integral_nonneg fun _ => Homogenization.vecNormSq_nonneg _
  have hMnonneg : 0 ≤ M := by
    have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
      AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
      rw [AVenhance.a]
      exact Real.rpow_pos_of_pos he _
    dsimp [M]
    positivity
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      |P t| ≤ 2 * M * Q t := by
    exact @first_order_stream_pairing_bound β κ m I Φ hΦ hm hA3 θ₀ θ hsol T w split hsplit hlen
        hφadm hφ hθ hMnonneg
  have h_abs_integral := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) hT.1 (f := P)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo
    (μ := volume) (a := 0) (b := T)
    (f := fun t => |P t|) (g := fun t => 2 * M * Q t)
    (hab := hT.1) (hf := hPI.norm)
    (hg := hQI.const_mul (2 * M)) hpoint
  have htimeQ :
      (∫ t in (0 : ℝ)..T, Q t) =
        ∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) T := by
      simpa only [Set.uIoc_of_le hT.1] using ht
    apply integral_congr_ae
    filter_upwards with x
    dsimp [Q, H]
    rw [thetaWordGradientExtension_eq_slice
      (u := θ) (w := split.2) t ht'.1 x]
  have hFubini := theta_intervalCube_integral_eq_interval_integral hT hF
  have hfinal : |∫ t in (0 : ℝ)..T, P t| ≤
      2 * M * (∫ t in (0 : ℝ)..T, ∫ x in AVenhance.unitCube,
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (classicalWordDerivative split.2 (θ t)) x)) := by
    calc
      |∫ t in (0 : ℝ)..T, P t| ≤ ∫ t in (0 : ℝ)..T, |P t| := h_abs_integral
      _ ≤ ∫ t in (0 : ℝ)..T, 2 * M * Q t := hmono
      _ = 2 * M * (∫ t in (0 : ℝ)..T, Q t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [htimeQ]
  rw [hFubini]
  simpa [P, F, φ, M, AVenhance.timeCube] using hfinal

/-- The joint continuous representative of one split in the differentiated
stream flux. -/
noncomputable def thetaStreamSplitExtension
    (φ u : ℝ → Vec 2 → ℝ)
    (split : List (Fin 2) × List (Fin 2))
    (p : ℝ × Vec 2) : Vec 2 :=
  fun j => thetaWordExtension φ split.1 p *
    thetaStreamWordExtension u split.2 p j

/-- Space-time integration commutes with the finite differentiated-flux
expansion. -/
theorem theta_time_flux_pairing_eq_split_sum
    {φ u : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      ((classicalWordCommutatorSplits w).map fun split =>
        fun p => vecDot (thetaWordGradientExtension u w p)
          (thetaStreamSplitExtension φ u split p)).sum p) =
      ((classicalWordCommutatorSplits w).map fun split =>
        ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          vecDot (thetaWordGradientExtension u w p)
            (thetaStreamSplitExtension φ u split p)).sum := by
  let L := classicalWordCommutatorSplits w
  let Terms : List (ℝ × Vec 2 → ℝ) := L.map fun split p =>
    vecDot (thetaWordGradientExtension u w p)
      (thetaStreamSplitExtension φ u split p)
  have hgrad : Continuous (thetaWordGradientExtension u w) :=
    thetaWordGradientExtension_continuous hu
  have hφword (split : List (Fin 2) × List (Fin 2)) :
      Continuous (thetaWordExtension φ split.1) :=
    thetaWordExtension_continuous hφ
  have hustream (split : List (Fin 2) × List (Fin 2)) :
      Continuous (thetaStreamWordExtension u split.2) :=
    thetaStreamWordExtension_continuous hu
  have hterm (split : List (Fin 2) × List (Fin 2)) :
      Continuous (fun p => vecDot (thetaWordGradientExtension u w p)
        (thetaStreamSplitExtension φ u split p)) := by
    have hvec : Continuous (fun p => thetaStreamSplitExtension φ u split p) := by
      apply continuous_pi
      intro j
      exact (hφword split).mul
        ((continuous_apply j).comp (hustream split))
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension u w p j *
        thetaStreamSplitExtension φ u split p j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hgrad).mul
      ((continuous_apply j).comp hvec)
  have hterms : ∀ f ∈ Terms, Continuous f := by
    intro f hf
    obtain ⟨split, hs, rfl⟩ := List.mem_map.mp hf
    exact hterm split
  have hpoint (p : ℝ × Vec 2) :
      Terms.sum p = (L.map fun split =>
        vecDot (thetaWordGradientExtension u w p)
          (thetaStreamSplitExtension φ u split p)).sum := by
    rw [theta_analytic_funList_sum_apply]
    simp [Terms, L, List.map_map, Function.comp_def]
  have hsumInt :
      (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, Terms.sum p) =
        (Terms.map fun f => ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p).sum := by
    calc
      (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, Terms.sum p) =
          ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
            (Terms.map fun f => f p).sum := by
        congr 1
        funext p
        exact theta_analytic_funList_sum_apply Terms p
      _ = (Terms.map fun f =>
          ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p).sum :=
        theta_intervalCube_integral_list_sum hT Terms hterms
  have hmap :
      (Terms.map fun f => ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, f p).sum =
        (L.map fun split =>
          ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
            vecDot (thetaWordGradientExtension u w p)
              (thetaStreamSplitExtension φ u split p)).sum := by
    simp [Terms, L, List.map_map, Function.comp_def]
  calc
    (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
        ((L.map fun split => fun p =>
          vecDot (thetaWordGradientExtension u w p)
            (thetaStreamSplitExtension φ u split p)).sum p)) =
      ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, Terms.sum p := by
        congr 1
    _ = _ := hsumInt.trans hmap

end AVenhance.Infra.Section4

end
