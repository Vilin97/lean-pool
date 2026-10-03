/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmPulledGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmDmScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.JhatFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmFlowTgrad
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.QMNRRecursion

/-! # `SourceErrorDContract`: open-time regularity and measurability inputs

The iterates `T_i` are smooth only for `t ≥ 0`, so the global continuity of `∇T` in the
    `dm_pulled_gradient_*` lemmas is replaced by continuity on `Ici 0 ×ˢ univ` through the time
clamp `sedClamp`, which changes nothing on the open time cube. -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section4

/-- A classical solution has continuous spatial gradient on `Ici 0 ×ˢ univ`. -/
theorem sed_gradient_continuousOn {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ}
    {u₀ : Vec 2 → ℝ} (hu : IsClassicalSol b κ F u₀ u) :
    ContinuousOn (fun z : ℝ × Vec 2 => spaceGrad (u z.1) z.2) (Ici (0 : ℝ) ×ˢ univ) := by
  refine continuousOn_pi.mpr (fun p => ?_)
  exact RelativeError.continuousOn_spaceGrad_joint hu.1 p

/-- The time-clamped copy of `T`: it agrees with `T` on `t ≥ 0` and has globally continuous
spatial gradient. -/
def sedClamp (T : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ := fun t => T (max t 0)

theorem sedClamp_gradient_continuous {T : ℝ → Vec 2 → ℝ}
    (hc : ContinuousOn (fun z : ℝ × Vec 2 => spaceGrad (T z.1) z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    Continuous (fun z : ℝ × Vec 2 => spaceGrad (sedClamp T z.1) z.2) := by
  have hmap : Continuous (fun z : ℝ × Vec 2 => (max z.1 0, z.2)) := by fun_prop
  exact hc.comp_continuous hmap (fun z => ⟨mem_Ici.mpr (le_max_right _ _), mem_univ _⟩)

theorem sedClamp_grad_eq {T : ℝ → Vec 2 → ℝ} {z : ℝ × Vec 2} (hz : 0 ≤ z.1) :
    spaceGrad (sedClamp T z.1) z.2 = spaceGrad (T z.1) z.2 := by
  simp [sedClamp, max_eq_left hz]

theorem sedClamp_energy_eq (T : ℝ → Vec 2 → ℝ) :
    spaceTimeGradNormSq (fun t => spaceGrad (sedClamp T t)) =
      spaceTimeGradNormSq (fun t => spaceGrad (T t)) := by
  unfold spaceTimeGradNormSq
  refine setIntegral_congr_fun (amnr_timeCube_isOpen.measurableSet) (fun z hz => ?_)
  simp only
  rw [sedClamp_grad_eq hz.1.1.le]

theorem sed_timeCube_ae_nonneg : ∀ᵐ z ∂(volume.restrict timeCube), 0 ≤ z.1 := by
  filter_upwards [ae_restrict_mem amnr_timeCube_isOpen.measurableSet] with z hz using hz.1.1.le

/-- The Section 4 `d_m` first summand is the first summand `hmFrozenDFirstFlux`. -/
theorem dmFrozenFluxFirst_eq_hmFrozenDFirstFlux {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) :
    dmFrozenFluxFirst I hΦ m κ T = fun z => hmFrozenDFirstFlux I hΦ m κ T z.1 z.2 := rfl

/-- The temperature-gradient `L²` bound for the actual (open-time smooth) `T`, from the
profile, through the time clamp. -/
theorem sed_Tgrad_eLpNorm_le {T : ℝ → Vec 2 → ℝ}
    (hc : ContinuousOn (fun z : ℝ × Vec 2 => spaceGrad (T z.1) z.2) (Ici (0 : ℝ) ×ˢ univ))
    {κprev N : ℝ} (hκprev : 0 < κprev)
    (hT : Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (T t))) ≤ N) :
    eLpNorm (fun z : ℝ × Vec 2 => spaceGrad (T z.1) z.2) 2 (volume.restrict timeCube) ≤
      ENNReal.ofReal (N / Real.sqrt κprev) := by
  have h := dm_Tgrad_eLpNorm_le_of_Tprofile (sedClamp T) (N := N)
    (sedClamp_gradient_continuous hc) hκprev (by rw [sedClamp_energy_eq]; exact hT)
  have hae : (fun z : ℝ × Vec 2 => spaceGrad (T z.1) z.2) =ᵐ[volume.restrict timeCube]
      (fun z : ℝ × Vec 2 => spaceGrad (sedClamp T z.1) z.2) := by
    filter_upwards [sed_timeCube_ae_nonneg] with z hz
    exact (sedClamp_grad_eq hz).symm
  rwa [eLpNorm_congr_ae hae]

/-- The matrix-vector product of measurable entries is measurable. -/
theorem sed_measurable_mulVec {α : Type*} [MeasurableSpace α]
    {A : α → Matrix (Fin 2) (Fin 2) ℝ} {v : α → Vec 2}
    (hA : ∀ i j, Measurable (fun a => A a i j)) (hv : Measurable v) :
    Measurable (fun a => (A a).mulVec (v a)) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ (fun j _ =>
    (hA i j).mul ((measurable_pi_apply j).comp hv))

/-- Measurability of the first term of `d_m`. -/
theorem sed_firstMeas {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) {T : ℝ → Vec 2 → ℝ}
    (hc : ContinuousOn (fun z : ℝ × Vec 2 => spaceGrad (T z.1) z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    AEStronglyMeasurable (dmFrozenFluxFirst I hΦ m κ T) (volume.restrict timeCube) := by
  have hmeas : Measurable (dmFrozenFluxFirst I hΦ m κ (sedClamp T)) := by
    have hgrad := (sedClamp_gradient_continuous hc).measurable
    have hM : ∀ i j : Fin 2, Measurable (fun z : ℝ × Vec 2 =>
        (I.Jhat κ m z.1 - I.flux κ m z.1) i j) := by
      intro i j
      have hcont : Continuous (fun t : ℝ => (I.Jhat κ m t - I.flux κ m t) i j) := by
        simp only [Matrix.sub_apply]
        exact (LeftToShow.Jhat_entry_continuous_pub I hm hκ i j).sub
          (Infra.Section3.flux_entry_time_continuous I hm κ i j)
      exact hcont.measurable.comp measurable_fst
    unfold dmFrozenFluxFirst
    refine Measurable.tsum (fun l => ?_)
    have hhat : Continuous (I.hatXiML m l) := by
      unfold Ingredients.hatXiML AVenhance.shiftCutoff
      exact (I.hatXi_smooth m).continuous.comp (by fun_prop)
    have hF : ∀ i j : Fin 2, Measurable (fun z : ℝ × Vec 2 =>
        I.flowGrad hΦ m l z.1 z.2 i j) := fun i j => flowGrad_measurable I hΦ m l i j
    have hFv := sed_measurable_mulVec hF hgrad
    have hMv := sed_measurable_mulVec hM hFv
    have hTv := sed_measurable_mulVec
      (A := fun z : ℝ × Vec 2 => (I.flowGrad hΦ m l z.1 z.2).transpose)
      (fun i j => hF j i) hMv
    exact (hhat.measurable.comp measurable_fst).smul hTv
  refine hmeas.aestronglyMeasurable.congr ?_
  filter_upwards [sed_timeCube_ae_nonneg] with z hz
  simp only [dmFrozenFluxFirst, sedClamp_grad_eq hz]

/-- The terminal AMNR tensor entries are measurable on the time cube. -/
theorem sed_amnrEntry_meas {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) (n : ℕ) (i j k : Fin 2) :
    AEStronglyMeasurable (fun z : ℝ × Vec 2 =>
      I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) z.1 z.2 i j k) (volume.restrict timeCube) := by
  have hJ : 0 + Jcut β ≤ Nstar β := by
    have := Jcut_le_iteration_budget β
    omega
  have h := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT n (Jcut β) 0 hJ i j k
  refine (h.continuousOn.mono ?_).aestronglyMeasurable amnr_timeCube_isOpen.measurableSet
  intro z hz
  exact ⟨hz.1.1, mem_univ _⟩

theorem sed_coordinate_meas {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n : ℕ) (i j k : Fin 2)
    (hA : AEStronglyMeasurable (fun z : ℝ × Vec 2 =>
      I.Amnr hΦ m κ n T (Jcut β) z.1 z.2 i j k) (volume.restrict timeCube)) :
    AEStronglyMeasurable (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k)
      (volume.restrict timeCube) := by
  apply AEMeasurable.aestronglyMeasurable
  refine aemeasurable_pi_iff.mpr (fun p => ?_)
  unfold dmFrozenTailCoordinateTerm
  by_cases h : i = p
  · subst h
    simp only [ite_true]
    exact hA.aemeasurable.mul ((Infra.Section3.qMNR_entry_continuous I κ m n (Jcut β) j
        k).measurable.comp
      measurable_fst).aemeasurable
  · simp only [h, ite_false]
    exact aemeasurable_const

/-- The whole `d_m` field is measurable on the time cube. -/
theorem sed_sourceErrorD_meas {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (hfirst : AEStronglyMeasurable (dmFrozenFluxFirst I hΦ m κ T) (volume.restrict timeCube))
    (hcoord : ∀ n ∈ Finset.range (Nstar β), ∀ i j k : Fin 2,
      AEStronglyMeasurable (dmFrozenTailCoordinateTerm I hΦ m κ T n i j k)
        (volume.restrict timeCube)) :
    AEStronglyMeasurable (fun z : ℝ × Vec 2 => AVenhance.Infra.Section5.sourceErrorD I hΦ m κ T
        z.1 z.2)
      (volume.restrict timeCube) := by
  rw [sourceErrorD_eq_dmFrozenSource I hΦ m κ T,
    ← dmFrozenFluxFirst_eq_hmFrozenDFirstFlux I hΦ m κ T]
  have htail : AEStronglyMeasurable (fun z : ℝ × Vec 2 =>
      ∑ n ∈ Finset.range (Nstar β), dmFrozenTailTerm I hΦ m κ T n z)
      (volume.restrict timeCube) := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun n hn => ?_)
    have : dmFrozenTailTerm I hΦ m κ T n = fun z =>
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, dmFrozenTailCoordinateTerm I hΦ m κ T n i j k z :=
      funext (dmFrozenTailTerm_eq_coordinate_sum I hΦ m κ T n)
    rw [this]
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => Finset.aestronglyMeasurable_fun_sum _
      (fun j _ => Finset.aestronglyMeasurable_fun_sum _ (fun k _ => hcoord n hn i j k)))
  exact hfirst.add htail

end AVenhance.Infra.Section5.Contracts

end
