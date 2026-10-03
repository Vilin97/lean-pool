/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-! # Time derivative of the periodic energy of a jointly `C¹` function

The classical `TimeEnergy` development assumes the joint function is `C^∞`.  The forced energy
estimate applies it to `w = u - v`, where `v` is only jointly `C²`; here the same statements are
proved from joint `C¹` regularity on `[0,∞) × ℝ²`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.Energy

theorem isOpen_positiveTimeDomain : IsOpen classicalPositiveTimeDomain :=
  isOpen_Ioi.prod isOpen_univ

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def TimeDerivative.closedCell : Set (Vec 2) := Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem TimeDerivative.isCompact_closedCell : IsCompact TimeDerivative.closedCell := by
  simpa [TimeDerivative.closedCell] using isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc)

theorem TimeDerivative.unitCell_subset_closedCell : unitCell 2 ⊆ TimeDerivative.closedCell := by
  intro x hx
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  simp only [TimeDerivative.closedCell, Set.mem_pi, mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, hx i |>.2⟩

/-- The time derivative of a fixed spatial section, read from the joint Fréchet derivative. -/
theorem timeSection_hasDerivAt_one {g : ℝ → Vec 2 → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun s => g s x) (fderiv ℝ (Function.uncurry g) (t, x) ((1 : ℝ), (0 : Vec 2))) t :=
        by
  have hp : (t, x) ∈ classicalPositiveTimeDomain := by simp [classicalPositiveTimeDomain, ht]
  have hAt : ContDiffAt ℝ 1 (Function.uncurry g) (t, x) :=
    hg.contDiffAt (isOpen_positiveTimeDomain.mem_nhds hp)
  have hf : HasFDerivAt (Function.uncurry g)
      (fderiv ℝ (Function.uncurry g) (t, x)) (t, x) :=
    (hAt.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hcomp := hf.comp_hasDerivAt t hline
  simpa [Function.uncurry, Function.comp_def] using hcomp

theorem deriv_timeSection_eq {g : ℝ → Vec 2 → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    deriv (fun s => g s x) t =
      fderiv ℝ (Function.uncurry g) (t, x) ((1 : ℝ), (0 : Vec 2)) :=
  (timeSection_hasDerivAt_one hg ht x).deriv

theorem continuousOn_timePartial_one {g : ℝ → Vec 2 → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) classicalPositiveTimeDomain) :
    ContinuousOn (fun p : ℝ × Vec 2 =>
      fderiv ℝ (Function.uncurry g) p ((1 : ℝ), (0 : Vec 2))) classicalPositiveTimeDomain :=
  (hg.continuousOn_fderiv_of_isOpen isOpen_positiveTimeDomain le_rfl).clm_apply continuousOn_const

theorem continuous_slice_one {g : ℝ → Vec 2 → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : Continuous (g t) := by
  have hline : Continuous fun x : Vec 2 => (t, x) := continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun x : Vec 2 => (t, x)) Set.univ classicalPositiveTimeDomain := by
    intro x _
    simp [classicalPositiveTimeDomain, ht]
  have h := hg.continuousOn.comp hline.continuousOn hmaps
  exact continuousOn_univ.mp (by simpa [Function.uncurry, Function.comp_def] using h)

theorem continuous_timePartial_slice_one {g : ℝ → Vec 2 → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) :
    Continuous (fun x => fderiv ℝ (Function.uncurry g) (t, x) ((1 : ℝ), (0 : Vec 2))) := by
  have hline : Continuous fun x : Vec 2 => (t, x) := continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun x : Vec 2 => (t, x)) Set.univ classicalPositiveTimeDomain := by
    intro x _
    simp [classicalPositiveTimeDomain, ht]
  have h := (continuousOn_timePartial_one hg).comp hline.continuousOn hmaps
  exact continuousOn_univ.mp h

/-- The unit-cell quadratic energy of a jointly `C¹` function is differentiable at positive
times. -/
theorem energy_hasDerivAt_one {g : ℝ → Vec 2 → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCell 2, (g s x) ^ 2)
      (∫ x in unitCell 2, 2 * g t x * deriv (fun s => g s x) t) t := by
  have hgOpen : ContDiffOn ℝ 1 (Function.uncurry g) classicalPositiveTimeDomain :=
    hg.mono (by
      intro p hp
      simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
      exact ⟨le_of_lt hp.1, trivial⟩)
  let radius : ℝ := t / 2
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hball : Metric.ball t radius ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    dsimp [radius] at hs
    have h := abs_lt.mp hs
    rw [Set.mem_Ioi]
    linarith
  let K : Set (ℝ × Vec 2) := Set.Icc (t - radius) (t + radius) ×ˢ TimeDerivative.closedCell
  have hKcompact : IsCompact K := isCompact_Icc.prod TimeDerivative.isCompact_closedCell
  have hKopen : K ⊆ classicalPositiveTimeDomain := by
    rintro ⟨s, x⟩ hp
    simp only [K, Set.mem_prod, Set.mem_Icc] at hp
    dsimp [radius] at hp
    simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ]
    exact ⟨by linarith [hp.1.1], trivial⟩
  obtain ⟨C₀, hC₀⟩ := hKcompact.exists_bound_of_continuousOn (hgOpen.continuousOn.mono hKopen)
  obtain ⟨C₁, hC₁⟩ := hKcompact.exists_bound_of_continuousOn
    ((continuousOn_timePartial_one hgOpen).mono hKopen)
  let bound : ℝ := 2 * (|C₀| + 1) * (|C₁| + 1)
  let μ : Measure (Vec 2) := volume.restrict (unitCell 2)
  let integrand : ℝ → Vec 2 → ℝ := fun s x => (g s x) ^ 2
  let integrandDeriv : ℝ → Vec 2 → ℝ :=
    fun s x => 2 * g s x * deriv (fun r => g r x) s
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (integrand s) μ := by
    filter_upwards [Metric.ball_mem_nhds t hradius] with s hs
    exact ((continuous_slice_one hgOpen (hball hs)).pow 2).aestronglyMeasurable
  have hFint : Integrable (integrand t) μ := by
    change IntegrableOn (fun x => (g t x) ^ 2) (unitCell 2)
    apply continuous_integrableOn_unitCell
    exact (continuous_slice_one hgOpen ht).pow 2
  have hF'diff : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t radius,
      HasDerivAt (integrand · x) (integrandDeriv s x) s := by
    apply (ae_restrict_iff' (measurableSet_unitCell 2)).2
    filter_upwards with x hx
    intro s hs
    have htime := timeSection_hasDerivAt_one hgOpen (hball hs) x
    have hpow := htime.pow 2
    have hfun : (fun r => g r x) ^ 2 = (fun r => g r x ^ 2) := by
      funext r
      rfl
    rw [hfun] at hpow
    simp only [integrandDeriv, integrand, deriv_timeSection_eq hgOpen (hball hs) x]
    simpa [mul_assoc] using hpow
  have hF'meas : AEStronglyMeasurable (integrandDeriv t) μ := by
    have hcont : Continuous (integrandDeriv t) := by
      have h1 := continuous_slice_one hgOpen ht
      have h2 := continuous_timePartial_slice_one hgOpen ht
      have : integrandDeriv t = fun x => 2 * g t x *
          fderiv ℝ (Function.uncurry g) (t, x) ((1 : ℝ), (0 : Vec 2)) := by
        funext x
        simp only [integrandDeriv, deriv_timeSection_eq hgOpen ht x]
      rw [this]
      exact (continuous_const.mul h1).mul h2
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t radius, ‖integrandDeriv s x‖ ≤ bound := by
    apply (ae_restrict_iff' (measurableSet_unitCell 2)).2
    filter_upwards with x hx
    intro s hs
    have hsK : (s, x) ∈ K := by
      simp only [K, Set.mem_prod, Set.mem_Icc]
      refine ⟨?_, TimeDerivative.unitCell_subset_closedCell hx⟩
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have h := abs_lt.mp hs
      constructor <;> linarith [h.1, h.2]
    have huAbs : |g s x| ≤ |C₀| + 1 := by
      have := hC₀ (s, x) hsK
      simp only [Function.uncurry, Real.norm_eq_abs] at this
      linarith [le_abs_self C₀]
    have hdtAbs : |fderiv ℝ (Function.uncurry g) (s, x) ((1 : ℝ), (0 : Vec 2))| ≤ |C₁| + 1 := by
      have := hC₁ (s, x) hsK
      simp only [Real.norm_eq_abs] at this
      linarith [le_abs_self C₁]
    have hs0 : 0 < s := hball hs
    simp only [integrandDeriv, deriv_timeSection_eq hgOpen hs0 x, Real.norm_eq_abs]
    calc
      |2 * g s x * fderiv ℝ (Function.uncurry g) (s, x) ((1 : ℝ), (0 : Vec 2))| =
          2 * (|g s x| * |fderiv ℝ (Function.uncurry g) (s, x) ((1 : ℝ), (0 : Vec 2))|) := by
        rw [abs_mul, abs_mul]
        simp [mul_assoc]
      _ ≤ 2 * ((|C₀| + 1) * (|C₁| + 1)) := by
        gcongr
      _ = bound := by simp only [bound]; ring
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t radius) (μ := μ) (bound := fun _ : Vec 2 => bound)
    (Metric.ball_mem_nhds t hradius) hFmeas hFint hF'meas hbound
    (by
      change IntegrableOn (fun _ : Vec 2 => bound) (unitCell 2)
      exact continuous_integrableOn_unitCell continuous_const)
    hF'diff
  simpa [integrand, integrandDeriv, μ] using hderiv.2

end AVenhance.Infra.Section5.Integration.Energy

end
