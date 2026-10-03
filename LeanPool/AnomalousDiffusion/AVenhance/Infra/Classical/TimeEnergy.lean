/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Time differentiation of the periodic quadratic energy. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open AVenhance.Infra.Torus
open scoped Topology

namespace AVenhance.Infra.Classical

/-- Joint time-space domain with strictly positive time. -/
def classicalPositiveTimeDomain : Set (ℝ × Vec 2) := Set.Ioi (0 : ℝ) ×ˢ Set.univ

theorem TimeEnergy.unitCell_subset_closedUnitCell :
    unitCell 2 ⊆ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  simp only [Set.mem_pi, mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, hx i |>.2⟩

theorem TimeEnergy.isCompact_closedUnitCell :
    IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) := by
  simpa using isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc)

theorem continuous_integrableOn_unitCell {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (unitCell 2) := by
  have hcell : IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
    TimeEnergy.isCompact_closedUnitCell
  have hsub : unitCell 2 ⊆ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    TimeEnergy.unitCell_subset_closedUnitCell
  exact (hf.continuousOn.integrableOn_compact hcell).mono_set hsub

/-- Pure time direction in the joint time-space domain. -/
def TimeEnergy.timeVector : ℝ × Vec 2 := (1, 0)

/-- Time partial derivative obtained by evaluating the joint Fréchet derivative. -/
def classicalTimePartial (u : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  fderiv ℝ (Function.uncurry u) p TimeEnergy.timeVector

theorem TimeEnergy.partialTime_continuousOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain) :
    ContinuousOn (classicalTimePartial u) classicalPositiveTimeDomain := by
  have hf := hu.continuousOn_fderiv_of_isOpen
    (isOpen_Ioi.prod isOpen_univ) (by simp)
  change ContinuousOn
    (fun p : ℝ × Vec 2 => (fderiv ℝ (Function.uncurry u) p) TimeEnergy.timeVector)
    classicalPositiveTimeDomain
  exact hf.clm_apply continuousOn_const

theorem classicalTimeSection_hasDerivAt {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun s => u s x) (classicalTimePartial u (t, x)) t := by
  have hp : (t, x) ∈ classicalPositiveTimeDomain := by simp [classicalPositiveTimeDomain, ht]
  have hAt : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry u) (t, x) :=
    hu.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have hf : HasFDerivAt (Function.uncurry u)
      (fderiv ℝ (Function.uncurry u) (t, x)) (t, x) :=
    (hAt.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => (s, x)) TimeEnergy.timeVector t := by
    convert (hasDerivAt_id t).prodMk (hasDerivAt_const t x) using 1 <;>
      simp [TimeEnergy.timeVector]
  have hcomp := hf.comp_hasDerivAt t hline
  simpa [classicalTimePartial, Function.uncurry, Function.comp_def] using hcomp

/-- The joint smooth representative's time partial is the ordinary derivative of a fixed spatial
section at every positive time. -/
theorem classicalTimePartial_eq_deriv {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    classicalTimePartial u (t, x) = deriv (fun s => u s x) t := by
  exact (classicalTimeSection_hasDerivAt hu ht x).deriv.symm

theorem classicalTimePartial_continuous_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : Continuous (fun x => classicalTimePartial u (t, x)) := by
  have hc := TimeEnergy.partialTime_continuousOn hu
  have hline : Continuous fun x : Vec 2 => (t, x) := continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun x : Vec 2 => (t, x)) Set.univ classicalPositiveTimeDomain := by
    intro x hx
    simp [classicalPositiveTimeDomain, ht]
  have hcomp : ContinuousOn (fun x : Vec 2 => classicalTimePartial u (t, x)) Set.univ := by
    exact hc.comp hline.continuousOn hmaps
  exact continuousOn_univ.mp (by simpa using hcomp)

theorem classicalSmooth_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec 2 => u t x) Set.univ := by
    have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) Set.univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmem : ∀ x ∈ Set.univ, (t, x) ∈ classicalPositiveTimeDomain := by
      intro x hx
      simp [classicalPositiveTimeDomain, ht]
    have hcomp := hu.comp hmap hmem
    simpa [Function.uncurry, Function.comp_def] using hcomp
  exact contDiffOn_univ.mp hcomp

theorem classicalSmooth_slice_nonneg {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) Set.univ :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmem : ∀ x : Vec 2, x ∈ Set.univ →
      (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    intro x hx
    exact ⟨ht, mem_univ _⟩
  have hcomp := hu.comp hmap hmem
  exact contDiffOn_univ.mp (by simpa [Function.uncurry, Function.comp_def] using hcomp)

theorem classicalContinuous_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : Continuous (u t) :=
  (classicalSmooth_slice hu ht).continuous

/-- The unit-cell quadratic energy is differentiable at every positive time, with the expected
pointwise time derivative under the integral. -/
theorem unitCell_energy_hasDerivAt {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCell 2, (u s x) ^ 2)
      (∫ x in unitCell 2, 2 * u t x * classicalTimePartial u (t, x)) t := by
  have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain :=
    hu.mono (by
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
  let K : Set (ℝ × Vec 2) :=
    Set.Icc (t - radius) (t + radius) ×ˢ
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
  have hKcompact : IsCompact K := by
    apply IsCompact.prod isCompact_Icc
    exact TimeEnergy.isCompact_closedUnitCell
  have hKopen : K ⊆ classicalPositiveTimeDomain := by
    rintro ⟨s, x⟩ hp
    simp only [K, Set.mem_prod, Set.mem_Icc] at hp
    dsimp [radius] at hp
    simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ]
    constructor
    · linarith
    · trivial
  have huCont := huOpen.continuousOn
  have huBound := hKcompact.exists_bound_of_continuousOn (huCont.mono hKopen)
  obtain ⟨C₀, hC₀⟩ := huBound
  have hdtCont := TimeEnergy.partialTime_continuousOn huOpen
  have hdtBound := hKcompact.exists_bound_of_continuousOn (hdtCont.mono hKopen)
  obtain ⟨C₁, hC₁⟩ := hdtBound
  let bound : ℝ := 2 * (C₀ + 1) * (C₁ + 1)
  let μ : Measure (Vec 2) := volume.restrict (unitCell 2)
  let integrand : ℝ → Vec 2 → ℝ := fun s x => (u s x) ^ 2
  let integrandDeriv : ℝ → Vec 2 → ℝ :=
    fun s x => 2 * u s x * classicalTimePartial u (s, x)
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (integrand s) μ := by
    filter_upwards [Metric.ball_mem_nhds t hradius] with s hs
    exact ((classicalContinuous_slice huOpen (hball hs)).pow 2).aestronglyMeasurable
  have hFint : Integrable (integrand t) μ := by
    change IntegrableOn (fun x => (u t x) ^ 2) (unitCell 2)
    apply continuous_integrableOn_unitCell
    exact (classicalContinuous_slice huOpen ht).pow 2
  have hF'diff : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t radius,
      HasDerivAt (integrand · x) (integrandDeriv s x) s := by
    apply (ae_restrict_iff' (measurableSet_unitCell 2)).2
    filter_upwards with x hx
    intro s hs
    have htime := classicalTimeSection_hasDerivAt huOpen (hball hs) x
    have hpow : HasDerivAt (fun r => u r x ^ 2)
        (2 * u s x * classicalTimePartial u (s, x)) s := by
      have hpow0 := htime.pow 2
      have hfun : (fun r => u r x) ^ 2 = (fun r => u r x ^ 2) := by
        funext r
        rfl
      rw [hfun] at hpow0
      simpa using hpow0
    change HasDerivAt (fun r => u r x ^ 2)
      (2 * u s x * classicalTimePartial u (s, x)) s
    exact hpow
  have hF'meas : AEStronglyMeasurable (integrandDeriv t) μ := by
    have hcont : Continuous (integrandDeriv t) := by
      have huC := classicalContinuous_slice huOpen ht
      have hdtC := classicalTimePartial_continuous_slice huOpen ht
      change Continuous (fun x => 2 * u t x * classicalTimePartial u (t, x))
      exact ((continuous_const : Continuous fun _ : Vec 2 => (2 : ℝ)).mul huC).mul hdtC
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t radius,
      ‖integrandDeriv s x‖ ≤ bound := by
    apply (ae_restrict_iff' (measurableSet_unitCell 2)).2
    filter_upwards with x hx
    intro s hs
    have hsK : (s, x) ∈ K := by
      simp only [K, Set.mem_prod, Set.mem_Icc]
      refine ⟨?_, TimeEnergy.unitCell_subset_closedUnitCell hx⟩
      rw [Metric.mem_ball, Real.dist_eq] at hs
      dsimp [radius] at hs
      have h := abs_lt.mp hs
      change t - radius ≤ s ∧ s ≤ t + radius
      dsimp [radius]
      constructor <;> linarith
    have huBound' := hC₀ (s, x) hsK
    have hdtBound' := hC₁ (s, x) hsK
    have huNorm : ‖u s x‖ ≤ C₀ + 1 := by
      have huBound'' : ‖u s x‖ ≤ C₀ := by
        simpa [Function.uncurry] using huBound'
      exact le_trans huBound'' (by linarith)
    have hdtNorm : ‖classicalTimePartial u (s, x)‖ ≤ C₁ + 1 := by
      exact le_trans hdtBound' (by linarith)
    have huAbs : |u s x| ≤ C₀ + 1 := by simpa [Real.norm_eq_abs] using huNorm
    have hdtAbs : |classicalTimePartial u (s, x)| ≤ C₁ + 1 := by
      simpa [Real.norm_eq_abs] using hdtNorm
    dsimp [integrandDeriv, bound]
    calc
          |2 * u s x * classicalTimePartial u (s, x)| =
          2 * |u s x| * |classicalTimePartial u (s, x)| := by simp [abs_mul]
      _ ≤ 2 * (C₀ + 1) * (C₁ + 1) := by
        have hC₀nonneg : 0 ≤ C₀ + 1 := le_trans (abs_nonneg _) huAbs
        have hmul := mul_le_mul huAbs hdtAbs (abs_nonneg _) hC₀nonneg
        calc
          2 * |u s x| * |classicalTimePartial u (s, x)| =
              2 * (|u s x| * |classicalTimePartial u (s, x)|) := by ring
          _ ≤ 2 * ((C₀ + 1) * (C₁ + 1)) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          _ = 2 * (C₀ + 1) * (C₁ + 1) := by ring
      _ = bound := rfl
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t radius) (μ := μ) (bound := fun _ : Vec 2 => bound)
    (Metric.ball_mem_nhds t hradius) hFmeas hFint hF'meas hbound
    (by
      change IntegrableOn (fun _ : Vec 2 => bound) (unitCell 2)
      exact continuous_integrableOn_unitCell continuous_const)
    hF'diff
  simpa [integrand, integrandDeriv, μ] using hderiv.2

/-- The cell energy is continuous down to the initial time for a jointly smooth function on the
closed nonnegative time half-space. -/
theorem unitCell_energy_continuousOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x in unitCell 2, (u t x) ^ 2) (Set.Icc (0 : ℝ) T) := by
  let μ : Measure (Vec 2) := volume.restrict (unitCell 2)
  let integrand : ℝ → Vec 2 → ℝ := fun t x => (u t x) ^ 2
  let K : Set (ℝ × Vec 2) := Set.Icc (0 : ℝ) T ×ˢ
    Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
  have hKcompact : IsCompact K := by
    apply IsCompact.prod isCompact_Icc
    exact TimeEnergy.isCompact_closedUnitCell
  have hKsubset : K ⊆ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨ht.1, mem_univ _⟩
  have hbound := hKcompact.exists_bound_of_continuousOn
    (hu.continuousOn.mono hKsubset)
  obtain ⟨C, hC⟩ := hbound
  have hCnonneg : 0 ≤ C := by
    have hzero : (0, (0 : Vec 2)) ∈ K := by
      refine ⟨⟨le_rfl, hT⟩, ?_⟩
      intro i
      simp
    exact le_trans (norm_nonneg _) (hC (0, 0) hzero)
  let bound : ℝ := (C + 1) ^ 2
  have hmeas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEStronglyMeasurable (integrand t) μ := by
    intro t ht
    have hslice := classicalSmooth_slice_nonneg hu ht.1
    exact ((hslice.continuous).pow 2).aestronglyMeasurable
  have hdom : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ᵐ x ∂μ, ‖integrand t x‖ ≤ bound := by
    intro t ht
    apply (ae_restrict_iff' (measurableSet_unitCell 2)).2
    filter_upwards with x hx
    have hx' : x ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
      TimeEnergy.unitCell_subset_closedUnitCell hx
    have hp : (t, x) ∈ K := ⟨ht, hx'⟩
    have huBound : ‖u t x‖ ≤ C := by
      simpa [Function.uncurry] using hC (t, x) hp
    have huBound' : ‖u t x‖ ≤ C + 1 := huBound.trans (by linarith)
    dsimp [integrand, bound]
    calc
      |u t x ^ 2| = ‖u t x ^ 2‖ := (Real.norm_eq_abs _).symm
      _ = ‖u t x‖ ^ 2 := by rw [norm_pow]
      _ ≤ (C + 1) ^ 2 := by gcongr
  have hboundInt : Integrable (fun _ : Vec 2 => bound) μ := by
    change IntegrableOn (fun _ : Vec 2 => bound) (unitCell 2)
    exact continuous_integrableOn_unitCell continuous_const
  have htimeCont : ∀ x : Vec 2,
      ContinuousOn (fun t => (u t x) ^ 2) (Set.Icc (0 : ℝ) T) := by
    intro x
    have hline : ContinuousOn (fun t : ℝ => (t, x)) (Set.Icc (0 : ℝ) T) := by
      fun_prop
    have hmaps : MapsTo (fun t : ℝ => (t, x)) (Set.Icc (0 : ℝ) T)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
      intro t ht
      exact ⟨ht.1, mem_univ _⟩
    have hcomp := hu.continuousOn.comp hline hmaps
    have hcomp' : ContinuousOn (fun t => u t x) (Set.Icc (0 : ℝ) T) := by
      simpa [Function.uncurry, Function.comp_def] using hcomp
    exact hcomp'.pow 2
  have hcont : ∀ᵐ x ∂μ,
      ContinuousOn (fun t => integrand t x) (Set.Icc (0 : ℝ) T) := by
    filter_upwards with x
    exact htimeCont x
  have hresult := continuousOn_of_dominated hmeas hdom hboundInt hcont
  simpa [integrand, μ] using hresult

theorem smooth_spaceGrad_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceGrad (fun x => f x - g x) =
      fun x => AVenhance.spaceGrad f x - AVenhance.spaceGrad g x := by
  funext x i
  change fderiv ℝ (fun y => f y - g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem smooth_spaceLap_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceLap (fun x => f x - g x) =
      fun x => AVenhance.spaceLap f x - AVenhance.spaceLap g x := by
  funext x
  simp only [AVenhance.spaceLap]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (Homogenization.basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hgi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad g y i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ g y (Homogenization.basisVec i))
    exact (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have hinner : (fun y => AVenhance.spaceGrad (fun z => f z - g z) y i) =
      (fun y => AVenhance.spaceGrad f y i - AVenhance.spaceGrad g y i) := by
    funext y
    exact congrFun (congrFun (smooth_spaceGrad_sub hf hg) y) i
  rw [hinner]
  change fderiv ℝ (fun y => AVenhance.spaceGrad f y i - AVenhance.spaceGrad g y i)
      x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hfi.differentiable (by simp) x) (hgi.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem continuous_integrableOn_unitCellAt {f : Vec 2 → ℝ} (a : Vec 2)
    (hf : Continuous f) : IntegrableOn f (AVenhance.Infra.Torus.unitCellAt 2 a) := by
  let closedCell : Set (Vec 2) := Set.pi Set.univ (fun i : Fin 2 => Set.Icc (a i) (a i + 1))
  have hclosed : IsCompact closedCell := by
    simpa [closedCell] using isCompact_univ_pi (fun i : Fin 2 => isCompact_Icc)
  have hsub : AVenhance.Infra.Torus.unitCellAt 2 a ⊆ closedCell := by
    intro x hx
    simp only [AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq] at hx
    simp only [closedCell, Set.mem_pi, mem_univ, forall_true_left]
    intro i
    exact ⟨le_of_lt (hx i).1, hx i |>.2⟩
  exact (hf.continuousOn.integrableOn_compact hclosed).mono_set hsub

end AVenhance.Infra.Classical

end
