/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBasic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesNormComponents
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVAbstractAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFiniteAnalyticSum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.IndyStepDownV2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Seed
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Function.L2Space

/-! # The S-normalised temperature error

The positive increments telescope to `T (Nstar β) - θprev`.  The abstract
amplitude V estimate is applied with an amplitude tending down to the exact
quantity `S = √κprev ‖∇θprev‖`; the small positive slack handles `S = 0` without
adding a nonvanishing-temperature hypothesis. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section4

/-- Euclidean-normed real vectors used in the temperature error L² estimates. -/
abbrev TemperatureError.TemperatureEuclideanVec2 := PiLp 2 (fun _ : Fin 2 => ℝ)

/-- View a spatial vector in the Euclidean-normed carrier for the temperature estimates. -/
def TemperatureError.temperatureEuclideanVec2Lift (v : Vec 2) :
    TemperatureError.TemperatureEuclideanVec2 :=
  WithLp.toLp 2 v

theorem TemperatureError.temperatureVec2Lift_norm_sq (v : Vec 2) :
    ‖TemperatureError.temperatureEuclideanVec2Lift v‖ ^ 2 = vecNormSq v := by
  have hn : ‖TemperatureError.temperatureEuclideanVec2Lift v‖ = Real.sqrt (vecNormSq v) := by
    change ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : Fin 2 => ℝ))‖ = _
    rw [PiLp.norm_eq_of_L2]
    congr 1
    simp [Homogenization.vecNormSq, Homogenization.vecDot, Fin.sum_univ_two]
    ring
  rw [hn, Real.sq_sqrt (Homogenization.vecNormSq_nonneg v)]

theorem TemperatureError.temperatureLp_norm_sq_eq_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ ((hf.toLp f) x) ((hf.toLp f) x) ∂μ :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]

theorem TemperatureError.temperatureLp_norm_eq_sqrt_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  calc
    ‖hf.toLp f‖ = Real.sqrt (‖hf.toLp f‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
      rw [TemperatureError.temperatureLp_norm_sq_eq_integral hf]

theorem TemperatureError.temperature_spaceTimeVectorNormSq_add_le {F G : ℝ × Vec 2 → Vec 2}
    (hF : MemLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (F p)) 2
      (volume.restrict timeCube))
    (hG : MemLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (G p)) 2
      (volume.restrict timeCube)) :
    Real.sqrt (∫ p in timeCube, vecNormSq (F p + G p)) ≤
      Real.sqrt (∫ p in timeCube, vecNormSq (F p)) +
        Real.sqrt (∫ p in timeCube, vecNormSq (G p)) := by
  let HF : ℝ × Vec 2 → TemperatureError.TemperatureEuclideanVec2 := fun p =>
      TemperatureError.temperatureEuclideanVec2Lift (F p)
  let HG : ℝ × Vec 2 → TemperatureError.TemperatureEuclideanVec2 := fun p =>
      TemperatureError.temperatureEuclideanVec2Lift (G p)
  have hadd : (fun p => TemperatureError.temperatureEuclideanVec2Lift (F p + G p)) = HF + HG := by
    funext p
    change WithLp.toLp 2 (F p + G p) =
      WithLp.toLp 2 (F p) + WithLp.toLp 2 (G p)
    exact WithLp.toLp_add 2 (F p) (G p)
  have hsum : MemLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (F p + G p))
      2 (volume.restrict timeCube) := by
    rw [hadd]
    exact hF.add hG
  have hLp : hsum.toLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (F p + G p)) =
      hF.toLp HF + hG.toLp HG := by
    apply Lp.ext
    filter_upwards [hsum.coeFn_toLp, hF.coeFn_toLp, hG.coeFn_toLp,
      Lp.coeFn_add (hF.toLp HF) (hG.toLp HG)] with p hsum' hF' hG' hadd'
    calc
      hsum.toLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (F p + G p)) p =
          TemperatureError.temperatureEuclideanVec2Lift (F p + G p) := hsum'
      _ = hF.toLp HF p + hG.toLp HG p := by
        rw [hF', hG']
        exact congrFun hadd p
      _ = (hF.toLp HF + hG.toLp HG) p := hadd'.symm
  have hnormsq (H : ℝ × Vec 2 → Vec 2)
      (hH : MemLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (H p)) 2
        (volume.restrict timeCube)) :
      ‖hH.toLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (H p))‖ ^ 2 =
        ∫ p in timeCube, vecNormSq (H p) := by
    rw [TemperatureError.temperatureLp_norm_sq_eq_integral hH]
    apply integral_congr_ae
    filter_upwards with p
    exact TemperatureError.temperatureVec2Lift_norm_sq (H p)
  have hnorm (H : ℝ × Vec 2 → Vec 2)
      (hH : MemLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (H p)) 2
        (volume.restrict timeCube)) :
      ‖hH.toLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (H p))‖ =
        Real.sqrt (∫ p in timeCube, vecNormSq (H p)) := by
    calc
      _ = Real.sqrt (‖hH.toLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (H p))‖ ^ 2)
          := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = _ := by rw [hnormsq]
  have htriangle : ‖hsum.toLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (F p + G
      p))‖ ≤
      ‖hF.toLp HF‖ + ‖hG.toLp HG‖ := by
    rw [hLp]
    exact norm_add_le _ _
  rw [hnorm _ hsum, hnorm _ hF, hnorm _ hG] at htriangle
  exact htriangle

theorem TemperatureError.temperature_spaceTimeVectorNormSq_finset_sum_le
    {ι : Type*} (s : Finset ι) (F : ι → ℝ × Vec 2 → Vec 2)
    (hF : ∀ i ∈ s, MemLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (F i p))
      2 (volume.restrict timeCube)) :
    Real.sqrt (∫ p in timeCube, vecNormSq (∑ i ∈ s, F i p)) ≤
      ∑ i ∈ s, Real.sqrt (∫ p in timeCube, vecNormSq (F i p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Homogenization.vecNormSq, Homogenization.vecDot]
  | @insert a s ha ih =>
      have htail : MemLp (fun p => TemperatureError.temperatureEuclideanVec2Lift (∑ i ∈ s, F i p))
          2 (volume.restrict timeCube) := by
        have hs : MemLp (fun p => ∑ i ∈ s, TemperatureError.temperatureEuclideanVec2Lift (F i p))
            2 (volume.restrict timeCube) := MeasureTheory.memLp_finsetSum
              s (fun i hi => hF i (Finset.mem_insert_of_mem hi))
        have hEq : (fun p => TemperatureError.temperatureEuclideanVec2Lift (∑ i ∈ s, F i p)) =
            fun p => ∑ i ∈ s, TemperatureError.temperatureEuclideanVec2Lift (F i p) := by
          funext p
          change WithLp.toLp 2 (∑ i ∈ s, F i p) = _
          rw [WithLp.toLp_sum]
          rfl
        rw [hEq]
        exact hs
      have hadd := TemperatureError.temperature_spaceTimeVectorNormSq_add_le (hF a
        (Finset.mem_insert_self a s)) htail
      have hInt : (∫ p in timeCube, vecNormSq (∑ i ∈ insert a s, F i p)) =
          ∫ p in timeCube, vecNormSq (F a p + ∑ i ∈ s, F i p) := by
        apply integral_congr_ae
        filter_upwards with p
        simp [Finset.sum_insert, ha]
      rw [hInt]
      calc
        _ ≤ Real.sqrt (∫ p in timeCube, vecNormSq (F a p)) +
            Real.sqrt (∫ p in timeCube, vecNormSq (∑ i ∈ s, F i p)) := hadd
        _ ≤ Real.sqrt (∫ p in timeCube, vecNormSq (F a p)) +
            ∑ i ∈ s, Real.sqrt (∫ p in timeCube, vecNormSq (F i p)) :=
          add_le_add le_rfl (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))
        _ = _ := by rw [Finset.sum_insert ha]

theorem TemperatureError.temperature_spaceGrad_finset_sum {ι : Type*}
    (s : Finset ι) (u : ι → ℝ → Vec 2 → ℝ)
    (hD : ∀ i ∈ s, ∀ t, 0 < t → Differentiable ℝ (u i t))
    (t : ℝ) (ht : 0 < t) (x : Vec 2) :
    spaceGrad (fun y => ∑ i ∈ s, u i t y) x =
      ∑ i ∈ s, spaceGrad (u i t) x := by
  classical
  funext j
  change fderiv ℝ (fun y => ∑ i ∈ s, u i t y) x (basisVec j) = _
  have hAt : ∀ i ∈ s, DifferentiableAt ℝ (fun y => u i t y) x := by
    intro i hi
    exact hD i hi t ht x
  have hsumfun : (fun y => ∑ i ∈ s, u i t y) = ∑ i ∈ s, fun y => u i t y := by
    funext y
    simp only [Finset.sum_apply]
  rw [hsumfun, fderiv_sum hAt]
  simp [spaceGrad]

theorem TemperatureError.temperature_sqrt_spaceTimeGradNormSq_finset_sum_le
    {ι : Type*} (s : Finset ι) (u : ι → ℝ → Vec 2 → ℝ)
    (hD : ∀ i ∈ s, ∀ t, 0 < t → Differentiable ℝ (u i t))
    (hLp : ∀ i ∈ s, MemLp
      (fun p : ℝ × Vec 2 => TemperatureError.temperatureEuclideanVec2Lift (spaceGrad (u i p.1) p.2))
      2 (volume.restrict timeCube)) :
    Real.sqrt (spaceTimeGradNormSq
      (fun t x => spaceGrad (fun y => ∑ i ∈ s, u i t y) x)) ≤
      ∑ i ∈ s, Real.sqrt (spaceTimeGradNormSq
        (fun t x => spaceGrad (u i t) x)) := by
  classical
  have h := TemperatureError.temperature_spaceTimeVectorNormSq_finset_sum_le s
    (fun i p => spaceGrad (u i p.1) p.2) hLp
  have hCube : MeasurableSet timeCube := by
    rw [timeCube]
    refine MeasurableSet.prod measurableSet_Ioo ?_
    unfold unitCube
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  have hgrad : (fun p : ℝ × Vec 2 =>
      spaceGrad (fun y => ∑ i ∈ s, u i p.1 y) p.2) =ᵐ[volume.restrict timeCube]
      fun p => ∑ i ∈ s, spaceGrad (u i p.1) p.2 := by
    filter_upwards [ae_restrict_mem hCube] with p hp
    exact TemperatureError.temperature_spaceGrad_finset_sum s u hD p.1 hp.1.1 p.2
  have hnorm : (∫ p in timeCube,
      vecNormSq (spaceGrad (fun y => ∑ i ∈ s, u i p.1 y) p.2)) =
      ∫ p in timeCube, vecNormSq (∑ i ∈ s, spaceGrad (u i p.1) p.2) := by
    apply integral_congr_ae
    filter_upwards [hgrad] with p hp
    rw [hp]
  change Real.sqrt (∫ p in timeCube,
      vecNormSq (spaceGrad (fun y => ∑ i ∈ s, u i p.1 y) p.2)) ≤
    ∑ i ∈ s, Real.sqrt (∫ p in timeCube, vecNormSq (spaceGrad (u i p.1) p.2))
  rw [hnorm]
  exact h

/-- Closed time-space unit cell for the temperature error estimates. -/
def TemperatureError.temperatureErrorClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem TemperatureError.temperatureErrorClosedCell_compact : IsCompact
    TemperatureError.temperatureErrorClosedCell := by
  apply IsCompact.prod isCompact_Icc
  simpa using isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc)

theorem TemperatureError.timeCube_subset_temperatureErrorClosedCell :
    timeCube ⊆ TemperatureError.temperatureErrorClosedCell := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  refine ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
  change ∀ i ∈ Set.univ, p.2 i ∈ Set.Ioo (0 : ℝ) 1 at hx
  change ∀ i ∈ Set.univ, p.2 i ∈ Set.Icc (0 : ℝ) 1
  intro i hi
  exact Set.Ioo_subset_Icc_self (hx i hi)

theorem TemperatureError.temperatureError_memLp_of_continuousOn_closedCell
    {E : Type*} [NormedAddCommGroup E] {f : ℝ × Vec 2 → E}
    (hf : ContinuousOn f TemperatureError.temperatureErrorClosedCell) :
    MemLp f 2 (volume.restrict timeCube) := by
  have hfinite : IsFiniteMeasure (volume.restrict timeCube) := by
    rw [MeasureTheory.isFiniteMeasure_iff, Measure.restrict_apply_univ]
    exact (measure_mono TemperatureError.timeCube_subset_temperatureErrorClosedCell).trans_lt
      TemperatureError.temperatureErrorClosedCell_compact.measure_lt_top
  have himage : IsCompact (f '' TemperatureError.temperatureErrorClosedCell) :=
    TemperatureError.temperatureErrorClosedCell_compact.image_of_continuousOn hf
  obtain ⟨C, _hCpos, hC⟩ := himage.isBounded.subset_ball_lt 0 0
  have hcont : ContinuousOn f timeCube := hf.mono
      TemperatureError.timeCube_subset_temperatureErrorClosedCell
  have hmeas : AEStronglyMeasurable f (volume.restrict timeCube) :=
    hcont.aestronglyMeasurable (μ := volume) amnr_timeCube_isOpen.measurableSet
  apply @MemLp.of_bound (ℝ × Vec 2) E _ 2 (volume.restrict timeCube) _ hfinite f hmeas C
  filter_upwards [ae_restrict_mem amnr_timeCube_isOpen.measurableSet] with p hp
  have hp' : p ∈ TemperatureError.temperatureErrorClosedCell :=
      TemperatureError.timeCube_subset_temperatureErrorClosedCell hp
  have hball := hC ⟨p, hp', rfl⟩
  have hnorm : ‖f p‖ < C := by
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  exact hnorm.le

theorem TemperatureError.iterateCoordinateEnergyProfile_mono_amplitude
    {u : ℝ → Vec 2 → ℝ} {κ N N' L : ℝ} {i : ℕ}
    (hκ : 0 < κ) (hN : 0 ≤ N) (hNN' : N ≤ N')
    (hp : iterateCoordinateEnergyProfile u κ N L i) :
    iterateCoordinateEnergyProfile u κ N' L i := by
  have hsq : N ^ 2 ≤ N' ^ 2 := by nlinarith
  have hdiv : N / Real.sqrt κ ≤ N' / Real.sqrt κ :=
    div_le_div_of_nonneg_right hNN' (Real.sqrt_pos.mpr hκ).le
  have hsqdiv : (N / Real.sqrt κ) ^ 2 ≤ (N' / Real.sqrt κ) ^ 2 := by
    apply (sq_le_sq₀ (div_nonneg hN (Real.sqrt_nonneg _))
      (div_nonneg (le_trans hN hNN') (Real.sqrt_nonneg _))).2
    exact hdiv
  constructor
  · intro w hw s hs hs1
    exact (hp.1 w hw s hs hs1).trans
      (mul_le_mul_of_nonneg_right hsq (sq_nonneg (iterateAnalyticWeight w.length i L)))
  · intro w
    exact (hp.2 w).trans
      (mul_le_mul_of_nonneg_right hsqdiv
        (sq_nonneg (iterateAnalyticWeight w.length i L)))

theorem TemperatureError.iterateIncrement_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    {i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ Nstar β) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => iterateIncrement T i p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hnext := (hT.2 i hi hiN).1
  have hprev : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => T (i - 1) p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    by_cases hi1 : i = 1
    · subst i
      simpa [hT.1] using hθ.1
    · have hi' : 1 ≤ i - 1 := by omega
      have hiN' : i - 1 ≤ Nstar β := by omega
      exact (hT.2 (i - 1) hi' hiN').1
  have hEq : (fun p : ℝ × Vec 2 => iterateIncrement T i p.1 p.2) =
      fun p => T i p.1 p.2 - T (i - 1) p.1 p.2 := by
    funext p
    simp [iterateIncrement, show i ≠ 0 by omega]
  rw [hEq]
  exact hnext.sub hprev

theorem TemperatureError.iterateIncrement_gradient_memLp {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    {i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ Nstar β) :
    MemLp (fun p : ℝ × Vec 2 => TemperatureError.temperatureEuclideanVec2Lift
      (spaceGrad (iterateIncrement T i p.1) p.2)) 2 (volume.restrict timeCube) := by
  have hinc := TemperatureError.iterateIncrement_contDiffOn I hΦ hT hθ hi hiN
  have hgrad := AVenhance.Infra.Section5.LeftToShow.spaceGrad_continuousOn hinc
  have hlift : ContinuousOn (fun p : ℝ × Vec 2 => TemperatureError.temperatureEuclideanVec2Lift
      (spaceGrad (iterateIncrement T i p.1) p.2))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have hliftFn : Continuous TemperatureError.temperatureEuclideanVec2Lift := by
      change Continuous (WithLp.toLp 2)
      exact PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)
    exact hliftFn.comp_continuousOn hgrad
  have hcell : TemperatureError.temperatureErrorClosedCell ⊆ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    intro p hp
    exact ⟨hp.1.1, Set.mem_univ _⟩
  exact TemperatureError.temperatureError_memLp_of_continuousOn_closedCell (hlift.mono hcell)

/-- Finite positive-increment telescope in the spacetime gradient norm.
The only quantitative input is the zeroth-word slice of `l.V`; the base
profile is absent because the difference is the sum over `i ≥ 1`. -/
theorem temperature_error_of_V_zero_bounds {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    {N η : ℝ} (hN : 0 ≤ N) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hV : ∀ i, 1 ≤ i → i ≤ Nstar β →
      Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (iterateIncrement T i s) x)) ≤
        N * iterateAmplitude η i * ((2 * i).factorial : ℝ)) :
    Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x)) ≤
      (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * η * N := by
  let n := Nstar β
  have hTnSmooth : ∀ s : ℝ, 0 ≤ s → ContDiff ℝ (⊤ : ℕ∞) (T n s) := by
    intro s hs
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (s, x)) := by fun_prop
    by_cases hn0 : n = 0
    · rw [hn0, hT.1]
      exact hθ.1.comp_contDiff hmap (fun x => ⟨hs, Set.mem_univ _⟩)
    · have hn : 1 ≤ n := by omega
      exact (hT.2 n hn (by simp [n])).1.comp_contDiff hmap
        (fun x => ⟨hs, Set.mem_univ _⟩)
  have hθSmooth : ∀ s : ℝ, 0 ≤ s → ContDiff ℝ (⊤ : ℕ∞) (θprev s) := by
    intro s hs
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (s, x)) := by fun_prop
    exact hθ.1.comp_contDiff hmap (fun x => ⟨hs, Set.mem_univ _⟩)
  have hsubGrad : ∀ s : ℝ, 0 < s → ∀ x : Vec 2,
      spaceGrad (fun y => T n s y - θprev s y) x =
        spaceGrad (T n s) x - spaceGrad (θprev s) x := by
    intro s hs x
    funext j
    exact Infra.Section3.spaceGrad_sub j
      ((hTnSmooth s hs.le).differentiable (by simp) x)
      ((hθSmooth s hs.le).differentiable (by simp) x)
  have hD : ∀ i ∈ Finset.range n, ∀ s : ℝ, 0 < s →
      Differentiable ℝ (iterateIncrement T (i + 1) s) := by
    intro i hi s hs
    have hiN : i + 1 ≤ n := by
      have hmem := Finset.mem_range.mp hi
      omega
    have hinc := TemperatureError.iterateIncrement_contDiffOn I hΦ hT hθ (by omega) hiN
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (s, x)) := by fun_prop
    have hslice : ContDiff ℝ (⊤ : ℕ∞) (iterateIncrement T (i + 1) s) :=
      hinc.comp_contDiff hmap (fun x => ⟨hs.le, Set.mem_univ _⟩)
    exact hslice.differentiable (by simp)
  have hLp : ∀ i ∈ Finset.range n, MemLp
      (fun p : ℝ × Vec 2 => TemperatureError.temperatureEuclideanVec2Lift
        (spaceGrad (iterateIncrement T (i + 1) p.1) p.2))
      2 (volume.restrict timeCube) := by
    intro i hi
    have hiN : i + 1 ≤ n := by
      have hmem := Finset.mem_range.mp hi
      omega
    exact TemperatureError.iterateIncrement_gradient_memLp I hΦ hT hθ (by omega) hiN
  have hsumGrad := TemperatureError.temperature_sqrt_spaceTimeGradNormSq_finset_sum_le
    (Finset.range n) (fun i => iterateIncrement T (i + 1)) hD hLp
  have hsumEq : (fun s x => spaceGrad (fun y =>
      T n s y - θprev s y) x) = fun s x => spaceGrad
        (fun y => ∑ i ∈ Finset.range n, iterateIncrement T (i + 1) s y) x := by
    funext s x
    congr 1
    funext y
    exact iterate_sub_theta_eq_sum I hΦ hT n s y
  have hgrad : Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (fun y => T n s y - θprev s y) x)) ≤
      ∑ i ∈ Finset.range n, Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (iterateIncrement T (i + 1) s) x)) := by
    simpa only [hsumEq] using hsumGrad
  have hnormEq : spaceTimeGradNormSq (fun s x =>
      spaceGrad (T n s) x - spaceGrad (θprev s) x) =
      spaceTimeGradNormSq (fun s x =>
        spaceGrad (fun y => T n s y - θprev s y) x) := by
    unfold spaceTimeGradNormSq
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem amnr_timeCube_isOpen.measurableSet] with p hp
    rw [hsubGrad p.1 hp.1.1 p.2]
  have hpiece : Real.sqrt κprev *
      (∑ i ∈ Finset.range n, Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (iterateIncrement T (i + 1) s) x))) ≤
      ∑ i ∈ Finset.range n,
        (N * iterateAmplitude η (i + 1) * ((2 * (i + 1)).factorial : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hV (i + 1) (by omega) (by
      have hmem := Finset.mem_range.mp hi
      omega)
  have hbound :
      (∑ i ∈ Finset.range n,
        (N * iterateAmplitude η (i + 1) * ((2 * (i + 1)).factorial : ℝ))) ≤
        (n : ℝ) * (N * η * ((2 * n).factorial : ℝ)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (N * η * ((2 * n).factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        have hamp := iterate_amplitude_le_parameter hη hη1 (by omega : 1 ≤ i + 1)
        have hfact : ((2 * (i + 1)).factorial : ℝ) ≤ ((2 * n).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le (by omega : 2 * (i + 1) ≤ 2 * n)
        have hprod : iterateAmplitude η (i + 1) * ((2 * (i + 1)).factorial : ℝ) ≤
            η * ((2 * n).factorial : ℝ) := by
          calc
            _ ≤ η * ((2 * (i + 1)).factorial : ℝ) :=
              mul_le_mul_of_nonneg_right hamp (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left hfact hη
        have hNmul := mul_le_mul_of_nonneg_left hprod hN
        simpa only [mul_assoc] using hNmul
      _ = (n : ℝ) * (N * η * ((2 * n).factorial : ℝ)) := by simp
  have hκsqrt : 0 ≤ Real.sqrt κprev := Real.sqrt_nonneg _
  have hfinal := (mul_le_mul_of_nonneg_left hgrad hκsqrt).trans
    (hpiece.trans hbound)
  dsimp [n] at hfinal ⊢
  calc
    _ = Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
        spaceGrad (fun y => T n s y - θprev s y) x)) := by rw [hnormEq]
    _ ≤ (Nstar β : ℝ) * (N * η * ((2 * Nstar β).factorial : ℝ)) := hfinal
    _ = (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * η * N := by ring

theorem TemperatureError.temperatureError_radius_max_eq_one {β : ℝ} (I : Ingredients β)
    {m : ℕ} {R : ℝ} (hR : 0 < R)
    (hLater : epsilon β I.Λ (m - 1) ^
      (1 + gamma β / 2 - delta β) ≤ R) :
    max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * R ^ (-2 : ℤ)) = 1 := by
  let E := epsilon β I.Λ (m - 1)
  let p := 1 + gamma β / 2 - delta β
  have hE : 0 < E := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hq : E ^ (1 + gamma β / 2) ≤ R := by
    have hgate : E ^ p ≤ R := by simpa [E, p] using hLater
    have hp : p ≤ 1 + gamma β / 2 := by dsimp [p]; linarith [hδ]
    exact (Real.rpow_le_rpow_of_exponent_ge hE hE1 hp).trans hgate
  have hpower : (E ^ (1 + gamma β / 2)) ^ (2 : ℕ) = E ^ (2 + gamma β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    ring
  have hsquare : E ^ (2 + gamma β) ≤ R ^ 2 := by
    rw [← hpower]
    exact (sq_le_sq₀ (Real.rpow_nonneg hE.le _) hR.le).2 hq
  apply max_eq_left
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  exact (div_le_one (pow_pos hR 2)).2 hsquare

/-- The `hTemperatureError` leaf with the exact S-normalisation of .

`hbase` is the scale-`S` theta profile in the precise shape
consumed by abstract l.V. The flow, coefficient and smallness hypotheses are
likewise kept in the exact shapes consumed there. `hCt` allows the surrounding
`RelativeLeaves` record to choose any constant at least the explicit bound. -/
theorem temperatureError_leaf_of_abstract_V {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 2 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {c Ck K Cflow Cmean Rflow Cθ Rθ C₀ Ct : ℝ}
    (hc : 0 < c) (hCk : 0 ≤ Ck) (hK : 0 ≤ K) (hCf : 0 ≤ Cflow) (hCm : 0 ≤ Cmean)
    (hRf : 256 ≤ Rflow) (hRθ : 0 < Rθ)
    (hlower : c * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) ≤ κprev)
    (hupper : κprev ≤ Ck * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)))
    (hC₀ : iterateSourceConstant
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Cθ ≤ C₀)
    (hsmall : C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) ≤ 1)
    (hKm : ∀ t j k, |I.Kmat κm m t j k| ≤ K * κprev)
    (hmean : ∀ j k, |(timeAvgMat (I.Kmat κm m) - κprev •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤ κprev * Cmean *
        epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * (Rflow / epsilon β I.Λ (m - 1)) ^ p.length)
    (hκscale : |κm| ≤ κprev)
    (hLater : epsilon β I.Λ (m - 1) ^
      (1 + gamma β / 2 - delta β) ≤ Rθ)
    (hbase : iterateCoordinateEnergyProfile θprev κprev
      (Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (θprev s) x)))
      (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) 0)
    (hCt : (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * C₀ ^ 3 ≤ Ct) :
    Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
      spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x)) ≤
      Ct * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
        (Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
          (fun s x => spaceGrad (θprev s) x))) := by
  let E := epsilon β I.Λ (m - 1)
  let ρ := E ^ (2 * delta β)
  let S := Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
    (fun s x => spaceGrad (θprev s) x))
  let η := C₀ ^ 3 * ρ * max 1 (E ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))
  let L := max (C₀ * E ^ (-1 - gamma β / 2)) (C₀ / Rθ)
  have hE : 0 < E := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hκ : 0 < κprev := by
    have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
    exact (mul_pos hc (mul_pos ha (Real.rpow_pos_of_pos hE _))).trans_le hlower
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg κprev) (Real.sqrt_nonneg _)
  have hmax := TemperatureError.temperatureError_radius_max_eq_one I hRθ hLater
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hE _
  have hC₀pos : 0 < C₀ := by
    have hC₀one := (iterate_source_constant_bounds
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean)
      Rflow Cθ).1.trans hC₀
    linarith
  have hη : 0 ≤ η := by positivity
  have hη1 : η ≤ 1 := by
    have hmax1 : 1 ≤ max 1 (E ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) := le_max_left _ _
    have hηle : η ≤ C₀ ^ 3 * ρ * max 1 (E ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) := by
      simp [η]
    have hηh : C₀ ^ 3 * ρ * max 1 (E ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) ≤ 1 := by
      simpa [E, ρ] using hsmall
    exact le_trans hηle hηh
  have hηeq : η = C₀ ^ 3 * ρ := by
    dsimp [η, E]
    rw [hmax]
    simp
  have hCt0 : 0 ≤ Ct := by
    apply le_trans _ hCt
    positivity
  have hprofile {q : ℝ} (hq : 0 ≤ q) :
      iterateCoordinateEnergyProfile θprev κprev (S + q) L 0 := by
    have hbase' : iterateCoordinateEnergyProfile θprev κprev S L 0 := by
      simpa [S, L, E] using hbase
    exact TemperatureError.iterateCoordinateEnergyProfile_mono_amplitude hκ hS
      (by linarith) hbase'
  have herrorSlack : ∀ q : ℝ, 0 < q →
      Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
        spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x)) ≤
      (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * η * (S + q) := by
    intro q hq
    have hV := iterate_V_abstract_amplitude_of_diffusivity_and_flow I hΦ hT hθ hm hκm
      hflow hflowp hA3 (N := S + q) (by linarith) hc hCk hK hCf hCm hRf hRθ
      hlower hupper hC₀ hsmall hKm hmean hzero hpositive hκscale (hprofile hq.le)
    have hAmpEq : C₀ ^ 3 * E ^ (2 * delta β) *
        max 1 (E ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) = η := by
      dsimp [η, ρ]
    have hVall : ∀ i, 1 ≤ i → i ≤ Nstar β → ∀ v w : List (Fin 2),
        v.length = w.length → ∀ s, 0 ≤ s → s ≤ 1 →
        Real.sqrt (l2NormSq (iterateSpatialWord v (iterateIncrement T i s))) +
          Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
            (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T i t)))) ≤
        (S + q) * iterateAmplitude η i * iterateAnalyticWeight v.length i L := by
      simpa only [hAmpEq, L] using hV
    have hV0 : ∀ i, 1 ≤ i → i ≤ Nstar β →
        Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
          (fun s x => spaceGrad (iterateIncrement T i s) x)) ≤
        (S + q) * iterateAmplitude η i * ((2 * i).factorial : ℝ) := by
      intro i hi hiN
      have h := hVall i hi hiN [] [] rfl 0 (by norm_num) (by norm_num)
      simp only [iterateSpatialWord, List.length_nil] at h
      have hnonneg : 0 ≤ Real.sqrt (l2NormSq (iterateIncrement T i 0)) := Real.sqrt_nonneg _
      have h' : Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
          (fun s x => spaceGrad (iterateIncrement T i s) x)) ≤
          (S + q) * iterateAmplitude η i * iterateAnalyticWeight 0 i L := by
        linarith
      simpa [iterateAnalyticWeight, iterateSpatialWord] using h'
    have herror := temperature_error_of_V_zero_bounds I hΦ hT hθ
      (by linarith : 0 ≤ S + q) hη hη1 hV0
    exact herror
  let B := (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * C₀ ^ 3
  let X := Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq (fun s x =>
    spaceGrad (T (Nstar β) s) x - spaceGrad (θprev s) x))
  have hrawcoef : (Nstar β : ℝ) * ((2 * Nstar β).factorial : ℝ) * η = B * ρ := by
    rw [hηeq]
    dsimp [B]
    ring
  have hcoef : B * ρ ≤ Ct * ρ :=
    mul_le_mul_of_nonneg_right hCt (Real.rpow_nonneg hE.le _)
  have hgoalAux : X ≤ Ct * ρ * S := by
    by_contra hnot
    have hlt : Ct * ρ * S < X := lt_of_not_ge hnot
    let q := (X - Ct * ρ * S) / (Ct * ρ + 1)
    have hq : 0 < q := by
      dsimp [q]
      exact div_pos (sub_pos.mpr hlt) (by positivity)
    have hbound := herrorSlack q hq
    have hCtMul : 0 ≤ Ct * ρ := mul_nonneg hCt0 (Real.rpow_nonneg hE.le _)
    have hqmul : Ct * ρ * q < X - Ct * ρ * S := by
      dsimp [q]
      have hfrac : Ct * ρ / (Ct * ρ + 1) < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
      calc
        _ = (X - Ct * ρ * S) *
              (Ct * ρ / (Ct * ρ + 1)) := by ring
        _ < (X - Ct * ρ * S) * 1 :=
          mul_lt_mul_of_pos_left hfrac (sub_pos.mpr hlt)
        _ = X - Ct * ρ * S := by ring
    have hbound' :
        X ≤ Ct * ρ * (S + q) := by
      rw [hrawcoef] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (add_nonneg hS hq.le))
    have : X ≤ Ct * ρ * S + Ct * ρ * q := by
      calc
        _ ≤ Ct * ρ * (S + q) := hbound'
        _ = _ := by ring
    linarith
  simpa [ρ, S, X] using hgoalAux

end AVenhance.Infra.Section5.RelativeError
