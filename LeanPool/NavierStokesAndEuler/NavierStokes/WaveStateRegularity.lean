/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeDebtIncrement
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricFlatFactor

/-!
# Regularity of covariances of the actual harmonic state

Finite harmonic fields are assembled before taking their actual angular
integral. Smoothness of that integral follows from local compact
domination of its genuine parameter derivatives. No covariance
regularity or covariance formula is an input.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.WaveStateRegularity

open Set Function Filter MeasureTheory CorrectionState HarmonicFields
open scoped Topology ContDiff BigOperators Interval


variable {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Angular smooth, given by `∀ n i, ContDiffOn ℝ ∞ (fun p => u n p i)
(HarmonicResidual.liftDomain Ω)`. -/
noncomputable def AngularSmooth (Ω : Set D) (u : Oscillation D) : Prop :=
  ∀ n i, ContDiffOn ℝ ∞ (fun p => u n p i) (HarmonicResidual.liftDomain Ω)

theorem AngularSmooth.add {Ω : Set D} {u v : Oscillation D}
    (hu : AngularSmooth Ω u) (hv : AngularSmooth Ω v) : AngularSmooth Ω (u + v) :=
  fun n i => (hu n i).add (hv n i)

/-- Joint local smoothness gives continuous actual parameter jets.
Compactness of the angular interval then supplies their local majorants. -/
theorem compactIntegral_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {F : D × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (HarmonicResidual.liftDomain Ω))
    (a b : ℝ) (hab : a ≤ b) :
    ContDiffOn ℝ ∞ (fun x => ∫ θ in a..b, F (x, θ)) Ω := by
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet hΩ hab
  · intro θ _
    exact hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx, Set.mem_univ θ⟩)
  · intro k
    rintro ⟨x, θ⟩ hp
    have hAt : ContDiffAt ℝ ∞ F (x, θ) :=
      hF.contDiffAt ((HarmonicResidual.liftDomain_open hΩ).mem_nhds ⟨hp.1, Set.mem_univ θ⟩)
    have hSwap : ContDiffAt ℝ ∞ (Function.uncurry (fun θ x => F (x, θ))) (θ, x) :=
      hAt.comp (θ, x) (contDiffAt_snd.prodMk contDiffAt_fst)
    have hj := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv
      (fun θ x => F (x, θ)) k θ x hSwap
    exact (hj.comp (x, θ) (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt.continuousWithinAt

theorem angularAverage_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {f : OscillatoryScalar D}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (HarmonicResidual.liftDomain Ω)) :
    MeanIncrementBounds.SmoothOn Ω (angularAverage f) := by
  intro n
  exact (compactIntegral_smooth hΩ (hf n) 0 (2 * Real.pi) (by positivity)).div_const (2 * Real.pi)

theorem bilinearCovariance_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {u v : Oscillation D} (hu : AngularSmooth Ω u) (hv : AngularSmooth Ω v) (i j : Fin 3) :
    MeanIncrementBounds.SmoothOn Ω (bilinearCovariance u v i j) :=
  angularAverage_smooth hΩ (fun n => (hu n i).mul (hv n j))

theorem covarianceIncrement_smooth [ProperSpace D] {Ω : Set D} (hΩ : IsOpen Ω)
    {u w : Oscillation D} (hu : AngularSmooth Ω u) (hw : AngularSmooth Ω w) (i j : Fin 3) :
    MeanIncrementBounds.SmoothOn Ω (SignedMeanGain.covarianceIncrement u w i j) :=
  (bilinearCovariance_smooth hΩ (hu.add hw) (hu.add hw) i j).sub
    (bilinearCovariance_smooth hΩ hu hu i j)

/-! ## Smoothness from the actual local harmonic coefficients -/

omit [NormedSpace ℝ D] in
theorem field_zero_germ {c : Coefficients D} (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {x : D} (θ : ℝ) (hz : ∀ j, c j =ᶠ[𝓝 x] fun _ => 0) :
    field c k Φ kp =ᶠ[𝓝 (x, θ)] fun _ => 0 := by
  have hbase : ∀ᶠ y in 𝓝 x, ∀ j ∈ c.support, c j y = 0 :=
    (Filter.eventually_all_finset c.support).2 (fun j _ => hz j)
  have hlift := (continuous_fst.continuousAt :
    Tendsto (Prod.fst : D × ℝ → D) (𝓝 (x, θ)) (𝓝 x)).eventually hbase
  filter_upwards [hlift] with p hp
  rw [show p = (p.1, p.2) from rfl, field_expansion]
  exact Finset.sum_eq_zero (fun j hj => by rw [hp j hj]; simp)

theorem field_smoothOn_of_germs {Ω C : Set D} (hΩ : IsOpen Ω) (hC : IsOpen C)
    {c : Coefficients D} (hc : HarmonicResidual.SmoothCoefficients (Ω ∩ C) c)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (Ω ∩ C)) (k : ℝ) (kp : ℤ)
    (hz : ∀ x, x ∈ Ω → x ∉ C → ∀ j, c j =ᶠ[𝓝 x] fun _ => 0) :
    ContDiffOn ℝ ∞ (field c k Φ kp) (HarmonicResidual.liftDomain Ω) := by
  intro p hp
  classical
  by_cases hi : p.1 ∈ C
  · exact ((HarmonicResidual.field_smoothOn hc hΦ k kp).contDiffAt
      ((HarmonicResidual.liftDomain_open (hΩ.inter hC)).mem_nhds
        ⟨⟨hp.1, hi⟩, Set.mem_univ p.2⟩)).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (field_zero_germ k Φ kp p.2 (hz p.1 hp.1 hi))).contDiffWithinAt

/-- Primitive local data for every active block. Harmonics are the
actual finite group-algebra coefficients, including harmonic zero. -/
structure LocalData (Ω : Set D) (labels : ℕ → Finset ι)
    (blocks : ι → HarmonicBlock D) (C : ℕ → ι → Set D) : Prop where
  patch_open : ∀ n l, l ∈ labels n → IsOpen (C n l)
  coefficient : ∀ n l, l ∈ labels n → ∀ i,
    HarmonicResidual.SmoothCoefficients (Ω ∩ C n l) ((blocks l).velocity n i)
  phase : ∀ n l, l ∈ labels n → ContDiffOn ℝ ∞ ((blocks l).phase n) (Ω ∩ C n l)
  off_patch : ∀ n l, l ∈ labels n → ∀ x, x ∈ Ω → x ∉ C n l →
    ∀ i j, (blocks l).velocity n i j =ᶠ[𝓝 x] fun _ => 0

namespace LocalData

variable {Ω : Set D} {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock D}
  {C : ℕ → ι → Set D}

theorem of_global
    (hc : ∀ n l, l ∈ labels n → ∀ i, HarmonicResidual.SmoothCoefficients Ω ((blocks l).velocity n
        i))
    (hΦ : ∀ n l, l ∈ labels n → ContDiffOn ℝ ∞ ((blocks l).phase n) Ω) :
    LocalData Ω labels blocks (fun _ _ => Set.univ) :=
  ⟨fun _ _ _ => isOpen_univ, fun n l hl i j => (hc n l hl i j).mono inter_subset_left,
    fun n l hl => (hΦ n l hl).mono inter_subset_left,
    fun _ _ _ _ _ hn => (hn (Set.mem_univ _)).elim⟩

theorem block_smooth (h : LocalData Ω labels blocks C) (hΩ : IsOpen Ω)
    (n : ℕ) (l : ι) (hl : l ∈ labels n) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun p => (blocks l).oscillation n p i) (HarmonicResidual.liftDomain Ω) :=
  Complex.reCLM.contDiff.comp_contDiffOn
    (field_smoothOn_of_germs hΩ (h.patch_open n l hl) (h.coefficient n l hl i)
      (h.phase n l hl) ((blocks l).frequency n) ((blocks l).angularFrequency n)
      (fun x hx hC j => h.off_patch n l hl x hx hC i j))

theorem fieldSum_smooth (h : LocalData Ω labels blocks C) (hΩ : IsOpen Ω) :
    AngularSmooth Ω (LabelSumBounds.fieldSum labels (fun l => (blocks l).oscillation)) := by
  intro n i
  exact ContDiffOn.sum (fun l hl => h.block_smooth hΩ n l hl i)

end LocalData

/-! ## Actual support in the moving radial annulus -/

/-- Plane: an abbreviation for `GaugeDebtIncrement.Plane`. -/
abbrev Plane := GaugeDebtIncrement.Plane
/-- Point: an abbreviation for `GaugeDebtIncrement.Point`. -/
abbrev Point := GaugeDebtIncrement.Point

/-- Wave support, given by `∀ n θ i, VariableGaugeMean.SupportedGauge a b
(VariableGaugeMean.qLength coord) U.carrier (fun x => u n (x, θ) i)`. -/
noncomputable def WaveSupport {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (a b : ℝ) (u : Oscillation Point) : Prop :=
  ∀ n θ i, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
    U.carrier (fun x => u n (x, θ) i)

theorem WaveSupport.add {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {u v : Oscillation Point} (hu : WaveSupport U a b u) (hv : WaveSupport U a b v) :
    WaveSupport U a b (u + v) := by
  intro n θ i x hx hn
  by_cases hz : u n (x, θ) i = 0
  · exact hv n θ i x hx (fun hv0 => hn (by simp [hz, hv0]))
  · exact hu n θ i x hx hz

theorem angularAverage_supported {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {f : OscillatoryScalar Point}
    (hs : ∀ n θ, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
      U.carrier (fun x => f n (x, θ))) :
    ∀ n, VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
      U.carrier (angularAverage f n) := by
  intro n x hx hn
  by_contra hout
  have hz (θ : ℝ) : f n (x, θ) = 0 := by
    by_contra hne
    exact hout (hs n θ x hx hne)
  apply hn
  simp only [angularAverage, hz, intervalIntegral.integral_zero, zero_div]

theorem bilinearCovariance_regular {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    {u v : Oscillation Point}
    (hu : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hv : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) v)
    (hs : WaveSupport U a b u) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b (bilinearCovariance u v i j) := by
  refine ⟨bilinearCovariance_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen) hu hv i j, ?_⟩
  apply angularAverage_supported
  intro n θ x hx hn
  exact hs n θ i x hx (left_ne_zero_of_mul hn)

/-- Only the new wave needs annular support: outside it the old
covariance cancels in the literal difference of angular integrals. -/
theorem covarianceIncrement_regular {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    {u w : Oscillation Point}
    (hu : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) u)
    (hw : AngularSmooth (PhysicalMeanDomain.slowDomain U.carrier) w)
    (hs : WaveSupport U a b w) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b (SignedMeanGain.covarianceIncrement u w i j) := by
  refine ⟨covarianceIncrement_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen) hu hw i j, ?_⟩
  intro n x hx hn
  by_contra hout
  have hz (θ : ℝ) (r : Fin 3) : w n (x, θ) r = 0 := by
    by_contra hne
    exact hout (hs n θ r x hx hne)
  apply hn
  simp only [SignedMeanGain.covarianceIncrement, bilinearCovariance, angularAverage,
    Pi.sub_apply, Pi.add_apply, hz, add_zero, sub_self]

/-- Geometric support of the actual complex coefficient functions.
This includes the zero harmonic and imposes no covariance condition. -/
noncomputable def CoefficientSupport {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (a b : ℝ) (labels : ℕ → Finset ι) (blocks : ι → HarmonicBlock Point) : Prop :=
  ∀ n l, l ∈ labels n → ∀ i j x, x.2.1 ∈ U.carrier → (blocks l).velocity n i j x ≠ 0 →
    x.1 ∈ Icc (VariableGaugeMean.qLength coord x.2.1 * a)
      (VariableGaugeMean.qLength coord x.2.1 * b)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem field_eq_zero_of_coefficients {c : Coefficients D} (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (x : D) (θ : ℝ) (hz : ∀ j, c j x = 0) : field c k Φ kp (x, θ) = 0 := by
  rw [field_expansion]
  exact Finset.sum_eq_zero (fun j _ => by rw [hz j]; simp)

theorem fieldSum_support_of_coefficients {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock Point}
    (hs : CoefficientSupport U a b labels blocks) :
    WaveSupport U a b (LabelSumBounds.fieldSum labels (fun l => (blocks l).oscillation)) := by
  intro n θ i x hx hn
  by_contra hout
  have hz (l : ι) (hl : l ∈ labels n) (j : ℤ) : (blocks l).velocity n i j x = 0 := by
    by_contra hne
    exact hout (hs n l hl i j x hx hne)
  apply hn
  apply Finset.sum_eq_zero
  intro l hl
  have hf := field_eq_zero_of_coefficients ((blocks l).frequency n) ((blocks l).phase n)
    ((blocks l).angularFrequency n) x θ (hz l hl)
  change (field _ _ _ _ _).re = 0
  rw [hf, Complex.zero_re]

theorem fieldSum_support {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {labels : ℕ → Finset ι} {u : ι → Oscillation Point}
    (hs : ∀ n l, l ∈ labels n → ∀ θ i,
      VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord)
        U.carrier (fun x => u l n (x, θ) i)) :
    WaveSupport U a b (LabelSumBounds.fieldSum labels u) := by
  intro n θ i x hx hn
  by_contra hout
  apply hn
  apply Finset.sum_eq_zero
  intro l hl
  by_contra hne
  exact hout (hs n l hl θ i x hx hne)

/-! ## Concrete finite-active state adapters -/

section State

variable {coord a b : ℝ} (U : LocalSignedRequest.SlowRegion coord)
  {labels₀ labels₁ : ℕ → Finset ι} {blocks₀ blocks₁ : ι → HarmonicBlock Point}
  {C₀ C₁ : ℕ → ι → Set Point}

theorem fieldSum_covariance_regular
    (h : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₀ blocks₀ C₀)
    (hs : CoefficientSupport U a b labels₀ blocks₀) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b
      (bilinearCovariance (LabelSumBounds.fieldSum labels₀ (fun l => (blocks₀ l).oscillation))
        (LabelSumBounds.fieldSum labels₀ (fun l => (blocks₀ l).oscillation)) i j) :=
  bilinearCovariance_regular U (h.fieldSum_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen))
    (h.fieldSum_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen))
    (fieldSum_support_of_coefficients hs) i j

theorem fieldSum_covarianceIncrement_regular
    (h₀ : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₀ blocks₀ C₀)
    (h₁ : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₁ blocks₁ C₁)
    (hs₁ : CoefficientSupport U a b labels₁ blocks₁) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b (SignedMeanGain.covarianceIncrement
      (LabelSumBounds.fieldSum labels₀ (fun l => (blocks₀ l).oscillation))
      (LabelSumBounds.fieldSum labels₁ (fun l => (blocks₁ l).oscillation)) i j) :=
  covarianceIncrement_regular U (h₀.fieldSum_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen))
    (h₁.fieldSum_smooth (PhysicalMeanDomain.slowDomain_open U.isOpen))
    (fieldSum_support_of_coefficients hs₁) i j

theorem state_covariance_regular (u : State Point)
    (hu : u.oscillation = LabelSumBounds.fieldSum labels₀ (fun l => (blocks₀ l).oscillation))
    (h : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₀ blocks₀ C₀)
    (hs : CoefficientSupport U a b labels₀ blocks₀) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b (u.covariance i j) := by
  change GaugeDebtIncrement.Regular U a b (bilinearCovariance u.oscillation u.oscillation i j)
  rw [hu]
  exact fieldSum_covariance_regular U h hs i j

theorem state_covarianceIncrement_regular (u : State Point)
    (hu : u.oscillation = LabelSumBounds.fieldSum labels₀ (fun l => (blocks₀ l).oscillation))
    (h₀ : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₀ blocks₀ C₀)
    (h₁ : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₁ blocks₁ C₁)
    (hs₁ : CoefficientSupport U a b labels₁ blocks₁) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b (SignedMeanGain.covarianceIncrement u.oscillation
      (LabelSumBounds.fieldSum labels₁ (fun l => (blocks₁ l).oscillation)) i j) := by
  rw [hu]
  exact fieldSum_covarianceIncrement_regular U h₀ h₁ hs₁ i j

theorem waveStage_covariance_regular (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point)
    (hu : u.oscillation = LabelSumBounds.fieldSum labels₀ (fun l => (blocks₀ l).oscillation))
    (h₀ : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₀ blocks₀ C₀)
    (h₁ : LocalData (PhysicalMeanDomain.slowDomain U.carrier) labels₁ blocks₁ C₁)
    (hs₀ : CoefficientSupport U a b labels₀ blocks₀)
    (hs₁ : CoefficientSupport U a b labels₁ blocks₁)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point) (i j : Fin 3) :
    GaugeDebtIncrement.Regular U a b ((SignedMeanGain.waveStage g c u
      (LabelSumBounds.fieldSum labels₁ (fun l => (blocks₁ l).oscillation)) q gaussian).covariance i
          j) := by
  rw [SignedMeanGain.waveStage_covariance]
  exact (state_covariance_regular U u hu h₀ hs₀ i j).add
    (state_covarianceIncrement_regular U u hu h₀ h₁ hs₁ i j)

end State

end NavierStokes.WaveStateRegularity
