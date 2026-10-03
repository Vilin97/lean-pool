/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.EquationModulus
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak extraction in the scalar and gradient time-L² spaces

The positive-cutoff paths are continuous with values in their spatial Hilbert spaces. The scalar
energy estimate bounds the time-L² scalar sequence, and the integrated Galerkin estimate bounds
the time-L² gradient sequence. This file extracts one subsequence weakly in both spaces.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance spacetimeTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance spacetimeOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance spacetimeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance spacetimeMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance spacetimeProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Scalar `L²` paths on the open time interval. -/
abbrev ScalarTimeL2 := Lp ScalarTorusL2 2 (volume.restrict (Ioc (0 : ℝ) 1))

/-- Gradient `L²` paths on the open time interval. -/
abbrev GradientTimeL2 := Lp SpatialGradientL2 2 (volume.restrict (Ioc (0 : ℝ) 1))

local instance spacetimeTorusMeasureSeparable : IsSeparable (volume : Measure Torus) :=
    inferInstance
local instance spacetimeScalarSecondCountable : SecondCountableTopology ScalarTorusL2 :=
    inferInstance
local instance spacetimeGradientSecondCountable : SecondCountableTopology SpatialGradientL2 :=
    inferInstance
local instance spacetimeTimeMeasureSeparable : IsSeparable
    (volume.restrict (Ioc (0 : ℝ) 1)) := inferInstance
local instance spacetimeScalarTimeSecondCountable : SecondCountableTopology ScalarTimeL2 :=
    inferInstance
local instance spacetimeGradientTimeSecondCountable : SecondCountableTopology GradientTimeL2 :=
    inferInstance
local instance spacetimeScalarTimeSeparable : TopologicalSpace.SeparableSpace ScalarTimeL2 :=
    inferInstance
local instance spacetimeGradientTimeSeparable : TopologicalSpace.SeparableSpace GradientTimeL2 :=
    inferInstance

/-- Extend the finite Galerkin coefficient path constantly beyond the unit time interval. -/
def SpacetimeCompactness.extendedCoefficients (P : FrozenDriftProblem) (N : ℕ) :
    ℝ → Coefficients (RealFourierDimension N) :=
  AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)

/-- The globally extended scalar Galerkin path, used only as an a.e. representative on `(0,1)`. -/
def FrozenDriftProblem.scalarTimeFunction (P : FrozenDriftProblem) (N : ℕ) :
    ℝ → ScalarTorusL2 := fun t =>
  realFourierScalarMap N (SpacetimeCompactness.extendedCoefficients P N t)

/-- The globally extended gradient Galerkin path, used only as an a.e. representative on `(0,1)`. -/
def FrozenDriftProblem.gradientTimeFunction (P : FrozenDriftProblem) (N : ℕ) :
    ℝ → SpatialGradientL2 := fun t =>
  (P.galerkinData N).gradient (SpacetimeCompactness.extendedCoefficients P N t)

theorem scalarTimeFunction_continuous (P : FrozenDriftProblem) (N : ℕ) :
    Continuous (P.scalarTimeFunction N) := by
  exact (realFourierScalarMap N).continuous.comp
    (AVenhance.Infra.ODE.continuous_extendCurve (by norm_num) (P.coefficientPath N))

theorem gradientTimeFunction_continuous (P : FrozenDriftProblem) (N : ℕ) :
    Continuous (P.gradientTimeFunction N) := by
  exact (P.galerkinData N).gradient.continuous.comp
    (AVenhance.Infra.ODE.continuous_extendCurve (by norm_num) (P.coefficientPath N))

/-- On the physical open time interval, the globally extended product representative agrees with
the chosen continuous Galerkin path. -/
theorem scalarTimeFunction_eq_scalarPath (P : FrozenDriftProblem) (N : ℕ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    P.scalarTimeFunction N t = P.scalarPath N ⟨t, ⟨le_of_lt ht.1, ht.2⟩⟩ := by
  let t' : Icc (0 : ℝ) 1 := ⟨t, ⟨le_of_lt ht.1, ht.2⟩⟩
  have hext : SpacetimeCompactness.extendedCoefficients P N t = P.coefficientPath N t' :=
    AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) (P.coefficientPath N)
      t'.property
  change realFourierScalarMap N (SpacetimeCompactness.extendedCoefficients P N t) =
    realFourierScalarMap N (P.coefficientPath N t')
  rw [hext]

theorem scalarTimeFunction_norm_bound (P : FrozenDriftProblem) (N : ℕ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖P.scalarTimeFunction N t‖ ≤ P.scalarBound := by
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
  have hext : SpacetimeCompactness.extendedCoefficients P N t = P.coefficientPath N ⟨t, ht'⟩ :=
    AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ ht'
  rw [FrozenDriftProblem.scalarTimeFunction, hext]
  exact P.scalarPath_norm_le N ⟨t, ht'⟩

theorem SpacetimeCompactness.gradientTimeFunction_energy (P : FrozenDriftProblem) (N : ℕ) :
    ∫ t in (0 : ℝ)..1, ‖P.gradientTimeFunction N t‖ ^ 2 ≤
      P.gradientEnergyBound := by
  simpa [FrozenDriftProblem.gradientTimeFunction, FrozenDriftProblem.gradientEnergyBound,
    FrozenDriftProblem.galerkinData, positiveCutoffGalerkinData,
        SpacetimeCompactness.extendedCoefficients] using
    P.gradientEnergy_le N

theorem scalarTimeFunction_memLp (P : FrozenDriftProblem) (N : ℕ) :
    MemLp (P.scalarTimeFunction N) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound (scalarTimeFunction_continuous P N).aestronglyMeasurable
    P.scalarBound
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact scalarTimeFunction_norm_bound P N ht

theorem gradientTimeFunction_memLp (P : FrozenDriftProblem) (N : ℕ) :
    MemLp (P.gradientTimeFunction N) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound (gradientTimeFunction_continuous P N).aestronglyMeasurable
    (‖(P.galerkinData N).gradient‖ * P.scalarBound)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
  have hext : SpacetimeCompactness.extendedCoefficients P N t = P.coefficientPath N ⟨t, ht'⟩ :=
    AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ ht'
  rw [FrozenDriftProblem.gradientTimeFunction, hext]
  have hstate := P.scalarPath_norm_le N ⟨t, ht'⟩
  change ‖realFourierScalarMap N ((P.coefficientPath N) ⟨t, ht'⟩)‖ ≤
    P.scalarBound at hstate
  rw [realFourierScalarMap_norm] at hstate
  calc
    ‖(P.galerkinData N).gradient ((P.coefficientPath N) ⟨t, ht'⟩)‖ ≤
        ‖(P.galerkinData N).gradient‖ * ‖(P.coefficientPath N) ⟨t, ht'⟩‖ :=
          (P.galerkinData N).gradient.le_opNorm _
    _ ≤ ‖(P.galerkinData N).gradient‖ * P.scalarBound :=
      mul_le_mul_of_nonneg_left hstate (norm_nonneg _)

theorem SpacetimeCompactness.timeL2_norm_sq_eq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure ℝ} {f : ℝ → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ t, inner ℝ ((hf.toLp f) t) ((hf.toLp f) t) ∂μ :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ t, ‖f t‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with t ht
      rw [ht, real_inner_self_eq_norm_sq]

theorem scalarTimeLp_norm_le (P : FrozenDriftProblem) (N : ℕ) :
    ‖(scalarTimeFunction_memLp P N).toLp (P.scalarTimeFunction N)‖ ≤ P.scalarBound := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hmass : μ Set.univ = 1 := by
    simp [μ, Real.volume_Ioc]
  rw [Lp.norm_toLp]
  have htbound : ∀ᵐ t ∂μ, ‖P.scalarTimeFunction N t‖ ≤ P.scalarBound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact scalarTimeFunction_norm_bound P N ht
  have hbound := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
    ((scalarTimeFunction_continuous P N).aestronglyMeasurable) htbound
  have hmeasure : μ Set.univ ^ ((2 : ENNReal).toReal)⁻¹ = 1 := by simp [hmass]
  rw [hmeasure] at hbound
  have hnonneg : 0 ≤ P.scalarBound := P.scalarBound_nonneg
  have hreal : ENNReal.toReal (ENNReal.ofReal P.scalarBound) = P.scalarBound :=
    ENNReal.toReal_ofReal hnonneg
  have hbound' : eLpNorm (P.scalarTimeFunction N) 2 μ ≤ ENNReal.ofReal P.scalarBound := by
    simpa [hmass] using hbound
  calc
    ENNReal.toReal (eLpNorm (P.scalarTimeFunction N) 2 μ) ≤
        ENNReal.toReal (ENNReal.ofReal P.scalarBound) :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound'
    _ = P.scalarBound := hreal

theorem gradientTimeLp_norm_sq_le (P : FrozenDriftProblem) (N : ℕ) :
    ‖(gradientTimeFunction_memLp P N).toLp (P.gradientTimeFunction N)‖ ^ 2 ≤
      P.gradientEnergyBound := by
  rw [SpacetimeCompactness.timeL2_norm_sq_eq_integral (gradientTimeFunction_memLp P N)]
  have henergy := SpacetimeCompactness.gradientTimeFunction_energy P N
  have hrestrict : (∫ t, ‖P.gradientTimeFunction N t‖ ^ 2 ∂
      (volume.restrict (Ioc (0 : ℝ) 1))) =
      ∫ t in (0 : ℝ)..1, ‖P.gradientTimeFunction N t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [hrestrict]
  exact henergy

/-- Scalar Galerkin evolution as an element of the time-L² space. -/
def scalarTimeLp (P : FrozenDriftProblem) (N : ℕ) : ScalarTimeL2 :=
  (scalarTimeFunction_memLp P N).toLp (P.scalarTimeFunction N)

/-- Galerkin gradient evolution as an element of the time-L² space. -/
def gradientTimeLp (P : FrozenDriftProblem) (N : ℕ) : GradientTimeL2 :=
  (gradientTimeFunction_memLp P N).toLp (P.gradientTimeFunction N)

/-- Extract a common weakly convergent subsequence of the scalar and gradient time-L² Galerkin
sequences. The scalar limit is bounded by the energy estimate, while the gradient limit is
bounded by the integrated dissipation estimate. -/
theorem FrozenDriftProblem.exists_weakSpacetime_subsequence (P : FrozenDriftProblem) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ScalarTimeL2, ∃ g : GradientTimeL2,
      (∀ v, Tendsto (fun n => inner ℝ (scalarTimeLp P (φ n)) v) atTop (𝓝 (inner ℝ u v))) ∧
      (∀ v, Tendsto (fun n => inner ℝ (gradientTimeLp P (φ n)) v) atTop
        (𝓝 (inner ℝ g v))) ∧
      ‖u‖ ≤ P.scalarBound ∧ ‖g‖ ^ 2 ≤ P.gradientEnergyBound := by
  have hs : ∀ N, ‖scalarTimeLp P N‖ ≤ P.scalarBound := scalarTimeLp_norm_le P
  obtain ⟨φ₁, hφ₁, u, huweak, hubound⟩ :=
    exists_subseq_inner_tendsto_of_norm_bounded (xSeq := scalarTimeLp P)
      (M := P.scalarBound) hs
  have hEb : 0 ≤ P.gradientEnergyBound := by
    have hcoef : 0 ≤ positiveCutoffDriftConstant P.b P.drift_bounded ^ 2 / P.κ :=
      div_nonneg (sq_nonneg _) P.κ_pos.le
    have hfactor : 0 ≤ 1 +
        positiveCutoffDriftConstant P.b P.drift_bounded ^ 2 / P.κ *
          Real.exp (positiveCutoffDriftConstant P.b P.drift_bounded ^ 2 / P.κ) :=
      add_nonneg (by norm_num) (mul_nonneg hcoef (Real.exp_nonneg _))
    unfold FrozenDriftProblem.gradientEnergyBound
    exact div_nonneg (mul_nonneg (sq_nonneg _) hfactor) P.κ_pos.le
  have hgBound : ∀ n, ‖gradientTimeLp P (φ₁ n)‖ ≤ Real.sqrt P.gradientEnergyBound := by
    intro n
    have hsquare := gradientTimeLp_norm_sq_le P (φ₁ n)
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 (by
      rw [Real.sq_sqrt hEb]
      exact hsquare)
  obtain ⟨φ₂, hφ₂, g, hgweak, hgbound⟩ :=
    exists_subseq_inner_tendsto_of_norm_bounded
      (xSeq := fun n => gradientTimeLp P (φ₁ n))
      (M := Real.sqrt P.gradientEnergyBound) hgBound
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, u, g, ?_, ?_, hubound, ?_⟩
  · intro v
    exact (huweak v).comp hφ₂.tendsto_atTop
  · exact hgweak
  · have hnonneg : 0 ≤ ‖g‖ := norm_nonneg _
    have hsqrt : 0 ≤ Real.sqrt P.gradientEnergyBound := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt hEb, hgbound]

/-- A common cutoff subsequence has weak scalar and gradient time-L² limits and a weakly continuous
scalar path limit with the correct initial trace. The path extraction is applied to the selected
spacetime subsequence, so all limits refer to the same sequence. -/
theorem FrozenDriftProblem.exists_simultaneous_weak_limit (P : FrozenDriftProblem) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ u : Icc (0 : ℝ) 1 → ScalarTorusL2, ∃ U : ScalarTimeL2, ∃ G : GradientTimeL2,
        (∀ v, Continuous (fun t => inner ℝ (u t) v)) ∧
        (∀ t v, Tendsto (fun n => inner ℝ (P.scalarPath (φ n) t) v) atTop
          (𝓝 (inner ℝ (u t) v))) ∧
        (∀ v, Tendsto (fun n => inner ℝ (scalarTimeLp P (φ n)) v) atTop
          (𝓝 (inner ℝ U v))) ∧
        (∀ v, Tendsto (fun n => inner ℝ (gradientTimeLp P (φ n)) v) atTop
          (𝓝 (inner ℝ G v))) ∧
        (∀ t, ‖u t‖ ≤ P.scalarBound) ∧
        u ⟨0, by norm_num, by norm_num⟩ = P.initialTorusL2 ∧
        ‖U‖ ≤ P.scalarBound ∧ ‖G‖ ^ 2 ≤ P.gradientEnergyBound := by
  obtain ⟨φ, hφ, U, G, hUweak, hGweak, hUbound, hGbound⟩ :=
    P.exists_weakSpacetime_subsequence
  have hinit (v : ScalarTorusL2) : Tendsto
      (fun n => inner ℝ (P.scalarPath (φ n) ⟨0, by norm_num, by norm_num⟩) v) atTop
      (𝓝 (inner ℝ P.initialTorusL2 v)) :=
    (P.initialTrace_weak_tendsto v).comp hφ.tendsto_atTop
  have hmod (w : ScalarTorusL2) (hw : w ∈ realFourierSpan) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n t s,
        |inner ℝ (P.scalarPath (φ n) t) w - inner ℝ (P.scalarPath (φ n) s) w| ≤
          C * Real.sqrt (dist t s) := by
    obtain ⟨C, hC, hCmod⟩ := P.fourierPairing_modulus hw
    exact ⟨C, hC, fun n t s => hCmod (φ n) t s⟩
  have happrox : ∀ v : ScalarTorusL2, ∀ ε : ℝ, 0 < ε →
      ∃ w ∈ realFourierSpan, dist v w < ε := by
    intro v ε hε
    obtain ⟨w, hw⟩ := (Metric.dense_iff.mp realFourierSpan_dense) v ε hε
    exact ⟨w, hw.2, by simpa [Metric.mem_ball, dist_comm] using hw.1⟩
  obtain ⟨ψ, hψ, u, hucont, huweak, hubound, hutrace⟩ :=
    exists_subseq_weakContinuousPath_of_dense_pairing_moduli
      (uSeq := fun n => P.scalarPath (φ n)) (M := P.scalarBound)
      (u₀ := P.initialTorusL2) (S := realFourierSpan)
      (fun n t => P.scalarPath_norm_le (φ n) t) hinit P.scalarBound_nonneg happrox hmod
  refine ⟨φ ∘ ψ, hφ.comp hψ, u, U, G, hucont, ?_, ?_, ?_, hubound, hutrace,
    hUbound, hGbound⟩
  · intro t v
    exact huweak t v
  · intro v
    exact (hUweak v).comp hψ.tendsto_atTop
  · intro v
    exact (hGweak v).comp hψ.tendsto_atTop

end AVenhance.Infra.Parabolic.FourierGalerkin

end
