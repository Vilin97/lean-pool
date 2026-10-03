/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.SpacetimeCompactness
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Product-space weak compactness for the explicit Galerkin sums

This file realizes the finite real Fourier paths as functions on time times the torus. Their
product-space `L²` bounds are the same scalar and dissipation bounds used for the Bochner paths.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance productCompactnessMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance productCompactnessMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance productCompactnessProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance productCompactnessTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance productCompactnessOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
local instance productCompactnessTopHolderTwo : (⊤ : ENNReal).HolderTriple 2 2 := by
  exact ENNReal.HolderTriple.symm

/-- The physical time measure used in the product-space realization. -/
abbrev GalerkinTimeMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

/-- Scalar product-space `L²` on `(0,1) × 𝕋²`. -/
abbrev ScalarProductTimeL2 := Lp ℝ 2 (GalerkinTimeMeasure.prod (volume : Measure Torus))

/-- Vector-gradient product-space `L²` on `(0,1) × 𝕋²`. -/
abbrev GradientProductTimeL2 :=
  Lp SpatialVector 2 (GalerkinTimeMeasure.prod (volume : Measure Torus))

local instance productCompactnessTimeSeparable : IsSeparable GalerkinTimeMeasure := inferInstance
local instance productCompactnessTorusSeparable :
    IsSeparable (volume : Measure Torus) := inferInstance
local instance productCompactnessProductMeasureSeparable :
    IsSeparable (GalerkinTimeMeasure.prod (volume : Measure Torus)) := inferInstance
local instance productCompactnessScalarSecondCountable :
    SecondCountableTopology ScalarProductTimeL2 := inferInstance
local instance productCompactnessGradientSecondCountable :
    SecondCountableTopology GradientProductTimeL2 := inferInstance
local instance productCompactnessScalarSeparable :
    TopologicalSpace.SeparableSpace ScalarProductTimeL2 := inferInstance
local instance productCompactnessGradientSeparable :
    TopologicalSpace.SeparableSpace GradientProductTimeL2 := inferInstance

/-- Coordinate of the extended finite Galerkin coefficient path. -/
def coefficientComponent (P : FrozenDriftProblem) (N : ℕ)
    (i : Fin (RealFourierDimension N)) : ℝ → ℝ :=
  fun t => (AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t) i

/-- The coefficient path extended to all real times for product-space representatives. -/
def productExtendedCoefficients (P : FrozenDriftProblem) (N : ℕ) :
    ℝ → Coefficients (RealFourierDimension N) :=
  AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)

/-- The explicit scalar Fourier sum on the product of time with the torus. -/
def FrozenDriftProblem.scalarProductFunction (P : FrozenDriftProblem) (N : ℕ) :
    ℝ × Torus → ℝ := fun p =>
  ∑ i : Fin (RealFourierDimension N),
    coefficientComponent P N i p.1 * realFourierModeFin N i p.2

/-- The explicit gradient Fourier sum on the product of time with the torus. -/
def FrozenDriftProblem.gradientProductFunction (P : FrozenDriftProblem) (N : ℕ) :
  ℝ × Torus → SpatialVector := fun p =>
  ∑ i : Fin (RealFourierDimension N),
    (coefficientComponent P N i p.1) •
      (WithLp.toLp 2 (realFourierModeGradFin N i p.2) : SpatialVector)

theorem ProductCompactness.coefficientComponent_continuous (P : FrozenDriftProblem) (N : ℕ)
    (i : Fin (RealFourierDimension N)) : Continuous (coefficientComponent P N i) := by
  exact ((PiLp.proj (𝕜 := ℝ) 2
    (fun _ : Fin (RealFourierDimension N) => ℝ) i).continuous.comp
      (AVenhance.Infra.ODE.continuous_extendCurve (by norm_num) (P.coefficientPath N)))

theorem ProductCompactness.coefficientComponent_bound (P : FrozenDriftProblem) (N : ℕ)
    (i : Fin (RealFourierDimension N)) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    |coefficientComponent P N i t| ≤ P.scalarBound := by
  let t' : Icc (0 : ℝ) 1 := ⟨t, ⟨le_of_lt ht.1, ht.2⟩⟩
  have hext : productExtendedCoefficients P N t = P.coefficientPath N t' :=
    AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ t'.2
  change |(productExtendedCoefficients P N t) i| ≤ P.scalarBound
  rw [hext]
  have hpath := P.scalarPath_norm_le N t'
  change ‖realFourierScalarMap N ((P.coefficientPath N) t')‖ ≤ P.scalarBound at hpath
  rw [realFourierScalarMap_norm] at hpath
  have hcoord : |((P.coefficientPath N) t') i| ≤ ‖(P.coefficientPath N) t'‖ := by
    let hc := P.coefficientPath N t'
    have hs : ‖hc‖ = Real.sqrt (∑ j, ‖hc.ofLp j‖ ^ 2) := PiLp.norm_eq_of_L2 hc
    have hsum : ‖hc.ofLp i‖ ^ 2 ≤ ∑ j, ‖hc.ofLp j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖hc.ofLp j‖) (Finset.mem_univ i)
    calc
      |((P.coefficientPath N) t') i| = ‖hc.ofLp i‖ := by
        simp [hc, Real.norm_eq_abs]
      _ ≤ Real.sqrt (∑ j, ‖hc.ofLp j‖ ^ 2) := by
        have hnonneg : 0 ≤ ‖hc.ofLp i‖ := norm_nonneg _
        apply (sq_le_sq₀ hnonneg (Real.sqrt_nonneg _)).1
        rw [Real.sq_sqrt (show 0 ≤ ∑ j, ‖hc.ofLp j‖ ^ 2 by positivity)]
        exact hsum
      _ = ‖(P.coefficientPath N) t'‖ := by simpa [hc] using hs.symm
  calc
    |((P.coefficientPath N) t') i| ≤ ‖(P.coefficientPath N) t'‖ := hcoord
    _ ≤ P.scalarBound := hpath

theorem ProductCompactness.coefficientComponent_memLp_top (P : FrozenDriftProblem) (N : ℕ)
    (i : Fin (RealFourierDimension N)) :
    MemLp (coefficientComponent P N i) ⊤ GalerkinTimeMeasure := by
  apply MemLp.of_bound (ProductCompactness.coefficientComponent_continuous P N
      i).aestronglyMeasurable
    P.scalarBound
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact ProductCompactness.coefficientComponent_bound P N i ht

theorem scalarProductFunction_memLp (P : FrozenDriftProblem) (N : ℕ) :
    MemLp (P.scalarProductFunction N) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  apply memLp_finsetSum Finset.univ
  intro i hi
  have ht := (ProductCompactness.coefficientComponent_memLp_top P N i).comp_fst
    (volume : Measure Torus)
  have hx := (realFourierModeFin_memLp N i).comp_snd GalerkinTimeMeasure
  exact ht.mul hx

theorem gradientProductFunction_memLp (P : FrozenDriftProblem) (N : ℕ) :
    MemLp (P.gradientProductFunction N) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
  apply memLp_finsetSum Finset.univ
  intro i hi
  have ht := (ProductCompactness.coefficientComponent_memLp_top P N i).comp_fst
    (volume : Measure Torus)
  have hx := (realFourierModeGradFin_memLp N i).comp_snd GalerkinTimeMeasure
  exact ht.smul hx

/-- The scalar product-space equivalence class of a finite Galerkin sum. -/
noncomputable def FrozenDriftProblem.scalarProductLp (P : FrozenDriftProblem) (N : ℕ) :
    ScalarProductTimeL2 :=
  (scalarProductFunction_memLp P N).toLp (P.scalarProductFunction N)

/-- The gradient product-space equivalence class of a finite Galerkin sum. -/
noncomputable def FrozenDriftProblem.gradientProductLp (P : FrozenDriftProblem) (N : ℕ) :
    GradientProductTimeL2 :=
  (gradientProductFunction_memLp P N).toLp (P.gradientProductFunction N)

theorem ProductCompactness.productTimeL2_norm_sq_eq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure (ℝ × Torus)} {f : ℝ × Torus → E}
    (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ p, ‖f p‖ ^ 2 ∂μ := by
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ p, inner ℝ ((hf.toLp f) p) ((hf.toLp f) p) ∂μ :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ p, ‖f p‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with p hp
      rw [hp, real_inner_self_eq_norm_sq]

theorem ProductCompactness.timeL2_norm_sq_eq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : ℝ → E} (hf : MemLp f 2 GalerkinTimeMeasure) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂GalerkinTimeMeasure := by
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ t, inner ℝ ((hf.toLp f) t) ((hf.toLp f) t) ∂GalerkinTimeMeasure :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ t, ‖f t‖ ^ 2 ∂GalerkinTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with t ht
      rw [ht, real_inner_self_eq_norm_sq]

theorem scalarProductFunction_slice_ae (P : FrozenDriftProblem) (N : ℕ)
    (t : ℝ) :
    (fun x : Torus => P.scalarProductFunction N (t, x)) =ᵐ[volume]
      fun x => P.scalarTimeFunction N t x := by
  let c := AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t
  have hexp : (fun x : Torus => P.scalarProductFunction N (t, x)) =
      modeExpansion (RealFourierDimension N) (realFourierModeFin N) c := by
    funext x
    simp [FrozenDriftProblem.scalarProductFunction, coefficientComponent, c,
      modeExpansion]
  have hcoef := realFourierScalarMap_coeFn N c
  have htime : P.scalarTimeFunction N t = realFourierScalarMap N c := by
    rfl
  rw [hexp, htime]
  exact hcoef.symm

theorem gradientProductFunction_slice_ae (P : FrozenDriftProblem) (N : ℕ)
    (t : ℝ) :
    (fun x : Torus => P.gradientProductFunction N (t, x)) =ᵐ[volume]
      fun x => P.gradientTimeFunction N t x := by
  let c := AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t
  have hsum : (fun x : Torus => P.gradientProductFunction N (t, x)) =
      fun x => WithLp.toLp 2
        (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x) := by
    funext x
    simp [FrozenDriftProblem.gradientProductFunction, coefficientComponent, c,
      ← WithLp.toLp_smul, ← WithLp.toLp_sum]
  have hcoef := realFourierGradientMap_coeFn N c
  have htime : P.gradientTimeFunction N t = realFourierGradientMap N c := by
    change positiveCutoffGradientMap N
        (AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t) =
      realFourierGradientMap N c
    unfold positiveCutoffGradientMap
    rfl
  rw [hsum, htime]
  exact hcoef.symm

/-- The product-space scalar norm is the Bochner time-L² norm of the Galerkin path. -/
theorem FrozenDriftProblem.scalarProductLp_norm_sq (P : FrozenDriftProblem) (N : ℕ) :
    ‖P.scalarProductLp N‖ ^ 2 = ‖scalarTimeLp P N‖ ^ 2 := by
  have hprod : ‖P.scalarProductLp N‖ ^ 2 =
      ∫ p, ‖P.scalarProductFunction N p‖ ^ 2
        ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    exact ProductCompactness.productTimeL2_norm_sq_eq_integral (scalarProductFunction_memLp P N)
  have hInt : Integrable (fun p : ℝ × Torus => ‖P.scalarProductFunction N p‖ ^ 2)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    simpa using (scalarProductFunction_memLp P N).integrable_norm_rpow
      (by norm_num) (by norm_num)
  rw [hprod, integral_prod _ hInt]
  have hslice (t : ℝ) :
      (∫ x : Torus, ‖P.scalarProductFunction N (t, x)‖ ^ 2) =
        ‖P.scalarTimeFunction N t‖ ^ 2 := by
    calc
      (∫ x : Torus, ‖P.scalarProductFunction N (t, x)‖ ^ 2) =
          ∫ x : Torus, ‖P.scalarTimeFunction N t x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [scalarProductFunction_slice_ae P N t] with x hx
        rw [hx]
      _ = ‖P.scalarTimeFunction N t‖ ^ 2 :=
        (l2_norm_sq_eq_integral_sq (P.scalarTimeFunction N t)).symm
  have hiter :
      (∫ t, ∫ x : Torus, ‖P.scalarProductFunction N (t, x)‖ ^ 2
        ∂(volume : Measure Torus) ∂GalerkinTimeMeasure) =
      ∫ t, ‖P.scalarTimeFunction N t‖ ^ 2 ∂GalerkinTimeMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hslice
  rw [hiter]
  exact (ProductCompactness.timeL2_norm_sq_eq_integral (scalarTimeFunction_memLp P N)).symm

/-- The product-space gradient norm is the Bochner time-L² gradient norm. -/
theorem FrozenDriftProblem.gradientProductLp_norm_sq (P : FrozenDriftProblem) (N : ℕ) :
    ‖P.gradientProductLp N‖ ^ 2 = ‖gradientTimeLp P N‖ ^ 2 := by
  have hprod : ‖P.gradientProductLp N‖ ^ 2 =
      ∫ p, ‖P.gradientProductFunction N p‖ ^ 2
        ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    exact ProductCompactness.productTimeL2_norm_sq_eq_integral (gradientProductFunction_memLp P N)
  have hInt : Integrable (fun p : ℝ × Torus => ‖P.gradientProductFunction N p‖ ^ 2)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    simpa using (gradientProductFunction_memLp P N).integrable_norm_rpow
      (by norm_num) (by norm_num)
  rw [hprod, integral_prod _ hInt]
  have hslice (t : ℝ) :
      (∫ x : Torus, ‖P.gradientProductFunction N (t, x)‖ ^ 2) =
        ‖P.gradientTimeFunction N t‖ ^ 2 := by
    calc
      (∫ x : Torus, ‖P.gradientProductFunction N (t, x)‖ ^ 2) =
          ∫ x : Torus, ‖P.gradientTimeFunction N t x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [gradientProductFunction_slice_ae P N t] with x hx
        rw [hx]
      _ = ‖P.gradientTimeFunction N t‖ ^ 2 :=
        (l2_norm_sq_eq_integral_sq (P.gradientTimeFunction N t)).symm
  have hiter :
      (∫ t, ∫ x : Torus, ‖P.gradientProductFunction N (t, x)‖ ^ 2
        ∂(volume : Measure Torus) ∂GalerkinTimeMeasure) =
      ∫ t, ‖P.gradientTimeFunction N t‖ ^ 2 ∂GalerkinTimeMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hslice
  rw [hiter]
  exact (ProductCompactness.timeL2_norm_sq_eq_integral (gradientTimeFunction_memLp P N)).symm

/-- Product-space boundedness follows from the uniform scalar and dissipation estimates. -/
theorem FrozenDriftProblem.productLp_norm_bounds (P : FrozenDriftProblem) (N : ℕ) :
    ‖P.scalarProductLp N‖ ≤ P.scalarBound ∧
      ‖P.gradientProductLp N‖ ^ 2 ≤ P.gradientEnergyBound := by
  constructor
  · have h := P.scalarProductLp_norm_sq N
    have hnorm : ‖P.scalarProductLp N‖ = ‖scalarTimeLp P N‖ := by
      nlinarith [h, norm_nonneg (P.scalarProductLp N), norm_nonneg (scalarTimeLp P N)]
    rw [hnorm]
    exact scalarTimeLp_norm_le P N
  · rw [P.gradientProductLp_norm_sq N]
    exact gradientTimeLp_norm_sq_le P N

/-- Product-space extraction along any preselected strictly increasing sequence of cutoffs. This
allows the product limits to be synchronized with the weakly continuous path extraction. -/
theorem FrozenDriftProblem.exists_product_weak_subsequence_of_sequence
    (P : FrozenDriftProblem) (σ : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : ScalarProductTimeL2, ∃ G : GradientProductTimeL2,
      (∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ (φ n))) v) atTop
        (𝓝 (inner ℝ U v))) ∧
      (∀ v, Tendsto (fun n => inner ℝ (P.gradientProductLp (σ (φ n))) v) atTop
        (𝓝 (inner ℝ G v))) ∧
      ‖U‖ ≤ P.scalarBound ∧ ‖G‖ ^ 2 ≤ P.gradientEnergyBound := by
  have hE : 0 ≤ P.gradientEnergyBound := by
    have h := (P.productLp_norm_bounds 0).2
    exact (sq_nonneg ‖P.gradientProductLp 0‖).trans h
  have hM : 0 ≤ Real.sqrt (P.scalarBound ^ 2 + P.gradientEnergyBound) :=
    Real.sqrt_nonneg _
  have hbound (n : ℕ) :
      ‖WithLp.toLp 2 (P.scalarProductLp (σ n), P.gradientProductLp (σ n))‖ ≤
        Real.sqrt (P.scalarBound ^ 2 + P.gradientEnergyBound) := by
    have hparts := P.productLp_norm_bounds (σ n)
    have hs : ‖P.scalarProductLp (σ n)‖ ^ 2 ≤ P.scalarBound ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) P.scalarBound_nonneg).2 hparts.1
    have hp : ‖P.gradientProductLp (σ n)‖ ^ 2 ≤ P.gradientEnergyBound := hparts.2
    have hpair := WithLp.prod_norm_sq_eq_of_L2
      (WithLp.toLp 2 (P.scalarProductLp (σ n), P.gradientProductLp (σ n)))
    have hpair' : ‖WithLp.toLp 2 (P.scalarProductLp (σ n), P.gradientProductLp (σ n))‖ ^ 2 =
        ‖P.scalarProductLp (σ n)‖ ^ 2 + ‖P.gradientProductLp (σ n)‖ ^ 2 := by
      simpa only [WithLp.toLp_fst, WithLp.toLp_snd] using hpair
    apply (sq_le_sq₀ (norm_nonneg _) hM).1
    rw [hpair', Real.sq_sqrt (add_nonneg (sq_nonneg _) hE)]
    nlinarith
  obtain ⟨φ, hφ, U, G, hUweak, hGweak, _hpairBound⟩ :=
    exists_subseq_inner_tendsto_pair_of_norm_bounded
      (uSeq := fun n => P.scalarProductLp (σ n))
      (vSeq := fun n => P.gradientProductLp (σ n))
      (M := Real.sqrt (P.scalarBound ^ 2 + P.gradientEnergyBound)) hbound
  have hUbound : ‖U‖ ≤ P.scalarBound := by
    apply norm_le_of_inner_tendsto hUweak
    intro n
    exact (P.productLp_norm_bounds (σ (φ n))).1
  have hGnorm : ‖G‖ ≤ Real.sqrt P.gradientEnergyBound := by
    apply norm_le_of_inner_tendsto hGweak
    intro n
    have h := (P.productLp_norm_bounds (σ (φ n))).2
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 (by
      rw [Real.sq_sqrt hE]
      exact h)
  have hGbound : ‖G‖ ^ 2 ≤ P.gradientEnergyBound := by
    calc
      ‖G‖ ^ 2 ≤ (Real.sqrt P.gradientEnergyBound) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hGnorm
      _ = P.gradientEnergyBound := Real.sq_sqrt hE
  exact ⟨φ, hφ, U, G, hUweak, hGweak, hUbound, hGbound⟩

end AVenhance.Infra.Parabolic.FourierGalerkin

end
