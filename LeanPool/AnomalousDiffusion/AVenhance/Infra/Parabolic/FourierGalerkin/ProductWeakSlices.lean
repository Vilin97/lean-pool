/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakGradient
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Almost-every-time weak derivative slices

Separated tests identify the spatial derivative of the synchronized product limit on almost every
time slice. The first step below rewrites product-space pairings as iterated spatial pairings.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance weakSlicesMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakSlicesMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakSlicesProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakSlicesSFiniteTorus : SFinite (volume : Measure Torus) := inferInstance
local instance weakSlicesProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance weakSlicesOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
local instance weakSlicesTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance weakSlicesScalarSeparableMeasure : IsSeparable (volume : Measure Torus) :=
  inferInstance
local instance weakSlicesScalarSecondCountable : SecondCountableTopology ScalarTorusL2 :=
  inferInstance

/-- Pairing a product-space gradient against a separated test is the time integral of its spatial
slice pairing. -/
theorem gradientProductTimeL2_pairing_iterated
    (G : GradientProductTimeL2) (η : ℝ → ℝ)
    (hη : MemLp η ⊤ GalerkinTimeMeasure) (g : SpatialGradientL2) :
    Integrable (fun t => η t * (∫ x : Torus,
        inner ℝ (G (t, x)) (g x) ∂volume)) GalerkinTimeMeasure ∧
      inner ℝ G (gradientProductTestLp η g hη) =
        ∫ t, η t * (∫ x : Torus, inner ℝ (G (t, x)) (g x) ∂volume)
          ∂GalerkinTimeMeasure := by
  let q : ℝ × Torus → SpatialVector := fun p => η p.1 • g p.2
  let qMem := gradientProductTest_memLp hη g
  let qLp : GradientProductTimeL2 := qMem.toLp q
  have hAE : (fun p : ℝ × Torus => inner ℝ (G p) (qLp p)) =ᵐ[
      GalerkinTimeMeasure.prod (volume : Measure Torus)]
      fun p => inner ℝ (G p) (q p) := by
    filter_upwards [qMem.coeFn_toLp] with p hp
    rw [hp]
  have hIntLp : Integrable (fun p : ℝ × Torus => inner ℝ (G p) (qLp p))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
    MeasureTheory.L2.integrable_inner G qLp
  have hInt : Integrable (fun p : ℝ × Torus => inner ℝ (G p) (q p))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := hIntLp.congr hAE
  have hslice (t : ℝ) :
      (∫ x : Torus, inner ℝ (G (t, x)) (q (t, x)) ∂volume) =
        η t * (∫ x : Torus, inner ℝ (G (t, x)) (g x) ∂volume) := by
    calc
      _ = ∫ x : Torus, η t * inner ℝ (G (t, x)) (g x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        simp [q, inner_smul_right]
      _ = _ := integral_const_mul _ _
  have hIterInt : Integrable
      (fun t => ∫ x : Torus, inner ℝ (G (t, x)) (q (t, x)) ∂volume)
      GalerkinTimeMeasure := hInt.integral_prod_left
  have hWeightedInt : Integrable (fun t => η t *
      (∫ x : Torus, inner ℝ (G (t, x)) (g x) ∂volume)) GalerkinTimeMeasure := by
    apply hIterInt.congr
    filter_upwards with t
    exact hslice t
  refine ⟨hWeightedInt, ?_⟩
  calc
    inner ℝ G (gradientProductTestLp η g hη) =
        ∫ p, inner ℝ (G p) (qLp p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
            MeasureTheory.L2.inner_def G qLp
    _ = ∫ p, inner ℝ (G p) (q p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
            integral_congr_ae hAE
    _ = ∫ t, ∫ x : Torus, inner ℝ (G (t, x)) (q (t, x)) ∂volume
          ∂GalerkinTimeMeasure := integral_prod _ hInt
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hslice

theorem ae_eq_zero_of_all_top_pairings {f : ℝ → ℝ}
    (hfMeas : AEStronglyMeasurable f GalerkinTimeMeasure)
    (hfInt : Integrable f GalerkinTimeMeasure)
    (hzero : ∀ η : ℝ → ℝ, MemLp η ⊤ GalerkinTimeMeasure →
      ∫ t, η t * f t ∂GalerkinTimeMeasure = 0) :
    f =ᵐ[GalerkinTimeMeasure] 0 := by
  let weight : ℝ → ℝ := fun x => x / (1 + |x|)
  have hweightCont : Continuous weight := by
    dsimp [weight]
    exact continuous_id.div (continuous_const.add continuous_abs) (by
      intro x
      positivity)
  have hweightMeas : AEStronglyMeasurable (fun t => weight (f t)) GalerkinTimeMeasure :=
    hweightCont.comp_aestronglyMeasurable hfMeas
  have hweightBound : ∀ᵐ t ∂GalerkinTimeMeasure, ‖weight (f t)‖ ≤ 1 := by
    filter_upwards with t
    rw [Real.norm_eq_abs, show weight (f t) = f t / (1 + |f t|) by rfl,
      abs_div]
    have hden : 0 < 1 + |f t| := by positivity
    rw [abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    linarith [abs_nonneg (f t)]
  have hweightMem : MemLp (fun t => weight (f t)) ⊤ GalerkinTimeMeasure :=
    MemLp.of_bound hweightMeas 1 hweightBound
  have hprodMeas : AEStronglyMeasurable
      (fun t => weight (f t) * f t) GalerkinTimeMeasure := hweightMeas.mul hfMeas
  have hprodBound : ∀ᵐ t ∂GalerkinTimeMeasure,
      ‖weight (f t) * f t‖ ≤ ‖f t‖ := by
    filter_upwards [hweightBound] with t ht
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hprodInt : Integrable (fun t => weight (f t) * f t) GalerkinTimeMeasure :=
    hfInt.norm.mono' hprodMeas hprodBound
  have hprodZero : ∫ t, weight (f t) * f t ∂GalerkinTimeMeasure = 0 :=
    hzero (fun t => weight (f t)) hweightMem
  have hprodNonneg : 0 ≤ᵐ[GalerkinTimeMeasure]
      fun t => weight (f t) * f t := by
    filter_upwards with t
    rw [show weight (f t) * f t = (f t) ^ 2 / (1 + |f t|) by
      dsimp [weight]
      ring]
    positivity
  have hprodAeZero := (integral_eq_zero_iff_of_nonneg_ae hprodNonneg hprodInt).mp hprodZero
  filter_upwards [hprodAeZero] with t hzeroT
  by_contra hft
  have hden : 1 + |f t| ≠ 0 := by positivity
  have hfactor : weight (f t) ≠ 0 := by
    dsimp [weight]
    exact div_ne_zero hft hden
  exact (mul_ne_zero hfactor hft) hzeroT

/-- Pairing a product-space scalar against a separated test is the time integral of its spatial
slice pairing. -/
theorem scalarProductTimeL2_pairing_iterated
    (U : ScalarProductTimeL2) (η : ℝ → ℝ)
    (hη : MemLp η ⊤ GalerkinTimeMeasure) (v : ScalarTorusL2) :
    Integrable (fun t => η t *
        (∫ x : Torus, inner ℝ (U (t, x)) (v x) ∂volume)) GalerkinTimeMeasure ∧
      inner ℝ U (scalarProductTestLp η v hη) =
        ∫ t, η t * (∫ x : Torus, inner ℝ (U (t, x)) (v x) ∂volume)
          ∂GalerkinTimeMeasure := by
  let q : ℝ × Torus → ℝ := fun p => η p.1 * v p.2
  let qMem := scalarProductTest_memLp hη v
  let qLp : ScalarProductTimeL2 := qMem.toLp q
  have hAE : (fun p : ℝ × Torus => inner ℝ (U p) (qLp p)) =ᵐ[
      GalerkinTimeMeasure.prod (volume : Measure Torus)]
      fun p => inner ℝ (U p) (q p) := by
    filter_upwards [qMem.coeFn_toLp] with p hp
    rw [hp]
  have hIntLp : Integrable (fun p : ℝ × Torus => inner ℝ (U p) (qLp p))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
    MeasureTheory.L2.integrable_inner U qLp
  have hInt : Integrable (fun p : ℝ × Torus => inner ℝ (U p) (q p))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := hIntLp.congr hAE
  have hslice (t : ℝ) :
      (∫ x : Torus, inner ℝ (U (t, x)) (q (t, x)) ∂volume) =
        η t * (∫ x : Torus, inner ℝ (U (t, x)) (v x) ∂volume) := by
    calc
      _ = ∫ x : Torus, η t * inner ℝ (U (t, x)) (v x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        simp [q, mul_assoc]
      _ = _ := integral_const_mul _ _
  have hIterInt : Integrable
      (fun t => ∫ x : Torus, inner ℝ (U (t, x)) (q (t, x)) ∂volume)
      GalerkinTimeMeasure := hInt.integral_prod_left
  have hWeightedInt : Integrable (fun t => η t *
      (∫ x : Torus, inner ℝ (U (t, x)) (v x) ∂volume)) GalerkinTimeMeasure := by
    apply hIterInt.congr
    filter_upwards with t
    exact hslice t
  refine ⟨hWeightedInt, ?_⟩
  calc
    inner ℝ U (scalarProductTestLp η v hη) =
        ∫ p, inner ℝ (U p) (qLp p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
            MeasureTheory.L2.inner_def U qLp
    _ = ∫ p, inner ℝ (U p) (q p)
          ∂(GalerkinTimeMeasure.prod (volume : Measure Torus)) :=
          integral_congr_ae hAE
    _ = ∫ t, ∫ x : Torus, inner ℝ (U (t, x)) (q (t, x)) ∂volume
          ∂GalerkinTimeMeasure := integral_prod _ hInt
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hslice

/-- The scalar product limit agrees on almost every time slice with the weakly continuous path,
when paired against any fixed spatial `L²` test. -/
def clampTimeToUnit : ℝ → Icc (0 : ℝ) 1 := fun t =>
  ⟨min (max t 0) 1,
    ⟨le_min (le_max_right t 0) (by norm_num), min_le_right _ _⟩⟩

theorem ProductWeakSlices.clampTimeToUnit_continuous : Continuous clampTimeToUnit := by
  exact ((continuous_id.max continuous_const).min continuous_const).subtype_mk _

theorem ProductWeakSlices.clampTimeToUnit_eq {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    clampTimeToUnit t = ⟨t, ⟨le_of_lt ht.1, ht.2⟩⟩ := by
  apply Subtype.ext
  simp [clampTimeToUnit, max_eq_left (le_of_lt ht.1), min_eq_left ht.2]

theorem FrozenDriftProblem.synchronized_scalar_slice_pairing_ae
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (Uprod : ScalarProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hUcont : ∀ v, Continuous (fun t => inner ℝ (u t) v))
    (v : ScalarTorusL2) :
    ∀ᵐ t ∂GalerkinTimeMeasure,
      ∫ x : Torus, inner ℝ (Uprod (t, x)) (v x) ∂volume =
        inner ℝ (u (clampTimeToUnit t)) v := by
  let slice : ℝ → ℝ := fun t =>
    ∫ x : Torus, inner ℝ (Uprod (t, x)) (v x) ∂volume
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) ⊤ GalerkinTimeMeasure :=
    continuous_time_memLp_top continuous_const
  have hsliceIter := scalarProductTimeL2_pairing_iterated Uprod
    (fun _ => 1) hone v
  have hsliceInt : Integrable slice GalerkinTimeMeasure := by
    simpa [slice] using hsliceIter.1
  let path : ℝ → ℝ := fun t => inner ℝ (u (clampTimeToUnit t)) v
  have hpathCont : Continuous path := (hUcont v).comp ProductWeakSlices.clampTimeToUnit_continuous
  have hpathInt : Integrable path GalerkinTimeMeasure :=
    ((continuous_time_memLp_top hpathCont).mono_exponent
      (by norm_num : (1 : ENNReal) ≤ ⊤)).integrable (by norm_num)
  let f : ℝ → ℝ := fun t => slice t - path t
  have hfMeas : AEStronglyMeasurable f GalerkinTimeMeasure :=
    hsliceInt.aestronglyMeasurable.sub hpathCont.aestronglyMeasurable
  have hfInt : Integrable f GalerkinTimeMeasure := hsliceInt.sub hpathInt
  have hzero : ∀ η : ℝ → ℝ, MemLp η ⊤ GalerkinTimeMeasure →
      ∫ t, η t * f t ∂GalerkinTimeMeasure = 0 := by
    intro η hη
    have hslicePair := scalarProductTimeL2_pairing_iterated Uprod η hη v
    have hpathPair := P.productScalar_pairing_eq_path_integral σ u Uprod
      hPathWeak hUweak hη v
    have hpathIntegral :
        (∫ t, if ht : t ∈ Icc (0 : ℝ) 1 then η t * inner ℝ (u ⟨t, ht⟩) v else 0
          ∂GalerkinTimeMeasure) = ∫ t, η t * path t ∂GalerkinTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
      have hpath : path t = inner ℝ (u ⟨t, htcc⟩) v := by
        dsimp [path]
        rw [ProductWeakSlices.clampTimeToUnit_eq ht]
      rw [hpath]
      simp [htcc]
    have hηbound : ∀ᵐ t ∂GalerkinTimeMeasure,
        ‖η t‖ ≤ lpNorm η ⊤ GalerkinTimeMeasure :=
      MeasureTheory.ae_le_lpNorm_exponent_top hη
    have hpathMemTop : MemLp path ⊤ GalerkinTimeMeasure :=
      continuous_time_memLp_top hpathCont
    have hpathbound : ∀ᵐ t ∂GalerkinTimeMeasure,
        ‖path t‖ ≤ lpNorm path ⊤ GalerkinTimeMeasure :=
      MeasureTheory.ae_le_lpNorm_exponent_top hpathMemTop
    have hweightedMeas : AEStronglyMeasurable (fun t => η t * path t)
        GalerkinTimeMeasure := hη.aestronglyMeasurable.mul hpathCont.aestronglyMeasurable
    have hweightedBound : ∀ᵐ t ∂GalerkinTimeMeasure,
        ‖η t * path t‖ ≤ lpNorm η ⊤ GalerkinTimeMeasure *
          lpNorm path ⊤ GalerkinTimeMeasure := by
      filter_upwards [hηbound, hpathbound] with t hηt hpt
      rw [norm_mul]
      exact mul_le_mul hηt hpt (norm_nonneg _) MeasureTheory.lpNorm_nonneg
    have hweightedInt : Integrable (fun t => η t * path t) GalerkinTimeMeasure :=
      (MemLp.of_bound hweightedMeas
        (lpNorm η ⊤ GalerkinTimeMeasure * lpNorm path ⊤ GalerkinTimeMeasure)
        hweightedBound).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2) |>.integrable
          (by norm_num)
    have hsumZero :
        (∫ t, η t * slice t ∂GalerkinTimeMeasure) -
          (∫ t, η t * path t ∂GalerkinTimeMeasure) = 0 := by
      have hpathPair' := hpathPair
      rw [hslicePair.2, hpathIntegral] at hpathPair'
      linarith
    calc
      ∫ t, η t * f t ∂GalerkinTimeMeasure =
          ∫ t, (η t * slice t - η t * path t) ∂GalerkinTimeMeasure := by
            apply integral_congr_ae
            filter_upwards with t
            simp [f, mul_sub]
      _ = _ := by
        rw [integral_sub hslicePair.1 hweightedInt]
        exact hsumZero
  have hfZero := ae_eq_zero_of_all_top_pairings hfMeas hfInt hzero
  filter_upwards [hfZero] with t hft
  dsimp [f] at hft
  linarith

/-- For almost every time, a product-space scalar `L²` class has an `L²` spatial slice. -/
theorem scalarProductTimeL2_memLp_sections (U : ScalarProductTimeL2) :
    ∀ᵐ t ∂GalerkinTimeMeasure,
      MemLp (fun x : Torus => U (t, x)) 2 (volume : Measure Torus) := by
  let hU : MemLp (fun p : ℝ × Torus => U p) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := Lp.memLp U
  have hUmeas : AEStronglyMeasurable (fun p : ℝ × Torus => U p)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := hU.aestronglyMeasurable
  have hsectionMeas := hUmeas.prodMk_left
  have hnormInt : Integrable (fun p : ℝ × Torus => ‖U p‖ ^ (2 : ℕ))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    simpa using hU.integrable_norm_rpow (by norm_num) (by norm_num)
  have hsqSection := (integrable_prod_iff hnormInt.aestronglyMeasurable).mp hnormInt |>.1
  filter_upwards [hsectionMeas, hsqSection] with t hmeas hsq
  exact (memLp_two_iff_integrable_sq hmeas).2 (by simpa using hsq)

/-- Choose the spatial `L²` class represented by a product-space scalar section, with zero as a
total value on the exceptional times where that section is not in `L²`. -/
noncomputable def scalarProductTimeL2Slice (U : ScalarProductTimeL2) (t : ℝ) : ScalarTorusL2 := by
  classical
  exact if h : MemLp (fun x : Torus => U (t, x)) 2 (volume : Measure Torus) then
    h.toLp (fun x => U (t, x)) else 0

/-- The selected scalar section agrees a.e. in space with the product representative at every time
whose section is in `L²`. -/
theorem scalarProductTimeL2_slice_coeFn (U : ScalarProductTimeL2) (t : ℝ)
    (h : MemLp (fun x : Torus => U (t, x)) 2 (volume : Measure Torus)) :
    (fun x : Torus => scalarProductTimeL2Slice U t x) =ᵐ[volume]
      fun x => U (t, x) := by
  simpa [scalarProductTimeL2Slice, h] using h.coeFn_toLp

/-- For almost every time, a product-space vector-gradient `L²` class has an `L²` spatial
slice. -/
theorem gradientProductTimeL2_memLp_sections (G : GradientProductTimeL2) :
    ∀ᵐ t ∂GalerkinTimeMeasure,
      MemLp (fun x : Torus => G (t, x)) 2 (volume : Measure Torus) := by
  let hG : MemLp (fun p : ℝ × Torus => G p) 2
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := Lp.memLp G
  have hGmeas : AEStronglyMeasurable (fun p : ℝ × Torus => G p)
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := hG.aestronglyMeasurable
  have hsectionMeas := hGmeas.prodMk_left
  have hnormInt : Integrable (fun p : ℝ × Torus => ‖G p‖ ^ (2 : ℕ))
      (GalerkinTimeMeasure.prod (volume : Measure Torus)) := by
    simpa using hG.integrable_norm_rpow (by norm_num) (by norm_num)
  have hsqSection := (integrable_prod_iff hnormInt.aestronglyMeasurable).mp hnormInt |>.1
  filter_upwards [hsectionMeas, hsqSection] with t hmeas hsq
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  convert hsq using 1

/-- Choose the spatial vector-valued `L²` class represented by a product-gradient section, with
zero as a total value at exceptional times. -/
noncomputable def gradientProductTimeL2Slice
    (G : GradientProductTimeL2) (t : ℝ) : SpatialGradientL2 := by
  classical
  exact if h : MemLp (fun x : Torus => G (t, x)) 2 (volume : Measure Torus) then
    h.toLp (fun x => G (t, x)) else 0

/-- The selected vector section agrees almost everywhere in space with the product representative
whenever the section belongs to `L²`. -/
theorem gradientProductTimeL2_slice_coeFn (G : GradientProductTimeL2) (t : ℝ)
    (h : MemLp (fun x : Torus => G (t, x)) 2 (volume : Measure Torus)) :
    (fun x : Torus => gradientProductTimeL2Slice G t x) =ᵐ[volume]
      fun x => G (t, x) := by
  simpa [gradientProductTimeL2Slice, h] using h.coeFn_toLp

/-- The product scalar limit and the weak path have the same spatial `L²` slice for almost every
time. -/
theorem FrozenDriftProblem.synchronized_scalar_slice_eq_path_ae
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (Uprod : ScalarProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hUcont : ∀ v, Continuous (fun t => inner ℝ (u t) v)) :
    (fun t => scalarProductTimeL2Slice Uprod t) =ᵐ[GalerkinTimeMeasure]
      fun t => u (clampTimeToUnit t) := by
  let diff : ℝ → ScalarTorusL2 := fun t =>
    scalarProductTimeL2Slice Uprod t - u (clampTimeToUnit t)
  have hdiff : ∀ v : ScalarTorusL2,
      (fun t => inner ℝ v (diff t)) =ᵐ[GalerkinTimeMeasure] 0 := by
    intro v
    have hpair := P.synchronized_scalar_slice_pairing_ae σ u Uprod
      hPathWeak hUweak hUcont v
    have hsection := scalarProductTimeL2_memLp_sections Uprod
    filter_upwards [hpair, hsection] with t hpairt hsectiont
    have hsliceeq := scalarProductTimeL2_slice_coeFn Uprod t hsectiont
    have hinner : inner ℝ (scalarProductTimeL2Slice Uprod t) v =
        ∫ x : Torus, inner ℝ (Uprod (t, x)) (v x) ∂volume := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hsliceeq] with x hx
      rw [hx]
    have hpair' : inner ℝ (scalarProductTimeL2Slice Uprod t) v =
        inner ℝ (u (clampTimeToUnit t)) v := hinner.trans hpairt
    have hpair'' : inner ℝ v (scalarProductTimeL2Slice Uprod t) =
        inner ℝ v (u (clampTimeToUnit t)) := by
      simpa [real_inner_comm] using hpair'
    simp [diff, inner_sub_right, hpair'']
  have hdiffZero := MeasureTheory.ae_eq_zero_of_forall_inner hdiff
  filter_upwards [hdiffZero] with t ht
  dsimp [diff] at ht
  exact sub_eq_zero.mp ht

/-- A fixed smooth periodic test satisfies the spatial weak derivative identity for almost every
time slice of the synchronized scalar path and product-gradient limit. -/
theorem FrozenDriftProblem.synchronized_limit_spatial_derivative_ae
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto
      (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (hUcont : ∀ v, Continuous (fun t => inner ℝ (u t) v))
    (hUbound : ∀ t, ‖u t‖ ≤ P.scalarBound)
    (i : Fin 2) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) :
    ∀ᵐ t ∂GalerkinTimeMeasure,
      (∫ x : Torus, inner ℝ (Gprod (t, x))
        (scalarToSpatialGradientL2 i (smoothPeriodicTestL2 hψ hperiodic) x) ∂volume) =
        -inner ℝ (u (clampTimeToUnit t))
          (smoothPeriodicTestL2
            (productWeakGradient_coord_contDiff hψ i)
            (productWeakGradient_coord_periodic hψ hperiodic i)) := by
  let g : SpatialGradientL2 := scalarToSpatialGradientL2 i
    (smoothPeriodicTestL2 hψ hperiodic)
  let dψ : ScalarTorusL2 := smoothPeriodicTestL2
    (productWeakGradient_coord_contDiff hψ i)
    (productWeakGradient_coord_periodic hψ hperiodic i)
  let slice : ℝ → ℝ := fun t =>
    ∫ x : Torus, inner ℝ (Gprod (t, x)) (g x) ∂volume
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) ⊤ GalerkinTimeMeasure :=
    continuous_time_memLp_top continuous_const
  have hsliceIter := gradientProductTimeL2_pairing_iterated Gprod
    (fun _ => 1) hone g
  have hsliceInt : Integrable slice GalerkinTimeMeasure := by
    simpa [slice] using hsliceIter.1
  let path : ℝ → ℝ := fun t => inner ℝ (u (clampTimeToUnit t)) dψ
  have hpathCont : Continuous path := by
    exact (hUcont dψ).comp ProductWeakSlices.clampTimeToUnit_continuous
  have hpathMemTop : MemLp path ⊤ GalerkinTimeMeasure :=
    continuous_time_memLp_top hpathCont
  have hpathInt : Integrable path GalerkinTimeMeasure :=
    (hpathMemTop.mono_exponent (by norm_num : (1 : ENNReal) ≤ ⊤)).integrable
      (by norm_num)
  have hpathBound : ∀ t, |path t| ≤ P.scalarBound * ‖dψ‖ := by
    intro t
    change |inner ℝ (u (clampTimeToUnit t)) dψ| ≤ P.scalarBound * ‖dψ‖
    calc
      |inner ℝ (u (clampTimeToUnit t)) dψ| ≤ ‖u (clampTimeToUnit t)‖ * ‖dψ‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ P.scalarBound * ‖dψ‖ :=
        mul_le_mul_of_nonneg_right (hUbound _) (norm_nonneg _)
  let f : ℝ → ℝ := fun t => slice t + path t
  have hfMeas : AEStronglyMeasurable f GalerkinTimeMeasure :=
    hsliceInt.aestronglyMeasurable.add hpathCont.aestronglyMeasurable
  have hfInt : Integrable f GalerkinTimeMeasure := hsliceInt.add hpathInt
  have hzeroPair : ∀ η : ℝ → ℝ, MemLp η ⊤ GalerkinTimeMeasure →
      ∫ t, η t * f t ∂GalerkinTimeMeasure = 0 := by
    intro η hη
    have hslicePair := gradientProductTimeL2_pairing_iterated Gprod η hη g
    have hweak := P.synchronized_path_spatial_derivative_identity σ u Uprod Gprod
      hPathWeak hUweak hGweak η hη i hψ hperiodic
    have hpathIntegral :
        (∫ t, if ht : t ∈ Icc (0 : ℝ) 1 then η t * inner ℝ (u ⟨t, ht⟩) dψ else 0
          ∂GalerkinTimeMeasure) = ∫ t, η t * path t ∂GalerkinTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
      have hpath : path t = inner ℝ (u ⟨t, htcc⟩) dψ := by
        dsimp [path]
        rw [ProductWeakSlices.clampTimeToUnit_eq ht]
      rw [hpath]
      simp [htcc]
    have hweightedPathMeas : AEStronglyMeasurable (fun t => η t * path t)
        GalerkinTimeMeasure := hη.aestronglyMeasurable.mul hpathCont.aestronglyMeasurable
    have hηbound : ∀ᵐ t ∂GalerkinTimeMeasure,
        ‖η t‖ ≤ lpNorm η ⊤ GalerkinTimeMeasure :=
      MeasureTheory.ae_le_lpNorm_exponent_top hη
    have hweightedPathBound : ∀ᵐ t ∂GalerkinTimeMeasure,
        ‖η t * path t‖ ≤ lpNorm η ⊤ GalerkinTimeMeasure *
          (P.scalarBound * ‖dψ‖) := by
      filter_upwards [hηbound] with t hηt
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul hηt (hpathBound t) (abs_nonneg _)
        MeasureTheory.lpNorm_nonneg
    have hweightedPathInt : Integrable (fun t => η t * path t) GalerkinTimeMeasure :=
      (MemLp.of_bound hweightedPathMeas
        (lpNorm η ⊤ GalerkinTimeMeasure * (P.scalarBound * ‖dψ‖))
        hweightedPathBound).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2) |>.integrable
          (by norm_num)
    have hsumZero :
        (∫ t, η t * slice t ∂GalerkinTimeMeasure) +
          (∫ t, η t * path t ∂GalerkinTimeMeasure) = 0 := by
      have hweak' := hweak
      change inner ℝ Gprod (gradientProductTestLp η g hη) =
        -(∫ t, if ht : t ∈ Icc (0 : ℝ) 1 then η t * inner ℝ (u ⟨t, ht⟩) dψ
          else 0 ∂GalerkinTimeMeasure) at hweak'
      rw [hslicePair.2, hpathIntegral] at hweak'
      linarith
    calc
      ∫ t, η t * f t ∂GalerkinTimeMeasure =
          ∫ t, (η t * slice t + η t * path t) ∂GalerkinTimeMeasure := by
            apply integral_congr_ae
            filter_upwards with t
            simp [f, mul_add]
      _ = _ := by
        rw [integral_add hslicePair.1 hweightedPathInt]
        exact hsumZero
  have hfZero := ae_eq_zero_of_all_top_pairings hfMeas hfInt hzeroPair
  filter_upwards [hfZero] with t hft
  change slice t = -inner ℝ (u (clampTimeToUnit t)) dψ
  dsimp [f] at hft
  linarith

/-- A countable family of smooth periodic tests has one common full-measure set of times on which
all spatial derivative pairings hold. This is the form used for the Fourier basis. -/
theorem FrozenDriftProblem.synchronized_limit_spatial_derivative_ae_countable
    (P : FrozenDriftProblem) (σ : ℕ → ℕ)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2)
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (hPathWeak : ∀ t v, Tendsto
      (fun n => inner ℝ (P.scalarPath (σ n) t) v) atTop
      (𝓝 (inner ℝ (u t) v)))
    (hUweak : ∀ v, Tendsto (fun n => inner ℝ (P.scalarProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Uprod v)))
    (hGweak : ∀ v, Tendsto (fun n => inner ℝ (P.gradientProductLp (σ n)) v) atTop
      (𝓝 (inner ℝ Gprod v)))
    (hUcont : ∀ v, Continuous (fun t => inner ℝ (u t) v))
    (hUbound : ∀ t, ‖u t‖ ≤ P.scalarBound)
    {ι : Type*} [Countable ι] (i : Fin 2) (ψ : ι → Vec 2 → ℝ)
    (hψ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (ψ a))
    (hperiodic : ∀ a, AVenhance.IsZ2Periodic (ψ a)) :
    ∀ᵐ t ∂GalerkinTimeMeasure, ∀ a,
      (∫ x : Torus, inner ℝ (Gprod (t, x))
        (scalarToSpatialGradientL2 i
          (smoothPeriodicTestL2 (hψ a) (hperiodic a)) x) ∂volume) =
        -inner ℝ (u (clampTimeToUnit t))
          (smoothPeriodicTestL2
            (productWeakGradient_coord_contDiff (hψ a) i)
            (productWeakGradient_coord_periodic (hψ a) (hperiodic a) i)) := by
  rw [ae_all_iff]
  intro a
  exact P.synchronized_limit_spatial_derivative_ae σ u Uprod Gprod
    hPathWeak hUweak hGweak hUcont hUbound i (hψ a) (hperiodic a)

end AVenhance.Infra.Parabolic.FourierGalerkin

end
