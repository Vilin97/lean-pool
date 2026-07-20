/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Smoothing
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
# `L²` compactness criterion: approximation-by-translation bounds (Euclidean)

This file will prove the key inequality used in the Fréchet–Kolmogorov approach: smoothing by a
probability kernel controls the `L²` error by the translation modulus.

## Main results (planned)

The principal statement will control `‖smoothL2 ψ u - extendByZeroL2 u‖₂` by an average (or sup) of
`‖translateL2 t (extendByZeroL2 u) - extendByZeroL2 u‖₂` over `t` in the support of `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceApproximation : MeasurableSpace E := borel E
local instance instBorelSpaceApproximation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceApproximation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddApproximation : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegApproximation : MeasurableNeg E := by
  infer_instance

variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)

/-- The measure with density `ψ` with respect to Lebesgue measure. This will be a probability
measure once `ψ ≥ 0` and `∫ ψ = 1`. -/
noncomputable def kernelMeasure : Measure E :=
  (volume : Measure E).withDensity fun x => ENNReal.ofReal (ψ x)

lemma kernelMeasure_univ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    kernelMeasure (E := E) ψ Set.univ = 1 := by
  have hψi : MeasureTheory.Integrable ψ (volume : Measure E) :=
    Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure E)) hψc hψcs
  have hψae : (MeasureTheory.ae (volume : Measure E)).EventuallyLE 0 ψ :=
    Filter.Eventually.of_forall hψ0
  have hlin :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) =
        ENNReal.ofReal (∫ x, ψ x ∂(volume : Measure E)) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψi hψae
  -- `withDensity` on `univ` is the `lintegral` of the density.
  have hwd :
      kernelMeasure (E := E) ψ Set.univ =
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E) := by
    simp [kernelMeasure, MeasureTheory.withDensity_apply, MeasurableSet.univ]
  -- Conclude using `∫ ψ = 1`.
  simpa [hψint] using (hwd.trans hlin)

/-- The kernel measure `kernelMeasure ψ` is a probability measure when `ψ` is a continuous,
compactly supported, nonnegative density integrating to `1`. -/
lemma isProbabilityMeasure_kernelMeasure
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    MeasureTheory.IsProbabilityMeasure (kernelMeasure (E := E) ψ) :=
  ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩

lemma integral_kernelMeasure_eq_integral_smul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) • (g x) ∂(volume : Measure E) := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ψ x) :=
    (hψc.measurable.ennreal_ofReal : Measurable fun x => ENNReal.ofReal (ψ x))
  have htop :
      (MeasureTheory.ae (volume : Measure E)).Eventually
        (fun x => ENNReal.ofReal (ψ x) < ∞) :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hwd :=
    (integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure E))
      (f := fun x => ENNReal.ofReal (ψ x)) hmeas htop g)
  have hwd' :
      (∫ x, g x ∂kernelMeasure (E := E) ψ) =
        ∫ x, (ENNReal.ofReal (ψ x)).toReal • (g x) ∂(volume : Measure E) := by
    simpa [kernelMeasure] using hwd
  -- Simplify `toReal (ofReal _)` using `ψ ≥ 0`.
  refine hwd'.trans ?_
  refine integral_congr_ae ?_
  refine ae_of_all _ (fun x => ?_)
  have hx : (ENNReal.ofReal (ψ x)).toReal = ψ x :=
    ENNReal.toReal_ofReal (hψ0 x)
  -- After rewriting `toReal (ofReal _)`, both sides are definitional.
  simp [hx]

lemma integral_kernelMeasure_eq_integral_mul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) * (g x) ∂(volume : Measure E) := by
  simpa [smul_eq_mul] using integral_kernelMeasure_eq_integral_smul (E := E) (ψ := ψ) hψc hψ0 g

lemma smoothFun_eq_integral_kernelMeasure (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ := by
  have hconv :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u) (x - t) • (ψ t) ∂(volume : Measure E) := by
    simp [smoothFun, convolution_lsmul_swap]
  have hconv' :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    refine hconv.trans ?_
    refine integral_congr_ae ?_
    refine ae_of_all _ (fun t => ?_)
    -- In `ℝ`, scalar multiplication is multiplication, so we can commute the factors.
    change
      extendByZeroFun (E := E) (K := K) u (x - t) • ψ t =
        ψ t * extendByZeroFun (E := E) (K := K) u (x - t)
    rw [smul_eq_mul]
    simp [mul_comm]
  -- Rewrite the convolution integral as an integral against the density measure.
  have hwd :
      (∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ) =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    exact integral_kernelMeasure_eq_integral_mul (E := E) (ψ := ψ) hψc hψ0
      (g := fun t => extendByZeroFun (E := E) (K := K) u (x - t))
  exact hconv'.trans hwd.symm

lemma sq_integral_le_integral_sq_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [MeasureTheory.IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : MeasureTheory.MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have hvar := ProbabilityTheory.variance_nonneg (X := f) μ
  have hvar' :
      0 ≤ (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    simpa [ProbabilityTheory.variance_eq_sub (μ := μ) hf] using hvar
  linarith

private lemma norm_sq_eq_integral_sq (v : (E →₂[(volume : Measure E)] ℝ)) :
    ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂(volume : Measure E) := by
  have hn : ‖v‖ ^ 2 = RCLike.re (inner ℝ v v) :=
    norm_sq_eq_re_inner (𝕜 := ℝ) v
  -- Unfold the `L²` inner product as an integral; for `ℝ`, `re` is the identity.
  rw [hn]
  -- `L²` inner product is an integral of pointwise inner products.
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ) (μ := (volume : Measure E)) v v]
  -- For `ℝ`, `RCLike.re` is the identity and `inner` simplifies to a square.
  simp [pow_two]

lemma norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq (t : E)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖(translateL2 (μ := (volume : Measure E)) (-t))
        (extendByZeroL2 (E := E) (K := K) hKm u)
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 =
      ∫ x,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂(volume : Measure E) := by
  classical
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  -- Translate AE equality along `x ↦ x - t`.
  have hF_shift :
      (fun x : E => (F : E → ℝ) (x - t)) =ᵐ[(volume : Measure E)] fun x => f (x - t) := by
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : E => x - t)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_sub_right (μ := (volume : Measure E)) t
    exact (hmp.quasiMeasurePreserving.ae_eq_comp hF_ae)
  -- TranslateL2 gives `F(x - t)` a.e.
  have htrans :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => (F : E → ℝ) (x - t) := by
    simpa [sub_eq_add_neg] using (translateL2_ae_eq (μ := (volume : Measure E)) (-t) F)
  have htrans' :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) := by
    exact htrans.trans hF_shift
  have hdiff :
      (fun x => ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((translateL2 (μ := (volume : Measure E)) (-t)) F) F,
      htrans', hF_ae] with x hxsub hx1 hx2
    -- `Lp.coeFn_sub` gives the pointwise relation between coercions of `Lp` subtraction.
    have hxsub' :
        ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x =
          ((translateL2 (μ := (volume : Measure E)) (-t)) F) x - F x := by
      simpa using hxsub
    -- Rewrite to the desired expression using the two pointwise identities.
    rw [hxsub', hx1, hx2]
  have hcalc :
      ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 =
        ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 :=
      norm_sq_eq_integral_sq (E := E) (v := ((translateL2 (μ := (volume : Measure E)) (-t)) F - F))
    have h2 :
        ∫ x, (((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) ^ 2
            ∂(volume : Measure E) =
          ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hdiff.pow_const 2
    exact h1.trans h2
  simpa [F, f] using hcalc

private lemma kernelMeasure_le_smul_volume (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ kernelMeasure (E := E) ψ ≤ c • (volume : Measure E) := by
  classical
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψc
  refine ⟨ENNReal.ofReal C, by simp, ?_⟩
  refine (Measure.le_iff).2 ?_
  intro s hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  have hψle : ∀ x, ENNReal.ofReal (ψ x) ≤ ENNReal.ofReal C := by
    intro x
    have hx : ψ x ≤ C := by
      have hx' : ‖ψ x‖ ≤ C := hC x
      -- `ψ ≥ 0`, so `‖ψ x‖ = ψ x`.
      simpa [Real.norm_eq_abs, abs_of_nonneg (hψ0 x)] using hx'
    exact ENNReal.ofReal_le_ofReal hx
  -- Unfold `withDensity` and bound the density by the constant `ENNReal.ofReal C`.
  simp only [kernelMeasure, MeasureTheory.withDensity_apply, hs]
  have hle :
      (∫⁻ x in s, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) ≤
        ∫⁻ x in s, ENNReal.ofReal C ∂(volume : Measure E) := by
    refine MeasureTheory.lintegral_mono ?_
    intro x
    exact hψle x
  refine hle.trans ?_
  simp

lemma smoothFun_sub_extendByZeroFun_sq_le_integral_sq
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    (smoothFun (E := E) (K := K) ψ u x - extendByZeroFun (E := E) (K := K) u x) ^ 2 ≤
      ∫ t,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  haveI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  rcases kernelMeasure_le_smul_volume (E := E) (ψ := ψ) hψc hψcs hψ0 with ⟨c, hc_top, hμle⟩
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hf_vol : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Use the `L²` packaging of `extendByZeroFun` and the AE bridge.
    let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    have hF_ae : (fun x : E => (F : E → ℝ) x) =ᵐ[(volume : Measure E)] f :=
      extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hmp :
      MeasureTheory.MeasurePreserving (fun t : E => x - t)
        (volume : Measure E) (volume : Measure E) := by
    -- `t ↦ x - t = (-t) + x` is measure-preserving for Lebesgue (Haar) measure.
    have hneg :
        MeasureTheory.MeasurePreserving (Neg.neg : E → E)
          (volume : Measure E) (volume : Measure E) :=
      (volume : Measure E).measurePreserving_neg
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : E => y + x)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_add_right
        (μ := (volume : Measure E)) x
    have hcomp : ((fun y : E => y + x) ∘ fun t : E => -t) = fun t : E => x - t := by
      funext t
      simp [sub_eq_add_neg, add_comm]
    have := hadd.comp hneg
    rwa [hcomp] at this
  have hf_shift_vol :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) (volume : Measure E) :=
    hf_vol.comp_measurePreserving hmp
  have hf_shift :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) μ := by
    exact MeasureTheory.MemLp.of_measure_le_smul
      (μ := (volume : Measure E)) (μ' := μ) (c := c)
      hc_top hμle hf_shift_vol
  have hf_const : MeasureTheory.MemLp (fun _ : E => f x) (2 : ℝ≥0∞) μ :=
    MeasureTheory.memLp_const (μ := μ) (c := f x)
  have hg : MeasureTheory.MemLp (fun t : E => f (x - t) - f x) (2 : ℝ≥0∞) μ :=
    hf_shift.sub hf_const
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u x = ∫ t, f (x - t) ∂μ := by
    simpa [μ, f] using smoothFun_eq_integral_kernelMeasure (E := E) (K := K) (ψ := ψ) hψc hψ0 u x
  have hdiff :
      smoothFun (E := E) (K := K) ψ u x - f x = ∫ t, (f (x - t) - f x) ∂μ := by
    have hconst : (∫ _t : E, f x ∂μ) = f x := by
      simp [MeasureTheory.integral_const]
    have hint : MeasureTheory.Integrable (fun t : E => f (x - t)) μ :=
      hf_shift.integrable (by norm_num)
    have :
        (∫ t, f (x - t) ∂μ) - (∫ _t : E, f x ∂μ) =
          ∫ t, (f (x - t) - f x) ∂μ := by
      simpa using (MeasureTheory.integral_sub hint (MeasureTheory.integrable_const (f x))).symm
    simpa [hsmooth, hconst] using this
  -- Apply Jensen/variance inequality to `t ↦ f(x - t) - f(x)`.
  have hJ :=
    sq_integral_le_integral_sq_of_isProbabilityMeasure
      (μ := μ) (f := fun t : E => f (x - t) - f x) hg
  simpa [hdiff, μ, f] using hJ

lemma norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤
      ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) (extendByZeroL2 (E := E) (K := K) hKm u)
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  haveI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  haveI : MeasureTheory.SFinite μ := by infer_instance
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  let S : (E →₂[(volume : Measure E)] ℝ) := smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  have hS_ae :
      (S : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
    smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  have hSF_ae :
      (fun x : E => (S - F) x) =ᵐ[(volume : Measure E)] fun x =>
        smoothFun (E := E) (K := K) ψ u x - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub S F, hS_ae, hF_ae] with x hxsub hxS hxF
    have hxsub' : (S - F) x = S x - F x := by
      simpa using hxsub
    rw [hxsub', hxS, hxF]
  have hnorm_sq :
      ‖S - F‖ ^ 2 =
        ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 := norm_sq_eq_integral_sq (E := E) (v := (S - F))
    have h2 :
        (∫ x, ((S - F) x) ^ 2 ∂(volume : Measure E)) =
          ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hSF_ae.pow_const 2
    exact h1.trans h2
  have hLHS_int :
      MeasureTheory.Integrable (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        (volume : Measure E) := by
    have hv_mem : MeasureTheory.MemLp (fun x : E => (S - F : E →₂[(volume : Measure E)] ℝ) x)
        (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp (S - F)
    have hv_int :
        MeasureTheory.Integrable
          (fun x : E => ‖(S - F : E →₂[(volume : Measure E)] ℝ) x‖ ^ (2 : ℕ))
          (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow (μ := (volume : Measure E)) (f := fun x =>
        (S - F : E →₂[(volume : Measure E)] ℝ) x) (p := 2) hv_mem (by decide)
    -- Replace `‖·‖^2` by `(_)^2` in `ℝ`, then transport along the AE equality.
    have hv_sq :
        MeasureTheory.Integrable (fun x : E => ((S - F : E →₂[(volume : Measure E)] ℝ) x) ^ 2)
          (volume : Measure E) := by
      simpa [Real.norm_eq_abs, sq_abs] using hv_int
    exact hv_sq.congr (hSF_ae.pow_const 2)
  -- Show integrability on the product measure, so we can use Fubini/Tonelli for the translation
  -- error.
  let h : E × E → ℝ := fun z => (f (z.1 - z.2) - f z.1) ^ 2
  have hf_mem : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Again use the AE bridge from the `L²` packaging.
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hf_sq_int : MeasureTheory.Integrable (fun x : E => (f x) ^ 2) (volume : Measure E) := by
    have hf_int :
        MeasureTheory.Integrable (fun x : E => ‖f x‖ ^ (2 : ℕ)) (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow
        (μ := (volume : Measure E)) (f := f) (p := 2)
        hf_mem (by decide)
    simpa [Real.norm_eq_abs, sq_abs] using hf_int
  have hfst_map :
      MeasureTheory.Integrable (fun x : E => (f x) ^ 2)
        (Measure.map Prod.fst ((volume : Measure E).prod μ)) := by
    simpa [Measure.map_fst_prod] using hf_sq_int
  have hf_fst_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f z.1) ^ 2) ((volume : Measure E).prod μ) :=
    (MeasureTheory.Integrable.comp_measurable (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := fun x : E => (f x) ^ 2) hfst_map measurable_fst)
  have hsub :
      MeasureTheory.MeasurePreserving
        (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod μ)
        ((volume : Measure E).prod μ) :=
    MeasureTheory.measurePreserving_sub_prod (μ := (volume : Measure E)) (ν := μ)
  have hf_shift_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f (z.1 - z.2)) ^ 2)
        ((volume : Measure E).prod μ) := by
    have := (hsub.integrable_comp hf_fst_sq_prod.aestronglyMeasurable).2 hf_fst_sq_prod
    exact this
  have hdom :
      MeasureTheory.Integrable (fun z : E × E => (2 : ℝ) * ((f (z.1 - z.2)) ^ 2 + (f z.1) ^ 2))
        ((volume : Measure E).prod μ) := by
    simpa [mul_add, two_mul] using (hf_shift_sq_prod.add hf_fst_sq_prod).const_mul (2 : ℝ)
  have hf_fst_aesm :
      MeasureTheory.AEStronglyMeasurable (fun z : E × E => f z.1)
        ((volume : Measure E).prod μ) := by
    have hf_map :
        MeasureTheory.AEStronglyMeasurable f
          (Measure.map Prod.fst
            ((volume : Measure E).prod μ)) := by
      simpa [Measure.map_fst_prod] using hf_mem.1
    exact MeasureTheory.AEStronglyMeasurable.comp_measurable
      (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := f) hf_map measurable_fst
  have hf_shift_aesm :
      MeasureTheory.AEStronglyMeasurable
        (fun z : E × E => f (z.1 - z.2))
        ((volume : Measure E).prod μ) := by
    have := MeasureTheory.AEStronglyMeasurable.comp_measurePreserving (g := fun z : E × E => f z.1)
      hf_fst_aesm hsub
    exact this
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable h ((volume : Measure E).prod μ) := by
    -- Build up AE-strong measurability from the two components.
    have hsub' :
        MeasureTheory.AEStronglyMeasurable (fun z : E × E => f (z.1 - z.2) - f z.1)
          ((volume : Measure E).prod μ) :=
      hf_shift_aesm.sub hf_fst_aesm
    exact (hsub'.pow 2)
  have hint_h : MeasureTheory.Integrable h ((volume : Measure E).prod μ) := by
    refine MeasureTheory.Integrable.mono (μ := (volume : Measure E).prod μ) hdom h_aesm ?_
    refine Filter.Eventually.of_forall ?_
    rintro ⟨x, t⟩
    have hineq :
        (f (x - t) - f x) ^ 2 ≤ (2 : ℝ) * ((f (x - t)) ^ 2 + (f x) ^ 2) := by
      -- `(a - b)^2 ≤ 2(a^2 + b^2)` as a special case of `add_sq_le`.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_sq_le (a := f (x - t)) (b := -f x))
    have hnonneg : 0 ≤ (f (x - t) - f x) ^ 2 := by nlinarith
    have hsum_nonneg : 0 ≤ (f (x - t)) ^ 2 + (f x) ^ 2 := by nlinarith
    simpa [h, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_mul,
      abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
      abs_of_nonneg hsum_nonneg] using hineq
  have hRHS_int :
      MeasureTheory.Integrable
        (fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ) (volume : Measure E) := by
    simpa [h] using hint_h.integral_prod_left
  have hpoint :
      (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        ≤ᶠ[MeasureTheory.ae (volume : Measure E)]
        fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [f, μ] using
      (smoothFun_sub_extendByZeroFun_sq_le_integral_sq (E := E) (K := K) (ψ := ψ)
        hψc hψcs hψ0 hψint hKm u x)
  have hinterm :
      ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) :=
    MeasureTheory.integral_mono_ae hLHS_int hRHS_int hpoint
  -- Swap the order of integration on the right-hand side.
  have hswap :
      (∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E)) =
        ∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ := by
    simpa using (MeasureTheory.integral_integral_swap (μ := (volume : Measure E)) (ν := μ)
      (f := fun x t => (f (x - t) - f x) ^ 2) hint_h)
  -- Identify the inner `x` integral with the `L²` translation norm squared.
  have hinner :
      (fun t : E => ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) =
        fun t : E =>
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 := by
    funext t
    -- Use the previously proved integral identity.
    simpa [F, f] using
      (norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
        (E := E) (K := K) (hKm := hKm) t u).symm
  have hRHS_rewrite :
      (∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ) =
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    simp [hinner]
  -- Assemble everything.
  have hmain :
      ‖S - F‖ ^ 2 ≤
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    -- Convert `‖S-F‖²` to an `x`-integral and apply the integral inequality chain.
    have : ‖S - F‖ ^ 2 ≤ ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) := by
      simpa [hnorm_sq] using hinterm
    exact this.trans_eq (hswap.trans hRHS_rewrite)
  -- Restore the original statement.
  simpa [S, F, μ] using hmain

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
