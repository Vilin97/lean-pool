/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationKernelComparison
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertFiniteTruncationWeakOneOne
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IsLUB

/-!
# Measurability of the quadratic maximal truncation

For every real quadratic modulation, the sharp truncation is continuous in
its positive radius. Hence its supremum over all positive real radii equals
a supremum over one fixed countable dense family and is measurable. The
argument applies to every measurable integrable input.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace QuadraticHilbertMaximalMeasurable

open HilbertFiniteTruncationWeakOneOne


noncomputable
section

/-- The translated input multiplied by the quadratic phase and divided by the integration
variable. -/
def quadraticHilbertIntegrand
    (lam : ℝ) (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  f (x - t) * phase (lam * t ^ 2) / (t : ℂ)

theorem integrableOn_quadraticHilbertTail
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    IntegrableOn (quadraticHilbertIntegrand lam f x) {t : ℝ | ε < |t|} := by
  have hbase := integrableOn_zeroHilbertTail hε hf x
  have hphase : Measurable fun t : ℝ ↦ phase (lam * t ^ 2) := by
    unfold phase
    fun_prop
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict {t : ℝ | ε < |t|},
      ‖phase (lam * t ^ 2)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun t ↦ by rw [norm_phase]
  have hmul := hbase.bdd_mul hphase.aestronglyMeasurable.restrict hbound
  apply hmul.congr
  filter_upwards with t
  dsimp only [quadraticHilbertIntegrand]
  field_simp

theorem quadraticHilbertTruncation_eq_oneSidedTails
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    quadraticHilbertTrunc lam ε f x =
      (∫ t in Iio (-ε), quadraticHilbertIntegrand lam f x t) +
        ∫ t in Ioi ε, quadraticHilbertIntegrand lam f x t := by
  have hset : {t : ℝ | ε < |t|} = Iio (-ε) ∪ Ioi ε := by
    ext t
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hwhole := integrableOn_quadraticHilbertTail lam hε hf x
  have hleft : IntegrableOn (quadraticHilbertIntegrand lam f x) (Iio (-ε)) := by
    apply hwhole.mono_set
    intro t ht
    change t < -ε at ht
    change ε < |t|
    have htneg : t < 0 := ht.trans (neg_neg_of_pos hε)
    rw [abs_of_neg htneg]
    linarith
  have hright : IntegrableOn (quadraticHilbertIntegrand lam f x) (Ioi ε) := by
    apply hwhole.mono_set
    intro t ht
    change ε < |t|
    rw [abs_of_pos (hε.trans ht)]
    exact ht
  have hdis : Disjoint (Iio (-ε)) (Ioi ε) := by
    apply Set.disjoint_left.2
    intro t htl htr
    change t < -ε at htl
    change ε < t at htr
    linarith
  unfold quadraticHilbertTrunc quadraticHilbertIntegrand
  rw [hset]
  exact setIntegral_union hdis measurableSet_Ioi hleft hright

theorem continuousAt_quadraticHilbertTruncation_radius
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    ContinuousAt (fun δ : ℝ ↦ quadraticHilbertTrunc lam δ f x) ε := by
  let a : ℝ := ε / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hwhole := integrableOn_quadraticHilbertTail lam ha hf x
  have hright : IntegrableOn (quadraticHilbertIntegrand lam f x) (Ioi a) := by
    apply hwhole.mono_set
    intro t ht
    change a < t at ht
    change a < |t|
    rw [abs_of_pos (ha.trans ht)]
    exact ht
  have hleft : IntegrableOn (quadraticHilbertIntegrand lam f x) (Iio (-a)) := by
    apply hwhole.mono_set
    intro t ht
    change t < -a at ht
    change a < |t|
    have htneg : t < 0 := ht.trans (neg_neg_of_pos ha)
    rw [abs_of_neg htneg]
    linarith
  have hεa : a < ε := by dsimp [a]; linarith
  have hrightAt : ContinuousAt
      (fun δ : ℝ ↦ ∫ t in Ioi δ, quadraticHilbertIntegrand lam f x t) ε := by
    apply (hright.continuousOn_Ici_primitive_Ioi ε hεa.le).continuousAt
    exact Ici_mem_nhds hεa
  have hleftAtBound : ContinuousAt
      (fun b : ℝ ↦ ∫ t in Iio b, quadraticHilbertIntegrand lam f x t) (-ε) := by
    apply (hleft.continuousOn_Iic_primitive_Iio (-ε)
      (by linarith : -ε ≤ -a)).continuousAt
    exact Iic_mem_nhds (by linarith : -ε < -a)
  have hleftAt : ContinuousAt
      (fun δ : ℝ ↦ ∫ t in Iio (-δ), quadraticHilbertIntegrand lam f x t) ε :=
    hleftAtBound.comp continuousAt_neg
  have hsum : ContinuousAt
      (fun δ : ℝ ↦
        (∫ t in Iio (-δ), quadraticHilbertIntegrand lam f x t) +
          ∫ t in Ioi δ, quadraticHilbertIntegrand lam f x t) ε :=
    hleftAt.add hrightAt
  apply ContinuousAt.congr_of_eventuallyEq hsum
  filter_upwards [Ioi_mem_nhds hε] with δ hδ
  exact quadraticHilbertTruncation_eq_oneSidedTails lam hδ hf x

theorem continuous_quadraticHilbertTruncation_positiveRadii
    (lam : ℝ) {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Continuous (fun ε : {ε : ℝ // 0 < ε} ↦
      quadraticHilbertTrunc lam ε.1 f x) := by
  rw [continuous_iff_continuousAt]
  intro ε
  exact (continuousAt_quadraticHilbertTruncation_radius
    lam ε.2 hf x).comp continuousAt_subtype_val

theorem continuous_enorm_quadraticHilbertTruncation_positiveRadii
    (lam : ℝ) {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Continuous (fun ε : {ε : ℝ // 0 < ε} ↦
      ‖quadraticHilbertTrunc lam ε.1 f x‖ₑ) :=
  (continuous_quadraticHilbertTruncation_positiveRadii lam hf x).enorm

/-- A fixed countable dense family of positive truncation radii. -/
def densePositiveRadii : Set {ε : ℝ // 0 < ε} :=
  (TopologicalSpace.exists_countable_dense {ε : ℝ // 0 < ε}).choose

theorem countable_densePositiveRadii : densePositiveRadii.Countable :=
  (TopologicalSpace.exists_countable_dense {ε : ℝ // 0 < ε}).choose_spec.1

theorem dense_densePositiveRadii : Dense densePositiveRadii :=
  (TopologicalSpace.exists_countable_dense {ε : ℝ // 0 < ε}).choose_spec.2

/-- The supremum of truncated quadratic Hilbert norms over a countable dense set of positive
radii. -/
def countableQuadraticHilbertMaximalTruncation
    (lam : ℝ) (f : ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ ε : densePositiveRadii, ‖quadraticHilbertTrunc lam ε.1.1 f x‖ₑ

theorem countableQuadraticHilbertMaximalTruncation_eq
    (lam : ℝ) {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    countableQuadraticHilbertMaximalTruncation lam f x =
      quadraticHilbertMaximalTruncation lam f x := by
  unfold countableQuadraticHilbertMaximalTruncation quadraticHilbertMaximalTruncation
  exact dense_densePositiveRadii.ciSup'
    (continuous_enorm_quadraticHilbertTruncation_positiveRadii lam hf x)

theorem measurable_quadraticHilbertTrunc
    (lam ε : ℝ) {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (quadraticHilbertTrunc lam ε f) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦
      f (p.1 - p.2) * phase (lam * p.2 ^ 2) / (p.2 : ℂ)) := by
    unfold phase
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict {t : ℝ | ε < |t|})).measurable

theorem measurable_countableQuadraticHilbertMaximalTruncation
    (lam : ℝ) {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (countableQuadraticHilbertMaximalTruncation lam f) := by
  let _ := countable_densePositiveRadii.toEncodable
  apply Measurable.iSup
  intro ε
  exact (measurable_quadraticHilbertTrunc lam ε.1.1 hf).enorm

/-- The genuine supremum over every positive real truncation radius is
measurable for any measurable integrable input. -/
theorem measurable_quadraticHilbertMaximalTruncation
    (lam : ℝ) {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) :
    Measurable (quadraticHilbertMaximalTruncation lam f) := by
  rw [← funext (countableQuadraticHilbertMaximalTruncation_eq lam hfi)]
  exact measurable_countableQuadraticHilbertMaximalTruncation lam hf


end
end QuadraticHilbertMaximalMeasurable
end QuadraticCarleson
