/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionKernel
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Two auxiliary steps for slicing distributional identities

The passage from a countable family of mollifier bumps to every test function
uses two ingredients that are independent of the differential operator at hand.

* `eq_zero_of_dense_of_continuousAt`: a function that is continuous on an open
  set and vanishes on a dense subset vanishes on the whole open set.
* `integral_mul_integral_translate_swap`: Fubini for the pairing of a compactly
  supported continuous function with the translation average of an integrable
  function against a compactly supported continuous kernel.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology


noncomputable section

namespace CKN

/-- A real function that is continuous at every point of an open set `U` and
vanishes on `U ∩ S` for a dense set `S` vanishes on all of `U`. -/
theorem eq_zero_of_dense_of_continuousAt {X : Type*} [TopologicalSpace X]
    {D : X → ℝ} {U S : Set X} (hS : Dense S) (hU : IsOpen U)
    (hcont : ∀ y ∈ U, ContinuousAt D y) (hzero : ∀ y ∈ U ∩ S, D y = 0) :
    ∀ y ∈ U, D y = 0 := by
  intro y hy
  have hmem : y ∈ closure (U ∩ S) := hS.open_subset_closure_inter hU hy
  have hne : (𝓝[U ∩ S] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have h1 : Filter.Tendsto D (𝓝[U ∩ S] y) (𝓝 (D y)) :=
    (hcont y hy).continuousWithinAt
  have h2 : Filter.Tendsto D (𝓝[U ∩ S] y) (𝓝 (0 : ℝ)) := by
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hzero z hz).symm
  exact tendsto_nhds_unique (l := 𝓝[U ∩ S] y) h1 h2

/-- The double integrand of the pairing of `ψ` with the translation averages of
`G` against `k` is integrable for the product measure. -/
theorem integrable_uncurry_mul_translate {d : ℕ} {ψ G k : Vec d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hG : MeasureTheory.Integrable G MeasureTheory.volume)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    MeasureTheory.Integrable
      (Function.uncurry fun y x => ψ y * (G x * k (x - y)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Vec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d))) := by
  classical
  obtain ⟨A, hA⟩ := hψc.exists_bound_of_continuous hψ
  obtain ⟨B, hB⟩ := hkc.exists_bound_of_continuous hk
  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg (k 0)).trans (hB 0)
  set u : Vec d → ℝ := Set.indicator (tsupport ψ) (fun _ => A) with hu_def
  set v : Vec d → ℝ := fun x => B * ‖G x‖ with hv_def
  have hu_nonneg : ∀ y, 0 ≤ u y := by
    intro y
    simp only [hu_def]
    by_cases hy : y ∈ tsupport ψ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy, hA0]
  have hψ_le : ∀ y, |ψ y| ≤ u y := by
    intro y
    by_cases hy : y ∈ tsupport ψ
    · simpa [hu_def, Set.indicator_of_mem hy, Real.norm_eq_abs] using hA y
    · simp [hu_def, Set.indicator_of_notMem hy,
        image_eq_zero_of_notMem_tsupport hy]
  have hu_int : MeasureTheory.Integrable u MeasureTheory.volume := by
    refine (MeasureTheory.integrable_indicator_iff
      (isClosed_tsupport ψ).measurableSet).2 ?_
    exact MeasureTheory.integrableOn_const (C := A) (hs := hψc.measure_lt_top.ne)
  have hv_int : MeasureTheory.Integrable v MeasureTheory.volume := hG.norm.const_mul B
  have hprod : MeasureTheory.Integrable
      (fun p : Vec d × Vec d => u p.1 * v p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Vec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d))) :=
    hu_int.mul_prod hv_int
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun y x => ψ y * (G x * k (x - y)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Vec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d))) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => ψ p.1)
        ((MeasureTheory.volume : MeasureTheory.Measure (Vec d)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Vec d))) :=
      (hψ.comp continuous_fst).aestronglyMeasurable
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => G p.2)
        ((MeasureTheory.volume : MeasureTheory.Measure (Vec d)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Vec d))) :=
      hG.aestronglyMeasurable.comp_snd
    have h3 : MeasureTheory.AEStronglyMeasurable
        (fun p : Vec d × Vec d => k (p.2 - p.1))
        ((MeasureTheory.volume : MeasureTheory.Measure (Vec d)).prod
          (MeasureTheory.volume : MeasureTheory.Measure (Vec d))) :=
      (hk.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
    exact h1.mul (h2.mul h3)
  have hint : MeasureTheory.Integrable
      (Function.uncurry fun y x => ψ y * (G x * k (x - y)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Vec d)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Vec d))) := by
    refine hprod.mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    have hfac : ‖ψ p.1 * (G p.2 * k (p.2 - p.1))‖
        = |ψ p.1| * (‖G p.2‖ * |k (p.2 - p.1)|) := by
      simp [Real.norm_eq_abs]
    rw [Function.uncurry_def, hfac]
    have hk' : |k (p.2 - p.1)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB (p.2 - p.1)
    have hstep : ‖G p.2‖ * |k (p.2 - p.1)| ≤ v p.2 := by
      have h0 : ‖G p.2‖ * |k (p.2 - p.1)| ≤ ‖G p.2‖ * B :=
        mul_le_mul_of_nonneg_left hk' (norm_nonneg _)
      simpa only [hv_def, mul_comm B (‖G p.2‖)] using h0
    have hnn : 0 ≤ ‖G p.2‖ * |k (p.2 - p.1)| := by positivity
    calc |ψ p.1| * (‖G p.2‖ * |k (p.2 - p.1)|)
        ≤ u p.1 * (‖G p.2‖ * |k (p.2 - p.1)|) :=
          mul_le_mul_of_nonneg_right (hψ_le p.1) hnn
      _ ≤ u p.1 * v p.2 := mul_le_mul_of_nonneg_left hstep (hu_nonneg p.1)
  exact hint

/-- The pairing of a compactly supported continuous function `ψ` with the
translation averages of an integrable function `G` against a compactly supported
continuous kernel `k` is itself integrable. -/
theorem integrable_mul_integral_translate {d : ℕ} {ψ G k : Vec d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hG : MeasureTheory.Integrable G MeasureTheory.volume)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    MeasureTheory.Integrable
      (fun y => ψ y * ∫ x, G x * k (x - y) ∂MeasureTheory.volume)
      MeasureTheory.volume := by
  have hint := (integrable_uncurry_mul_translate hψ hψc hG hk hkc).integral_prod_left
  refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
  change (∫ x, ψ y * (G x * k (x - y)) ∂MeasureTheory.volume)
    = ψ y * ∫ x, G x * k (x - y) ∂MeasureTheory.volume
  exact MeasureTheory.integral_const_mul (ψ y) (fun x => G x * k (x - y))

/-- Exchanging the order of integration in the pairing of a compactly supported
continuous function `ψ` with the translation averages of an integrable function
`G` against a compactly supported continuous kernel `k`. -/
theorem integral_mul_integral_translate_swap {d : ℕ} {ψ G k : Vec d → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hG : MeasureTheory.Integrable G MeasureTheory.volume)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    (∫ y, ψ y * ∫ x, G x * k (x - y) ∂MeasureTheory.volume ∂MeasureTheory.volume)
      = ∫ x, G x * ∫ y, ψ y * k (x - y) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  have hint := integrable_uncurry_mul_translate hψ hψc hG hk hkc
  calc (∫ y, ψ y * ∫ x, G x * k (x - y) ∂MeasureTheory.volume ∂MeasureTheory.volume)
      = ∫ y, ∫ x, ψ y * (G x * k (x - y)) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (MeasureTheory.integral_const_mul (ψ y)
          (fun x => G x * k (x - y))).symm
    _ = ∫ x, ∫ y, ψ y * (G x * k (x - y)) ∂MeasureTheory.volume ∂MeasureTheory.volume :=
        MeasureTheory.integral_integral_swap hint
    _ = ∫ x, G x * ∫ y, ψ y * k (x - y) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change (∫ y, ψ y * (G x * k (x - y)) ∂MeasureTheory.volume)
          = G x * ∫ y, ψ y * k (x - y) ∂MeasureTheory.volume
        rw [← MeasureTheory.integral_const_mul (G x) (fun y => ψ y * k (x - y))]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring

end CKN

end
