/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Layer Cake

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal


namespace CKN.Foundation.Measure

/-- The layer-cake formula for the `p`-th power integral of an a.e.-finite measurable
`ℝ≥0∞`-valued function: `∫⁻ f^p ∂μ = p * ∫⁻_{t>0} μ {f > t} * t^(p-1) dt`. -/
theorem lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 0 < p)
    (hfinite : ∀ᵐ z ∂μ, f z < ∞) :
    ∫⁻ z, f z ^ p ∂μ =
      ENNReal.ofReal p * ∫⁻ t in Ioi 0,
        μ {z | ENNReal.ofReal t < f z} * ENNReal.ofReal (t ^ (p - 1)) := by
  have hpow_eq : (fun z ↦ f z ^ p) =ᵐ[μ]
      (fun z ↦ ENNReal.ofReal ((f z).toReal ^ p)) := by
    filter_upwards [hfinite] with z hz
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal hz.ne]
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (Eventually.of_forall (fun z ↦ ENNReal.toReal_nonneg))
    hf.ennreal_toReal.aemeasurable hp
  have hlevel : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      μ {z | t < (f z).toReal} = μ {z | ENNReal.ofReal t < f z} := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with t ht
    have hset : {z | t < (f z).toReal} =ᵐ[μ] {z | ENNReal.ofReal t < f z} := by
      filter_upwards [hfinite] with z hz
      by_cases hzero : f z = 0
      · have ht0 : 0 ≤ t := ht.le
        simp [hzero, ht0]
      · have hpos : 0 < (f z).toReal := ENNReal.toReal_pos hzero hz.ne
        apply propext
        constructor
        · intro h
          rw [← ENNReal.ofReal_toReal hz.ne, ENNReal.ofReal_lt_ofReal_iff hpos]
          exact h
        · intro h
          rw [← ENNReal.ofReal_toReal hz.ne, ENNReal.ofReal_lt_ofReal_iff hpos] at h
          exact h
    exact measure_congr hset
  calc
    ∫⁻ z, f z ^ p ∂μ = ∫⁻ z, ENNReal.ofReal ((f z).toReal ^ p) ∂μ :=
      lintegral_congr_ae hpow_eq
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi 0,
        μ {z | t < (f z).toReal} * ENNReal.ofReal (t ^ (p - 1)) := hlayer
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi 0,
        μ {z | ENNReal.ofReal t < f z} * ENNReal.ofReal (t ^ (p - 1)) := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [hlevel] with t ht
      rw [ht]

end CKN.Foundation.Measure
