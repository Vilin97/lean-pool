/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpPairing

@[expose] public section

/-! Strong Bochner energy passage on every genuine subinterval of the original time interval. -/

noncomputable section

namespace EulerTimeLpSubinterval

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerVolterraConvolution EulerTimeLpPairing
open scoped Topology

/-- Restrict a genuine scalar L² coefficient to a measurable closed time subinterval. -/
def subintervalWeight (T s t : ℝ) (c : TimeLp T ℝ) : TimeLp T ℝ :=
  (MemLp.indicator measurableSet_Icc (Lp.memLp c)).toLp ((Icc s t).indicator c)

/-- The subinterval coefficient has its actual indicator representative. -/
theorem subintervalWeight_ae (T s t : ℝ) (c : TimeLp T ℝ) :
    subintervalWeight T s t c =ᵐ[timeMeasure T] (Icc s t).indicator c :=
  MemLp.coeFn_toLp _

/-- A subinterval pairing is exactly the integral of the actual forcing over that subinterval. -/
theorem subinterval_inner_eq (T s t : ℝ) (c f : TimeLp T ℝ) :
    ⟪subintervalWeight T s t c, f⟫_ℝ = ∫ r in Icc s t, c r * f r ∂timeMeasure T := by
  rw [inner_eq_integral]
  calc
    _ = ∫ r, (Icc s t).indicator (fun r => c r * f r) r ∂timeMeasure T := by
      apply integral_congr_ae
      filter_upwards [subintervalWeight_ae T s t c] with r hr
      rw [hr]
      by_cases h : r ∈ Icc s t <;> simp [h]
    _ = _ := integral_indicator measurableSet_Icc

/-- For actual continuous paths a subinterval pairing is the ordinary interval integral. -/
theorem subinterval_path_inner (T : ℝ) (hT : 0 ≤ T) (s t : ℝ)
    (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (a b : C(Icc (0 : ℝ) T, ℝ)) :
    ⟪subintervalWeight T s t (pathLp T hT a), pathLp T hT b⟫_ℝ =
      ∫ r in s..t, extendPath T hT a r * extendPath T hT b r := by
  rw [subinterval_inner_eq]
  have he : (∫ r in Icc s t, pathLp T hT a r * pathLp T hT b r ∂timeMeasure T) =
      ∫ r in Icc s t, extendPath T hT a r * extendPath T hT b r ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_of_ae (pathLp_ae T hT a)),
      (ae_restrict_of_ae (pathLp_ae T hT b))] with r ha hb
    rw [ha, hb]
  rw [he]
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := fun _ hr => ⟨h0s.trans hr.1, hr.2.trans htT⟩
  change (∫ r, extendPath T hT a r * extendPath T hT b r ∂(volume.restrict (Icc 0 T)).restrict (Icc
    s t)) = _
  rw [Measure.restrict_restrict_of_subset hsub, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hst]

/-- Uniform scalar path limits preserve every signed subinterval integral. -/
theorem subinterval_path_tendsto (T : ℝ) (hT : 0 ≤ T) (s t : ℝ)
    (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (a : C(Icc (0 : ℝ) T, ℝ))
    (X : ℕ → C(Icc (0 : ℝ) T, ℝ)) (x : C(Icc (0 : ℝ) T, ℝ))
    (hX : Filter.Tendsto X Filter.atTop (𝓝 x)) :
    Filter.Tendsto (fun n => ∫ r in s..t, extendPath T hT a r * extendPath T hT (X n) r)
      Filter.atTop (𝓝 (∫ r in s..t, extendPath T hT a r * extendPath T hT x r)) := by
  have h : Filter.Tendsto (fun n => ⟪subintervalWeight T s t (pathLp T hT a), pathLp T hT (X n)⟫_ℝ)
      Filter.atTop (𝓝 ⟪subintervalWeight T s t (pathLp T hT a), pathLp T hT x⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds (pathLp_tendsto T hT X x hX)
  simpa only [subinterval_path_inner T hT s t h0s hst htT] using h

/-- Strong L² time limits preserve every actual signed subinterval forcing integral. -/
theorem subinterval_forcing_tendsto (T s t : ℝ) (c : TimeLp T ℝ)
    (F : ℕ → TimeLp T ℝ) (f : TimeLp T ℝ) (hF : Filter.Tendsto F Filter.atTop (𝓝 f)) :
    Filter.Tendsto (fun n => ∫ r in Icc s t, c r * F n r ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ r in Icc s t, c r * f r ∂timeMeasure T)) := by
  have h : Filter.Tendsto (fun n => ⟪subintervalWeight T s t c, F n⟫_ℝ) Filter.atTop
      (𝓝 ⟪subintervalWeight T s t c, f⟫_ℝ) := Filter.Tendsto.inner tendsto_const_nhds hF
  simpa only [subinterval_inner_eq] using h

/-- Actual integral energy bounds pass to limits on each subinterval, with the radius term retaining its sign. -/
theorem integral_energy_subinterval_limit (T : ℝ) (hT : 0 ≤ T) (s t : ℝ)
    (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (a b : C(Icc (0 : ℝ) T, ℝ)) (c : TimeLp T ℝ)
    (X Y : ℕ → C(Icc (0 : ℝ) T, ℝ)) (F : ℕ → TimeLp T ℝ)
    (x y : C(Icc (0 : ℝ) T, ℝ)) (f : TimeLp T ℝ)
    (hX : Filter.Tendsto X Filter.atTop (𝓝 x)) (hY : Filter.Tendsto Y Filter.atTop (𝓝 y))
    (hF : Filter.Tendsto F Filter.atTop (𝓝 f))
    (henergy : ∀ n, X n ⟨t, h0s.trans hst, htT⟩ - X n ⟨s, h0s, hst.trans htT⟩ ≤
      (∫ r in s..t, extendPath T hT a r * extendPath T hT (X n) r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT (Y n) r) +
      ∫ r in Icc s t, c r * F n r ∂timeMeasure T) :
    x ⟨t, h0s.trans hst, htT⟩ - x ⟨s, h0s, hst.trans htT⟩ ≤
      (∫ r in s..t, extendPath T hT a r * extendPath T hT x r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT y r) +
      ∫ r in Icc s t, c r * f r ∂timeMeasure T := by
  have ht := (continuous_eval_const (⟨t, h0s.trans hst, htT⟩ : Icc (0 : ℝ)
    T)).continuousAt.tendsto.comp hX
  have hs := (continuous_eval_const (⟨s, h0s, hst.trans htT⟩ : Icc (0 : ℝ)
    T)).continuousAt.tendsto.comp hX
  exact le_of_tendsto_of_tendsto' (ht.sub hs)
    (((subinterval_path_tendsto T hT s t h0s hst htT a X x hX).add
      (subinterval_path_tendsto T hT s t h0s hst htT b Y y hY)).add
      (subinterval_forcing_tendsto T s t c F f hF)) henergy

end EulerTimeLpSubinterval
