/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic

/-! # Limits for the scalar Obata gradient ODE

These are limits of function values. They do not assert convergence of
manifold-valued curves or uniqueness of the geometric poles.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology

namespace LichnerowiczObata

theorem monotone_obata_scalar {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {u : ℝ → ℝ} (hb : ∀ t, -a ≤ u t ∧ u t ≤ a)
    (hd : ∀ t, HasDerivAt u (K * (a ^ 2 - u t ^ 2)) t) : Monotone u := by
  apply monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  apply mul_nonneg hK.le
  nlinarith [(hb t).1, (hb t).2]

/-- A bounded complete solution starting above the lower equilibrium tends
to the upper equilibrium. -/
theorem tendsto_obata_scalar_atTop {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {u : ℝ → ℝ} (hb : ∀ t, -a ≤ u t ∧ u t ≤ a)
    (hd : ∀ t, HasDerivAt u (K * (a ^ 2 - u t ^ 2)) t)
    (h0 : -a < u 0) : Tendsto u atTop (𝓝 a) := by
  have hm := monotone_obata_scalar hK ha hb hd
  have hdiff : Differentiable ℝ u := fun t => (hd t).differentiableAt
  have hbounded : BddAbove (range u) := ⟨a, by rintro _ ⟨t, rfl⟩; exact (hb t).2⟩
  let L : ℝ := ⨆ t, u t
  have hle : ∀ t, u t ≤ L := fun t => le_ciSup hbounded t
  have hLa : L ≤ a := ciSup_le (fun t => (hb t).2)
  have hL : L = a := by
    by_contra hne
    have hlt : L < a := lt_of_le_of_ne hLa hne
    let c : ℝ := K * ((a - L) * (a + u 0))
    have hc : 0 < c := mul_pos hK (mul_pos (sub_pos.2 hlt) (by linarith))
    have hlower : ∀ t, 0 ≤ t → c ≤ deriv u t := by
      intro t ht
      rw [(hd t).deriv]
      calc
        c ≤ K * ((a - u t) * (a + u t)) := by
          dsimp [c]
          gcongr <;> nlinarith [hle t, hm ht, (hb t).1, (hb t).2]
        _ = K * (a ^ 2 - u t ^ 2) := by ring
    let T : ℝ := (a - u 0) / c + 1
    have hT : 0 ≤ T := by
      dsimp [T]
      have := div_nonneg (sub_nonneg.2 (hb 0).2) hc.le
      linarith
    have hg := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      hdiff.continuous.continuousOn hdiff.differentiableOn
      (fun t ht => hlower t (interior_subset ht))
      0 (by simp) T hT hT
    have hprod : c * T = a - u 0 + c := by
      dsimp [T]
      field_simp
    have hbound := (hb T).2
    simp only [sub_zero] at hg
    rw [hprod] at hg
    linarith
  simpa only [← hL] using tendsto_atTop_ciSup hm hbounded

/-- Reversing time and sign gives the lower limiting value. -/
theorem tendsto_obata_scalar_atBot {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {u : ℝ → ℝ} (hb : ∀ t, -a ≤ u t ∧ u t ≤ a)
    (hd : ∀ t, HasDerivAt u (K * (a ^ 2 - u t ^ 2)) t)
    (h0 : u 0 < a) : Tendsto u atBot (𝓝 (-a)) := by
  have hb' : ∀ t, -a ≤ -u (-t) ∧ -u (-t) ≤ a := by
    intro t
    have := hb (-t)
    constructor <;> linarith
  have hd' : ∀ t, HasDerivAt (fun s => -u (-s)) (K * (a ^ 2 - (-u (-t)) ^ 2)) t := by
    intro t
    simpa only [Function.comp_def, Pi.neg_def, neg_mul, mul_neg, mul_one, neg_neg, neg_sq]
      using ((hd (-t)).comp t (hasDerivAt_neg t)).neg
  have ht := tendsto_obata_scalar_atTop hK ha hb' hd' (by simpa using neg_lt_neg h0)
  simpa only [Function.comp_def, neg_neg] using ht.neg.comp tendsto_neg_atBot_atTop

/-- Every intermediate level is reached by a complete regular scalar solution. -/
theorem exists_time_obata_scalar {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {u : ℝ → ℝ} (hb : ∀ t, -a ≤ u t ∧ u t ≤ a)
    (hd : ∀ t, HasDerivAt u (K * (a ^ 2 - u t ^ 2)) t)
    (h0 : -a < u 0 ∧ u 0 < a) {b : ℝ} (hba : -a < b ∧ b < a) :
    ∃ t : ℝ, u t = b := by
  have htop := tendsto_obata_scalar_atTop hK ha hb hd h0.1
  have hbot := tendsto_obata_scalar_atBot hK ha hb hd h0.2
  have hupper : ∀ᶠ t in atTop, b < u t := htop (Ioi_mem_nhds hba.2)
  have hlower : ∀ᶠ t in atBot, u t < b := hbot (Iio_mem_nhds hba.1)
  obtain ⟨s, hs0, hs⟩ := ((eventually_le_atBot (0 : ℝ)).and hlower).exists
  obtain ⟨t, ht0, ht⟩ := ((eventually_ge_atTop (0 : ℝ)).and hupper).exists
  have hc : Continuous u := continuous_iff_continuousAt.2 (fun t => (hd t).continuousAt)
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc (hs0.trans ht0) hc.continuousOn ⟨hs.le, ht.le⟩
  exact ⟨z, he⟩

end LichnerowiczObata
