/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder

/-!
# Parabolic `C^{0,1}` membership of the model mild solution

The model heat-kernel theory in `HeatKernel1D.lean` proves, for the genuine mild solution `z`
(any fixed point of `heatMildSelfMap`), a full parabolic space-time regularity suite away from the
initial time `t₀`:

* spatial `C¹` (Lipschitz) modulus `lipschitzWith_heatMildFixedPoint_apply`, and
* time `Hölder-1/2` modulus `heatMildFixedPoint_apply_time_holder_bound`.

The parabolic Hölder framework in `ParabolicHolder.lean` packages both moduli into a single class:
`ParabolicC0AlphaOn 1` (parabolic-Lipschitz `C^{0,1}`) uses the parabolic distance
`max (√|Δt|) (dist x x')`, so a spatial-Lipschitz bound and a time-`Hölder-1/2` bound combine
exactly into the exponent-`1` parabolic Hölder estimate.

This module bridges the two files: on any interior parabolic slab `Icc t_lo T ×ˢ univ` with
`t₀ < t_lo`, the model mild solution belongs to `ParabolicC0AlphaOn 1`.  This is the canonical
parabolic Hölder-class membership that the Schauder / smooth-realization side of the Ricci–DeTurck
chart closure consumes (GAP 2 analytic core: the assembled space-time modulus in parabolic-class
form).  The uniform constants are obtained by bounding the interior-time coefficients over
`[t_lo, T]`.
-/

@[expose] public noncomputable section

open Real
open scoped Real NNReal Topology

namespace RicciFlow
namespace AnalyticPDE

/-- **Parabolic Hölder exponent lowering on a parabolic-bounded set.**  A parabolic-Lipschitz
(`ParabolicHolderWith C 1`) function on a set whose points are pairwise within parabolic distance
`D` is `ParabolicHolderWith (C · D^{1−α}) α` for every exponent `0 ≤ α ≤ 1`.  This is the standard
"Lipschitz ⟹ Hölder on a bounded set" downgrade in the parabolic metric: from
`‖u p − u q‖ ≤ C·parabolicDistance p q` and `parabolicDistance p q ≤ D`, split
`parabolicDistance p q = (parabolicDistance p q)^α · (parabolicDistance p q)^{1−α}` and bound the
second factor by `D^{1−α}`. -/
theorem ParabolicHolderWith.exponent_le_of_bounded
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    {C D α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (h : ParabolicHolderWith C 1 u s)
    (hbdd : ∀ p ∈ s, ∀ q ∈ s, parabolicDistance p q ≤ D)
    (hC : 0 ≤ C) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ParabolicHolderWith (C * D ^ (1 - α)) α u s := by
  intro p hp q hq
  have hpd_nonneg : 0 ≤ parabolicDistance p q := parabolicDistance.nonneg p q
  have hpd_le_D : parabolicDistance p q ≤ D := hbdd p hp q hq
  have hD_nonneg : 0 ≤ D := le_trans hpd_nonneg hpd_le_D
  have hkey : parabolicDistance p q ≤ D ^ (1 - α) * (parabolicDistance p q) ^ α := by
    rcases eq_or_lt_of_le hpd_nonneg with hpd0 | hpd_pos
    · calc parabolicDistance p q = 0 := hpd0.symm
        _ ≤ D ^ (1 - α) * (parabolicDistance p q) ^ α :=
            mul_nonneg (Real.rpow_nonneg hD_nonneg _) (Real.rpow_nonneg hpd_nonneg _)
    · have hsplit : parabolicDistance p q
          = (parabolicDistance p q) ^ α * (parabolicDistance p q) ^ (1 - α) := by
        rw [← Real.rpow_add hpd_pos, show α + (1 - α) = 1 by ring, Real.rpow_one]
      have hbound : (parabolicDistance p q) ^ (1 - α) ≤ D ^ (1 - α) :=
        Real.rpow_le_rpow hpd_nonneg hpd_le_D (by linarith)
      calc parabolicDistance p q
          = (parabolicDistance p q) ^ α * (parabolicDistance p q) ^ (1 - α) := hsplit
        _ ≤ (parabolicDistance p q) ^ α * D ^ (1 - α) :=
            mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hpd_nonneg _)
        _ = D ^ (1 - α) * (parabolicDistance p q) ^ α := by ring
  have h1 : ‖u p - u q‖ ≤ C * parabolicDistance p q := by
    have hh := h hp hq
    rwa [Real.rpow_one] at hh
  calc ‖u p - u q‖ ≤ C * parabolicDistance p q := h1
    _ ≤ C * (D ^ (1 - α) * (parabolicDistance p q) ^ α) := mul_le_mul_of_nonneg_left hkey hC
    _ = C * D ^ (1 - α) * (parabolicDistance p q) ^ α := by ring

/-- **Parabolic `C^{0,α}` from `C^{0,1}` on a parabolic-bounded set.**  On a set of parabolic
diameter `≤ D`, membership in the parabolic-Lipschitz class `ParabolicC0AlphaOn 1` implies membership
in `ParabolicC0AlphaOn α` for every `0 ≤ α ≤ 1` (the sup part is unchanged; the Hölder constant picks
up a `D^{1−α}` factor from `ParabolicHolderWith.exponent_le_of_bounded`). -/
theorem ParabolicC0AlphaOn.exponent_le_of_bounded
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    {D α : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)} (hD : 0 ≤ D)
    (h : ParabolicC0AlphaOn 1 u s)
    (hbdd : ∀ p ∈ s, ∀ q ∈ s, parabolicDistance p q ≤ D)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ParabolicC0AlphaOn α u s := by
  obtain ⟨B, hB, H, hH, hbounded, hholder⟩ := h
  exact ⟨B, hB, H * D ^ (1 - α), mul_nonneg hH (Real.rpow_nonneg hD _),
    hbounded, hholder.exponent_le_of_bounded hbdd hH hα0 hα1⟩

/-- **Parabolic `C^{0,1}` (parabolic-Lipschitz) membership of the model mild solution.**  For the
genuine model mild solution `z` (any fixed point of `heatMildSelfMap` for an `L`-Lipschitz initial
datum `u₀` and a `CQ`-bounded continuous reaction nonlinearity `Q`), on any interior parabolic slab
`Icc t_lo T ×ˢ univ` bounded away from the initial time (`t₀ < t_lo ≤ T`), the time-space function
`(t, x) ↦ z(t)(x)` (clamped in time by `Set.IccExtend`) belongs to the parabolic `C^{0,α}` class with
exponent `α = 1`.

The membership assembles the two interior regularity moduli of the mild solution into the parabolic
distance `parabolicDistance p q = max (√|Δt|) (dist x x')`:

* the spatial Lipschitz modulus `lipschitzWith_heatMildFixedPoint_apply` controls the `dist x x'`
  direction with a coefficient uniformly bounded over `[t_lo, T]` by
  `Ksp_max = n·‖u₀‖/√(π(t_lo−t₀)) + 2n·CQ·√(T−t₀)/√π`;
* the `Hölder-1/2` time modulus `heatMildFixedPoint_apply_time_holder_bound` controls the `√|Δt|`
  direction with a coefficient uniformly bounded over `[t_lo, T]` by `Ktm_coef` (the interior-time
  coefficients bounded by their endpoint values, absorbing the linear `|Δt|` term into `√|Δt|` via
  `|Δt| ≤ √(T−t_lo)·√|Δt|`).

The sup part is the a-priori bound `norm_heatMildFixedPoint_le` (`‖u₀‖ + CQ·(T − t₀)`). -/
theorem heatMildFixedPoint_parabolicC0AlphaOn {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T) :
    ParabolicC0AlphaOn 1
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2)
      (Set.Icc t_lo T ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
  have hCQ : 0 ≤ CQ := le_trans (norm_nonneg _) (hQb 0)
  have hlo_pos : 0 < t_lo - t₀ := by linarith
  have hsqrt_lo_pos : 0 < Real.sqrt (π * (t_lo - t₀)) :=
    Real.sqrt_pos.mpr (mul_pos Real.pi_pos hlo_pos)
  set Ksp_max : ℝ :=
    (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
      + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π with hKsp_def
  set Ktm_coef : ℝ :=
    (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
      + CQ * Real.sqrt (T - t_lo)
      + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) with hKtm_def
  set H : ℝ := Ksp_max + Ktm_coef with hH_def
  set B : ℝ := ‖u₀‖ + CQ * (T - t₀) with hB_def
  have hKsp_max_nonneg : 0 ≤ Ksp_max := by
    rw [hKsp_def]
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by positivity
    have h2 : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      rw [show 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
          = (2 * (n : ℝ) * Real.sqrt (T - t₀) / Real.sqrt π) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  have hKtm_coef_nonneg : 0 ≤ Ktm_coef := by
    rw [hKtm_def]
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π) := by
      positivity
    have h2 : 0 ≤ CQ * Real.sqrt (T - t_lo) := mul_nonneg hCQ (Real.sqrt_nonneg _)
    have h3 : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) := by
      rw [show 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀)
          = (4 * (n : ℝ) ^ 2 / π * Real.sqrt (T - t₀)) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  have hH_nonneg : 0 ≤ H := by rw [hH_def]; linarith
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]; exact add_nonneg (norm_nonneg _) (mul_nonneg hCQ (by linarith))
  -- Spatial Lipschitz modulus with a uniform interior constant.
  have hspace_le : ∀ (a : ℝ) (ha_mem : a ∈ Set.Icc t₀ T), t_lo ≤ a → a ≤ T →
      ∀ y y' : Fin n → ℝ, |z ⟨a, ha_mem⟩ y - z ⟨a, ha_mem⟩ y'| ≤ Ksp_max * dist y y' := by
    intro a ha_mem hla haT y y'
    have ht₀a : t₀ < a := lt_of_lt_of_le ht_lo hla
    have hlip_a : LipschitzWith
        (((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀)))).toNNReal
          + (2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π).toNNReal)
        (⇑(z ⟨a, ha_mem⟩)) :=
      lipschitzWith_heatMildFixedPoint_apply hT u₀ hLnn hlip Q hQcont hQb z hz
        (t := ⟨a, ha_mem⟩) ht₀a
    have hd := hlip_a.dist_le_mul y y'
    rw [Real.dist_eq] at hd
    refine le_trans hd (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    have hA_nonneg : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) := by positivity
    have hBc_nonneg : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π := by
      rw [show 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π
          = (2 * (n : ℝ) * Real.sqrt (a - t₀) / Real.sqrt π) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    rw [NNReal.coe_add, Real.coe_toNNReal _ hA_nonneg, Real.coe_toNNReal _ hBc_nonneg, hKsp_def]
    have hA_le : (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀)))
        ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (norm_nonneg _) hsqrt_lo_pos
        (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
    have hB_le : 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π
        ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have h2nCQ : 0 ≤ 2 * (n : ℝ) * CQ := by
        rw [show 2 * (n : ℝ) * CQ = (2 * (n : ℝ)) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) h2nCQ
    linarith
  -- Time `Hölder-1/2` modulus with a uniform interior coefficient.
  have htime_le : ∀ (a b : ℝ) (ha_mem : a ∈ Set.Icc t₀ T) (hb_mem : b ∈ Set.Icc t₀ T),
      t_lo ≤ a → b ≤ T → a < b → ∀ y : Fin n → ℝ,
      |z ⟨b, hb_mem⟩ y - z ⟨a, ha_mem⟩ y| ≤ Ktm_coef * Real.sqrt (b - a) := by
    intro a b ha_mem hb_mem hla hbT hab y
    have ht₀a : t₀ < a := lt_of_lt_of_le ht_lo hla
    have hba_nonneg : 0 ≤ b - a := by linarith
    have hmod : |z ⟨b, hb_mem⟩ y - z ⟨a, ha_mem⟩ y| ≤
        (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) * (n : ℝ)
            * (2 / Real.sqrt π * Real.sqrt (b - a))
          + (CQ * (b - a)
              + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (a - t₀) * Real.sqrt (b - a)) :=
      heatMildFixedPoint_apply_time_holder_bound hT u₀ hLnn hlip Q hQcont hQb z hz
        (t₁ := ⟨a, ha_mem⟩) (t₂ := ⟨b, hb_mem⟩) ht₀a hab y
    refine le_trans hmod ?_
    have hsqrt_ba_le : Real.sqrt (b - a) ≤ Real.sqrt (T - t_lo) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt_a_le : Real.sqrt (a - t₀) ≤ Real.sqrt (T - t₀) :=
      Real.sqrt_le_sqrt (by linarith)
    have hB1 : (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) * (n : ℝ)
          * (2 / Real.sqrt π * Real.sqrt (b - a))
        ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
          * (2 / Real.sqrt π * Real.sqrt (b - a)) := by
      have hdiv : ‖u₀‖ / Real.sqrt (π * (a - t₀)) ≤ ‖u₀‖ / Real.sqrt (π * (t_lo - t₀)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hsqrt_lo_pos
          (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
      have hcoef : 0 ≤ (n : ℝ) * (n : ℝ) * (2 / Real.sqrt π * Real.sqrt (b - a)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdiv hcoef]
    have hB2a : CQ * (b - a) ≤ CQ * Real.sqrt (T - t_lo) * Real.sqrt (b - a) := by
      have h1 : CQ * Real.sqrt (b - a) ≤ CQ * Real.sqrt (T - t_lo) :=
        mul_le_mul_of_nonneg_left hsqrt_ba_le hCQ
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (b - a))
      rwa [mul_assoc CQ (Real.sqrt (b - a)) (Real.sqrt (b - a)), Real.mul_self_sqrt hba_nonneg] at h2
    have hB2b : 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (a - t₀) * Real.sqrt (b - a)
        ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) * Real.sqrt (b - a) := by
      have hc : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π := by
        rw [show 4 * (n : ℝ) ^ 2 * CQ / π = (4 * (n : ℝ) ^ 2 / π) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      have h1 := mul_le_mul_of_nonneg_left hsqrt_a_le hc
      exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (b - a))
    have hEq : Ktm_coef * Real.sqrt (b - a)
        = (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
            * (2 / Real.sqrt π * Real.sqrt (b - a))
          + CQ * Real.sqrt (T - t_lo) * Real.sqrt (b - a)
          + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) * Real.sqrt (b - a) := by
      rw [hKtm_def]; ring
    rw [hEq]
    linarith [hB1, hB2a, hB2b]
  -- Assemble the parabolic `C^{0,1}` class membership.
  refine ⟨B, hB_nonneg, H, hH_nonneg, ?_, ?_⟩
  · -- Sup (`C^0`) part.
    intro p hp
    rw [Set.mem_prod, Set.mem_Icc] at hp
    obtain ⟨⟨hlo_p, hhi_p⟩, -⟩ := hp
    have hp_mem : p.1 ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_p), hhi_p⟩
    show ‖Set.IccExtend hT (⇑z) p.1 p.2‖ ≤ B
    rw [Set.IccExtend_of_mem hT (⇑z) hp_mem, hB_def]
    exact le_trans ((z ⟨p.1, hp_mem⟩).norm_coe_le_norm p.2)
      (le_trans (z.norm_coe_le_norm ⟨p.1, hp_mem⟩)
        (norm_heatMildFixedPoint_le hT u₀ hLnn hlip Q hQcont hQb z hz))
  · -- Parabolic Hölder (exponent `1`) part.
    intro p hp q hq
    obtain ⟨t, x⟩ := p
    obtain ⟨t', x'⟩ := q
    rw [Set.mem_prod, Set.mem_Icc] at hp hq
    obtain ⟨⟨hlo_t, hhi_t⟩, -⟩ := hp
    obtain ⟨⟨hlo_t', hhi_t'⟩, -⟩ := hq
    have ht_mem : t ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_t), hhi_t⟩
    have ht'_mem : t' ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_t'), hhi_t'⟩
    show ‖Set.IccExtend hT (⇑z) t x - Set.IccExtend hT (⇑z) t' x'‖
      ≤ H * (parabolicDistance (t, x) (t', x')) ^ (1 : ℝ)
    rw [Set.IccExtend_of_mem hT (⇑z) ht_mem, Set.IccExtend_of_mem hT (⇑z) ht'_mem,
      Real.norm_eq_abs, Real.rpow_one]
    have hspace : |z ⟨t, ht_mem⟩ x - z ⟨t, ht_mem⟩ x'| ≤ Ksp_max * dist x x' :=
      hspace_le t ht_mem hlo_t hhi_t x x'
    have htime : |z ⟨t, ht_mem⟩ x' - z ⟨t', ht'_mem⟩ x'|
        ≤ Ktm_coef * Real.sqrt |t - t'| := by
      rcases lt_trichotomy t t' with h | h | h
      · have hle := htime_le t t' ht_mem ht'_mem hlo_t hhi_t' h x'
        rw [abs_sub_comm, show |t - t'| = t' - t by rw [abs_of_neg (by linarith)]; ring]
        exact hle
      · subst h
        simp
      · have hle := htime_le t' t ht'_mem ht_mem hlo_t' hhi_t h x'
        rw [show |t - t'| = t - t' by rw [abs_of_pos (by linarith)]]
        exact hle
    calc |z ⟨t, ht_mem⟩ x - z ⟨t', ht'_mem⟩ x'|
        ≤ |z ⟨t, ht_mem⟩ x - z ⟨t, ht_mem⟩ x'| + |z ⟨t, ht_mem⟩ x' - z ⟨t', ht'_mem⟩ x'| :=
          abs_sub_le _ _ _
      _ ≤ Ksp_max * dist x x' + Ktm_coef * Real.sqrt |t - t'| := add_le_add hspace htime
      _ ≤ Ksp_max * parabolicDistance (t, x) (t', x')
            + Ktm_coef * parabolicDistance (t, x) (t', x') := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (parabolicDistance.space_dist_le (t, x) (t', x')) hKsp_max_nonneg
          · exact mul_le_mul_of_nonneg_left
              (parabolicDistance.sqrt_time_le (t, x) (t', x')) hKtm_coef_nonneg
      _ = H * parabolicDistance (t, x) (t', x') := by rw [hH_def]; ring

/-- **Parabolic `C^{0,α}` membership of the model mild solution on a parabolic-bounded interior
subset.**  Combining the parabolic-Lipschitz slab membership `heatMildFixedPoint_parabolicC0AlphaOn`
with the exponent-lowering `ParabolicC0AlphaOn.exponent_le_of_bounded`: on any subset `s` of the
interior slab `Icc t_lo T ×ˢ univ` (`t₀ < t_lo ≤ T`) of parabolic diameter `≤ D`, the model mild
solution belongs to the parabolic `C^{0,α}` class for every `0 ≤ α ≤ 1`.  This is the Hölder-exponent
form (`α ∈ (0,1)`) of the mild-solution regularity that the parabolic Schauder / smooth-realization
side consumes on local parabolic cylinders. -/
theorem heatMildFixedPoint_parabolicC0AlphaOn_of_bounded {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T)
    {s : Set (ℝ × (Fin n → ℝ))} {D : ℝ} (hD : 0 ≤ D)
    (hsub : s ⊆ Set.Icc t_lo T ×ˢ (Set.univ : Set (Fin n → ℝ)))
    (hbdd : ∀ p ∈ s, ∀ q ∈ s, parabolicDistance p q ≤ D)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ParabolicC0AlphaOn α
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2) s :=
  ((heatMildFixedPoint_parabolicC0AlphaOn hT u₀ hLnn hlip Q hQcont hQb z hz ht_lo ht_loT).mono_set
    hsub).exponent_le_of_bounded hD hbdd hα0 hα1

/-- **Parabolic `C^{0,α}` membership of the model mild solution on an interior parabolic closed
ball.**  Specialisation of `heatMildFixedPoint_parabolicC0AlphaOn_of_bounded` to a concrete
`parabolicClosedBall c R` whose full time-extent `[c.1 − R², c.1 + R²]` lies in the interior
`[t_lo, T]` (`t₀ < t_lo`).  The ball is contained in the interior slab (its time coordinate is pinned
by `time_abs_le_sq_of_mem`) and has parabolic diameter `≤ 2R` (triangle inequality through the
centre), so the mild solution is parabolic `C^{0,α}` on it for every `0 ≤ α ≤ 1`.  This is the
ball-localised regularity datum consumed by the parabolic Schauder local-to-global gluing
(`ParabolicC0AlphaOn.of_parabolicBall_cover_closedBall` and companions). -/
theorem heatMildFixedPoint_parabolicC0AlphaOn_closedBall {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T)
    (c : ℝ × (Fin n → ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hlo : t_lo ≤ c.1 - R ^ 2) (hhi : c.1 + R ^ 2 ≤ T)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ParabolicC0AlphaOn α
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2) (parabolicClosedBall c R) := by
  refine heatMildFixedPoint_parabolicC0AlphaOn_of_bounded hT u₀ hLnn hlip Q hQcont hQb z hz
    ht_lo ht_loT (D := 2 * R) (by linarith) ?_ ?_ hα0 hα1
  · intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    rw [Set.mem_Icc]
    have htime := parabolicClosedBall.time_abs_le_sq_of_mem hR hp
    have h2 := abs_le.mp htime
    constructor <;> linarith [h2.1, h2.2]
  · intro p hp q hq
    have hpc : parabolicDistance p c ≤ R := by
      rw [parabolicDistance.comm]; exact hp
    calc parabolicDistance p q
        ≤ parabolicDistance p c + parabolicDistance c q := parabolicDistance.triangle p c q
      _ ≤ R + R := add_le_add hpc hq
      _ = 2 * R := by ring

/-- **Explicit parabolic sup bound of the model mild solution.**  The `C^0` part of the parabolic
`C^{0,α}` norm package with an *explicit* constant: the (time-clamped) model mild solution
`(t, x) ↦ z(t)(x)` is uniformly bounded by `‖u₀‖ + CQ·(T − t₀)` on *every* time-space set `s`
(the a-priori sup bound `norm_heatMildFixedPoint_le` holds globally and `Set.IccExtend` only clamps
the time argument into `[t₀, T]`).  Unlike the existential `ParabolicC0AlphaOn` membership, this
exposes the concrete constant the parabolic Schauder fixed-point a-priori estimate consumes. -/
theorem heatMildFixedPoint_parabolicBoundedWith {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    (s : Set (ℝ × (Fin n → ℝ))) :
    ParabolicBoundedWith (‖u₀‖ + CQ * (T - t₀))
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2) s := by
  intro p _hp
  calc ‖Set.IccExtend hT (⇑z) p.1 p.2‖
      ≤ ‖Set.IccExtend hT (⇑z) p.1‖ :=
        (Set.IccExtend hT (⇑z) p.1).norm_coe_le_norm p.2
    _ = ‖(⇑z) (Set.projIcc t₀ T hT p.1)‖ := rfl
    _ ≤ ‖z‖ := z.norm_coe_le_norm _
    _ ≤ ‖u₀‖ + CQ * (T - t₀) :=
        norm_heatMildFixedPoint_le hT u₀ hLnn hlip Q hQcont hQb z hz

/-- **Explicit parabolic sup-norm bound of the model mild solution.**  The parabolic sup-norm
functional of the (time-clamped) model mild solution is bounded by the explicit a-priori constant
`‖u₀‖ + CQ·(T − t₀)` on every time-space set.  Immediate from
`heatMildFixedPoint_parabolicBoundedWith` and `parabolicSupNorm_le`. -/
theorem heatMildFixedPoint_parabolicSupNorm_le {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    (s : Set (ℝ × (Fin n → ℝ))) :
    parabolicSupNorm (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2) s
      ≤ ‖u₀‖ + CQ * (T - t₀) := by
  have hCQ : 0 ≤ CQ := le_trans (norm_nonneg _) (hQb 0)
  have hB_nonneg : (0 : ℝ) ≤ ‖u₀‖ + CQ * (T - t₀) :=
    add_nonneg (norm_nonneg _) (mul_nonneg hCQ (by linarith))
  exact parabolicSupNorm_le hB_nonneg
    (heatMildFixedPoint_parabolicBoundedWith hT u₀ hLnn hlip Q hQcont hQb z hz s)

/-- **Explicit parabolic Hölder-`1` (parabolic-Lipschitz) modulus of the model mild solution.**
The parabolic Hölder part of the `C^{0,1}` package with the *explicit* interior constant
`Ksp_max + Ktm_coef` (the same coefficients as in `heatMildFixedPoint_parabolicC0AlphaOn`, but now
exposed rather than hidden behind the existential `ParabolicC0AlphaOn`).  On the interior slab
`Icc t_lo T ×ˢ univ` (`t₀ < t_lo ≤ T`) the (time-clamped) model mild solution satisfies the parabolic
Hölder estimate with exponent `1` and this concrete constant.  This is the quantitative Hölder-seminorm
datum the parabolic Schauder fixed-point contraction consumes (explicit constants are needed for the
a-priori norm bounds, which the existential class membership does not supply). -/
theorem heatMildFixedPoint_parabolicHolderWith {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T) :
    ParabolicHolderWith
      ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
          + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
        + ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
          + CQ * Real.sqrt (T - t_lo)
          + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀))) 1
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2)
      (Set.Icc t_lo T ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
  have hCQ : 0 ≤ CQ := le_trans (norm_nonneg _) (hQb 0)
  have hlo_pos : 0 < t_lo - t₀ := by linarith
  have hsqrt_lo_pos : 0 < Real.sqrt (π * (t_lo - t₀)) :=
    Real.sqrt_pos.mpr (mul_pos Real.pi_pos hlo_pos)
  set Ksp_max : ℝ :=
    (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
      + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π with hKsp_def
  set Ktm_coef : ℝ :=
    (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
      + CQ * Real.sqrt (T - t_lo)
      + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) with hKtm_def
  set H : ℝ := Ksp_max + Ktm_coef with hH_def
  have hKsp_max_nonneg : 0 ≤ Ksp_max := by
    rw [hKsp_def]
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by positivity
    have h2 : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      rw [show 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
          = (2 * (n : ℝ) * Real.sqrt (T - t₀) / Real.sqrt π) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  have hKtm_coef_nonneg : 0 ≤ Ktm_coef := by
    rw [hKtm_def]
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π) := by
      positivity
    have h2 : 0 ≤ CQ * Real.sqrt (T - t_lo) := mul_nonneg hCQ (Real.sqrt_nonneg _)
    have h3 : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) := by
      rw [show 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀)
          = (4 * (n : ℝ) ^ 2 / π * Real.sqrt (T - t₀)) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  -- Spatial Lipschitz modulus with a uniform interior constant.
  have hspace_le : ∀ (a : ℝ) (ha_mem : a ∈ Set.Icc t₀ T), t_lo ≤ a → a ≤ T →
      ∀ y y' : Fin n → ℝ, |z ⟨a, ha_mem⟩ y - z ⟨a, ha_mem⟩ y'| ≤ Ksp_max * dist y y' := by
    intro a ha_mem hla haT y y'
    have ht₀a : t₀ < a := lt_of_lt_of_le ht_lo hla
    have hlip_a : LipschitzWith
        (((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀)))).toNNReal
          + (2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π).toNNReal)
        (⇑(z ⟨a, ha_mem⟩)) :=
      lipschitzWith_heatMildFixedPoint_apply hT u₀ hLnn hlip Q hQcont hQb z hz
        (t := ⟨a, ha_mem⟩) ht₀a
    have hd := hlip_a.dist_le_mul y y'
    rw [Real.dist_eq] at hd
    refine le_trans hd (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    have hA_nonneg : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) := by positivity
    have hBc_nonneg : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π := by
      rw [show 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π
          = (2 * (n : ℝ) * Real.sqrt (a - t₀) / Real.sqrt π) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    rw [NNReal.coe_add, Real.coe_toNNReal _ hA_nonneg, Real.coe_toNNReal _ hBc_nonneg, hKsp_def]
    have hA_le : (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀)))
        ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (norm_nonneg _) hsqrt_lo_pos
        (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
    have hB_le : 2 * (n : ℝ) * CQ * Real.sqrt (a - t₀) / Real.sqrt π
        ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have h2nCQ : 0 ≤ 2 * (n : ℝ) * CQ := by
        rw [show 2 * (n : ℝ) * CQ = (2 * (n : ℝ)) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) h2nCQ
    linarith
  -- Time `Hölder-1/2` modulus with a uniform interior coefficient.
  have htime_le : ∀ (a b : ℝ) (ha_mem : a ∈ Set.Icc t₀ T) (hb_mem : b ∈ Set.Icc t₀ T),
      t_lo ≤ a → b ≤ T → a < b → ∀ y : Fin n → ℝ,
      |z ⟨b, hb_mem⟩ y - z ⟨a, ha_mem⟩ y| ≤ Ktm_coef * Real.sqrt (b - a) := by
    intro a b ha_mem hb_mem hla hbT hab y
    have ht₀a : t₀ < a := lt_of_lt_of_le ht_lo hla
    have hba_nonneg : 0 ≤ b - a := by linarith
    have hmod : |z ⟨b, hb_mem⟩ y - z ⟨a, ha_mem⟩ y| ≤
        (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) * (n : ℝ)
            * (2 / Real.sqrt π * Real.sqrt (b - a))
          + (CQ * (b - a)
              + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (a - t₀) * Real.sqrt (b - a)) :=
      heatMildFixedPoint_apply_time_holder_bound hT u₀ hLnn hlip Q hQcont hQb z hz
        (t₁ := ⟨a, ha_mem⟩) (t₂ := ⟨b, hb_mem⟩) ht₀a hab y
    refine le_trans hmod ?_
    have hsqrt_ba_le : Real.sqrt (b - a) ≤ Real.sqrt (T - t_lo) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt_a_le : Real.sqrt (a - t₀) ≤ Real.sqrt (T - t₀) :=
      Real.sqrt_le_sqrt (by linarith)
    have hB1 : (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (a - t₀))) * (n : ℝ)
          * (2 / Real.sqrt π * Real.sqrt (b - a))
        ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
          * (2 / Real.sqrt π * Real.sqrt (b - a)) := by
      have hdiv : ‖u₀‖ / Real.sqrt (π * (a - t₀)) ≤ ‖u₀‖ / Real.sqrt (π * (t_lo - t₀)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hsqrt_lo_pos
          (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
      have hcoef : 0 ≤ (n : ℝ) * (n : ℝ) * (2 / Real.sqrt π * Real.sqrt (b - a)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdiv hcoef]
    have hB2a : CQ * (b - a) ≤ CQ * Real.sqrt (T - t_lo) * Real.sqrt (b - a) := by
      have h1 : CQ * Real.sqrt (b - a) ≤ CQ * Real.sqrt (T - t_lo) :=
        mul_le_mul_of_nonneg_left hsqrt_ba_le hCQ
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (b - a))
      rwa [mul_assoc CQ (Real.sqrt (b - a)) (Real.sqrt (b - a)), Real.mul_self_sqrt hba_nonneg] at h2
    have hB2b : 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (a - t₀) * Real.sqrt (b - a)
        ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) * Real.sqrt (b - a) := by
      have hc : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π := by
        rw [show 4 * (n : ℝ) ^ 2 * CQ / π = (4 * (n : ℝ) ^ 2 / π) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      have h1 := mul_le_mul_of_nonneg_left hsqrt_a_le hc
      exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (b - a))
    have hEq : Ktm_coef * Real.sqrt (b - a)
        = (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
            * (2 / Real.sqrt π * Real.sqrt (b - a))
          + CQ * Real.sqrt (T - t_lo) * Real.sqrt (b - a)
          + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) * Real.sqrt (b - a) := by
      rw [hKtm_def]; ring
    rw [hEq]
    linarith [hB1, hB2a, hB2b]
  -- Parabolic Hölder (exponent `1`) estimate.
  intro p hp q hq
  obtain ⟨t, x⟩ := p
  obtain ⟨t', x'⟩ := q
  rw [Set.mem_prod, Set.mem_Icc] at hp hq
  obtain ⟨⟨hlo_t, hhi_t⟩, -⟩ := hp
  obtain ⟨⟨hlo_t', hhi_t'⟩, -⟩ := hq
  have ht_mem : t ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_t), hhi_t⟩
  have ht'_mem : t' ∈ Set.Icc t₀ T := ⟨le_of_lt (lt_of_lt_of_le ht_lo hlo_t'), hhi_t'⟩
  show ‖Set.IccExtend hT (⇑z) t x - Set.IccExtend hT (⇑z) t' x'‖
    ≤ H * (parabolicDistance (t, x) (t', x')) ^ (1 : ℝ)
  rw [Set.IccExtend_of_mem hT (⇑z) ht_mem, Set.IccExtend_of_mem hT (⇑z) ht'_mem,
    Real.norm_eq_abs, Real.rpow_one]
  have hspace : |z ⟨t, ht_mem⟩ x - z ⟨t, ht_mem⟩ x'| ≤ Ksp_max * dist x x' :=
    hspace_le t ht_mem hlo_t hhi_t x x'
  have htime : |z ⟨t, ht_mem⟩ x' - z ⟨t', ht'_mem⟩ x'|
      ≤ Ktm_coef * Real.sqrt |t - t'| := by
    rcases lt_trichotomy t t' with h | h | h
    · have hle := htime_le t t' ht_mem ht'_mem hlo_t hhi_t' h x'
      rw [abs_sub_comm, show |t - t'| = t' - t by rw [abs_of_neg (by linarith)]; ring]
      exact hle
    · subst h
      simp
    · have hle := htime_le t' t ht'_mem ht_mem hlo_t' hhi_t h x'
      rw [show |t - t'| = t - t' by rw [abs_of_pos (by linarith)]]
      exact hle
  calc |z ⟨t, ht_mem⟩ x - z ⟨t', ht'_mem⟩ x'|
      ≤ |z ⟨t, ht_mem⟩ x - z ⟨t, ht_mem⟩ x'| + |z ⟨t, ht_mem⟩ x' - z ⟨t', ht'_mem⟩ x'| :=
        abs_sub_le _ _ _
    _ ≤ Ksp_max * dist x x' + Ktm_coef * Real.sqrt |t - t'| := add_le_add hspace htime
    _ ≤ Ksp_max * parabolicDistance (t, x) (t', x')
          + Ktm_coef * parabolicDistance (t, x) (t', x') := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (parabolicDistance.space_dist_le (t, x) (t', x')) hKsp_max_nonneg
        · exact mul_le_mul_of_nonneg_left
            (parabolicDistance.sqrt_time_le (t, x) (t', x')) hKtm_coef_nonneg
    _ = H * parabolicDistance (t, x) (t', x') := by rw [hH_def]; ring

/-- **Explicit parabolic `C^{0,1}` norm bound of the model mild solution.**  Assembles the explicit
sup bound `heatMildFixedPoint_parabolicSupNorm_le` and the explicit parabolic Hölder-`1` modulus
`heatMildFixedPoint_parabolicHolderWith` into a concrete upper bound on the honest parabolic
`C^{0,1}` norm functional `parabolicC0AlphaNorm 1` of the (time-clamped) model mild solution on the
interior slab `Icc t_lo T ×ˢ univ`.  The bound is `B + (Ksp_max + Ktm_coef)` with `B = ‖u₀‖ + CQ·(T−t₀)`
the a-priori sup constant and `Ksp_max + Ktm_coef` the interior parabolic-Lipschitz constant.  This is
the quantitative Hölder-space norm control (rather than mere existential class membership) that the
parabolic Schauder fixed-point iteration and its contraction estimates consume. -/
theorem heatMildFixedPoint_parabolicC0AlphaNorm_le {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T) :
    parabolicC0AlphaNorm 1
        (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2)
        (Set.Icc t_lo T ×ˢ (Set.univ : Set (Fin n → ℝ)))
      ≤ (‖u₀‖ + CQ * (T - t₀))
        + ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
            + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
          + ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
            + CQ * Real.sqrt (T - t_lo)
            + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀))) := by
  have hCQ : 0 ≤ CQ := le_trans (norm_nonneg _) (hQb 0)
  have hKsp_nonneg : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
      + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by positivity
    have h2 : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      rw [show 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
          = (2 * (n : ℝ) * Real.sqrt (T - t₀) / Real.sqrt π) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  have hKtm_nonneg : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
        * (2 / Real.sqrt π)
      + CQ * Real.sqrt (T - t_lo)
      + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) := by
    have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π) := by
      positivity
    have h2 : 0 ≤ CQ * Real.sqrt (T - t_lo) := mul_nonneg hCQ (Real.sqrt_nonneg _)
    have h3 : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) := by
      rw [show 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀)
          = (4 * (n : ℝ) ^ 2 / π * Real.sqrt (T - t₀)) * CQ by ring]
      exact mul_nonneg (by positivity) hCQ
    linarith
  unfold parabolicC0AlphaNorm
  exact add_le_add
    (heatMildFixedPoint_parabolicSupNorm_le hT u₀ hLnn hlip Q hQcont hQb z hz _)
    (parabolicHolderSeminorm_le (add_nonneg hKsp_nonneg hKtm_nonneg)
      (heatMildFixedPoint_parabolicHolderWith hT u₀ hLnn hlip Q hQcont hQb z hz ht_lo ht_loT))

/-- **Explicit parabolic `C^{0,1}` class membership of the model mild solution.**  The
explicit-constant companion of the existential `heatMildFixedPoint_parabolicC0AlphaOn`: on the interior
slab the (time-clamped) model mild solution satisfies the parabolic `C^{0,1}` control with the concrete
sup constant `‖u₀‖ + CQ·(T−t₀)` and the concrete parabolic-Lipschitz constant `Ksp_max + Ktm_coef`,
packaged as `ParabolicC0AlphaWith`.  Immediate from `heatMildFixedPoint_parabolicBoundedWith` and
`heatMildFixedPoint_parabolicHolderWith`; this is the form whose constants the parabolic Schauder
iteration reads off directly. -/
theorem heatMildFixedPoint_parabolicC0AlphaWith {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T) :
    ParabolicC0AlphaWith (‖u₀‖ + CQ * (T - t₀))
      ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
          + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
        + ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
          + CQ * Real.sqrt (T - t_lo)
          + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀))) 1
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2)
      (Set.Icc t_lo T ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
  ⟨heatMildFixedPoint_parabolicBoundedWith hT u₀ hLnn hlip Q hQcont hQb z hz _,
    heatMildFixedPoint_parabolicHolderWith hT u₀ hLnn hlip Q hQcont hQb z hz ht_lo ht_loT⟩

/-- **Explicit parabolic `C^{0,α}` norm bound of the model mild solution on an interior parabolic
closed ball.**  The Schauder-local (general-exponent) quantitative form: on a `parabolicClosedBall c R`
whose full time-extent `[c.1 − R², c.1 + R²]` lies in the interior `[t_lo, T]` (`t₀ < t_lo`), the honest
parabolic `C^{0,α}` norm functional of the model mild solution is bounded, for every `0 ≤ α ≤ 1`, by
`B + (Ksp_max + Ktm_coef)·(2R)^{1−α}`, with `B = ‖u₀‖ + CQ·(T−t₀)` the a-priori sup constant.  The
sup part is `heatMildFixedPoint_parabolicSupNorm_le`; the Hölder-`α` part restricts the interior-slab
Hölder-`1` modulus `heatMildFixedPoint_parabolicHolderWith` to the ball (which is inside the slab, its
time coordinate pinned by `time_abs_le_sq_of_mem`) and downgrades the exponent by
`ParabolicHolderWith.exponent_le_of_bounded` on the ball of parabolic diameter `≤ 2R`.  This is the
explicit-constant, ball-localised, general-`α` Hölder-space norm control the parabolic Schauder
local-to-global gluing and interior fixed-point iteration consume. -/
theorem heatMildFixedPoint_parabolicC0AlphaNorm_closedBall_le {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ) {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ L * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    (z : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLnn hlip Q hQcont hQb z = z)
    {t_lo : ℝ} (ht_lo : t₀ < t_lo) (ht_loT : t_lo ≤ T)
    (c : ℝ × (Fin n → ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hlo : t_lo ≤ c.1 - R ^ 2) (hhi : c.1 + R ^ 2 ≤ T)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    parabolicC0AlphaNorm α
        (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2)
        (parabolicClosedBall c R)
      ≤ (‖u₀‖ + CQ * (T - t₀))
        + ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
            + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
          + ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
            + CQ * Real.sqrt (T - t_lo)
            + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀))) * (2 * R) ^ (1 - α) := by
  have hCQ : 0 ≤ CQ := le_trans (norm_nonneg _) (hQb 0)
  set Hslab : ℝ :=
    (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
        + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
      + ((n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π)
        + CQ * Real.sqrt (T - t_lo)
        + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀)) with hHslab_def
  have hHslab_nonneg : 0 ≤ Hslab := by
    rw [hHslab_def]
    have hKsp_nonneg : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀)))
        + 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
      have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) := by positivity
      have h2 : 0 ≤ 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π := by
        rw [show 2 * (n : ℝ) * CQ * Real.sqrt (T - t₀) / Real.sqrt π
            = (2 * (n : ℝ) * Real.sqrt (T - t₀) / Real.sqrt π) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      linarith
    have hKtm_nonneg : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ)
          * (2 / Real.sqrt π)
        + CQ * Real.sqrt (T - t_lo)
        + 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) := by
      have h1 : 0 ≤ (n : ℝ) * (‖u₀‖ / Real.sqrt (π * (t_lo - t₀))) * (n : ℝ) * (2 / Real.sqrt π) := by
        positivity
      have h2 : 0 ≤ CQ * Real.sqrt (T - t_lo) := mul_nonneg hCQ (Real.sqrt_nonneg _)
      have h3 : 0 ≤ 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀) := by
        rw [show 4 * (n : ℝ) ^ 2 * CQ / π * Real.sqrt (T - t₀)
            = (4 * (n : ℝ) ^ 2 / π * Real.sqrt (T - t₀)) * CQ by ring]
        exact mul_nonneg (by positivity) hCQ
      linarith
    linarith
  have h2R_nonneg : (0 : ℝ) ≤ 2 * R := mul_nonneg (by norm_num) hR
  have hsub : parabolicClosedBall c R
      ⊆ Set.Icc t_lo T ×ˢ (Set.univ : Set (Fin n → ℝ)) := by
    intro p hp
    refine ⟨?_, Set.mem_univ _⟩
    rw [Set.mem_Icc]
    have htime := parabolicClosedBall.time_abs_le_sq_of_mem hR hp
    have h2 := abs_le.mp htime
    constructor <;> linarith [h2.1, h2.2]
  have hdiam : ∀ p ∈ parabolicClosedBall c R, ∀ q ∈ parabolicClosedBall c R,
      parabolicDistance p q ≤ 2 * R := by
    intro p hp q hq
    have hpc : parabolicDistance p c ≤ R := by
      rw [parabolicDistance.comm]; exact hp
    calc parabolicDistance p q
        ≤ parabolicDistance p c + parabolicDistance c q := parabolicDistance.triangle p c q
      _ ≤ R + R := add_le_add hpc hq
      _ = 2 * R := by ring
  have hHball : ParabolicHolderWith Hslab 1
      (fun p : ℝ × (Fin n → ℝ) => Set.IccExtend hT (⇑z) p.1 p.2)
      (parabolicClosedBall c R) := by
    rw [hHslab_def]
    intro p hp q hq
    exact heatMildFixedPoint_parabolicHolderWith hT u₀ hLnn hlip Q hQcont hQb z hz
      ht_lo ht_loT (hsub hp) (hsub hq)
  have hHball_alpha := hHball.exponent_le_of_bounded hdiam hHslab_nonneg hα0 hα1
  unfold parabolicC0AlphaNorm
  exact add_le_add
    (heatMildFixedPoint_parabolicSupNorm_le hT u₀ hLnn hlip Q hQcont hQb z hz _)
    (parabolicHolderSeminorm_le (mul_nonneg hHslab_nonneg (Real.rpow_nonneg h2R_nonneg _))
      hHball_alpha)

/-- **Explicit parabolic sup-norm data-difference contraction of the model mild solution.**  The
`C^0` (sup) half of the parabolic Schauder *contraction* on differences of genuine mild solutions:
for two model mild solutions `z, w` (fixed points of `heatMildSelfMap` for the *same* reaction `Q`,
initial data `u₀, v₀`), the parabolic sup-norm of the (time-clamped) *difference* is bounded by the
*initial-data* difference on every time-space set:
`parabolicSupNorm (z − w) s ≤ ‖u₀ − v₀‖/(1 − Kstate(T − t₀))`.
Pointwise, the clamped difference `z(projIcc t)(x) − w(projIcc t)(x)` is bounded in absolute value by
the state-space distance `‖z − w‖ = dist z w`, which the reaction-Lipschitz Banach fixed-point
stability `dist_heatMildFixedPoint_le` controls by the data difference.  This packages the abstract
data-stability contraction into the parabolic Hölder framework: the explicit `parabolicSupNorm`
a-priori constant a parabolic Schauder interior fixed-point iteration reads for the `C^0` part of its
contraction estimate (the parabolic-Hölder-seminorm part of the contraction being carried by
`heatMildFixedPoint_sub_spatial_holder_bound` in the spatial directions). -/
theorem heatMildFixedPoint_parabolicSupNorm_sub_le {n : ℕ} {t₀ T : ℝ} (hT : t₀ ≤ T)
    (u₀ v₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {Lu : ℝ} (hLunn : 0 ≤ Lu) (hulip : ∀ a b : Fin n → ℝ, |u₀ a - u₀ b| ≤ Lu * ‖a - b‖)
    {Lv : ℝ} (hLvnn : 0 ≤ Lv) (hvlip : ∀ a b : Fin n → ℝ, |v₀ a - v₀ b| ≤ Lv * ‖a - b‖)
    (Q : BoundedContinuousFunction (Fin n → ℝ) ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hQcont : Continuous Q) {CQ : ℝ} (hQb : ∀ v, ‖Q v‖ ≤ CQ)
    {Kstate : ℝ} (hKnn : 0 ≤ Kstate)
    (hQlip : ∀ v w, ‖Q v - Q w‖ ≤ Kstate * ‖v - w‖)
    (hsmall : Kstate * (T - t₀) < 1)
    (z w : BoundedContinuousFunction (↥(Set.Icc t₀ T)) (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hz : heatMildSelfMap hT u₀ hLunn hulip Q hQcont hQb z = z)
    (hw : heatMildSelfMap hT v₀ hLvnn hvlip Q hQcont hQb w = w)
    (s : Set (ℝ × (Fin n → ℝ))) :
    parabolicSupNorm
        (fun p : ℝ × (Fin n → ℝ) =>
          Set.IccExtend hT (⇑z) p.1 p.2 - Set.IccExtend hT (⇑w) p.1 p.2) s
      ≤ ‖u₀ - v₀‖ / (1 - Kstate * (T - t₀)) := by
  have hpos : 0 < 1 - Kstate * (T - t₀) := by linarith
  have hBnn : 0 ≤ ‖u₀ - v₀‖ / (1 - Kstate * (T - t₀)) := div_nonneg (norm_nonneg _) hpos.le
  have hdistzw : dist z w ≤ ‖u₀ - v₀‖ / (1 - Kstate * (T - t₀)) :=
    dist_heatMildFixedPoint_le hT u₀ v₀ hLunn hulip hLvnn hvlip Q hQcont hQb hKnn hQlip hsmall
      z w hz hw
  have hb : ParabolicBoundedWith (‖u₀ - v₀‖ / (1 - Kstate * (T - t₀)))
      (fun p : ℝ × (Fin n → ℝ) =>
        Set.IccExtend hT (⇑z) p.1 p.2 - Set.IccExtend hT (⇑w) p.1 p.2) s := by
    intro p _hp
    have hbcf : ‖Set.IccExtend hT (⇑z) p.1 - Set.IccExtend hT (⇑w) p.1‖ ≤ ‖z - w‖ := by
      have hEq : Set.IccExtend hT (⇑z) p.1 - Set.IccExtend hT (⇑w) p.1
          = (z - w) (Set.projIcc t₀ T hT p.1) := by
        show (⇑z) (Set.projIcc t₀ T hT p.1) - (⇑w) (Set.projIcc t₀ T hT p.1)
            = (z - w) (Set.projIcc t₀ T hT p.1)
        rw [BoundedContinuousFunction.sub_apply]
      rw [hEq]
      exact (z - w).norm_coe_le_norm _
    have hscal : Set.IccExtend hT (⇑z) p.1 p.2 - Set.IccExtend hT (⇑w) p.1 p.2
        = (Set.IccExtend hT (⇑z) p.1 - Set.IccExtend hT (⇑w) p.1) p.2 := by
      rw [BoundedContinuousFunction.sub_apply]
    calc ‖Set.IccExtend hT (⇑z) p.1 p.2 - Set.IccExtend hT (⇑w) p.1 p.2‖
        = ‖(Set.IccExtend hT (⇑z) p.1 - Set.IccExtend hT (⇑w) p.1) p.2‖ := by rw [hscal]
      _ ≤ ‖Set.IccExtend hT (⇑z) p.1 - Set.IccExtend hT (⇑w) p.1‖ :=
            (Set.IccExtend hT (⇑z) p.1 - Set.IccExtend hT (⇑w) p.1).norm_coe_le_norm p.2
      _ ≤ ‖z - w‖ := hbcf
      _ = dist z w := (dist_eq_norm z w).symm
      _ ≤ ‖u₀ - v₀‖ / (1 - Kstate * (T - t₀)) := hdistzw
  exact parabolicSupNorm_le hBnn hb

end AnalyticPDE
end RicciFlow
