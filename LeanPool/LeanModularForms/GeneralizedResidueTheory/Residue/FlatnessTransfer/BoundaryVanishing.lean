/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.Flatness

/-!
# Boundary Vanishing for Higher-Order Polar Terms

Chain rules for zpow compositions (L0), FTC for negative powers (L1),
exit-time direction convergence (L2), and boundary term vanishing under
angle conditions with flatness rate (L3).

## Main results

* `zpow_boundary_diff_tendsto_zero`: boundary zpow difference → 0 under angle + flatness
* `cutoff_zpow_infrastructure`: full infrastructure for cutoff zpow integrals
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

/-! ## L0: Chain rule for zpow compositions

The derivative of `t ↦ (γ(t) - s)^n` where `n : ℤ` and `γ(t) ≠ s`. -/

/-- HasDerivAt for `(γ(t) - s)^n` when `γ` is differentiable and `γ(t) ≠ s`.
This is the chain rule applied to `z ↦ z^n` composed with `t ↦ γ(t) - s`. -/
theorem hasDerivAt_zpow_comp_sub
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {t : ℝ} {L : ℂ}
    (hγ : HasDerivAt γ L t) (hne : γ t ≠ s) :
    HasDerivAt (fun t => (γ t - s) ^ n)
      (↑n * (γ t - s) ^ (n - 1) * L) t := by
  have h_comp := (hasDerivAt_zpow n (γ t - s) (Or.inl (sub_ne_zero.mpr hne))).comp t
    (hγ.sub_const s)
  refine h_comp.congr_deriv ?_
  ring

/-- ContinuousOn for `t ↦ (γ(t) - s)^n` on a set where `γ(t) ≠ s`. -/
theorem continuousOn_zpow_comp_sub
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {A : Set ℝ}
    (hγ : ContinuousOn γ A)
    (hne : ∀ t ∈ A, γ t ≠ s) :
    ContinuousOn (fun t => (γ t - s) ^ n) A := by
  apply ContinuousOn.zpow₀ (hγ.sub continuousOn_const)
  intro t ht
  exact Or.inl (sub_ne_zero.mpr (hne t ht))

/-! ## L1: FTC for negative powers on parameterized curves

When `γ` is differentiable and avoids `s` on `[a, b]`, the integral of
`(γ(t) - s)^{-m} · γ'(t)` equals the boundary difference of the primitive
`(γ(t) - s)^{1-m} / (1-m)`. -/

/-- FTC for the integral of `(γ(t) - s)^n · γ'(t)` on `[a, b]` when `γ(t) ≠ s`
on `[a, b]` and `n ≠ -1`. The primitive is `(γ(t) - s)^{n+1} / (n+1)`. -/
theorem integral_zpow_comp_sub_mul_deriv
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} (hn : n ≠ -1)
    {a b : ℝ} (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ s)
    (E : Set ℝ) (hE : E.Countable) (_hE_sub : E ∩ Ioo a b ⊆ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ E → DifferentiableAt ℝ γ t)
    (h_int : IntervalIntegrable
      (fun t => (γ t - s) ^ n * (deriv γ t : ℂ)) MeasureTheory.volume a b) :
    ∫ t in a..b, (γ t - s) ^ n * (deriv γ t : ℂ) =
      ((γ b - s) ^ (n + 1) - (γ a - s) ^ (n + 1)) / (↑(n + 1) : ℂ) := by
  have hn1 : (n : ℤ) + 1 ≠ 0 := by omega
  have hn1_cast : (↑(n + 1) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn1
  set F : ℝ → ℂ := fun t => (γ t - s) ^ (n + 1) / (↑(n + 1) : ℂ) with hF_def
  set f : ℝ → ℂ := fun t => (γ t - s) ^ n * (deriv γ t : ℂ) with hf_def
  have hF_cont : ContinuousOn F (Icc a b) :=
    (continuousOn_zpow_comp_sub hγ_cont hγ_ne (n := n + 1)).div_const _
  have hE_count : (E ∩ Ioo a b).Countable := hE.mono Set.inter_subset_left
  have hF_deriv : ∀ t ∈ Ioo a b \ (E ∩ Ioo a b),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not_E : t ∉ E := fun hE_mem => ht_not ⟨hE_mem, ht⟩
    have hγ_da := (hγ_diff t ht ht_not_E).hasDerivAt
    have hne : γ t ≠ s := hγ_ne t (Ioo_subset_Icc_self ht)
    have h_zpow := hasDerivAt_zpow_comp_sub (n := n + 1) hγ_da hne
    have h_div := h_zpow.div_const (↑(n + 1) : ℂ)
    change HasDerivAt F ((γ t - s) ^ n * ↑(deriv γ t)) t
    have : (↑(n + 1) : ℂ) * (γ t - s) ^ (n + 1 - 1) * ↑(deriv γ t) / (↑(n + 1) : ℂ)
        = (γ t - s) ^ n * ↑(deriv γ t) := by
      rw [show (n + 1 : ℤ) - 1 = n from by ring]
      rw [mul_assoc, mul_div_cancel_left₀ _ hn1_cast]
    rw [← this]
    exact h_div
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f hab hE_count hF_cont hF_deriv h_int
  rw [h_ftc]
  simp only [F]
  rw [← sub_div]

/-! ## L2: Exit times and direction convergence

For a piecewise C¹ immersion passing through `s` at parameter `t₀`, the curve
enters and exits the ε-ball around `s` at unique parameters near `t₀`. The
directions `(γ(t±) - s) / ‖γ(t±) - s‖` converge to the tangent directions. -/

/-- Near a crossing point of an immersion, there exists a neighborhood such that
the curve only crosses the singularity at that one point. -/
theorem exists_unique_crossing_neighborhood
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s) :
    ∃ a' b', t₀ ∈ Set.Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
      ∀ t ∈ Icc a' b', γ.toFun t = s → t = t₀ := by
  obtain ⟨a', b', ha'_lt, ht₀_lt_b', h_sub, h_unique, _⟩ :=
    _root_.exists_isolated_crossing_interval γ s t₀ ht₀ hcross
  exact ⟨a', b', ⟨ha'_lt, ht₀_lt_b'⟩, h_sub, h_unique⟩

private lemma slope_tendsto_right_of_deriv
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L : ℂ) (hL_lim : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (γ.toFun (t₀ + ε) - s)) (𝓝[>] 0) (𝓝 L) := by
  have ht₀_Icc : t₀ ∈ Icc γ.a γ.b := Ioo_subset_Icc_self ht₀
  let P := γ.toPiecewiseC1Curve.partition.filter (t₀ < ·)
  have hP_ne : P.Nonempty :=
    ⟨γ.b, Finset.mem_filter.mpr
      ⟨γ.toPiecewiseC1Curve.endpoints_in_partition.2, ht₀.2⟩⟩
  let δ := P.min' hP_ne
  have hδ_in : δ ∈ P := Finset.min'_mem _ hP_ne
  have hδ_in_part : δ ∈ γ.toPiecewiseC1Curve.partition :=
    (Finset.mem_filter.mp hδ_in).1
  have hδ_gt : t₀ < δ := (Finset.mem_filter.mp hδ_in).2
  have hδ_le_b : δ ≤ γ.b := (γ.toPiecewiseC1Curve.partition_subset hδ_in_part).2
  have h_no_part : ∀ t ∈ Ioo t₀ δ, t ∉ γ.toPiecewiseC1Curve.partition := by
    intro t ht htp
    have ht_in : t ∈ P := Finset.mem_filter.mpr ⟨htp, ht.1⟩
    linarith [Finset.min'_le P t ht_in, ht.2]
  have h_sub : Ioo t₀ δ ⊆ Icc γ.a γ.b :=
    fun t ht => ⟨le_of_lt (lt_trans ht₀.1 ht.1), le_trans (le_of_lt ht.2) hδ_le_b⟩
  have h_diff : DifferentiableOn ℝ γ.toFun (Ioo t₀ δ) := fun t ht =>
    (γ.toPiecewiseC1Curve.smooth_off_partition t (h_sub ht)
      (h_no_part t ht)).differentiableWithinAt
  have h_cont : ContinuousWithinAt γ.toFun (Ioo t₀ δ) t₀ :=
    (γ.toPiecewiseC1Curve.continuous_toFun.continuousWithinAt ht₀_Icc).mono h_sub
  have h_deriv : HasDerivWithinAt γ.toFun L (Ici t₀) t₀ :=
    hasDerivWithinAt_Ici_of_tendsto_deriv h_diff h_cont (Ioo_mem_nhdsGT hδ_gt) hL_lim
  rw [hasDerivWithinAt_iff_tendsto_slope] at h_deriv
  rw [show (Ici t₀ \ {t₀} : Set ℝ) = Ioi t₀ from Ici_sdiff_left] at h_deriv
  have h_map : Tendsto (fun ε : ℝ => t₀ + ε) (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => t₀ + ε) (𝓝 (0 : ℝ)) (𝓝 t₀) := by
        have := (continuous_const_add t₀).tendsto (0 : ℝ)
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
      exact lt_add_of_pos_right t₀ hε
  refine (h_deriv.comp h_map).congr (fun ε => ?_)
  simp only [Function.comp, slope, vsub_eq_sub, hcross, add_sub_cancel_left]

private lemma direction_of_slope_tendsto
    (f : ℝ → ℂ) (L : ℂ) (hL : L ≠ 0)
    (h_slope : Tendsto (fun ε : ℝ => ε⁻¹ • (f ε)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε => f ε / ↑‖f ε‖) (𝓝[>] 0) (𝓝 (L / ↑‖L‖)) := by
  suffices h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f ε / ↑‖f ε‖ = (ε⁻¹ • f ε) / ↑‖ε⁻¹ • f ε‖ by
    have h_norm_cont : Tendsto (fun w : ℂ => w / ↑‖w‖) (𝓝 L)
        (𝓝 (L / ↑‖L‖)) := by
      apply Tendsto.div tendsto_id
        (Complex.continuous_ofReal.continuousAt.tendsto.comp
          continuous_norm.continuousAt.tendsto)
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hL)
    exact (h_norm_cont.comp h_slope).congr' (h_eq.mono fun ε h => h.symm)
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with ε (hε : (0 : ℝ) < ε)
  set w := f ε
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw]
  · have h_inv_pos : (0 : ℝ) < ε⁻¹ := inv_pos_of_pos hε
    have h_inv_ne : (↑(ε⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt h_inv_pos)
    rw [Complex.real_smul]
    have h_norm : (↑‖↑(ε⁻¹ : ℝ) * w‖ : ℂ) = ↑(ε⁻¹ : ℝ) * ↑‖w‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos h_inv_pos, Complex.ofReal_mul]
    rw [h_norm, mul_div_mul_left _ _ h_inv_ne]

/-- As `ε → 0⁺`, the direction from `s` to the first right exit point of the
ε-ball converges to the right tangent direction (normalized). Specifically,
`(γ(t₊(ε)) - s) / ‖γ(t₊(ε)) - s‖ → L_right / ‖L_right‖`.

This follows from the first-order Taylor approximation
`γ(t) - s ≈ (t - t₀) · L_right` and `‖γ(t) - s‖ ≈ |t - t₀| · ‖L_right‖`. -/
theorem crossing_direction_right_tendsto
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_right : ℂ) (hL : L_right ≠ 0)
    (hL_lim : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_right)) :
    Tendsto (fun ε => (γ.toFun (t₀ + ε) - s) / ‖γ.toFun (t₀ + ε) - s‖)
      (𝓝[>] 0) (𝓝 (L_right / ‖L_right‖)) :=
  direction_of_slope_tendsto _ L_right hL
    (slope_tendsto_right_of_deriv γ s t₀ ht₀ hcross L_right hL_lim)

private lemma slope_tendsto_left_of_deriv
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L : ℂ) (hL_lim : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (γ.toFun (t₀ - ε) - s)) (𝓝[>] 0) (𝓝 (-L)) := by
  let P := γ.toPiecewiseC1Curve.partition.filter (· < t₀)
  have hP_ne : P.Nonempty :=
    ⟨γ.a, Finset.mem_filter.mpr
      ⟨γ.toPiecewiseC1Curve.endpoints_in_partition.1, ht₀.1⟩⟩
  let δ := P.max' hP_ne
  have hδ_in : δ ∈ P := Finset.max'_mem _ hP_ne
  have hδ_in_part : δ ∈ γ.toPiecewiseC1Curve.partition :=
    (Finset.mem_filter.mp hδ_in).1
  have hδ_lt : δ < t₀ := (Finset.mem_filter.mp hδ_in).2
  have ha_le_δ : γ.a ≤ δ := (γ.toPiecewiseC1Curve.partition_subset hδ_in_part).1
  have h_no_part : ∀ t ∈ Ioo δ t₀, t ∉ γ.toPiecewiseC1Curve.partition := by
    intro t ht htp
    have ht_in : t ∈ P := Finset.mem_filter.mpr ⟨htp, ht.2⟩
    linarith [Finset.le_max' P t ht_in, ht.1]
  have h_sub : Ioo δ t₀ ⊆ Icc γ.a γ.b :=
    fun t ht => ⟨le_of_lt (lt_of_le_of_lt ha_le_δ ht.1), le_of_lt (lt_trans ht.2 ht₀.2)⟩
  have h_diff : DifferentiableOn ℝ γ.toFun (Ioo δ t₀) := fun t ht =>
    (γ.toPiecewiseC1Curve.smooth_off_partition t (h_sub ht)
      (h_no_part t ht)).differentiableWithinAt
  have h_cont : ContinuousWithinAt γ.toFun (Ioo δ t₀) t₀ :=
    (γ.toPiecewiseC1Curve.continuous_toFun.continuousWithinAt
      (Ioo_subset_Icc_self ht₀)).mono h_sub
  have h_deriv : HasDerivWithinAt γ.toFun L (Iic t₀) t₀ :=
    hasDerivWithinAt_Iic_of_tendsto_deriv h_diff h_cont (Ioo_mem_nhdsLT hδ_lt) hL_lim
  rw [hasDerivWithinAt_iff_tendsto_slope, show (Iic t₀ \ {t₀} : Set ℝ) = Iio t₀ from
    Iic_sdiff_right] at h_deriv
  have h_map : Tendsto (fun ε : ℝ => t₀ - ε) (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => t₀ - ε) (𝓝 (0 : ℝ)) (𝓝 t₀) := by
        have := (continuous_sub_left t₀).tendsto (0 : ℝ)
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
      exact sub_lt_self t₀ hε
  have h_comp := h_deriv.comp h_map
  have h_neg : Tendsto (fun ε : ℝ => -((-ε)⁻¹ • (γ.toFun (t₀ - ε) - s)))
      (𝓝[>] 0) (𝓝 (-L)) := h_comp.neg.congr (fun ε => by
    simp only [Function.comp, slope, vsub_eq_sub]
    rw [hcross]; erw [Complex.real_smul, Complex.real_smul]; ring)
  convert h_neg using 1
  ext ε
  erw [Complex.real_smul, Complex.real_smul]
  push_cast; ring

/-- Left-side analogue of `crossing_direction_right_tendsto`:
`(γ(t₋(ε)) - s) / ‖γ(t₋(ε)) - s‖ → -L_left / ‖L_left‖`. -/
theorem crossing_direction_left_tendsto
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_left : ℂ) (hL : L_left ≠ 0)
    (hL_lim : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_left)) :
    Tendsto (fun ε => (γ.toFun (t₀ - ε) - s) / ‖γ.toFun (t₀ - ε) - s‖)
      (𝓝[>] 0) (𝓝 (-L_left / ‖L_left‖)) := by
  have h_dir := direction_of_slope_tendsto _ (-L_left) (neg_ne_zero.mpr hL)
    (slope_tendsto_left_of_deriv γ s t₀ ht₀ hcross L_left hL_lim)
  rwa [norm_neg] at h_dir

/-! ## L3: Boundary term vanishing under angle condition (with flatness rate)

The FTC boundary terms at the ε-cutoff points have the form `w₊^k - w₋^k` where
`w₊, w₋` lie on the ε-sphere (`‖w‖ = ε`) and `k ≤ -1`. Writing `w = ε · u`
with `‖u‖ = 1`, the difference is `ε^k · (u₊^k - u₋^k)`.

Since `k ≤ -1`, `ε^k → ∞` while the angle condition gives `u₊^k - u₋^k → 0`.
Whether the product tends to 0 depends on the **rate** of direction convergence:

- With flatness of order `n`: direction error is `o(ε^{n-1})`, giving
  `u₊^k - u₋^k = o(ε^{n-1})` and the product is `o(ε^{k+n-1})`.
- For this to tend to 0, we need `k + n - 1 ≥ 0`, i.e., `n + k ≥ 1`.
- At a pole of order `m` with Laurent term `(z-s)^{-(k_L+1)}`, the FTC boundary
  exponent is `k = -k_L`. Flatness of order `n = m ≥ k_L + 1` gives
  `k + n - 1 = m - k_L - 1 ≥ 0`. -/

private lemma zpow_sub_isBigO (k : ℤ) (u : ℂ) (hu : u ≠ 0) :
    (fun v => v ^ k - u ^ k) =O[𝓝 u] (fun v => v - u) :=
  (hasDerivAt_zpow k u (Or.inl hu)).differentiableAt.isBigO_sub

open Asymptotics in
private lemma direction_tendsto_of_rate
    (w : ℝ → ℂ) (u : ℂ) (n : ℕ) (hn : 2 ≤ n)
    (h_rate : (fun ε => ‖w ε / (↑‖w ε‖ : ℂ) - u‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ)) :
    Tendsto (fun ε => w ε / (↑‖w ε‖ : ℂ)) (𝓝[>] 0) (𝓝 u) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff ℝ]
  calc (fun ε => w ε / ↑‖w ε‖ - u)
      =o[𝓝[>] 0] (fun ε => (ε : ℝ) ^ (n - 1 : ℕ)) := isLittleO_norm_left.mp h_rate
    _ =o[𝓝[>] 0] (fun _ => (1 : ℝ)) := by
        rw [isLittleO_one_iff]
        have := ((continuous_pow (n - 1)).continuousAt (x := (0 : ℝ))).tendsto
        simp only [zero_pow (by omega : n - 1 ≠ 0)] at this
        exact this.mono_left nhdsWithin_le_nhds

open Asymptotics in
private lemma direction_zpow_diff_isLittleO
    (k : ℤ) (u : ℂ) (hu : u ≠ 0) (w : ℝ → ℂ) (n : ℕ) (hn : 2 ≤ n)
    (h_rate : (fun ε => ‖w ε / (↑‖w ε‖ : ℂ) - u‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ)) :
    (fun ε => (w ε / (↑‖w ε‖ : ℂ)) ^ k - u ^ k) =o[𝓝[>] (0 : ℝ)]
      (fun ε => (ε : ℝ) ^ (n - 1 : ℕ)) :=
  ((zpow_sub_isBigO k u hu).comp_tendsto
    (direction_tendsto_of_rate w u n hn h_rate)).trans_isLittleO
    (Asymptotics.isLittleO_norm_left.mp h_rate)

/-- Boundary term vanishing for zpow under angle condition with flatness rate.

When `w_R, w_L` lie on the ε-sphere (`‖w‖ = ε`), directions converge to unit
vectors `uR, uL` at rate `o(ε^{n-1})` (from flatness of order `n`), and the
angle condition ensures `uR^k = uL^k`, the zpow boundary difference tends to 0
provided `n + k ≥ 1`. -/
theorem zpow_boundary_diff_tendsto_zero
    (k : ℤ) (hk : k ≤ -1)
    (wR wL : ℝ → ℂ)
    (h_norm_R : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wR ε‖ = ε)
    (h_norm_L : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wL ε‖ = ε)
    (h_neR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), wR ε ≠ 0)
    (h_neL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), wL ε ≠ 0)
    (uR uL : ℂ) (huR : ‖uR‖ = 1) (huL : ‖uL‖ = 1)
    (h_angle : uR ^ k = uL ^ k)
    (n : ℕ) (hn : (n : ℤ) + k ≥ 1)
    (h_rate_R : (fun ε => ‖wR ε / (↑‖wR ε‖ : ℂ) - uR‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ))
    (h_rate_L : (fun ε => ‖wL ε / (↑‖wL ε‖ : ℂ) - uL‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ)) :
    Tendsto (fun ε => wR ε ^ k - wL ε ^ k)
      (𝓝[>] 0) (𝓝 0) := by
  have hn2 : 2 ≤ n := by omega
  have huR_ne : uR ≠ 0 := norm_ne_zero_iff.mp (by rw [huR]; exact one_ne_zero)
  have huL_ne : uL ≠ 0 := norm_ne_zero_iff.mp (by rw [huL]; exact one_ne_zero)
  have h_oR := direction_zpow_diff_isLittleO k uR huR_ne wR n hn2 h_rate_R
  have h_oL := direction_zpow_diff_isLittleO k uL huL_ne wL n hn2 h_rate_L
  have h_diff : (fun ε =>
      (wR ε / (↑‖wR ε‖ : ℂ)) ^ k - (wL ε / (↑‖wL ε‖ : ℂ)) ^ k)
      =o[𝓝[>] 0] (fun ε => (ε : ℝ) ^ (n - 1 : ℕ)) := by
    have h_eq : (fun ε => (wR ε / ↑‖wR ε‖) ^ k - (wL ε / ↑‖wL ε‖) ^ k) =
        fun ε => ((wR ε / ↑‖wR ε‖) ^ k - uR ^ k) -
          ((wL ε / ↑‖wL ε‖) ^ k - uL ^ k) := by
      ext ε; rw [h_angle]; ring
    rw [h_eq]; exact h_oR.sub h_oL
  rw [Metric.tendsto_nhds]
  intro η hη
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(wR ε / (↑‖wR ε‖ : ℂ)) ^ k - (wL ε / (↑‖wL ε‖ : ℂ)) ^ k‖ ≤
      η / 2 * ‖(ε : ℝ) ^ (n - 1 : ℕ)‖ := (h_diff.def' (half_pos hη)).bound
  filter_upwards [h_bound, h_norm_R, h_norm_L, h_neR, h_neL,
    Ioo_mem_nhdsGT one_pos] with ε h_bnd h_nR h_nL h_ne_R h_ne_L hε_mem
  obtain ⟨hε_pos, hε_lt⟩ := hε_mem
  rw [dist_eq_norm, sub_zero]
  have h_factR : wR ε ^ k = (↑ε : ℂ) ^ k * (wR ε / (↑‖wR ε‖ : ℂ)) ^ k := by
    have h_ne : (↑‖wR ε‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h_ne_R)
    have : wR ε = (↑‖wR ε‖ : ℂ) * (wR ε / (↑‖wR ε‖ : ℂ)) := by field_simp
    conv_lhs => rw [this]
    rw [mul_zpow, h_nR]
  have h_factL : wL ε ^ k = (↑ε : ℂ) ^ k * (wL ε / (↑‖wL ε‖ : ℂ)) ^ k := by
    have h_ne : (↑‖wL ε‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h_ne_L)
    have : wL ε = (↑‖wL ε‖ : ℂ) * (wL ε / (↑‖wL ε‖ : ℂ)) := by field_simp
    conv_lhs => rw [this]
    rw [mul_zpow, h_nL]
  rw [h_factR, h_factL, ← mul_sub, norm_mul, Complex.norm_zpow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
  have h_norm_pow : ‖(ε : ℝ) ^ (n - 1 : ℕ)‖ = ε ^ (n - 1 : ℕ) :=
    (Real.norm_eq_abs _).trans (abs_of_pos (pow_pos hε_pos _))
  rw [h_norm_pow] at h_bnd
  have h_pow_le : (ε : ℝ) ^ k * (ε : ℝ) ^ (n - 1 : ℕ) ≤ 1 := by
    rw [← zpow_natCast ε (n - 1), ← zpow_add₀ (ne_of_gt hε_pos)]
    exact zpow_le_one₀ hε_pos hε_lt.le (by omega)
  calc ε ^ k * ‖(wR ε / ↑‖wR ε‖) ^ k - (wL ε / ↑‖wL ε‖) ^ k‖
      ≤ ε ^ k * (η / 2 * ε ^ (n - 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left h_bnd (zpow_nonneg hε_pos.le k)
    _ = η / 2 * (ε ^ k * ε ^ (n - 1 : ℕ)) := by ring
    _ ≤ η / 2 * 1 := mul_le_mul_of_nonneg_left h_pow_le (half_pos hη).le
    _ = η / 2 := mul_one _
    _ < η := half_lt_self hη

/-! ## Bridge: tangent deviation → direction norm difference

For unit vectors `u, v` with `‖u - v‖ ≤ 1`:
`‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖`.

This bridges `IsFlatOfOrder` (stated in terms of tangent deviation) to the
direction rate condition in `zpow_boundary_diff_tendsto_zero` (L3). -/

private lemma orthogonalProjectionComplex_of_norm_one (u v : ℂ) (hv : ‖v‖ = 1) :
    orthogonalProjectionComplex u v = (u * starRingEnd ℂ v).re • v := by
  unfold orthogonalProjectionComplex
  rw [Complex.normSq_eq_norm_sq, hv, one_pow, div_one]

private lemma tangentDeviation_of_norm_one (u v : ℂ) (hv : ‖v‖ = 1) :
    tangentDeviation u v = u - (u * starRingEnd ℂ v).re • v := by
  rw [tangentDeviation, orthogonalProjectionComplex_of_norm_one u v hv]

/-- For unit vectors `u, v` with `‖u - v‖ ≤ 1`:
`‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖`. -/
theorem norm_sub_le_tangentDeviation_of_unit (u v : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h_close : ‖u - v‖ ≤ 1) :
    ‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖ := by
  have h_decomp : u - v = tangentDeviation u v + ((u * starRingEnd ℂ v).re - 1) • v := by
    rw [tangentDeviation_of_norm_one u v hv]
    simp only [Complex.real_smul]; push_cast; ring
  have h_normSq : ‖u - v‖ ^ 2 = 2 - 2 * (u * starRingEnd ℂ v).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, hu, hv, one_pow, starRingEnd_apply]
    ring
  have h_re_le : (u * starRingEnd ℂ v).re ≤ 1 := by
    have h1 : |(u * starRingEnd ℂ v).re| ≤ 1 := by
      calc |(u * starRingEnd ℂ v).re| ≤ ‖u * starRingEnd ℂ v‖ :=
            Complex.abs_re_le_norm _
        _ = 1 := by rw [norm_mul, hu, starRingEnd_apply, norm_star, hv, mul_one]
    exact le_of_abs_le h1
  have h_re_bound : 1 - (u * starRingEnd ℂ v).re = ‖u - v‖ ^ 2 / 2 := by linarith
  have h_tri := norm_add_le (tangentDeviation u v) (((u * starRingEnd ℂ v).re - 1) • v)
  rw [← h_decomp] at h_tri
  have h_smul_norm : ‖((u * starRingEnd ℂ v).re - 1) • v‖ = ‖u - v‖ ^ 2 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_nonpos (by linarith), neg_sub,
      h_re_bound]
  have h_sq_le : ‖u - v‖ ^ 2 / 2 ≤ ‖u - v‖ / 2 := by
    rw [div_le_div_iff_of_pos_right two_pos]
    calc ‖u - v‖ ^ 2 = ‖u - v‖ * ‖u - v‖ := sq _
      _ ≤ ‖u - v‖ * 1 := mul_le_mul_of_nonneg_left h_close (norm_nonneg _)
      _ = ‖u - v‖ := mul_one _
  linarith [h_smul_norm, h_sq_le, h_tri]

/-- For unit vectors `z₁, z₂` and integer exponent `k`, if
`k · (arg z₁ - arg z₂) ∈ 2πℤ`, then `z₁^k = z₂^k`. -/
lemma unit_zpow_eq_of_angle_multiple
    (z₁ z₂ : ℂ) (k : ℤ)
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (h : ∃ n : ℤ, (↑k : ℝ) * (arg z₁ - arg z₂) = ↑n * (2 * Real.pi)) :
    z₁ ^ k = z₂ ^ k := by
  have h₁ : z₁ = exp (↑(arg z₁) * I) := by
    have := norm_mul_exp_arg_mul_I z₁
    rw [hz₁, ofReal_one, one_mul] at this
    exact this.symm
  have h₂ : z₂ = exp (↑(arg z₂) * I) := by
    have := norm_mul_exp_arg_mul_I z₂
    rw [hz₂, ofReal_one, one_mul] at this
    exact this.symm
  rw [h₁, h₂, ← exp_int_mul, ← exp_int_mul]
  rw [exp_eq_exp_iff_exists_int]
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← sub_eq_zero]
  have h_eq : ↑k * (↑(arg z₁) * I) -
      (↑k * (↑(arg z₂) * I) + ↑n * (2 * ↑Real.pi * I)) =
      ↑((↑k : ℝ) * (arg z₁ - arg z₂) -
        (↑n : ℝ) * (2 * Real.pi)) * I := by
    push_cast; ring
  rw [h_eq, mul_eq_zero]
  left
  rw [ofReal_eq_zero]
  linarith

private lemma orthogonalProjectionComplex_real_smul_left (c : ℝ) (w L : ℂ) :
    orthogonalProjectionComplex (c • w) L = c • orthogonalProjectionComplex w L := by
  simp only [orthogonalProjectionComplex, Complex.real_smul]
  rw [show ↑c * w * (starRingEnd ℂ) L = ↑c * (w * (starRingEnd ℂ) L) from mul_assoc _ _ _,
    Complex.re_ofReal_mul]
  push_cast; ring

lemma tangentDeviation_real_smul_left (c : ℝ) (w L : ℂ) :
    tangentDeviation (c • w) L = c • tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex_real_smul_left]
  simp only [RCLike.real_smul_eq_coe_mul]; ring

private lemma orthogonalProjectionComplex_real_smul_right (c : ℝ) (hc : c ≠ 0) (w L : ℂ) :
    orthogonalProjectionComplex w (c • L) = orthogonalProjectionComplex w L := by
  unfold orthogonalProjectionComplex
  simp only [Complex.real_smul]
  conv_lhs =>
    rw [show starRingEnd ℂ (↑c * L) = star (↑c * L) from rfl,
      star_mul', show star (↑c : ℂ) = ↑c from by
        rw [Complex.star_def]; exact Complex.conj_ofReal c,
      show star L = starRingEnd ℂ L from rfl]
  rw [show Complex.normSq ((↑c : ℂ) * L) = c ^ 2 * Complex.normSq L from by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, sq],
    show w * (↑c * starRingEnd ℂ L) = ↑c * (w * starRingEnd ℂ L) from by ring,
    Complex.re_ofReal_mul]
  set r := (w * starRingEnd ℂ L).re
  set nS := Complex.normSq L
  rw [show (↑(c * r / (c ^ 2 * nS)) : ℂ) * ((↑c : ℂ) * L) =
    ↑(c * r / (c ^ 2 * nS) * c) * L from by push_cast; ring,
    show c * r / (c ^ 2 * nS) * c = r / nS from by rw [sq]; field_simp]

lemma tangentDeviation_real_smul_right (c : ℝ) (hc : c ≠ 0) (w L : ℂ) :
    tangentDeviation w (c • L) = tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex_real_smul_right c hc]

private lemma unit_sq_le_two_mul_tangentDeviation_sq
    (u v₀ : ℂ) (hu : ‖u‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hR_pos : 0 < (u * starRingEnd ℂ v₀).re) :
    ‖u - v₀‖ ^ 2 ≤ 2 * ‖tangentDeviation u v₀‖ ^ 2 := by
  set R := (u * starRingEnd ℂ v₀).re
  have h_lhs : ‖u - v₀‖ ^ 2 = 2 - 2 * R := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, hu, hv₀, one_pow]; ring
  have h_rhs : ‖tangentDeviation u v₀‖ ^ 2 = 1 - R ^ 2 := by
    rw [tangentDeviation_of_norm_one u v₀ hv₀,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, hu, one_pow,
      norm_smul, Real.norm_eq_abs, hv₀, mul_one, sq_abs]
    have hstar : (starRingEnd ℂ) (R • v₀) = (↑R : ℂ) * (starRingEnd ℂ) v₀ := by
      rw [Complex.real_smul, map_mul (starRingEnd ℂ), Complex.conj_ofReal]
    rw [hstar]
    have hre : (u * ((↑R : ℂ) * starRingEnd ℂ v₀)).re = R * R := by
      rw [← mul_assoc, mul_comm u (↑R : ℂ), mul_assoc,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hre]; ring
  have hR_le : R ≤ 1 := by nlinarith [sq_nonneg (‖tangentDeviation u v₀‖)]
  rw [h_lhs, h_rhs]; nlinarith [hR_pos.le, hR_le]

private lemma norm_sub_le_sqrt2_tangentDeviation
    (u v₀ : ℂ) (hu : ‖u‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hR_pos : 0 < (u * starRingEnd ℂ v₀).re) :
    ‖u - v₀‖ ≤ Real.sqrt 2 * ‖tangentDeviation u v₀‖ := by
  have h_sq := unit_sq_le_two_mul_tangentDeviation_sq u v₀ hu hv₀ hR_pos
  rw [← Real.sqrt_sq (norm_nonneg (u - v₀)),
    ← Real.sqrt_sq (norm_nonneg (tangentDeviation u v₀)),
    ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.sqrt_le_sqrt h_sq

lemma direction_rate_final_calc
    (m : ℕ) (c ε : ℝ) (hε_pos : 0 < ε) (hm : 2 ≤ m)
    (w : ℂ) (L : ℂ) (u v₀ : ℂ)
    (hu : ‖u‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hR_pos : 0 < (u * starRingEnd ℂ v₀).re)
    (h_td_scale : ‖tangentDeviation u v₀‖ = ‖tangentDeviation w L‖ / ‖w‖)
    (hε_norm : ‖w‖ = ε)
    (h_td_bound' : ‖tangentDeviation w L‖ ≤ c / Real.sqrt 2 * ε ^ m) :
    ‖u - v₀‖ ≤ c * ‖ε ^ (m - 1 : ℕ)‖ := by
  have h_bound := norm_sub_le_sqrt2_tangentDeviation u v₀ hu hv₀ hR_pos
  rw [h_td_scale, hε_norm] at h_bound
  rw [Real.norm_of_nonneg (pow_nonneg hε_pos.le _)]
  calc ‖u - v₀‖
      ≤ Real.sqrt 2 * (‖tangentDeviation w L‖ / ε) := h_bound
    _ ≤ Real.sqrt 2 * (c / Real.sqrt 2 * ε ^ m / ε) := by gcongr
    _ = c * (ε ^ m / ε) := by field_simp
    _ = c * ε ^ (m - 1) := by
        congr 1
        have hpow : ε ^ m = ε ^ (m - 1) * ε := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
        rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hε_pos)]

lemma re_pos_right_of_slope
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_R : ℂ) (hL_R_ne : L_R ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R)) :
    ∀ᶠ t in 𝓝[>] t₀, 0 < ((γ.toFun t - s) * starRingEnd ℂ L_R).re := by
  have hcont : ContinuousAt γ.toFun t₀ :=
    γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hdiff_right : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ.toFun t := by
    have hcl : IsClosed ((↑γ.partition : Set ℝ) \ {t₀}) :=
      (γ.partition.finite_toSet.subset Set.sdiff_subset).isClosed
    filter_upwards [nhdsWithin_le_nhds
        (hcl.isOpen_compl.mem_nhds (Set.mem_compl (fun h => h.2 rfl))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2),
      self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂
      fun hm => ht₁ ⟨hm, ne_of_gt (Set.mem_Ioi.mp ht₃)⟩
  obtain ⟨s_set, hs_mem, hs_diff⟩ := hdiff_right.exists_mem
  have hderiv : HasDerivWithinAt γ.toFun L_R (Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_iff_Ici.mpr (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hcont.continuousWithinAt hs_mem htend_R)
  have hReLR : 0 < (L_R * starRingEnd ℂ L_R).re := by
    rw [Complex.mul_conj]; simp only [Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hL_R_ne
  have h_slope : Tendsto (slope γ.toFun t₀) (𝓝[>] t₀) (𝓝 L_R) :=
    (hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi).mp hderiv
  have h_slope_re : Tendsto (fun t => (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re)
      (𝓝[>] t₀) (𝓝 (L_R * starRingEnd ℂ L_R).re) :=
    (continuous_re.comp (continuous_mul_const _)).continuousAt.tendsto.comp h_slope
  have h_ev := h_slope_re (Ioi_mem_nhds hReLR)
  filter_upwards [h_ev, self_mem_nhdsWithin] with t ht ht_pos
  have ht_gt : t₀ < t := Set.mem_Ioi.mp ht_pos
  have h_pos_factor : (0 : ℝ) < t - t₀ := sub_pos.mpr ht_gt
  have h_slope_pos : 0 < (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re :=
    Set.mem_Ioi.mp (Set.mem_preimage.mp ht)
  have h_key : (t - t₀) * (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re =
      ((γ.toFun t - s) * starRingEnd ℂ L_R).re := by
    have hsub : (t - t₀) • slope γ.toFun t₀ t = γ.toFun t -ᵥ γ.toFun t₀ :=
      sub_smul_slope _ _ _
    rw [vsub_eq_sub, hcross] at hsub
    have hmul : (↑(t - t₀) : ℂ) * (slope γ.toFun t₀ t * starRingEnd ℂ L_R) =
        (γ.toFun t - s) * starRingEnd ℂ L_R := by
      rw [← mul_assoc, ← Complex.real_smul, hsub]
    simp only [← hmul, mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  linarith [mul_pos h_pos_factor h_slope_pos]

lemma re_pos_left_of_slope
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_L : ℂ) (hL_L_ne : L_L ≠ 0)
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L)) :
    ∀ᶠ t in 𝓝[<] t₀, 0 < ((γ.toFun t - s) * starRingEnd ℂ (-L_L)).re := by
  have hcont : ContinuousAt γ.toFun t₀ :=
    γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hdiff_left : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ.toFun t := by
    have hcl : IsClosed ((↑γ.partition : Set ℝ) \ {t₀}) :=
      (γ.partition.finite_toSet.subset Set.sdiff_subset).isClosed
    filter_upwards [nhdsWithin_le_nhds
        (hcl.isOpen_compl.mem_nhds (Set.mem_compl (fun h => h.2 rfl))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2),
      self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂
      fun hm => ht₁ ⟨hm, ne_of_lt (Set.mem_Iio.mp ht₃)⟩
  obtain ⟨s_set, hs_mem, hs_diff⟩ := hdiff_left.exists_mem
  have hderiv : HasDerivWithinAt γ.toFun L_L (Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_iff_Iic.mpr (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hcont.continuousWithinAt hs_mem htend_L)
  have hReLLneg : (L_L * starRingEnd ℂ (-L_L)).re < 0 := by
    rw [map_neg, mul_neg, Complex.neg_re, neg_neg_iff_pos, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hL_L_ne
  have h_slope : Tendsto (slope γ.toFun t₀) (𝓝[<] t₀) (𝓝 L_L) :=
    (hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Iio).mp hderiv
  have h_slope_re : Tendsto (fun t => (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re)
      (𝓝[<] t₀) (𝓝 (L_L * starRingEnd ℂ (-L_L)).re) :=
    (continuous_re.comp (continuous_mul_const _)).continuousAt.tendsto.comp h_slope
  have h_ev := h_slope_re (Iio_mem_nhds hReLLneg)
  filter_upwards [h_ev, self_mem_nhdsWithin] with t ht ht_neg
  have ht_lt : t < t₀ := Set.mem_Iio.mp ht_neg
  have h_neg_factor : t - t₀ < 0 := sub_neg.mpr ht_lt
  have h_slope_neg : (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re < 0 :=
    Set.mem_Iio.mp (Set.mem_preimage.mp ht)
  have h_key : (t - t₀) * (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re =
      ((γ.toFun t - s) * starRingEnd ℂ (-L_L)).re := by
    have hsub : (t - t₀) • slope γ.toFun t₀ t = γ.toFun t -ᵥ γ.toFun t₀ :=
      sub_smul_slope _ _ _
    rw [vsub_eq_sub, hcross] at hsub
    have hmul : (↑(t - t₀) : ℂ) * (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)) =
        (γ.toFun t - s) * starRingEnd ℂ (-L_L) := by
      rw [← mul_assoc, ← Complex.real_smul, hsub]
    simp only [← hmul, mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  linarith [mul_pos_of_neg_of_neg h_neg_factor h_slope_neg]

lemma tangentDeviation_scale_eq
    (w L : ℂ) (_hw_ne : ‖w‖ ≠ 0) (hL_ne : ‖L‖ ≠ 0) :
    ‖tangentDeviation (w / (↑‖w‖ : ℂ)) (L / (↑‖L‖ : ℂ))‖ =
      ‖tangentDeviation w L‖ / ‖w‖ := by
  rw [show (w / (↑‖w‖ : ℂ) : ℂ) = (‖w‖⁻¹ : ℝ) • w from by
      simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div],
    show (L / (↑‖L‖ : ℂ) : ℂ) = (‖L‖⁻¹ : ℝ) • L from by
      simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div],
    tangentDeviation_real_smul_right _ (inv_ne_zero hL_ne),
    tangentDeviation_real_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_eq_div]


end GeneralizedResidueTheory
