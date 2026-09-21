/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Tactic

/-!
# Riccati lower barriers

This file proves the one-dimensional comparison estimate used after the
spatial maximum principle reduces scalar-curvature evolution to the minimum
value ODE.  The barrier is the exact solution of `b' = (2 / n) b²` with
initial value `-n C`.
-/

@[expose] public noncomputable section

open Filter Set Topology

/-- A differentiable real function that points strictly upward wherever it is
negative cannot cross below zero from a nonnegative initial value. -/
theorem nonneg_on_Icc_of_deriv_pos_on_negative
    {f f' : ℝ → ℝ} {T : ℝ}
    (hcont : ContinuousOn f (Icc 0 T))
    (hderiv : ∀ x ∈ Icc 0 T, HasDerivAt f (f' x) x)
    (hzero : 0 ≤ f 0)
    (hpoints : ∀ x ∈ Icc 0 T, f x < 0 → 0 < f' x) :
    ∀ x ∈ Icc 0 T, 0 ≤ f x := by
  intro b hb
  by_contra hbnonneg
  have hbneg : f b < 0 := lt_of_not_ge hbnonneg
  have hb0 : 0 ≤ b := hb.1
  obtain ⟨c, hc, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hb0)
      (hcont.mono (by
        intro x hx
        exact ⟨hx.1, hx.2.trans hb.2⟩))
  have hcneg : f c < 0 := (hmin ⟨hb0, le_rfl⟩).trans_lt hbneg
  have hcpos : 0 < c := by
    have hcne : c ≠ 0 := by
      intro hc0
      subst c
      linarith
    exact lt_of_le_of_ne hc.1 (Ne.symm hcne)
  have hlocal : IsLocalMinOn f (Icc 0 b) c := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hmin hx
  have hzero_mem : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb0⟩
  have htangent : (0 : ℝ) - c ∈ posTangentConeAt (Icc 0 b) c :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) b).segment_subset hc hzero_mem)
  have hnonneg := hlocal.hasFDerivWithinAt_nonneg
    (hderiv c ⟨hc.1, hc.2.trans hb.2⟩).hasFDerivAt.hasFDerivWithinAt htangent
  have hderivpos := hpoints c ⟨hc.1, hc.2.trans hb.2⟩ hcneg
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hnonneg
  nlinarith

/-- Sharp lower comparison for the scalar Riccati inequality.

If `m' ≥ (2 / n) m²`, `n > 0`, and `m(0) ≥ -nC`, then
`m(t) ≥ -nC/(1+2Ct)` for every `t ∈ [0,T]`. -/
theorem riccati_lower_barrier
    {m m' : ℝ → ℝ} {n C T : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Icc 0 T, HasDerivAt m (m' t) t)
    (hinequality : ∀ t ∈ Icc 0 T, (2 / n) * m t ^ 2 ≤ m' t)
    (hinitial : -n * C ≤ m 0) :
    ∀ t ∈ Icc 0 T, -n * C / (1 + 2 * C * t) ≤ m t := by
  let z : ℝ → ℝ := fun t => (1 + 2 * C * t) * m t + n * C
  let z' : ℝ → ℝ := fun t => 2 * C * m t + (1 + 2 * C * t) * m' t
  have hzderiv : ∀ t ∈ Icc 0 T, HasDerivAt z (z' t) t := by
    intro t ht
    have hlinear : HasDerivAt (fun s : ℝ => 1 + 2 * C * s) (2 * C) t := by
      convert! (hasDerivAt_const t (1 : ℝ)).add
        ((hasDerivAt_id t).const_mul (2 * C)) using 1
      ring
    convert! (hlinear.mul (hderiv t ht)).add_const (n * C) using 1
  have hzcont : ContinuousOn z (Icc 0 T) := by
    intro t ht
    exact (hzderiv t ht).continuousAt.continuousWithinAt
  have hzinitial : 0 ≤ z 0 := by
    dsimp [z]
    linarith
  have hzpoints : ∀ t ∈ Icc 0 T, z t < 0 → 0 < z' t := by
    intro t ht hzneg
    have ht0 : 0 ≤ t := ht.1
    have hden : 0 < 1 + 2 * C * t := by positivity
    have hmneg : m t < 0 := by
      have hnC : 0 ≤ n * C := mul_nonneg hn.le hC
      dsimp [z] at hzneg
      by_contra hm
      have hm0 : 0 ≤ m t := le_of_not_gt hm
      nlinarith [mul_nonneg hden.le hm0]
    have hscaled :
        (1 + 2 * C * t) * ((2 / n) * m t ^ 2) ≤
          (1 + 2 * C * t) * m' t :=
      mul_le_mul_of_nonneg_left (hinequality t ht) hden.le
    have hfactor :
        2 * C * m t + (1 + 2 * C * t) * ((2 / n) * m t ^ 2) =
          (2 / n) * m t * z t := by
      dsimp [z]
      field_simp [hn.ne']
      ring
    have h2n : 0 < 2 / n := div_pos (by norm_num) hn
    have hpositive : 0 < (2 / n) * m t * z t :=
      mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg h2n hmneg) hzneg
    dsimp [z']
    rw [← hfactor] at hpositive
    linarith
  have hznonneg :=
    nonneg_on_Icc_of_deriv_pos_on_negative hzcont hzderiv hzinitial hzpoints
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hden : 0 < 1 + 2 * C * t := by positivity
  have hz := hznonneg t ht
  dsimp [z] at hz
  rw [div_le_iff₀ hden]
  nlinarith
