/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.OdeCompare

/-! # Abstract short-time chain for the gradient energy

Pure real analysis.  From the three integral inequalities (upper and lower for `G`, upper for `H`)
produced by the differential inequalities of the PDE side, deduce
`(9/10) G₀ ≤ G r ≤ (11/10) G₀` on `[0,t]`, using `Lu t ≤ 1/10000`, `κ t λ ≤ 1/10000`. -/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

theorem integral_le_mul {B : ℝ → ℝ} {C r t : ℝ} (hr0 : 0 ≤ r) (hrt : r ≤ t)
    (hB : ContinuousOn B (Icc 0 t)) (hle : ∀ s ∈ Icc 0 t, B s ≤ C) :
    ∫ s in (0 : ℝ)..r, B s ≤ r * C := by
  have hBint : IntervalIntegrable B volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr0]
    exact hB.mono (Icc_subset_Icc le_rfl hrt)
  have := intervalIntegral.integral_mono_on hr0 hBint
    (intervalIntegrable_const (c := C)) (fun s hs => hle s ⟨hs.1, hs.2.trans hrt⟩)
  simpa using this

theorem mul_le_of_le {r t c A : ℝ} (hrt : r ≤ t) (hA : 0 ≤ A) (hc : 0 ≤ c)
    {ε : ℝ} (hct : c * t ≤ ε) : r * (c * A) ≤ ε * A := by
  calc r * (c * A) ≤ t * (c * A) := mul_le_mul_of_nonneg_right hrt (mul_nonneg hc hA)
    _ = (c * t) * A := by ring
    _ ≤ ε * A := mul_le_mul_of_nonneg_right hct hA

theorem G_two_sided
    {G H : ℝ → ℝ} {κ Lu lam t : ℝ} (hκ : 0 < κ) (hLu : 0 ≤ Lu) (ht : 0 < t)
    (hLt : Lu * t ≤ 1 / 10000) (hkl : κ * t * lam ≤ 1 / 10000)
    (hGc : ContinuousOn G (Icc 0 t)) (hHc : ContinuousOn H (Icc 0 t))
    (hG0 : ∀ r ∈ Icc 0 t, 0 ≤ G r) (hH0 : ∀ r ∈ Icc 0 t, 0 ≤ H r)
    (hHinit : H 0 ≤ lam * G 0)
    (hGu : ∀ r ∈ Icc 0 t, G r ≤ G 0 + ∫ s in (0 : ℝ)..r, 4 * Lu * G s)
    (hGl : ∀ r ∈ Icc 0 t,
      G 0 - ∫ s in (0 : ℝ)..r, (2 * κ * H s + 4 * Lu * G s) ≤ G r)
    (hHu : ∀ r ∈ Icc 0 t,
      H r ≤ H 0 + ∫ s in (0 : ℝ)..r, (12 * Lu * H s + 8 * (Lu ^ 2 / κ) * G s)) :
    ∀ r ∈ Icc 0 t, (9 / 10) * G 0 ≤ G r ∧ G r ≤ (11 / 10) * G 0 := by
  have h0 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht.le⟩
  obtain ⟨s₁, hs₁, hmax₁⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 ht.le) hGc
  obtain ⟨s₂, hs₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 ht.le) hHc
  have hMG : ∀ r ∈ Icc (0 : ℝ) t, G r ≤ G s₁ := fun r hr => isMaxOn_iff.mp hmax₁ r hr
  have hMH : ∀ r ∈ Icc (0 : ℝ) t, H r ≤ H s₂ := fun r hr => isMaxOn_iff.mp hmax₂ r hr
  set MG := G s₁ with hMGdef
  set MH := H s₂ with hMHdef
  have hMG0 : 0 ≤ MG := (hG0 s₁ hs₁)
  have hMH0 : 0 ≤ MH := (hH0 s₂ hs₂)
  have hGM0 : G 0 ≤ MG := hMG 0 h0
  have hG00 : 0 ≤ G 0 := hG0 0 h0
  -- upper bound of G
  have hGup : ∀ r ∈ Icc (0 : ℝ) t, G r ≤ G 0 + (1 / 10000) * (4 * MG) := by
    intro r hr
    have hint : ∫ s in (0 : ℝ)..r, 4 * Lu * G s ≤ r * (4 * Lu * MG) :=
      integral_le_mul hr.1 hr.2 (continuousOn_const.mul hGc) (fun s hs => by
        have := hMG s hs
        have : 4 * Lu * G s ≤ 4 * Lu * MG :=
          mul_le_mul_of_nonneg_left this (by positivity)
        exact this)
    have h4 : r * (4 * Lu * MG) ≤ (1 / 10000) * (4 * MG) := by
      have := mul_le_of_le hr.2 hMG0 hLu hLt
      nlinarith [this]
    linarith [hGu r hr]
  have hMGle : MG ≤ (1001 / 1000) * G 0 := by
    have := hGup s₁ hs₁
    linarith
  -- upper bound of H
  have hHup : ∀ r ∈ Icc (0 : ℝ) t,
      H r ≤ H 0 + (1 / 10000) * (12 * MH) + t * (8 * (Lu ^ 2 / κ) * MG) := by
    intro r hr
    have hint : ∫ s in (0 : ℝ)..r, (12 * Lu * H s + 8 * (Lu ^ 2 / κ) * G s) ≤
        r * (12 * Lu * MH + 8 * (Lu ^ 2 / κ) * MG) := by
      refine integral_le_mul hr.1 hr.2 ?_ (fun s hs => ?_)
      · exact (continuousOn_const.mul hHc).add (continuousOn_const.mul hGc)
      · have h1 : 12 * Lu * H s ≤ 12 * Lu * MH :=
          mul_le_mul_of_nonneg_left (hMH s hs) (by positivity)
        have h2 : 8 * (Lu ^ 2 / κ) * G s ≤ 8 * (Lu ^ 2 / κ) * MG :=
          mul_le_mul_of_nonneg_left (hMG s hs) (by positivity)
        linarith
    have h5 : r * (12 * Lu * MH) ≤ (1 / 10000) * (12 * MH) := by
      have := mul_le_of_le hr.2 hMH0 hLu hLt
      nlinarith [this]
    have h6 : r * (8 * (Lu ^ 2 / κ) * MG) ≤ t * (8 * (Lu ^ 2 / κ) * MG) :=
      mul_le_mul_of_nonneg_right hr.2 (by positivity)
    have h7 : r * (12 * Lu * MH + 8 * (Lu ^ 2 / κ) * MG) =
        r * (12 * Lu * MH) + r * (8 * (Lu ^ 2 / κ) * MG) := by ring
    linarith [hHu r hr]
  have hMHle : MH * (1 - 12 / 10000) ≤ H 0 + t * (8 * (Lu ^ 2 / κ) * MG) := by
    have := hHup s₂ hs₂
    linarith
  -- multiply by κ t
  have hkt : 0 < κ * t := mul_pos hκ ht
  have hscaled : (κ * t) * (MH * (1 - 12 / 10000)) ≤
      (κ * t) * H 0 + 8 * (Lu * t) ^ 2 * MG := by
    have := mul_le_mul_of_nonneg_left hMHle hkt.le
    have e : (κ * t) * (t * (8 * (Lu ^ 2 / κ) * MG)) = 8 * (Lu * t) ^ 2 * MG := by
      field_simp
    nlinarith [this, e]
  have hκtH : (κ * t) * H 0 ≤ (1 / 10000) * G 0 := by
    have h1 : (κ * t) * H 0 ≤ (κ * t) * (lam * G 0) :=
      mul_le_mul_of_nonneg_left hHinit hkt.le
    have h2 : (κ * t) * (lam * G 0) = (κ * t * lam) * G 0 := by ring
    have h3 : (κ * t * lam) * G 0 ≤ (1 / 10000) * G 0 :=
      mul_le_mul_of_nonneg_right hkl hG00
    linarith
  have hLt2 : (Lu * t) ^ 2 ≤ (1 / 10000) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hLu ht.le) hLt 2
  have hterm : 8 * (Lu * t) ^ 2 * MG ≤ 8 * (1 / 10000) ^ 2 * MG := by
    have := mul_le_mul_of_nonneg_right hLt2 hMG0
    nlinarith [this]
  have hKM : (κ * t) * MH ≤ (1 / 5000) * G 0 := by
    have h1 : (κ * t) * (MH * (1 - 12 / 10000)) ≤
        (1 / 10000) * G 0 + 8 * (1 / 10000) ^ 2 * ((1001 / 1000) * G 0) := by
      have : 8 * (1 / 10000 : ℝ) ^ 2 * MG ≤ 8 * (1 / 10000) ^ 2 * ((1001 / 1000) * G 0) :=
        mul_le_mul_of_nonneg_left hMGle (by positivity)
      linarith
    have h2 : 0 ≤ (κ * t) * MH := mul_nonneg hkt.le hMH0
    nlinarith [h1, h2, hG00]
  intro r hr
  constructor
  · have hint : ∫ s in (0 : ℝ)..r, (2 * κ * H s + 4 * Lu * G s) ≤
        r * (2 * κ * MH + 4 * Lu * MG) := by
      refine integral_le_mul hr.1 hr.2 ?_ (fun s hs => ?_)
      · exact (continuousOn_const.mul hHc).add (continuousOn_const.mul hGc)
      · have h1 : 2 * κ * H s ≤ 2 * κ * MH :=
          mul_le_mul_of_nonneg_left (hMH s hs) (by positivity)
        have h2 : 4 * Lu * G s ≤ 4 * Lu * MG :=
          mul_le_mul_of_nonneg_left (hMG s hs) (by positivity)
        linarith
    have h5 : r * (2 * κ * MH) ≤ (κ * t) * MH * 2 := by
      have : r * (2 * κ * MH) ≤ t * (2 * κ * MH) :=
        mul_le_mul_of_nonneg_right hr.2 (by positivity)
      nlinarith [this]
    have h6 : r * (4 * Lu * MG) ≤ (1 / 10000) * (4 * MG) := by
      have := mul_le_of_le hr.2 hMG0 hLu hLt
      nlinarith [this]
    have h7 : r * (2 * κ * MH + 4 * Lu * MG) =
        r * (2 * κ * MH) + r * (4 * Lu * MG) := by ring
    linarith [hGl r hr]
  · have := hMG r hr
    linarith
end AVenhance.Infra.FullTheorem.Separation
