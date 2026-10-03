/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AnalyticDerivativeTail
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceSpectrum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.Combination
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragedCompositionNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaProfileDischarge

/-! # recombine the low Fourier trace and analytic tail -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Ergodic
open AVenhance.Infra.Torus

theorem TraceInstanceRecombination.orderedRealDerivative_contDiff_instance (w : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (orderedRealDerivative w f) := by
  induction w with
  | nil => simpa [orderedRealDerivative] using hf
  | cons i w ih =>
      simpa [orderedRealDerivative] using
        (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem TraceInstanceRecombination.orderedRealDerivative_add_instance (w : List (Fin 2))
    {f g : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    orderedRealDerivative w (f + g) =
      orderedRealDerivative w f + orderedRealDerivative w g := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      have hfd := TraceInstanceRecombination.orderedRealDerivative_contDiff_instance w hf
      have hgd := TraceInstanceRecombination.orderedRealDerivative_contDiff_instance w hg
      have hfc := hfd.differentiable (by simp)
      have hgc := hgd.differentiable (by simp)
      funext x
      change fderiv ℝ (orderedRealDerivative w (f + g)) x (basisVec i) = _
      rw [ih, fderiv_add (hfc x) (hgc x), add_apply]
      rfl

theorem TraceInstanceRecombination.continuous_cell_l2_add_le
    {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Real.sqrt (∫ x in unitCell 2, (f x + g x) ^ 2) ≤
      Real.sqrt (∫ x in unitCell 2, f x ^ 2) +
        Real.sqrt (∫ x in unitCell 2, g x ^ 2) := by
  let μ : Measure (Vec 2) := volume.restrict (unitCell 2)
  have hfm : MemLp f 2 μ := by
    exact continuous_unitCell_memLp hf 2
  have hgm : MemLp g 2 μ := by
    exact continuous_unitCell_memLp hg 2
  have hsum : MemLp (f + g) 2 μ := hfm.add hgm
  have hfi := hfm.integrable_sq
  have hgi := hgm.integrable_sq
  have hsi := hsum.integrable_sq
  have hfeq := AVenhance.Infra.Section4.amnr_scalar_eLpNorm_two_eq_sqrt
    (f := f) hfm.aestronglyMeasurable hfi
  have hgeq := AVenhance.Infra.Section4.amnr_scalar_eLpNorm_two_eq_sqrt
    (f := g) hgm.aestronglyMeasurable hgi
  have hseq := AVenhance.Infra.Section4.amnr_scalar_eLpNorm_two_eq_sqrt
    (f := f + g) hsum.aestronglyMeasurable hsi
  have htriangle : eLpNorm (f + g) 2 μ ≤
      eLpNorm f 2 μ + eLpNorm g 2 μ :=
    eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
  rw [hseq, hfeq, hgeq, ← ENNReal.ofReal_add
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)] at htriangle
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htriangle
  change Real.sqrt (∫ x, (f x + g x) ^ 2 ∂μ) ≤
    Real.sqrt (∫ x, f x ^ 2 ∂μ) + Real.sqrt (∫ x, g x ^ 2 ∂μ) at hreal
  simpa [μ] using hreal

theorem TraceInstanceRecombination.ordered_eq_classical_instance (w : List (Fin 2))
    (f : Vec 2 → ℝ) :
    orderedRealDerivative w f =
      AVenhance.Infra.Section4.classicalWordDerivative w f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      funext x
      simp [orderedRealDerivative,
        AVenhance.Infra.Section4.classicalWordDerivative,
        AVenhance.Infra.Classical.classicalWordDerivative, AVenhance.spaceGrad, ih]

/-- A positive-order derivative of the sum of the low projection and its
spectral complement is bounded by the sum of their cell `L²` bounds. -/
theorem e44_initialDerivative_cell_l2_le_low_add_high
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ ∞ g) (M : ℕ)
    (w : List (Fin 2)) :
    Real.sqrt (∫ x in unitCell 2,
      (orderedRealDerivative w g x) ^ 2) ≤
      Real.sqrt (∫ x in unitCell 2,
        (orderedRealDerivative w (lowProjection g M) x) ^ 2) +
      Real.sqrt (∫ x in unitCell 2,
        (orderedRealDerivative w (highRemainder g M) x) ^ 2) := by
  have hlow : ContDiff ℝ ∞ (lowProjection g M) :=
    (lowProjection_contDiff M).of_le le_top
  have hhigh : ContDiff ℝ ∞ (highRemainder g M) := highRemainder_contDiff hg M
  have hsplit : (fun x => g x) = lowProjection g M + highRemainder g M := by
    funext x
    simp [highRemainder]
  have hderiv : orderedRealDerivative w g =
      orderedRealDerivative w (lowProjection g M) +
        orderedRealDerivative w (highRemainder g M) := by
    calc
      orderedRealDerivative w g =
          orderedRealDerivative w (lowProjection g M + highRemainder g M) := by
            exact congrArg (orderedRealDerivative w) hsplit
      _ = _ := TraceInstanceRecombination.orderedRealDerivative_add_instance w hlow hhigh
  rw [hderiv]
  exact TraceInstanceRecombination.continuous_cell_l2_add_le
    (TraceInstanceRecombination.orderedRealDerivative_contDiff_instance w hlow).continuous
    (TraceInstanceRecombination.orderedRealDerivative_contDiff_instance w hhigh).continuous

/-- The AV-facing scalar assembly used after the low-mode trace and analytic
tail estimates have been instantiated. The tail absorption and mean-zero
Poincare estimate are kept explicit so callers can verify their exact scales. -/
theorem e44_initialDerivative_bound_of_low_high
    {w : List (Fin 2)} {r R A ν S N Cₚ Cₜ c : ℝ}
    {low high total : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (hA : 1 ≤ A)
    (hν : 0 < ν) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hCp : 0 ≤ Cₚ) (hCt : 1 ≤ Cₜ)
    (habs : (Real.sqrt ν)⁻¹ * Real.exp (-c * R * (A / r)) ≤ 1)
    (hPoincare : N ≤ Cₚ * (Real.sqrt ν)⁻¹ * S)
    (hlow : low ≤ 2 * Real.exp 1 * (A / r) ^ w.length * S)
    (hhigh : high ≤ Cₜ * (w.length.factorial : ℝ) *
      (Cₜ / R) ^ w.length * Real.exp (-c * R * (A / r)) * N)
    (htotal : total ≤ low + high) :
    total ≤ (2 * Real.exp 1 + Cₜ * Cₚ) * (w.length.factorial : ℝ) *
      (max A Cₜ / r) ^ w.length * S :=
  e44_combine_low_mode_and_analytic_tail hr hR hA hν hS hN hCp hCt
    habs hPoincare low high total hlow hhigh htotal

/-- Explicit scalar used to turn the low/high estimate into a radius-loss
trace. It depends only on the cutoff amplitude and the two scalar estimate
constants, so it can be fixed before the Ingredients instance. -/
def e44TraceCombinationConstant (A Cₚ Cₜ : ℝ) : ℝ :=
  max 1 (max (2 * Real.exp 1 + Cₜ * Cₚ) (max A Cₜ))

/-- Convert the low/high derivative bounds into the exact positive-order
initial-trace shape consumed by the theta profile. The reduced radius is `r / Ctr^2` and
the amplitude remains `S`. -/
theorem e44_initialTrace_of_spectral_piece_bounds
    {g : Vec 2 → ℝ} {r R A ν S N Cₚ Cₜ c : ℝ} (M : ℕ)
    (hg : ContDiff ℝ ∞ g) (hr : 0 < r) (hR : r ≤ R) (hA : 1 ≤ A)
    (hν : 0 < ν) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hCp : 0 ≤ Cₚ) (hCt : 1 ≤ Cₜ)
    (habs : (Real.sqrt ν)⁻¹ * Real.exp (-c * R * (A / r)) ≤ 1)
    (hPoincare : N ≤ Cₚ * (Real.sqrt ν)⁻¹ * S)
    (hLow : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCell 2,
        (orderedRealDerivative w (lowProjection g M) x) ^ 2) ≤
        2 * Real.exp 1 * (A / r) ^ w.length * S)
    (hHigh : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCell 2,
        (orderedRealDerivative w
          (highRemainder g M) x) ^ 2) ≤
        Cₜ * (w.length.factorial : ℝ) * (Cₜ / R) ^ w.length *
          Real.exp (-c * R * (A / r)) * N) :
    ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in AVenhance.unitCube,
        (AVenhance.Infra.Section4.classicalWordDerivative w g x) ^ 2) ≤
      S * ((w.length.factorial : ℝ) /
        (r / e44TraceCombinationConstant A Cₚ Cₜ ^ 2) ^ w.length) := by
  let Csum := 2 * Real.exp 1 + Cₜ * Cₚ
  let Cscale := max A Cₜ
  let Ctr := e44TraceCombinationConstant A Cₚ Cₜ
  have hCtr1 : 1 ≤ Ctr := by dsimp [Ctr]; exact le_max_left _ _
  have hCtr0 : 0 < Ctr := lt_of_lt_of_le (by norm_num) hCtr1
  have hsumCtr : Csum ≤ Ctr := by
    dsimp [Ctr]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hscaleCtr : Cscale ≤ Ctr := by
    dsimp [Ctr]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  change ∀ w : List (Fin 2), 1 ≤ w.length →
    Real.sqrt (∫ x in AVenhance.unitCube,
      (AVenhance.Infra.Section4.classicalWordDerivative w g x) ^ 2) ≤
    S * ((w.length.factorial : ℝ) / (r / Ctr ^ 2) ^ w.length)
  intro w hw
  let low := Real.sqrt (∫ x in unitCell 2,
    (orderedRealDerivative w (lowProjection g M) x) ^ 2)
  let high := Real.sqrt (∫ x in unitCell 2,
    (orderedRealDerivative w (highRemainder g M) x) ^ 2)
  let total := Real.sqrt (∫ x in unitCell 2,
    (orderedRealDerivative w g x) ^ 2)
  have hMlow := e44_initialDerivative_cell_l2_le_low_add_high hg M w
  have htotal : total ≤ low + high := by
    dsimp [total, low, high] at hMlow ⊢
    exact hMlow
  have hcombined := e44_initialDerivative_bound_of_low_high
    (w := w) (r := r) (R := R) (A := A) (ν := ν) (S := S)
    (N := N) (Cₚ := Cₚ) (Cₜ := Cₜ) (c := c)
    hr hR hA hν hS hN hCp hCt habs hPoincare
    (low := low) (high := high) (total := total)
    (by simpa [low] using hLow w hw)
    (by simpa [high] using hHigh w hw) htotal
  have hcoef : Csum * (Cscale / r) ^ w.length ≤
      (Ctr ^ 2 / r) ^ w.length := by
    have hbase : Cscale / r ≤ Ctr / r :=
      div_le_div_of_nonneg_right hscaleCtr hr.le
    have hpow : (Cscale / r) ^ w.length ≤ (Ctr / r) ^ w.length :=
      pow_le_pow_left₀ (by positivity) hbase _
    have hpowCtr : Ctr ^ (w.length + 1) ≤ Ctr ^ (2 * w.length) :=
      pow_le_pow_right₀ hCtr1 (by omega)
    have hlast : Ctr * (Ctr / r) ^ w.length ≤
        (Ctr ^ 2 / r) ^ w.length := by
      have hfirst : Ctr * (Ctr / r) ^ w.length =
          Ctr ^ (w.length + 1) / r ^ w.length := by
        rw [div_pow]
        rw [pow_succ]
        ring
      have hsecond : (Ctr ^ 2 / r) ^ w.length =
          Ctr ^ (2 * w.length) / r ^ w.length := by
        rw [div_pow, ← pow_mul]
      rw [hfirst, hsecond]
      exact div_le_div_of_nonneg_right hpowCtr (by positivity)
    have htmp : Csum * (Cscale / r) ^ w.length ≤
        Ctr * (Ctr / r) ^ w.length := by
      exact mul_le_mul hsumCtr hpow (by positivity) (by positivity)
    calc
      Csum * (Cscale / r) ^ w.length ≤
          Ctr * (Ctr / r) ^ w.length := htmp
      _ ≤ (Ctr ^ 2 / r) ^ w.length := hlast
  have hfact : 0 ≤ (w.length.factorial : ℝ) := Nat.cast_nonneg _
  have hSc : 0 ≤ S := hS
  have hfinalCell : total ≤
      S * ((w.length.factorial : ℝ) / (r / Ctr ^ 2) ^ w.length) := by
    have hfactor := hcoef
    have hscaled := mul_le_mul_of_nonneg_right hfactor
      ((mul_nonneg hfact hSc))
    have hcombine' : total ≤ Csum * (w.length.factorial : ℝ) *
        (Cscale / r) ^ w.length * S := by
      simpa [Csum, Cscale] using hcombined
    calc
      total ≤ Csum * (w.length.factorial : ℝ) *
          (Cscale / r) ^ w.length * S := hcombine'
      _ ≤ (w.length.factorial : ℝ) *
          (Ctr ^ 2 / r) ^ w.length * S := by
            nlinarith [hscaled]
      _ = S * ((w.length.factorial : ℝ) /
          (r / Ctr ^ 2) ^ w.length) := by
            have hbase : Ctr ^ 2 / r = (r / Ctr ^ 2)⁻¹ := by
              field_simp [ne_of_gt hr, ne_of_gt hCtr0]
            rw [hbase, div_eq_mul_inv, ← inv_pow]
            ring
  have hcube :
      Real.sqrt (∫ x in AVenhance.unitCube,
        (AVenhance.Infra.Section4.classicalWordDerivative w g x) ^ 2) = total := by
    rw [← integral_unitCell_eq_unitCube]
    rw [← TraceInstanceRecombination.ordered_eq_classical_instance]
  rw [hcube]
  exact hfinalCell

end AVenhance.Infra.Section5.RelativeError

end
