/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Moving Taylor coefficients

Mathlib's `FormalMultilinearSeries.changeOrigin` is the bridge from one power
series at the ambient origin to Taylor coefficients at the moving centers
`(z, 0)`.  In particular, every coefficient in the distinguished variable is
an analytic function of `z`, with all radii controlled by the original series.
-/


namespace ClassicalComplexWPT

/-- Continuous-linear inclusion of the distinguished complex axis. -/
noncomputable def lastAxis (n : ℕ) : ℂ →L[ℂ] Ambient n :=
  ContinuousLinearMap.inr ℂ (Base n) ℂ

@[simp]
theorem lastAxis_apply (n : ℕ) (w : ℂ) : lastAxis n w = (0, w) := rfl

/-- The unit vector in the distinguished complex direction. -/
def lastDirection (n : ℕ) : Ambient n := (0, 1)

/-- The `k`-th (factorial-normalized) distinguished-variable Taylor coefficient at `(z, 0)`. -/
noncomputable def lastTaylorCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ) (z : Base n) : ℂ :=
  p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n)

/-- At the base origin, changing origin leaves the diagonal distinguished coefficient unchanged. -/
theorem lastTaylorCoefficient_zero {n k : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) :
    lastTaylorCoefficient p k 0 = p k (fun _ ↦ lastDirection n) := by
  classical
  unfold lastTaylorCoefficient FormalMultilinearSeries.changeOrigin
  rw [FormalMultilinearSeries.sum, tsum_eq_single 0]
  · simp only [FormalMultilinearSeries.changeOriginSeries]
    rw [Finset.sum_eq_single ⟨∅, by simp⟩]
    · exact FormalMultilinearSeries.changeOriginSeriesTerm_apply p k 0 ∅ (by simp)
        (0 : Ambient n) (lastDirection n)
    · intro b _ hb
      exact (hb (Subtype.ext (Finset.card_eq_zero.mp b.property))).elim
    · simp
  · intro b hb
    cases b with
    | zero => exact (hb rfl).elim
    | succ b =>
      apply ContinuousMultilinearMap.map_coord_zero _ (0 : Fin (b + 1))
      rfl

/--
The moving coefficient at the base origin is the usual factorial-normalized
iterated derivative of the distinguished slice.
-/
theorem factorial_smul_lastTaylorCoefficient_zero {n k : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    k.factorial • lastTaylorCoefficient p k 0 =
      iteratedDeriv k (lastSlice f) 0 := by
  have hpa0 : HasFPowerSeriesAt (fun w : ℂ ↦ f ((0 : Base n), w))
      (p.compContinuousLinearMap (lastAxis n)) 0 := by
    simpa [lastAxis, Function.comp_def] using
      hp.compContinuousLinearMap (u := lastAxis n) (x := (0 : ℂ))
  have hpa : HasFPowerSeriesAt (lastSlice f)
      (p.compContinuousLinearMap (lastAxis n)) 0 := by
    change HasFPowerSeriesAt (fun w : ℂ ↦ f ((0 : Base n), w))
      (p.compContinuousLinearMap (lastAxis n)) 0
    exact hpa0
  have hc := hpa.analyticAt.hasFPowerSeriesAt
  have heq := hpa.eq_formalMultilinearSeries hc
  have hcoeff := congrArg
    (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q k (fun _ ↦ (1 : ℂ))) heq
  have hcoeff' : p k (fun _ ↦ lastDirection n) =
      iteratedDeriv k (lastSlice f) 0 / k.factorial := by
    simpa [lastAxis, lastDirection, FormalMultilinearSeries.compContinuousLinearMap,
      FormalMultilinearSeries.ofScalars] using hcoeff
  rw [lastTaylorCoefficient_zero, hcoeff', nsmul_eq_mul]
  have hfact : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  exact mul_div_cancel₀ _ hfact

/-- Vanishing of a directional Taylor coefficient is equivalent to vanishing of the derivative. -/
theorem lastTaylorCoefficient_zero_iff_iteratedDeriv_zero {n k : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    lastTaylorCoefficient p k 0 = 0 ↔ iteratedDeriv k (lastSlice f) 0 = 0 := by
  rw [← factorial_smul_lastTaylorCoefficient_zero p hp]
  simp [nsmul_eq_mul, Nat.factorial_ne_zero]

/-- The public exact-order condition is exactly the first-nonzero-coefficient condition. -/
theorem exactOrderInLastVariable_iff_lastTaylorCoefficients {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (hp : HasFPowerSeriesAt f p 0) :
    ExactOrderInLastVariable f d ↔
      (∀ k < d, lastTaylorCoefficient p k 0 = 0) ∧
        lastTaylorCoefficient p d 0 ≠ 0 := by
  constructor
  · rintro ⟨hlow, htop⟩
    refine ⟨fun k hk ↦
      (lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mpr (hlow k hk), ?_⟩
    intro hzero
    exact htop ((lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mp hzero)
  · rintro ⟨hlow, htop⟩
    refine ⟨fun k hk ↦
      (lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mp (hlow k hk), ?_⟩
    intro hzero
    exact htop ((lastTaylorCoefficient_zero_iff_iteratedDeriv_zero p hp).mpr hzero)

/-- Every moving distinguished-variable coefficient is analytic in the base variables. -/
theorem analyticAt_lastTaylorCoefficient {n k : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : 0 < p.radius) :
    AnalyticAt ℂ (lastTaylorCoefficient p k) 0 := by
  let ev : ((Ambient n)[×k]→L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ Ambient n) ℂ
      (fun _ ↦ lastDirection n)
  have hc : AnalyticAt ℂ (fun z : Base n ↦ p.changeOrigin (z, 0) k) 0 :=
    (p.analyticAt_changeOrigin hp k).comp (f := fun z : Base n ↦ (z, (0 : ℂ)))
      (analyticAt_id.prod analyticAt_const :
        AnalyticAt ℂ (fun z : Base n ↦ (z, (0 : ℂ))) 0)
  have hev : AnalyticAt ℂ ev (p.changeOrigin (0, 0) k) := ev.analyticAt _
  change AnalyticAt ℂ
    (fun z : Base n ↦ p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n)) 0
  simpa [ev, Function.comp_def] using
    hev.comp (f := fun z : Base n ↦ p.changeOrigin (z, 0) k) hc

/-- An analytic germ admits one ambient series whose moving last-variable
coefficients are analytic. -/
theorem AnalyticAt.exists_powerSeries_with_analytic_lastCoefficients
    {n : ℕ} {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ p : FormalMultilinearSeries ℂ (Ambient n) ℂ,
      HasFPowerSeriesAt f p 0 ∧
        ∀ k, AnalyticAt ℂ (lastTaylorCoefficient p k) 0 := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp, fun k ↦ analyticAt_lastTaylorCoefficient p hp.radius_pos⟩

end ClassicalComplexWPT
