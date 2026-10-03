/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceProjectionSpectrum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceEuclideanClassical

/-! # apply the classical trace bridge to the square cutoff -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Ergodic
open AVenhance.Infra.Torus

/-- The cutoff `lowProjection g M` is contained in the Euclidean
frequency ball of radius `2π√2 M`. The spectral identities therefore feed
directly into the classical transport trace argument. -/
theorem classical_lowProjection_trace_bound
    {b : ℝ → Vec 2 → Vec 2} {κ B : ℝ}
    {g : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    (M : ℕ)
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hX : IsFlow b X)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    (hmax : max 1 B ≤ κ * (2 * Real.pi * Real.sqrt 2 * (M : ℝ)) ^ 2)
    (hB : 0 ≤ B) (hκ : 0 < κ) (hM : 0 < M)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    (hg : ContDiff ℝ 3 g) (hgper : IsZ2Periodic g) :
    Real.sqrt (gradNormSq (spaceGrad (lowProjection g M))) ≤
      2 * Real.exp 1 * (2 * Real.pi * Real.sqrt 2 * (M : ℝ)) *
      Real.sqrt κ *
        Real.sqrt (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) := by
  let f : Vec 2 → ℝ := lowProjection g M
  let K : ℝ := 2 * Real.pi * Real.sqrt 2 * (M : ℝ)
  let G : ℝ := Real.sqrt (gradNormSq (spaceGrad f))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hGdef : G = Real.sqrt (gradNormSq (spaceGrad f)) := rfl
  have hGnonneg : 0 ≤ G := Real.sqrt_nonneg _
  have hgradNonneg : 0 ≤ gradNormSq (spaceGrad f) := by
    unfold gradNormSq
    exact integral_nonneg (fun x => vecNormSq_nonneg _)
  have henergy : gradNormSq (spaceGrad f) = G ^ 2 := by
    rw [hGdef, Real.sq_sqrt hgradNonneg]
  have hinitial :
      (∫ x in unitCell 2, g x * (-spaceLap f x)) = G ^ 2 := by
    calc
      (∫ x in unitCell 2, g x * (-spaceLap f x)) =
          gradNormSq (spaceGrad f) :=
        by simpa [f] using lowProjection_initialPairing_eq_gradientEnergy hg hgper M
      _ = G ^ 2 := henergy
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa [f] using ((lowProjection_contDiff (f := g) M).of_le le_top)
  have hfper : IsZ2Periodic f :=
    (isZPeriodic_iff_isZ2Periodic f).1 (lowProjection_periodic (f := g) M)
  have hlapGrad :
      (∫ x in unitCell 2,
        vecNormSq (spaceGrad (fun x => -spaceLap f x) x)) ≤ K ^ 4 * G ^ 2 := by
    rw [← henergy]
    simpa [f, K] using lowProjection_laplacianGradient_energy_le (g := g) M
  have hmaxK : max 1 B ≤ κ * K ^ 2 := by
    simpa only [K] using hmax
  have htrace : G ≤ 2 * Real.exp 1 * K * Real.sqrt κ *
      Real.sqrt (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t) := by
    exact classical_lowMode_trace_bound_of_spectralFacts_euclidean
      (κ := κ) (K := K) (B := B) (G := G) (g := g) (f := f)
      (u := u) (X := X) hb hdiv hX hDb hmaxK hB hκ hK hGnonneg hsol
      hf hfper hinitial henergy hlapGrad
  exact htrace

end AVenhance.Infra.Section5.RelativeError

end
