/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialInduction

/-! Amplitude-generic adapters for the mixed temperature/material calculus.

The rate variables below are deliberately named L and Q: in the AMNR
engine they are the spatial and material rates, while the separate G is the
temperature-gradient amplitude. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
open AVenhance.Infra.Section4

namespace AVenhance.Infra.Section5.RelativeError

/-- Apply the mixed AMNR induction to the actual terminal iterate, keeping an
arbitrary gradient amplitude and keeping the two derivative rates separate.
The three quantitative inputs are the source coefficient, flow-gradient and
positive spatial-gradient bounds; the conclusion is the full mixed-word
profile used by the later RelativeError material adapters. -/
theorem relative_mixed_material_jets_of_source_profiles {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev : ℝ} (hκm : 0 < κm) (hκprev : 0 < κprev)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol (AVenhance.streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {μ : Measure AmnrSpace}
    (hμ : μ ≪ volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {L Q G Ccoeff Cb Cd : ℝ}
    (hL : 0 < L) (hQ : 0 < Q) (hG : 0 ≤ G)
    (hCcoeff : 0 ≤ Ccoeff) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hRate : κprev * L ^ 2 ≤ Cd * Q)
    (hCoefficient : ∀ j p w, IsAmnrMixedWord w →
      amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrTemperatureCoefficient I hΦ m κm κprev j p) z| ≤
          (Ccoeff * κprev) * amnrWeight L Q w)
    (hVelocityGradient : ∀ q p α n,
      α.length + 2 * n + 2 ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α n) (amnrVelocityGradient
          (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) q p) z| ≤
        (Cb * Q) * amnrWeight L Q (amnrMixedWord α n))
    (hSpatialGradient : ∀ i, i ≤ AVenhance.Nstar β → ∀ (p : Fin 2)
      (α : List (Fin 2)), α.length ≤ AVenhance.Nstar β →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (α.map some) (amnrTGradient (T i) p)) 2 μ ≤
          ENNReal.ofReal (G * L ^ α.length)) :
    let N := AVenhance.Nstar β
    let K := amnrNormalOrderConstant N Cb N * (amnrCanonicalSamples N N).card
    let Cmix := 1 + 2 * Cd * K * (1 + (2 : ℝ) ^ (N + 1) * Ccoeff) +
      (2 : ℝ) ^ (N + 1) * Cb
    ∀ (r i : ℕ), i ≤ N → ∀ p (α : List (Fin 2)), α.length + 2 * r ≤ N →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α r) (amnrTGradient (T i) p)) 2 μ ≤
        ENNReal.ofReal (Cmix ^ r * G * amnrWeight L Q (amnrMixedWord α r)) := by
  let N := AVenhance.Nstar β
  let K := amnrNormalOrderConstant N Cb N * (amnrCanonicalSamples N N).card
  let Cmix := 1 + 2 * Cd * K * (1 + (2 : ℝ) ^ (N + 1) * Ccoeff) +
    (2 : ℝ) ^ (N + 1) * Cb
  have hInd := AVenhance.Infra.Section4.amnr_tIterates_material_gradient_induction
    I hΦ hm hκm hκprev hθprev hT hμ hL hQ hG hCcoeff hCb hCd hRate
    hCoefficient hVelocityGradient hSpatialGradient
  intro N K Cmix r i hi p α hbudget
  exact hInd r i hi p α hbudget

end AVenhance.Infra.Section5.RelativeError
