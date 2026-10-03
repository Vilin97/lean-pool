/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Seed
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SeedMultiplierSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.MaterialMixedJets

/-! Amplitude-generic adapter for the correction tensor recursion.

The hypotheses are primitive seed, temperature, and velocity profiles. The
conclusion is the actual `I.Amnr` field with separate spatial and material
rates, so the amplitude can be set from the relative energy scale. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open AVenhance.Infra.Section4

namespace AVenhance.Infra.Section5.RelativeError

/-- The uniform finite-recursion factor in the AMNR tensor estimate. -/
def relativeAmnrRecursionConstant (β F G Cb : ℝ) : ℝ :=
  (2 : ℝ) ^ (AVenhance.Nstar β + 1) * F * G *
    (1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Cb) ^ AVenhance.Jcut β

/-- The finite mixed-material induction factor. -/
def relativeMixedTemperatureConstant (β Ccoeff Cb Cd : ℝ) : ℝ :=
  1 + 2 * Cd *
      (amnrNormalOrderConstant (AVenhance.Nstar β) Cb (AVenhance.Nstar β) *
        (amnrCanonicalSamples (AVenhance.Nstar β) (AVenhance.Nstar β)).card) *
        (1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Ccoeff) +
    (2 : ℝ) ^ (AVenhance.Nstar β + 1) * Cb

/-- Primitive amplitude profiles imply the exact mixed-word estimate for the
actual AMNR correction tensors. In applications use `L = r⁻¹`,
`Q = (tauP)⁻¹`, `F ≍ ε_m²/κ_m`, and `G ≍ S/√ν`. -/
theorem relative_Amnr_mixed_bounds_of_primitive_profiles {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol
      (AVenhance.streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (n : ℕ) (j k : Fin 2)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    {L Q F G Cb : ℝ} (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hCb : 0 ≤ Cb)
    (hSeed : ∀ i p w, IsAmnrMixedWord w → amnrBudget w ≤ AVenhance.Nstar β →
      ∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
          (amnrSeedMultiplier I hΦ m κm n j k i p) z| ≤ F * amnrWeight L Q w)
    (hTemperature : ∀ i, i ≤ AVenhance.Nstar β → ∀ p α r,
      α.length + 2 * r ≤ AVenhance.Nstar β →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord α r) (amnrTGradient (T i) p)) 2 μ ≤
          ENNReal.ofReal (G * amnrWeight L Q (amnrMixedWord α r)))
    (hVelocity : ∀ i p w, IsAmnrMixedWord w →
      amnrBudget w + 2 ≤ AVenhance.Nstar β →
      ∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
          (amnrVelocityGradient
            (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) i p) z| ≤
            Cb * Q * amnrWeight L Q w)
    (ρ : ℕ) (hρ : ρ ≤ AVenhance.Jcut β) (α : List (Fin 2)) (ℓ : ℕ)
    (hbudget : α.length + 2 * ℓ ≤ AVenhance.Nstar β - 2 * ρ) :
    ∀ a : Fin 2,
    eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord α ℓ)
      (fun y => I.Amnr hΦ m κm n (T (AVenhance.Nstar β)) ρ y.1 y.2 a j k)) 2 μ ≤
      ENNReal.ofReal
        (relativeAmnrRecursionConstant β F G Cb *
          L ^ α.length * Q ^ (ℓ + ρ)) := by
  let U : Set AmnrSpace := Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hbInf : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) :=
    contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ hm N)
  have hb : ContDiffOn ℝ (AVenhance.Nstar β)
      (fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) U :=
    (hbInf.of_le (by simp)).contDiffOn
  have hB (a p : Fin 2) : ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrVelocityGradient
        (fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) a p) U :=
    (amnrVelocityGradient_contDiffOn_infty hU hbInf.contDiffOn a p).of_le (by simp)
  obtain ⟨_, hfinal⟩ := amnr_tIterates_classical_family I hΦ hθprev hT
    (AVenhance.Nstar β) le_rfl
  have hg (p : Fin 2) : ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrTGradient (T (AVenhance.Nstar β)) p) U :=
    amnr_classical_gradient_smooth hfinal p (AVenhance.Nstar β)
  have hf (a p : Fin 2) : ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrSeedMultiplier I hΦ m κm n j k a p) U :=
    (amnr_seedMultiplier_contDiff I hΦ hm hκm n (AVenhance.Nstar β)
      le_rfl j k a p).contDiffOn
  have hTemperature' : ∀ p w, IsAmnrMixedWord w →
      amnrBudget w ≤ AVenhance.Nstar β →
      eLpNorm (amnrWord
        (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrTGradient (T (AVenhance.Nstar β)) p)) 2 μ ≤
          ENNReal.ofReal (G * amnrWeight L Q w) := by
    intro p w hw hbudgetw
    obtain ⟨η, r, rfl⟩ := IsAmnrMixedWord.normalForm hw
    have hcanonical : η.length + 2 * r ≤ AVenhance.Nstar β := by
      rw [amnrMixedWord_budget] at hbudgetw
      exact hbudgetw
    exact hTemperature (AVenhance.Nstar β) le_rfl p η r hcanonical
  intro a
  have hresult := Amnr_mixed_induction_of_factors I hΦ hm κm n
    (T (AVenhance.Nstar β)) hU hμ j k hb hB hf hg hL hQ hF hG hCb
    (fun i p w hw hbud z hz => hSeed i p w hw hbud z hz)
    hTemperature'
    (fun i p w hw hbud z hz => hVelocity i p w hw hbud z hz)
    ρ hρ α ℓ hbudget a
  simpa only [relativeAmnrRecursionConstant] using hresult

/-- Compose the temperature material induction with the actual
correction recursion. The only temperature estimate supplied is the
positive-order spatial profile at material level zero; higher material
temperature bounds are produced by `relative_mixed_material_jets_of_source_profiles`.
-/
theorem relative_Amnr_mixed_bounds_of_spatial_profiles {β : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev : ℝ} (hκm : 0 < κm) (hκprev : 0 < κprev)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : AVenhance.IsClassicalSol
      (AVenhance.streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (n : ℕ) (j k : Fin 2)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    {L Q G Ccoeff Cb Cd F : ℝ} (hL : 0 < L) (hQ : 0 < Q)
    (hG : 0 ≤ G) (hCcoeff : 0 ≤ Ccoeff) (hCb : 0 ≤ Cb)
    (hCd : 0 ≤ Cd) (hF : 0 ≤ F)
    (hRate : κprev * L ^ 2 ≤ Cd * Q)
    (hCoefficient : ∀ a p w, IsAmnrMixedWord w →
      amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
        |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
          (amnrTemperatureCoefficient I hΦ m κm κprev a p) z| ≤
            (Ccoeff * κprev) * amnrWeight L Q w)
    (hVelocityGradient : ∀ (a p : Fin 2) (α : List (Fin 2)) (r : ℕ),
      α.length + 2 * r + 2 ≤ AVenhance.Nstar β → ∀ z,
        |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
          (amnrMixedWord α r) (amnrVelocityGradient
            (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) a p) z| ≤
          (Cb * Q) * amnrWeight L Q (amnrMixedWord α r))
    (hSpatialGradient : ∀ (i : ℕ), i ≤ AVenhance.Nstar β →
      ∀ (p : Fin 2) (α : List (Fin 2)),
      α.length ≤ AVenhance.Nstar β →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (α.map some) (amnrTGradient (T i) p)) 2 μ ≤
          ENNReal.ofReal (G * L ^ α.length))
    (hSeed : ∀ a p w, IsAmnrMixedWord w →
      amnrBudget w ≤ AVenhance.Nstar β →
      ∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
          (amnrSeedMultiplier I hΦ m κm n j k a p) z| ≤ F * amnrWeight L Q w)
    (ρ : ℕ) (hρ : ρ ≤ AVenhance.Jcut β) (α : List (Fin 2)) (ℓ : ℕ)
    (hbudget : α.length + 2 * ℓ ≤ AVenhance.Nstar β - 2 * ρ) :
    ∀ a : Fin 2,
    eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord α ℓ)
      (fun y => I.Amnr hΦ m κm n (T (AVenhance.Nstar β)) ρ y.1 y.2 a j k)) 2 μ ≤
      ENNReal.ofReal
        (relativeAmnrRecursionConstant β F
          (G * relativeMixedTemperatureConstant β Ccoeff Cb Cd ^ AVenhance.Nstar β) Cb *
          L ^ α.length * Q ^ (ℓ + ρ)) := by
  let N := AVenhance.Nstar β
  let K := amnrNormalOrderConstant N Cb N * (amnrCanonicalSamples N N).card
  let Cmix := 1 + 2 * Cd * K * (1 + (2 : ℝ) ^ (N + 1) * Ccoeff) +
    (2 : ℝ) ^ (N + 1) * Cb
  have hK : 0 ≤ K := mul_nonneg
    (le_trans (by norm_num) (amnrNormalOrderConstant_one_le hCb N))
    (Nat.cast_nonneg _)
  have hCmix : 1 ≤ Cmix := by
    have hfirst : 0 ≤ 2 * Cd * K * (1 + (2 : ℝ) ^ (N + 1) * Ccoeff) := by positivity
    have hsecond : 0 ≤ (2 : ℝ) ^ (N + 1) * Cb := by positivity
    dsimp [Cmix]
    linarith
  have hCmix_nonneg : 0 ≤ Cmix := le_trans (by norm_num) hCmix
  let Gmix := G * Cmix ^ N
  have hGmix : 0 ≤ Gmix := mul_nonneg hG (pow_nonneg hCmix_nonneg _)
  have hRaw := relative_mixed_material_jets_of_source_profiles I hΦ hm hκm hκprev
    hθprev hT hμ hL hQ hG hCcoeff hCb hCd hRate
    hCoefficient hVelocityGradient hSpatialGradient
  dsimp only at hRaw
  have hMixed : ∀ (r i : ℕ), i ≤ N → ∀ p (η : List (Fin 2)),
      η.length + 2 * r ≤ N →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord η r) (amnrTGradient (T i) p)) 2 μ ≤
        ENNReal.ofReal (Cmix ^ r * G * amnrWeight L Q (amnrMixedWord η r)) := by
    simpa only [N, K, Cmix] using hRaw
  have hTemperature : ∀ (i : ℕ), i ≤ N → ∀ (p : Fin 2) (η : List (Fin 2)) (r : ℕ),
      η.length + 2 * r ≤ N →
      eLpNorm (amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
        (amnrMixedWord η r) (amnrTGradient (T i) p)) 2 μ ≤
        ENNReal.ofReal (Gmix * amnrWeight L Q (amnrMixedWord η r)) := by
    intro i hi p η r hcanonical
    have hbase := hMixed r i hi p η hcanonical
    have hr : r ≤ N := by omega
    have hpow : Cmix ^ r ≤ Cmix ^ N := pow_le_pow_right₀ hCmix hr
    have hreal : Cmix ^ r * G * amnrWeight L Q (amnrMixedWord η r) ≤
        Gmix * amnrWeight L Q (amnrMixedWord η r) := by
      apply mul_le_mul_of_nonneg_right _ (amnrWeight_nonneg hL.le hQ.le _)
      have hscaled := mul_le_mul_of_nonneg_right hpow hG
      nlinarith only [hscaled]
    exact hbase.trans (ENNReal.ofReal_le_ofReal hreal)
  have hVelocity : ∀ a p w, IsAmnrMixedWord w →
      amnrBudget w + 2 ≤ N →
      ∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
          (amnrVelocityGradient
            (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) a p) z| ≤
          Cb * Q * amnrWeight L Q w := by
    intro a p w hw hbud z hz
    obtain ⟨η, r, rfl⟩ := IsAmnrMixedWord.normalForm hw
    have hcanonical : η.length + 2 * r + 2 ≤ N := by
      rw [amnrMixedWord_budget] at hbud
      exact hbud
    exact hVelocityGradient a p η r hcanonical z
  have hresult := relative_Amnr_mixed_bounds_of_primitive_profiles I hΦ hm hκm
    hθprev hT n j k hμ hL.le hQ.le hF hGmix hCb hSeed hTemperature hVelocity
    ρ hρ α ℓ hbudget
  simpa only [relativeMixedTemperatureConstant, Gmix, N, K, Cmix] using hresult

end AVenhance.Infra.Section5.RelativeError
