/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPositivePairingAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimePairingInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmHalfCellGain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPerTimeAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmTransportedEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmMeasurability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourceRatesFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourceRatesGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.ScalarQuadraticL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.SourceErrorD
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Conditional assembly of the positive-time `H_m` bound

The one-instance quantitative leaves are the `HmGradientContract` and
`SourceErrorDContract`, together with the spacetime rate for the regular
part of the source. The family wrapper obtains the first two from their
datum producers, leaving only the regular-source rate as an input. The assembly
consumes the actual positive-time joint regularity fields and the
`HmMeasurability` adapters; no measurability premise is exposed to callers.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Ergodic
open scoped ContDiff

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration

theorem HmSup.hm_gradNormSq_nonneg (F : Vec 2 → Vec 2) :
    0 ≤ gradNormSq F := by
  unfold gradNormSq
  exact integral_nonneg fun x => vecNormSq_nonneg (F x)

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Conditional spacetime rate for the Piola scalar source in the actual
endpoint split. The old estimate for `(flux - Kmat) : ∇Gbar` does not
discharge this producer obligation. -/
def HmPiolaSourceRate (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (Creg B : ℝ) : Prop :=
  eLpNorm
      (fun z : ℝ × Vec 2 =>
        hmFrozenPiolaSource I hΦ m κm (T (Nstar β)) z.1 z.2)
      2 (volume.restrict AVenhance.timeCube) ≤
    ENNReal.ofReal
      (Creg * B * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
        (Real.sqrt κprev)⁻¹ *
        epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)))

/-- The chosen constants from the `l_recurse` and its scale
consequence.  Their definitions depend only on `(β,C₀)`, before any instance
data is supplied. -/
noncomputable def hmSupKappaLower (β C₀ : ℝ) : ℝ :=
  Classical.choose (AVenhance.l_recurse β C₀)

/-- Chosen upper diffusivity bound from the Hm recursion existence theorem. -/
noncomputable def hmSupKappaUpper (β C₀ : ℝ) : ℝ :=
  Classical.choose (Classical.choose_spec (AVenhance.l_recurse β C₀))

theorem hmSupKappaBounds_spec (β C₀ : ℝ) :
    0 < hmSupKappaLower β C₀ ∧
    hmSupKappaLower β C₀ < hmSupKappaUpper β C₀ ∧
    (∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
        (∀ m : ℕ, 1 ≤ m → m < M →
          hmSupKappaLower β C₀ * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) ≤
              I.kappaAt κ m (M - m) ∧
            I.kappaAt κ m (M - m) ≤
              hmSupKappaUpper β C₀ * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β))) ∧
        (∀ m : ℕ, 2 ≤ m → m < M →
          hmSupKappaLower β C₀ * epsilon β I.Λ (m - 1) ^ (4 * delta β) ≤
              epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ∧
            epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤
              hmSupKappaUpper β C₀ * epsilon β I.Λ (m - 1) ^ (4 * delta β))) := by
  exact Classical.choose_spec (Classical.choose_spec (AVenhance.l_recurse β C₀))

/-- Chosen scale constant satisfying the remaining Hm scale estimates. -/
noncomputable def hmSupScalesK (β C₀ : ℝ) : ℝ :=
  Classical.choose (AVenhance.Infra.Section5.LeftToShow.left_to_show_scales β C₀)

theorem hmSupScalesK_spec (β C₀ : ℝ) :
    1 ≤ hmSupScalesK β C₀ ∧
    (∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
        0 < I.kappaSeq κ M m ∧
        I.kappaSeq κ M m ≤ I.kappaSeq κ M (m - 1) ∧
        I.kappaSeq κ M (m - 1) ≤ hmSupScalesK β C₀ ∧
        a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m ≤
          hmSupScalesK β C₀ * I.kappaSeq κ M (m - 1) ∧
        epsilon β I.Λ m ^ 2 /
            (I.kappaSeq κ M m * tau β I.Λ m) ≤
          hmSupScalesK β C₀ * epsilon β I.Λ (m - 1) ^ (2 * delta β) ∧
        a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m ≤
          hmSupScalesK β C₀ * epsilon β I.Λ m ^ (-gamma β) ∧
        epsilon β I.Λ m ≤ hmSupScalesK β C₀ * epsilon β I.Λ (m - 1) ^ q β) := by
  exact Classical.choose_spec
    (AVenhance.Infra.Section5.LeftToShow.left_to_show_scales β C₀)

/-- Uniform coefficient delivered by the moving half-cell FTC. -/
noncomputable def hmSupRateConstant
    (β C₀ Cgrad Cd Creg : ℝ) : ℝ :=
  2 * Creg * hmSupScalesK β C₀ *
      Real.sqrt (hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) +
    Real.sqrt (2 * (2 * Cgrad) * Cd)

private theorem hmSup_contract_of_rates_Bound1 :
  ∀ {β C₀ Cgrad Cd Creg : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq
    I Φ) (κ : ℝ) (M m : ℕ) (θ₀ : Vec (2 : ℕ) → ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ),
  let κm : ℝ := I.kappaSeq κ M m;
  let κprev : ℝ := I.kappaSeq κ M (m - (1 : ℕ));
  let Tlast : ℝ → Vec (2 : ℕ) → ℝ := T (Nstar β);
  let B : ℝ := √(l2NormSq θ₀);
  let E : ℝ := epsilon β I.Λ (m - (1 : ℕ));
  let Qreg : ℝ := Creg * B * (a β I.Λ m ^ (2 : ℕ) * epsilon β I.Λ m ^ (4 : ℕ) / κm) * (√κprev)⁻¹
    * E ^ (-((1 : ℝ) + gamma β / (2 : ℝ)));
  let Qgrad : ℝ := Cgrad * E ^ ((4 : ℝ) * delta β) * (√κprev)⁻¹ * B;
  let Qd : ℝ := Cd * E ^ ((2 : ℝ) * delta β) * √κm * B;
  let Qflux : ℝ := (2 : ℝ) * (Qgrad * Qd);
  (1 : ℕ) ≤ m → (∀ (t : ℝ), (0 : ℝ) < t → IsZ2Periodic (I.Hm hΦ m κm (T (Nstar β)) t)) → (∀ (t :
    ℝ), (0 : ℝ) < t → IsZ2Periodic fun (x : Vec (2 : ℕ)) => hmFrozenPiolaSource I hΦ m κm (T
    (Nstar β)) t x + vecDiv (sourceErrorD I hΦ m κm (T (Nstar β)) t) x) → (∀ (t : ℝ), (0 : ℝ) <
    t → ∀ (i : Fin (2 : ℕ)), IsZ2Periodic fun (x : Vec (2 : ℕ)) => sourceErrorD I hΦ m κm (T
    (Nstar β)) t x i) → (∀ (t : ℝ), (0 : ℝ) < t → ContDiff ℝ (1 : ℕ∞ω) (I.Hm hΦ m κm (T (Nstar
    β)) t)) → (∀ (t : ℝ), (0 : ℝ) < t → Continuous (hmFrozenPiolaSource I hΦ m κm (T (Nstar β))
    t)) → (∀ (t : ℝ), (0 : ℝ) < t → ContDiff ℝ (1 : ℕ∞ω) (sourceErrorD I hΦ m κm (T (Nstar β))
    t)) → ContinuousOn (fun (p : ℝ × Vec (2 : ℕ)) => I.Hm hΦ m κm (T (Nstar β)) p.1 (((fun (t :
    ℝ) => LeftToShow.xFlowDiffeo I hΦ m (0 : ℤ) t) p.1).toFun p.2)) (Ioi (0 : ℝ) ×ˢ univ) →
    ContinuousOn (fun (p : ℝ × Vec (2 : ℕ)) => (fun (x : Vec (2 : ℕ)) => hmFrozenPiolaSource I
    hΦ m κm (T (Nstar β)) p.1 x + vecDiv (sourceErrorD I hΦ m κm (T (Nstar β)) p.1) x) (((fun (t
    : ℝ) => LeftToShow.xFlowDiffeo I hΦ m (0 : ℤ) t) p.1).toFun p.2)) (Ioi (0 : ℝ) ×ˢ univ) → (∀
    (t : ℝ), (0 : ℝ) < t → ∀ (x : Vec (2 : ℕ)), HasDerivAt (fun (s : ℝ) => I.Hm hΦ m κm (T
    (Nstar β)) s (((fun (t : ℝ) => LeftToShow.xFlowDiffeo I hΦ m (0 : ℤ) t) s).toFun x)) ((fun
    (y : Vec (2 : ℕ)) => hmFrozenPiolaSource I hΦ m κm (T (Nstar β)) t y + vecDiv (sourceErrorD
    I hΦ m κm (T (Nstar β)) t) y) (((fun (t : ℝ) => LeftToShow.xFlowDiffeo I hΦ m (0 : ℤ) t)
    t).toFun x)) t) → (0 : ℝ) ≤ Qreg → (0 : ℝ) ≤ Qflux → ∀ (l : ℝ → ℤ), (∀ t ∈ Ioc (0 : ℝ) (1 :
    ℝ), √(max (hmHalfCellEndpointAt I m l t) t - min (hmHalfCellEndpointAt I m l t) t) * Qreg ≤
    Creg * hmSupScalesK β C₀ * √(hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) * epsilon β I.Λ (m
    - (1 : ℕ)) ^ delta β * B) →
  let c : ℝ → ℝ := hmHalfCellEndpointAt I m l;
  (∀ t ∈ Ioc (0 : ℝ) (1 : ℝ), (0 : ℝ) < c t ∧ c t ≤ (1 : ℝ)) → ((∀ t ∈ Ioc (0 : ℝ) (1 : ℝ), ∀ s
    ∈ Icc (min (c t) t) (max (c t) t), IntervalIntegrable (hmRegularPairing (F := I.Hm hΦ m κm
    Tlast) (G := hmFrozenPiolaSource I hΦ m κm Tlast)) volume (c t) s) ∧ (∀ t ∈ Ioc (0 : ℝ) (1 :
    ℝ), ∀ s ∈ Icc (min (c t) t) (max (c t) t), IntervalIntegrable (hmFluxPairing (F := I.Hm hΦ m
    κm Tlast) (V := sourceErrorD I hΦ m κm Tlast)) volume (c t) s) ∧ (∀ t ∈ Ioc (0 : ℝ) (1 : ℝ),
    ∀ (H : ℝ), (∀ s ∈ Icc (min (c t) t) (max (c t) t), √(l2NormSq (I.Hm hΦ m κm Tlast s)) ≤ H) →
    ∀ s ∈ Icc (min (c t) t) (max (c t) t), |∫ (r : ℝ) in c t..s, (hmRegularPairing (F := I.Hm hΦ
    m κm Tlast) (G := hmFrozenPiolaSource I hΦ m κm Tlast)) r| ≤ √(max (c t) t - min (c t) t) *
    Qreg * H) ∧ ∀ t ∈ Ioc (0 : ℝ) (1 : ℝ), ∀ s ∈ Icc (min (c t) t) (max (c t) t), |∫ (r : ℝ) in
    c t..s, (hmFluxPairing (F := I.Hm hΦ m κm Tlast) (V := sourceErrorD I hΦ m κm Tlast)) r| ≤
    √(2 : ℝ) * Qgrad * (√(2 : ℝ) * Qd)) → (∀ t ∈ Ioc (0 : ℝ) (1 : ℝ), ContinuousOn (fun (s : ℝ)
    => √(l2NormSq (I.Hm hΦ m κm Tlast s))) (Icc (min (c t) t) (max (c t) t))) →
  let _ : ℝ → PeriodicVolumePreservingDiffeomorphism (2 : ℕ) := fun (t : ℝ) =>
    LeftToShow.xFlowDiffeo I hΦ m (0 : ℤ) t;
  (2 : ℝ) * (Creg * hmSupScalesK β C₀ * √(hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) * E ^
    delta β * B) + √((2 : ℝ) * Qflux) ≤ hmSupRateConstant β C₀ Cgrad Cd Creg * E ^ delta β * B →
    ∀ t ∈ Ioc (0 : ℝ) (1 : ℝ), √(l2NormSq (I.Hm hΦ m κm Tlast t)) ≤ hmSupRateConstant β C₀ Cgrad
    Cd Creg * E ^ delta β * B
    := by
  intro β C₀ Cgrad Cd Creg I Φ hΦ κ M m θ₀ T κm κprev Tlast B E Qreg Qgrad Qd Qflux hm1 hFper
      hSourcePer hVper hF hG hV hComp hSourceComp hMaterial hQreg_nonneg hQflux_nonneg l hHalfGain
      c hEndpoint hPairData hNormCont_l X hScaleTotal t ht
  let a := min (c t) t
  let b := max (c t) t
  have ha : 0 < a := lt_min (hEndpoint t ht).1 ht.1
  have hab : a ≤ b := min_le_max
  have hanchor : c t ∈ Set.Icc a b := by
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hzero : I.Hm hΦ m κm Tlast (c t) = fun _ => 0 := by
    simpa [c, hmHalfCellEndpointAt] using
      (frozen_hm_halfCell_endpoints_zero I hΦ hm1 κm Tlast (l t)).1
  have hpair := hm_transported_norm_uniform_of_integrated_pairings
    (F := I.Hm hΦ m κm Tlast)
    (G := hmFrozenPiolaSource I hΦ m κm Tlast)
    (source := fun s x => hmFrozenPiolaSource I hΦ m κm Tlast s x +
      vecDiv (sourceErrorD I hΦ m κm Tlast s) x)
    (V := fun s => sourceErrorD I hΦ m κm Tlast s)
    X hFper hSourcePer hVper hF hG hV hComp hSourceComp
    (by intro s x; rfl) hMaterial ha hab hanchor hzero
    (hNormCont_l t ht) hQreg_nonneg hQflux_nonneg
    (by intro s hs; simpa [a, b, c] using hPairData.1 t ht s hs)
    (by intro s hs; simpa [a, b, c] using hPairData.2.1 t ht s hs)
    (by intro s hs H hEnvelope
        simpa [a, b, c] using hPairData.2.2.1 t ht H hEnvelope s hs)
    (by
      intro s hs
      calc
        _ ≤ (Real.sqrt 2 * Qgrad) * (Real.sqrt 2 * Qd) := by
          simpa [a, b, c] using hPairData.2.2.2 t ht s hs
        _ = 2 * (Qgrad * Qd) := by
          calc
            _ = (Real.sqrt 2) ^ 2 * (Qgrad * Qd) := by ring
            _ = 2 * (Qgrad * Qd) := by
              rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        _ = Qflux := by simp [Qflux])
  have hhalf := hHalfGain t ht
  have hfirst : 2 * (Real.sqrt (b - a) * Qreg) ≤
      2 * (Creg * hmSupScalesK β C₀ *
        Real.sqrt (hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) *
        E ^ delta β * B) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa [a, b, c, Qreg, E] using hhalf
  have hpoint := hpair t (by simp [a, b])
  calc
    _ ≤ (2 * Real.sqrt (b - a) * Qreg) + Real.sqrt (2 * Qflux) := hpoint
    _ = 2 * (Real.sqrt (b - a) * Qreg) + Real.sqrt (2 * Qflux) := by ring
    _ = Real.sqrt (2 * Qflux) + 2 * (Real.sqrt (b - a) * Qreg) := by ring
    _ ≤ Real.sqrt (2 * Qflux) + 2 * (Creg * hmSupScalesK β C₀ *
          Real.sqrt (hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) *
          E ^ delta β * B) := add_le_add_right hfirst (Real.sqrt (2 * Qflux))
    _ = 2 * (Creg * hmSupScalesK β C₀ *
          Real.sqrt (hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) *
          E ^ delta β * B) + Real.sqrt (2 * Qflux) := by ring
    _ ≤ hmSupRateConstant β C₀ Cgrad Cd Creg * E ^ delta β * B := hScaleTotal

private theorem hmSup_contract_of_rates_GradRoot1 :
  ∀ {β Cgrad : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (κ :
    ℝ) (M m : ℕ) (θ₀ : Vec (2 : ℕ) → ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ), HmGradientContract I hΦ m
    (I.kappaSeq κ M m) (I.kappaSeq κ M (m - (1 : ℕ))) T Cgrad √(l2NormSq θ₀) →
  let κm : ℝ := I.kappaSeq κ M m;
  let κprev : ℝ := I.kappaSeq κ M (m - (1 : ℕ));
  let Tlast : ℝ → Vec (2 : ℕ) → ℝ := T (Nstar β);
  let B : ℝ := √(l2NormSq θ₀);
  let E : ℝ := epsilon β I.Λ (m - (1 : ℕ));
  let Qgrad : ℝ := Cgrad * E ^ ((4 : ℝ) * delta β) * (√κprev)⁻¹ * B;
  (0 : ℝ) < E → (0 : ℝ) < κprev → (0 : ℝ) < κprev → √(spaceTimeGradNormSq fun (t : ℝ) (x : Vec
    (2 : ℕ)) => spaceGrad (I.Hm hΦ m κm Tlast t) x) ≤ Qgrad
    := by
  intro β Cgrad I Φ hΦ κ M m θ₀ T hGradient κm κprev Tlast B E Qgrad hE hκprevpos hκprevpos'
  have hsκ : 0 < Real.sqrt κprev := Real.sqrt_pos.2 hκprevpos'
  have hdiv : Real.sqrt (spaceTimeGradNormSq
      (fun t x => spaceGrad (I.Hm hΦ m κm Tlast t) x)) ≤
      (Cgrad * E ^ (4 * delta β) * B) / Real.sqrt κprev := by
    apply (le_div_iff₀ hsκ).2
    change Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
      (fun s x => spaceGrad (I.Hm hΦ m κm Tlast s) x)) ≤
      Cgrad * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B at hGradient
    nlinarith [hGradient]
  calc
    _ ≤ (Cgrad * E ^ (4 * delta β) * B) / Real.sqrt κprev := hdiv
    _ = Qgrad := by
      dsimp [Qgrad]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hκprevpos')]

/-- Assemble the positive-time `HmSupContract` from exactly the three
quantitative rates used by its proof: the gradient, `d_m`, and the Piola-source rate. The
    field-measurability and spacetime-rate adapters
discharge the measurability and vector `L²` inputs internally. -/
theorem hmSup_contract_of_rates
    {β C₀ Cgrad Cd Creg : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ)
    (hCzeta : I.Czeta ≤ C₀) (hCxi : I.Cxi ≤ C₀) (hChat : I.Chat ≤ C₀)
    (κ : ℝ) (hκPerm : κ ∈ permissibleSet β I.Λ)
    (M : ℕ) (hM : 1 ≤ M) (hPerm : κ ∈ permittedInterval β I.Λ M)
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (hmStart : mTheta0 β I.Λ R ≤ m) (hmM : m ≤ M)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1)))
      (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m (I.kappaSeq κ M m)
      (I.kappaSeq κ M (m - 1)) θ₀ θprev T)
    (hCgrad : 0 ≤ Cgrad) (hCd : 0 ≤ Cd) (hCreg : 0 ≤ Creg)
    (hGradient : HmGradientContract I hΦ m (I.kappaSeq κ M m)
      (I.kappaSeq κ M (m - 1)) T Cgrad (Real.sqrt (l2NormSq θ₀)))
    (hDcontract : SourceErrorDContract I hΦ m (I.kappaSeq κ M m) T Cd
      (Real.sqrt (l2NormSq θ₀)))
    (hRegular : HmPiolaSourceRate I hΦ m (I.kappaSeq κ M m)
      (I.kappaSeq κ M (m - 1)) T Creg (Real.sqrt (l2NormSq θ₀)))
    :
    HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T
      (hmSupRateConstant β C₀ Cgrad Cd Creg) := by
  classical
  let κm : ℝ := I.kappaSeq κ M m
  let κprev : ℝ := I.kappaSeq κ M (m - 1)
  let Tlast : ℝ → Vec 2 → ℝ := T (Nstar β)
  let B : ℝ := Real.sqrt (l2NormSq θ₀)
  let E : ℝ := epsilon β I.Λ (m - 1)
  let Qreg : ℝ := Creg * B *
    (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
      (Real.sqrt κprev)⁻¹ * E ^ (-(1 + gamma β / 2))
  let Qgrad : ℝ := Cgrad * E ^ (4 * delta β) *
    (Real.sqrt κprev)⁻¹ * B
  let Qd : ℝ := Cd * E ^ (2 * delta β) * Real.sqrt κm * B
  let Qflux : ℝ := 2 * (Qgrad * Qd)
  have hβ : 1 < β := I.one_lt_beta
  have hβ' : β < 4 / 3 := I.beta_lt
  have hΛ : 2 ^ 7 ≤ I.Λ := I.two_pow_seven_le
  have hm2 : 2 ≤ m :=
    le_trans (AVenhance.Infra.Section5.mTheta0_spec hβ hβ' hΛ hR).1 hmStart
  have hm1 : 1 ≤ m := by omega
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 < E := by
    dsimp [E]
    exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hE1 : E ≤ 1 := by
    dsimp [E]
    exact Infra.Construction.epsilon_le_one hβ hβ' hΛ
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ hβ'
  have hρ : 0 ≤ 2 * delta β := by positivity
  have hδpow : 0 ≤ E ^ (2 * delta β) := Real.rpow_nonneg hE.le _
  have hScale := hmSupScalesK_spec β C₀
  have hScaleData := hScale.2 I hCzeta hCxi hChat κ hκPerm M hM hPerm m hm2 hmM
  rcases hScaleData with
    ⟨hκmpos, hκmono, hκprevUpper, hProduct, _hExprat, _hFlux, _hEpsilon⟩
  have hκprevpos : 0 < κprev := lt_of_lt_of_le hκmpos hκmono
  have hκmpos' : 0 < κm := by simpa [κm] using hκmpos
  have hκprevpos' : 0 < κprev := by simpa [κprev] using hκprevpos
  have hκmono' : κm ≤ κprev := by simpa [κm, κprev] using hκmono
  have hκmnonneg : 0 ≤ κm := hκmpos'.le
  have hRec := hmSupKappaBounds_spec β C₀
  have hRecData := hRec.2.2 I hCzeta hCxi hChat κ hκPerm M hM hPerm
  have hKprev : κprev ≤ hmSupKappaUpper β C₀ *
      (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) := by
    have hbound := hRecData.1 (m - 1) (by omega) (by omega)
    simpa [κprev, Ingredients.kappaSeq] using hbound.2
  have hCκpos : 0 < hmSupKappaUpper β C₀ :=
    lt_trans hRec.1 hRec.2.1
  have hCκ : 0 ≤ hmSupKappaUpper β C₀ := hCκpos.le
  have hKone := hScale.1
  have hKnonneg : 0 ≤ hmSupScalesK β C₀ := le_trans (by norm_num) hKone
  have hRegularityData := hm_positive_time_actual_regular_data
    I hΦ hm1 hκmpos' hθprev hT
  rcases hRegularityData with
    ⟨hFper, hSourcePer, hVper, hPairCont, hHmJoint, hGJoint, hDivJoint,
      hF, hG, hV, hComp, hSourceComp, hMaterial, hNormCont⟩
  obtain ⟨hMeas_regular, hMeas_grad, hMeas_gradMag, hMeas_d, hMeas_dMag⟩ :=
    hm_actual_pairing_field_measurability I hΦ hm1 hκmpos' hθprev hT
  have hProduct' : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm ≤
      hmSupScalesK β C₀ * κprev := by simpa [κm, κprev] using hProduct
  have hQgrad_nonneg : 0 ≤ Qgrad := by
    dsimp [Qgrad]
    positivity
  have hQd_nonneg : 0 ≤ Qd := by
    dsimp [Qd]
    positivity
  have hQreg_nonneg : 0 ≤ Qreg := by
    dsimp [Qreg]
    positivity
  have hGradRoot : Real.sqrt (spaceTimeGradNormSq
      (fun t x => spaceGrad (I.Hm hΦ m κm Tlast t) x)) ≤ Qgrad := by
    exact @hmSup_contract_of_rates_GradRoot1 β Cgrad I Φ hΦ κ M m θ₀ T hGradient hE hκprevpos
        hκprevpos'
  have hGradBound : eLpNorm
      (fun z : ℝ × Vec 2 => spaceGrad (I.Hm hΦ m κm Tlast z.1) z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Qgrad := by
    convert hm_gradient_spacetime_eLpNorm_bound_of_contract
      I hΦ hm1 hκmpos' hκprevpos' hθprev hT hCgrad hB hGradient using 1
    dsimp [Qgrad, E, B]
    ring_nf
  have hDbound : eLpNorm
      (fun z : ℝ × Vec 2 => sourceErrorD I hΦ m κm Tlast z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Qd := by
    convert hm_sourceErrorD_spacetime_eLpNorm_bound_of_contract
      I hΦ hm1 hκmpos' hθprev hT hCd hB hDcontract using 1
  have hRegularValue : HmPiolaSourceRate I hΦ m κm κprev T Creg B := by
    simpa [κm, κprev, Tlast, B] using hRegular
  have hGbound : eLpNorm
      (fun z : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κm Tlast z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal Qreg := by
    change eLpNorm
      (fun z : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κm Tlast z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal
        (Creg * B * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
          (Real.sqrt κprev)⁻¹ *
          epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) at hRegularValue
    simpa [Qreg, E] using hRegularValue
  have hQdBound : Qd ≤ Cd * Real.sqrt κprev * B * E ^ (2 * delta β) := by
    have hsqrt : Real.sqrt κm ≤ Real.sqrt κprev := Real.sqrt_le_sqrt hκmono'
    calc
      Qd = (Cd * E ^ (2 * delta β) * B) * Real.sqrt κm := by
        dsimp [Qd]
        ring
      _ ≤ (Cd * E ^ (2 * delta β) * B) * Real.sqrt κprev :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = Cd * Real.sqrt κprev * B * E ^ (2 * delta β) := by ring
  have hScaleFlux := hm_pairing_scale_of_l2_source_rates
    (E := E) (δ := delta β) (ρ := 2 * delta β) (Θ := B) (κ := κprev)
    (Creg := 0) (Cgrad := 2 * Cgrad) (Cdm := Cd)
    (G := 0) (Grad := 2 * Qgrad) (D := Qd)
    hE hE1 hδ hρ hB hκprevpos' (by positivity) hCd hQd_nonneg
    (by norm_num)
    (by
      have : 2 * Qgrad =
          (2 * Cgrad) * E ^ (4 * delta β) *
            (Real.sqrt κprev)⁻¹ * B := by
        dsimp [Qgrad]
        ring
      rw [this])
    hQdBound
  have hScaleFlux' : Real.sqrt (2 * (2 * Qgrad * Qd)) ≤
      Real.sqrt (2 * (2 * Cgrad) * Cd) * E ^ delta β * B := by
    simpa using hScaleFlux
  have hQflux_nonneg : 0 ≤ Qflux := by dsimp [Qflux]; positivity
  have hFluxRoot : Real.sqrt (2 * Qflux) ≤
      Real.sqrt (2 * (2 * Cgrad) * Cd) * E ^ delta β * B := by
    calc
      _ = Real.sqrt (2 * (2 * Qgrad * Qd)) := by
        congr 1
        dsimp [Qflux]
        ring
      _ ≤ _ := hScaleFlux'
  have hGain := hm_positive_time_halfCell_source_gain_from_A5
    I hm1 hκmpos' hκprevpos' hCreg hKnonneg hCκ hB hQreg_nonneg
    hKprev hProduct' (by
      change Qreg ≤ Creg * B *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
          (Real.sqrt κprev)⁻¹ * E ^ (-(1 + gamma β / 2))
      rfl)
  obtain ⟨l, hIndex, hHalfGain⟩ := hm_positive_time_halfCell_index_of_gain I hGain
  let c : ℝ → ℝ := hmHalfCellEndpointAt I m l
  have hEndpoint : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      0 < c t ∧ c t ≤ 1 := by
    intro t ht
    exact ⟨(hIndex t ht).1, (hIndex t ht).2.1⟩
  have hPairData := hm_per_time_pairing_data_of_joint_fields_and_spacetime_eLpNorm
    (F := fun t => I.Hm hΦ m κm Tlast t)
    (G := fun t => hmFrozenPiolaSource I hΦ m κm Tlast t)
    (V := fun t => sourceErrorD I hΦ m κm Tlast t)
    (c := c) (QG := Qreg) (Qgrad := Qgrad) (QV := Qd)
    hEndpoint hFper hVper hF hV hHmJoint hGJoint hDivJoint
    hMeas_regular hQreg_nonneg hGbound
    hMeas_grad hMeas_gradMag (by positivity) hGradBound
    hMeas_d hMeas_dMag hQd_nonneg hDbound
  have hNormCont_l : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ContinuousOn (fun s => Real.sqrt (l2NormSq (I.Hm hΦ m κm Tlast s)))
        (Set.Icc (min (c t) t) (max (c t) t)) := by
    intro t ht
    exact hNormCont l
      (by intro s hs; exact (hIndex s hs).1) t ht
  let X : ℝ → PeriodicVolumePreservingDiffeomorphism 2 :=
    fun t => AVenhance.Infra.Section5.LeftToShow.xFlowDiffeo I hΦ m 0 t
  have hScaleTotal :
      2 * (Creg * hmSupScalesK β C₀ *
          Real.sqrt (hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) *
          E ^ delta β * B) + Real.sqrt (2 * Qflux) ≤
        hmSupRateConstant β C₀ Cgrad Cd Creg * E ^ delta β * B := by
    rw [hmSupRateConstant]
    calc
      _ ≤ 2 * (Creg * hmSupScalesK β C₀ *
            Real.sqrt (hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) *
          E ^ delta β * B) +
          Real.sqrt (2 * (2 * Cgrad) * Cd) * E ^ delta β * B :=
        add_le_add_right hFluxRoot
          (2 * (Creg * hmSupScalesK β C₀ *
            Real.sqrt (hmSupKappaUpper β C₀ * (2 : ℝ) ^ (-25 : ℤ)) *
            E ^ delta β * B))
      _ = _ := by ring
  have hBound : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      Real.sqrt (l2NormSq (I.Hm hΦ m κm Tlast t)) ≤
        hmSupRateConstant β C₀ Cgrad Cd Creg * E ^ delta β * B := by
    exact @hmSup_contract_of_rates_Bound1 β C₀ Cgrad Cd Creg I Φ hΦ κ M m θ₀ T hm1 hFper
        hSourcePer hVper hF hG hV hComp hSourceComp hMaterial hQreg_nonneg hQflux_nonneg l
        hHalfGain hEndpoint hPairData hNormCont_l hScaleTotal
  change ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
    Real.sqrt (l2NormSq
      (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t)) ≤
      hmSupRateConstant β C₀ Cgrad Cd Creg *
        epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)
  intro t ht
  simpa [κm, Tlast, E, B] using hBound t ht

/-- Family producer for the positive-time `HmSupContract`, conditional on the
Piola-source rate. The gradient and `d_m` rates are obtained from their
unconditional datum producers; their constants and the combined cutoff are
chosen before the `OnA7Instances` block. -/
theorem hmSup_contract_onA7_of_piola_source_rate (β C₀ Creg : ℝ) :
    ∃ CHs C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        HmPiolaSourceRate I hΦ m (I.kappaSeq κ M m)
          (I.kappaSeq κ M (m - 1)) T Creg (Real.sqrt (l2NormSq θ₀)) →
        HmSupContract I hΦ m (I.kappaSeq κ M m) θ₀ T CHs) := by
  obtain ⟨Cgrad, C₁grad, hGradientFamily⟩ := hmGradient_contract β C₀
  obtain ⟨Cd, C₁d, hDFamily⟩ := sourceErrorD_contract β C₀
  refine ⟨hmSupRateConstant β C₀ (max Cgrad 0) (max Cd 0) (max Creg 0),
    max C₁grad C₁d, ?_⟩
  intro I hCzeta hCxi hChat hC₁ Φ hΦ κ hκPerm M hM hPerm R hR θ₀ hθ₀smooth
    hθ₀periodic hθ₀mean hθ₀analytic m hmStart hmM θprev T hθprev hT hRegular
  have hC₁grad : C₁grad ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hC₁
  have hC₁d : C₁d ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hC₁
  have hGradient := hGradientFamily I hCzeta hCxi hChat hC₁grad Φ hΦ κ hκPerm
    M hM hPerm R hR θ₀ hθ₀smooth hθ₀periodic hθ₀mean hθ₀analytic
    m hmStart hmM θprev T hθprev hT
  have hD := hDFamily I hCzeta hCxi hChat hC₁d Φ hΦ κ hκPerm
    M hM hPerm R hR θ₀ hθ₀smooth hθ₀periodic hθ₀mean hθ₀analytic
    m hmStart hmM θprev T hθprev hT
  let B : ℝ := Real.sqrt (l2NormSq θ₀)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hβ : 1 < β := I.one_lt_beta
  have hβ' : β < 4 / 3 := I.beta_lt
  have hΛ : 2 ^ 7 ≤ I.Λ := I.two_pow_seven_le
  have hm2 : 2 ≤ m :=
    le_trans (mTheta0_spec hβ hβ' hΛ hR).1 hmStart
  have hScales := hmSupScalesK_spec β C₀
  have hScaleData := hScales.2 I hCzeta hCxi hChat κ hκPerm M hM hPerm m hm2 hmM
  rcases hScaleData with ⟨hκm, _, _, _, _, _, _⟩
  have hκmpos : 0 < I.kappaSeq κ M m := hκm
  have hEprev : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hEm : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hGradPow : 0 ≤ epsilon β I.Λ (m - 1) ^ (4 * delta β) :=
    Real.rpow_nonneg hEprev.le _
  have hGradient' : HmGradientContract I hΦ m (I.kappaSeq κ M m)
      (I.kappaSeq κ M (m - 1)) T (max Cgrad 0) B := by
    unfold HmGradientContract at hGradient ⊢
    calc
      _ ≤ Cgrad * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B := hGradient
      _ ≤ max Cgrad 0 * epsilon β I.Λ (m - 1) ^ (4 * delta β) * B := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hGradPow) hB
  have hDfactor : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      Real.sqrt (I.kappaSeq κ M m) * B := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hEprev.le _) (Real.sqrt_nonneg _)) hB
  have hDreal : Cd * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      Real.sqrt (I.kappaSeq κ M m) * B ≤
      max Cd 0 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
        Real.sqrt (I.kappaSeq κ M m) * B := by
    calc
      _ = Cd * (epsilon β I.Λ (m - 1) ^ (2 * delta β) *
          Real.sqrt (I.kappaSeq κ M m) * B) := by ring
      _ ≤ max Cd 0 * (epsilon β I.Λ (m - 1) ^ (2 * delta β) *
          Real.sqrt (I.kappaSeq κ M m) * B) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hDfactor
      _ = _ := by ring
  have hD' : SourceErrorDContract I hΦ m (I.kappaSeq κ M m) T
      (max Cd 0) B := by
    unfold SourceErrorDContract at hD ⊢
    exact hD.trans (ENNReal.ofReal_le_ofReal hDreal)
  have hRegFactor : 0 ≤ B *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m) *
      (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
      epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) := by
    positivity
  have hRegReal : Creg * B *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m) *
      (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
      epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) ≤
      max Creg 0 * B *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m) *
        (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
        epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) := by
    calc
      _ = Creg * (B *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m) *
          (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
          epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) := by ring
      _ ≤ max Creg 0 * (B *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m) *
          (Real.sqrt (I.kappaSeq κ M (m - 1)))⁻¹ *
          epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hRegFactor
      _ = _ := by ring
  have hRegular' : HmPiolaSourceRate I hΦ m (I.kappaSeq κ M m)
      (I.kappaSeq κ M (m - 1)) T (max Creg 0) B := by
    unfold HmPiolaSourceRate at hRegular ⊢
    exact hRegular.trans (ENNReal.ofReal_le_ofReal hRegReal)
  exact hmSup_contract_of_rates
    (β := β) (C₀ := C₀) (Cgrad := max Cgrad 0) (Cd := max Cd 0)
    (Creg := max Creg 0) I hΦ hCzeta hCxi hChat κ hκPerm M hM hPerm m R hR
    hmStart hmM θ₀ θprev T hθprev hT (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _) hGradient' hD' hRegular'

/- There is no unconditional family producer here: the Piola rate is an
explicit input until its producer is proved. -/

end AVenhance.Infra.Section5.Contracts

end
