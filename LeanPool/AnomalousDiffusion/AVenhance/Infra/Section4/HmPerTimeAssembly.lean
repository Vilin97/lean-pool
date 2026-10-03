/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPositivePairingAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmHalfCellGain

/-! Positive-time `H_m` assembly when the half-cell base point may vary with time.
The regular pairing retains its raw source coefficient; the scalar energy
closure uses the square-root-length gain supplied by `HmHalfCellGain`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Ergodic AVenhance.Infra.Section5

namespace AVenhance.Infra.Section4

/-- The refresh endpoint selected at time `t` by an index function `l`. -/
def hmHalfCellEndpointAt {β : ℝ} (I : AVenhance.Ingredients β)
    (m : ℕ) (l : ℝ → ℤ) (t : ℝ) : ℝ :=
  (l t + 1 / 2) * AVenhance.tauPP β I.Λ m

/-- Turn the existential endpoint and coefficient gain from
`hm_positive_time_halfCell_source_gain_from_A5` into the function-valued
interface used by the per-time assembler. -/
theorem hm_positive_time_halfCell_index_of_gain
    {β : ℝ} (I : AVenhance.Ingredients β) {m : ℕ}
    {Gsource Ghalf : ℝ}
    (hGain : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∃ j : ℤ,
        let c := (j + 1 / 2) * AVenhance.tauPP β I.Λ m
        0 < c ∧ c ≤ 1 ∧ max c t - min c t ≤ AVenhance.tauPP β I.Λ m ∧
          Real.sqrt (max c t - min c t) * Gsource ≤ Ghalf) :
    ∃ l : ℝ → ℤ,
      (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
        0 < hmHalfCellEndpointAt I m l t ∧
        hmHalfCellEndpointAt I m l t ≤ 1 ∧
        max (hmHalfCellEndpointAt I m l t) t -
          min (hmHalfCellEndpointAt I m l t) t ≤ AVenhance.tauPP β I.Λ m) ∧
      (∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
        Real.sqrt (max (hmHalfCellEndpointAt I m l t) t -
          min (hmHalfCellEndpointAt I m l t) t) * Gsource ≤ Ghalf) := by
  classical
  let l : ℝ → ℤ := fun t =>
    if ht : t ∈ Set.Ioc (0 : ℝ) 1 then Classical.choose (hGain t ht) else 0
  refine ⟨l, ?_, ?_⟩
  · intro t ht
    have hindex : l t = Classical.choose (hGain t ht) := by
      dsimp [l]
      rw [dite_eq_left ht]
    rcases Classical.choose_spec (hGain t ht) with
      ⟨hc, hc1, hlen, hcoef⟩
    change 0 < (((l t : ℝ) + 1 / 2) * AVenhance.tauPP β I.Λ m) ∧
      ((l t : ℝ) + 1 / 2) * AVenhance.tauPP β I.Λ m ≤ 1 ∧
      max (((l t : ℝ) + 1 / 2) * AVenhance.tauPP β I.Λ m) t -
        min (((l t : ℝ) + 1 / 2) * AVenhance.tauPP β I.Λ m) t ≤
          AVenhance.tauPP β I.Λ m
    rw [hindex]
    exact ⟨hc, hc1, hlen⟩
  · intro t ht
    have hindex : l t = Classical.choose (hGain t ht) := by
      dsimp [l]
      rw [dite_eq_left ht]
    rcases Classical.choose_spec (hGain t ht) with
      ⟨hc, hc1, hlen, hcoef⟩
    change Real.sqrt
      (max (((l t : ℝ) + 1 / 2) * AVenhance.tauPP β I.Λ m) t -
        min (((l t : ℝ) + 1 / 2) * AVenhance.tauPP β I.Λ m) t) * Gsource ≤ Ghalf
    rw [hindex]
    exact hcoef

/-- Assemble the positive-time `H_m` bounds with a time-dependent refresh
index. The regular pairing hypothesis uses the raw coefficient `Gsource`:
its Cauchy bound contains `sqrt(interval length) * Gsource`. The endpoint
gain hypothesis bounds that product by `Ghalf`, which is the coefficient
used in the scalar energy closure. This is the interface consumed by the
per-time half-cell estimate. -/
theorem frozen_hm_positive_time_bounds_of_pairings_per_time
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, 0 < t → IsZ2Periodic (I.Hm hΦ m κ T t))
    (hSourcePer : ∀ t, 0 < t → IsZ2Periodic
      (fun x => hmFrozenRegularSource I hΦ m κ T t x +
        AVenhance.vecDiv (sourceErrorD I hΦ m κ T t) x))
    (hVper : ∀ t, 0 < t → ∀ i : Fin 2,
      IsZ2Periodic (fun x => sourceErrorD I hΦ m κ T t x i))
    (hF : ∀ t, 0 < t → ContDiff ℝ 1 (I.Hm hΦ m κ T t))
    (hG : ∀ t, 0 < t → Continuous (hmFrozenRegularSource I hΦ m κ T t))
    (hV : ∀ t, 0 < t → ContDiff ℝ 1 (sourceErrorD I hΦ m κ T t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 =>
        (fun x => hmFrozenRegularSource I hΦ m κ T p.1 x +
          AVenhance.vecDiv (sourceErrorD I hΦ m κ T p.1) x)
          ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => I.Hm hΦ m κ T s ((X s).toFun x))
        ((fun y => hmFrozenRegularSource I hΦ m κ T t y +
          AVenhance.vecDiv (sourceErrorD I hΦ m κ T t) y)
          ((X t).toFun x)) t)
    {Gsource Ghalf Q C₀ E δ Θ C₁ Khalf : ℝ}
    (l : ℝ → ℤ)
    (hEndpoint : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      0 < hmHalfCellEndpointAt I m l t ∧
      hmHalfCellEndpointAt I m l t ≤ 1 ∧
      max (hmHalfCellEndpointAt I m l t) t -
        min (hmHalfCellEndpointAt I m l t) t ≤ AVenhance.tauPP β I.Λ m)
    (hHalfGain : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      Real.sqrt (max (hmHalfCellEndpointAt I m l t) t -
        min (hmHalfCellEndpointAt I m l t) t) * Gsource ≤ Ghalf)
    (hNormCont : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ContinuousOn
        (fun s => Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T s)))
        (Set.Icc (min (hmHalfCellEndpointAt I m l t) t)
          (max (hmHalfCellEndpointAt I m l t) t)))
    (hregInt : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc
        (min (hmHalfCellEndpointAt I m l t) t)
        (max (hmHalfCellEndpointAt I m l t) t),
        IntervalIntegrable (hmRegularPairing
          (F := I.Hm hΦ m κ T)
          (G := hmFrozenRegularSource I hΦ m κ T)) volume
          (hmHalfCellEndpointAt I m l t) s)
    (hfluxInt : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc
        (min (hmHalfCellEndpointAt I m l t) t)
        (max (hmHalfCellEndpointAt I m l t) t),
        IntervalIntegrable (hmFluxPairing
          (F := I.Hm hΦ m κ T) (V := sourceErrorD I hΦ m κ T) ) volume
          (hmHalfCellEndpointAt I m l t) s)
    (hregBound : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 → ∀ H : ℝ,
      (∀ s ∈ Set.Icc
        (min (hmHalfCellEndpointAt I m l t) t)
        (max (hmHalfCellEndpointAt I m l t) t),
        Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T s)) ≤ H) →
      ∀ s ∈ Set.Icc
        (min (hmHalfCellEndpointAt I m l t) t)
        (max (hmHalfCellEndpointAt I m l t) t),
        |∫ r in (hmHalfCellEndpointAt I m l t)..s,
          hmRegularPairing (F := I.Hm hΦ m κ T)
            (G := hmFrozenRegularSource I hΦ m κ T) r| ≤
          Real.sqrt (max (hmHalfCellEndpointAt I m l t) t -
            min (hmHalfCellEndpointAt I m l t) t) * Gsource * H)
    (hfluxBound : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc
        (min (hmHalfCellEndpointAt I m l t) t)
        (max (hmHalfCellEndpointAt I m l t) t),
        |∫ r in (hmHalfCellEndpointAt I m l t)..s,
          hmFluxPairing (F := I.Hm hΦ m κ T)
            (V := sourceErrorD I hΦ m κ T) r| ≤ Q)
    (hGsourceNonneg : 0 ≤ Gsource) (hQnonneg : 0 ≤ Q)
    (hScale : 2 * Ghalf + Real.sqrt (2 * Q) ≤ C₀ * E ^ δ * Θ)
    (hD : ∀ r ∈ Finset.range (AVenhance.Jcut β), ∀ t x,
      DifferentiableAt ℝ (fun y : Vec 2 => I.Hmr hΦ m κ T r t y) x)
    (hGradHmr : ∀ r ∈ Finset.range (AVenhance.Jcut β),
      eLpNorm (fun z : ℝ × Vec 2 =>
        AVenhance.spaceGrad (fun x => I.Hmr hΦ m κ T r z.1 x) z.2) 2
          (volume.restrict AVenhance.timeCube) ≤
        ENNReal.ofReal (C₁ * E ^ (4 * δ) * Khalf * Θ))
    (hE : 0 ≤ E) (hC₁ : 0 ≤ C₁) (hΘ : 0 ≤ Θ) (hKhalf : 0 ≤ Khalf) :
    (∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T t)) ≤ C₀ * E ^ δ * Θ) ∧
    eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => I.Hm hΦ m κ T z.1 x) z.2) 2
        (volume.restrict AVenhance.timeCube) ≤
      ENNReal.ofReal
        ((AVenhance.Jcut β : ℝ) * C₁ * E ^ (4 * δ) * Khalf * Θ) := by
  have hbounded :
      ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T t)) ≤ C₀ * E ^ δ * Θ := by
    intro t ht
    let c := hmHalfCellEndpointAt I m l t
    let a := min c t
    let b := max c t
    have hpoint := hEndpoint t ht
    have hc : 0 < c := by simpa [c] using hpoint.1
    have hc1 : c ≤ 1 := by simpa [c] using hpoint.2.1
    have hlen : b - a ≤ AVenhance.tauPP β I.Λ m := by
      simpa [a, b, c] using hpoint.2.2
    have ha : 0 < a := lt_min hc ht.1
    have hab : a ≤ b := min_le_max
    have hanchor : c ∈ Set.Icc a b := by
      exact ⟨min_le_left c t, le_max_left c t⟩
    have hb : b ≤ 1 := max_le_iff.mpr ⟨hc1, ht.2⟩
    have hlength : b - a ≤ 1 := by
      have hlen' : 0 ≤ b - a := sub_nonneg.mpr hab
      nlinarith
    have hzero : I.Hm hΦ m κ T c = fun _ => 0 := by
      simpa [c, hmHalfCellEndpointAt] using
        (frozen_hm_halfCell_endpoints_zero I hΦ hm κ T (l t)).1
    have hpair := hm_transported_norm_uniform_of_integrated_pairings
      (F := I.Hm hΦ m κ T)
      (G := hmFrozenRegularSource I hΦ m κ T)
      (V := sourceErrorD I hΦ m κ T)
      X hFper hSourcePer hVper hF hG hV hComp hSourceComp
      (by intro s x; rfl) hMaterial ha hab hanchor hzero
      (hNormCont t ht) hGsourceNonneg hQnonneg
      (by intro s hs; exact hregInt t ht s hs)
      (by intro s hs; exact hfluxInt t ht s hs)
      (by
        intro s hs H hEnvelope
        exact hregBound t ht H hEnvelope s hs)
      (by intro s hs; exact hfluxBound t ht s hs)
    have htime : Real.sqrt (b - a) ≤ 1 := by
      calc
        Real.sqrt (b - a) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hlength
        _ = 1 := by norm_num
    have hhalf : Real.sqrt (b - a) * Gsource ≤ Ghalf := by
      simpa [a, b, c] using hHalfGain t ht
    have hfirst : 2 * (Real.sqrt (b - a) * Gsource) ≤ 2 * Ghalf :=
      mul_le_mul_of_nonneg_left hhalf (by norm_num)
    have hlocal :
        Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T t)) ≤
          2 * Ghalf + Real.sqrt (2 * Q) := by
      have hbound := hpair t (by simp [a, b])
      calc
        _ ≤ 2 * Real.sqrt (b - a) * Gsource + Real.sqrt (2 * Q) := hbound
        _ = 2 * (Real.sqrt (b - a) * Gsource) + Real.sqrt (2 * Q) := by ring
        _ ≤ 2 * Ghalf + Real.sqrt (2 * Q) := by nlinarith [hfirst]
    exact hlocal.trans hScale
  have hgrad := hm_gradient_source_scale_of_hmr I hΦ m κ T hD
    hE hC₁ hΘ hKhalf hGradHmr
  exact ⟨hbounded, hgrad⟩

end AVenhance.Infra.Section4

end
