/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmTransportedEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmDmScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmFlowTgrad

/-! Positive-time `H_m` assembly from a positive half-cell base point. The
extension-dependent value `H_m(0)` is never used. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Ergodic AVenhance.Infra.Section5
open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section4

/-- Scalar closure for the positive-time pairing estimate.  The regular
source has its direct `E^δ Θ` rate, while the flux pairing is the product of
the `E^(4δ) Θ / √κ` gradient rate and an `E^ρ √κ Θ` vector-source rate.  The
κ factors cancel before taking the square root, leaving the same abstract
amplitude `Θ`; in particular this applies to the gradient normalization. -/
theorem hm_pairing_scale_of_l2_source_rates
    {E δ ρ Θ κ Creg Cgrad Cdm G Grad D : ℝ}
    (hE : 0 < E) (hE1 : E ≤ 1) (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hΘ : 0 ≤ Θ) (hκ : 0 < κ)
    (hCgrad : 0 ≤ Cgrad) (hCdm : 0 ≤ Cdm) (hD : 0 ≤ D)
    (hGreg : G ≤ Creg * E ^ δ * Θ)
    (hGradRate : Grad ≤ Cgrad * E ^ (4 * δ) * (Real.sqrt κ)⁻¹ * Θ)
    (hDRate : D ≤ Cdm * Real.sqrt κ * Θ * E ^ ρ) :
    2 * G + Real.sqrt (2 * (Grad * D)) ≤
      (2 * Creg + Real.sqrt (2 * Cgrad * Cdm)) * E ^ δ * Θ := by
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsκinv : 0 ≤ (Real.sqrt κ)⁻¹ := inv_nonneg.mpr hsκ.le
  have hcoef : 0 ≤ Cgrad * Cdm := mul_nonneg hCgrad hCdm
  have hpower : (E ^ (2 * δ + ρ / 2)) ^ 2 = E ^ (4 * δ + ρ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    ring
  have hgradD : Grad * D ≤ Cgrad * Cdm * E ^ (4 * δ + ρ) * Θ ^ 2 := by
    calc
      Grad * D ≤ (Cgrad * E ^ (4 * δ) * (Real.sqrt κ)⁻¹ * Θ) * D :=
        mul_le_mul_of_nonneg_right hGradRate hD
      _ ≤ (Cgrad * E ^ (4 * δ) * (Real.sqrt κ)⁻¹ * Θ) *
          (Cdm * Real.sqrt κ * Θ * E ^ ρ) :=
        mul_le_mul_of_nonneg_left hDRate
          (by positivity : 0 ≤ Cgrad * E ^ (4 * δ) * (Real.sqrt κ)⁻¹ * Θ)
      _ = Cgrad * Cdm * E ^ (4 * δ + ρ) * Θ ^ 2 := by
        rw [Real.rpow_add hE]
        field_simp [ne_of_gt hsκ]
  have hroot : Real.sqrt (2 * (Grad * D)) ≤
      Real.sqrt (2 * Cgrad * Cdm) * E ^ (2 * δ + ρ / 2) * Θ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        2 * (Grad * D) ≤ 2 * (Cgrad * Cdm * E ^ (4 * δ + ρ) * Θ ^ 2) :=
          mul_le_mul_of_nonneg_left hgradD (by norm_num)
        _ = (Real.sqrt (2 * Cgrad * Cdm) *
              E ^ (2 * δ + ρ / 2) * Θ) ^ 2 := by
          rw [show (Real.sqrt (2 * Cgrad * Cdm) *
                E ^ (2 * δ + ρ / 2) * Θ) ^ 2 =
              (Real.sqrt (2 * Cgrad * Cdm)) ^ 2 *
                (E ^ (2 * δ + ρ / 2)) ^ 2 * Θ ^ 2 by ring]
          rw [Real.sq_sqrt (by positivity)]
          rw [hpower]
          ring
  have hexp : δ ≤ 2 * δ + ρ / 2 := by linarith
  have hEpow : E ^ (2 * δ + ρ / 2) ≤ E ^ δ :=
    Real.rpow_le_rpow_of_exponent_ge hE hE1 hexp
  have hroot' : Real.sqrt (2 * (Grad * D)) ≤
      Real.sqrt (2 * Cgrad * Cdm) * E ^ δ * Θ := by
    calc
      _ ≤ Real.sqrt (2 * Cgrad * Cdm) * E ^ (2 * δ + ρ / 2) * Θ := hroot
      _ ≤ Real.sqrt (2 * Cgrad * Cdm) * E ^ δ * Θ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEpow (Real.sqrt_nonneg _)) hΘ
  have hregular : 2 * G ≤ 2 * Creg * E ^ δ * Θ := by
    calc
      _ ≤ 2 * (Creg * E ^ δ * Θ) := mul_le_mul_of_nonneg_left hGreg (by norm_num)
      _ = 2 * Creg * E ^ δ * Θ := by ring
  calc
    _ ≤ 2 * Creg * E ^ δ * Θ +
        Real.sqrt (2 * Cgrad * Cdm) * E ^ δ * Θ :=
      add_le_add hregular hroot'
    _ = (2 * Creg + Real.sqrt (2 * Cgrad * Cdm)) * E ^ δ * Θ := by ring

/-- Pairing FTC on the positive half-cell adjacent to zero and on the rest of
`(0,1]`. The base point is the positive half-cell endpoint where `H_m`
vanishes. Signed flux contributions stay in the gradient pairing. -/
theorem frozen_hm_positive_time_bounds_of_pairings
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (X : ℝ → PeriodicVolumePreservingDiffeomorphism 2)
    (hFper : ∀ t, 0 < t → IsZ2Periodic (I.Hm hΦ m κ T t))
    (hSourcePer : ∀ t, 0 < t → IsZ2Periodic
      (fun x => hmFrozenPiolaSource I hΦ m κ T t x +
        AVenhance.vecDiv (sourceErrorD I hΦ m κ T t) x))
    (hVper : ∀ t, 0 < t → ∀ i : Fin 2,
      IsZ2Periodic (fun x => sourceErrorD I hΦ m κ T t x i))
    (hF : ∀ t, 0 < t → ContDiff ℝ 1 (I.Hm hΦ m κ T t))
    (hG : ∀ t, 0 < t → Continuous (hmFrozenPiolaSource I hΦ m κ T t))
    (hV : ∀ t, 0 < t → ContDiff ℝ 1 (sourceErrorD I hΦ m κ T t))
    (hComp : ContinuousOn
      (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hSourceComp : ContinuousOn
      (fun p : ℝ × Vec 2 =>
        (fun x => hmFrozenPiolaSource I hΦ m κ T p.1 x +
          AVenhance.vecDiv (sourceErrorD I hΦ m κ T p.1) x)
          ((X p.1).toFun p.2))
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))))
    (hMaterial : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => I.Hm hΦ m κ T s ((X s).toFun x))
        ((fun y => hmFrozenPiolaSource I hΦ m κ T t y +
          AVenhance.vecDiv (sourceErrorD I hΦ m κ T t) y)
          ((X t).toFun x)) t)
    {G Q C₀ E δ Θ C₁ Khalf : ℝ}
    (l : ℤ)
    (hc : 0 < (l + 1 / 2) * AVenhance.tauPP β I.Λ m)
    (hc1 : (l + 1 / 2) * AVenhance.tauPP β I.Λ m ≤ 1)
    (hNormCont : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ContinuousOn
        (fun s => Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T s)))
        (Set.Icc (min ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t)
          (max ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t)))
    (hregInt : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc
        (min ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t)
        (max ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t),
        IntervalIntegrable (hmRegularPairing
          (F := I.Hm hΦ m κ T)
          (G := hmFrozenPiolaSource I hΦ m κ T)) volume
          ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) s)
    (hfluxInt : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc
        (min ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t)
        (max ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t),
        IntervalIntegrable (hmFluxPairing
          (F := I.Hm hΦ m κ T) (V := sourceErrorD I hΦ m κ T)) volume
          ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) s)
    (hregBound : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 → ∀ H : ℝ,
      (∀ s ∈ Set.Icc
        (min ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t)
        (max ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t),
        Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T s)) ≤ H) →
      ∀ s ∈ Set.Icc
        (min ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t)
        (max ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t),
        |∫ r in ((l + 1 / 2) * AVenhance.tauPP β I.Λ m)..s,
          hmRegularPairing (F := I.Hm hΦ m κ T)
            (G := hmFrozenPiolaSource I hΦ m κ T) r| ≤
          Real.sqrt (max ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t -
            min ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t) * G * H)
    (hfluxBound : ∀ t, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ s ∈ Set.Icc
        (min ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t)
        (max ((l + 1 / 2) * AVenhance.tauPP β I.Λ m) t),
        |∫ r in ((l + 1 / 2) * AVenhance.tauPP β I.Λ m)..s,
          hmFluxPairing (F := I.Hm hΦ m κ T)
            (V := sourceErrorD I hΦ m κ T) r| ≤ Q)
    (hGnonneg : 0 ≤ G) (hQnonneg : 0 ≤ Q)
    (hScale : 2 * G + Real.sqrt (2 * Q) ≤ C₀ * E ^ δ * Θ)
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
      ENNReal.ofReal ((AVenhance.Jcut β : ℝ) * C₁ * E ^ (4 * δ) * Khalf * Θ) := by
  let c : ℝ := (l + 1 / 2) * AVenhance.tauPP β I.Λ m
  have hzero : I.Hm hΦ m κ T c = fun _ => 0 := by
    simpa [c] using
      (frozen_hm_halfCell_endpoints_zero I hΦ hm κ T l).1
  have hbounded :
      (∀ t ∈ Set.Ioc (0 : ℝ) 1,
        Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T t)) ≤ C₀ * E ^ δ * Θ) := by
    intro t ht
    let a : ℝ := min c t
    let b : ℝ := max c t
    have ha : 0 < a := lt_min hc ht.1
    have hab : a ≤ b := min_le_max
    have hanchor : c ∈ Set.Icc a b := by
      exact ⟨min_le_left c t, le_max_left c t⟩
    have hb : b ≤ 1 := max_le_iff.mpr ⟨hc1, ht.2⟩
    have haNonneg : 0 ≤ a := ha.le
    have hlength : b - a ≤ 1 := by linarith
    have hpair := hm_transported_norm_uniform_of_integrated_pairings
      (F := I.Hm hΦ m κ T)
      (G := hmFrozenPiolaSource I hΦ m κ T)
      (V := sourceErrorD I hΦ m κ T)
      X hFper hSourcePer hVper hF hG hV hComp hSourceComp
      (by intro s x; rfl) hMaterial ha hab hanchor hzero
      (hNormCont t ht) hGnonneg hQnonneg
      (hregInt t ht) (hfluxInt t ht)
      (by intro s hs H hEnvelope; exact hregBound t ht H hEnvelope s hs)
      (by intro s hs; exact hfluxBound t ht s hs)
    have htime : Real.sqrt (b - a) ≤ 1 := by
      calc
        Real.sqrt (b - a) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hlength
        _ = 1 := by norm_num
    have hlocal : Real.sqrt (AVenhance.l2NormSq (I.Hm hΦ m κ T t)) ≤
        2 * G + Real.sqrt (2 * Q) := by
      have hbound := hpair t (by simp [a, b])
      have hfirst : 2 * Real.sqrt (b - a) * G ≤ 2 * G := by
        nlinarith [mul_le_mul_of_nonneg_right htime hGnonneg]
      linarith
    exact hlocal.trans hScale
  have hgrad := hm_gradient_source_scale_of_hmr I hΦ m κ T hD
    hE hC₁ hΘ hKhalf hGradHmr
  exact ⟨hbounded, hgrad⟩

end AVenhance.Infra.Section4

end
