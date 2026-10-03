/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualIndependentNorms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingProfilesFromFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPhysicalCoefficientBundle
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesInflatedRadiusScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocityPhysicalBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesThetaSourceBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoordinateProfile
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergyIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalSignedPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticRadiusDoubling
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesSourceRadius
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params

/-! # Iterates VAbstract Amplitude

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Abstract-amplitude corrected l.V for positive increments. The theta base
profile excludes its undifferentiated scalar energy, so both the initial-data
and RelativeError relative-dissipation normalizations use this same theorem. -/
theorem iterate_V_abstract_amplitude_of_diffusivity_and_flow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hm : 2 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {c Ck K Cflow Cmean Rflow Cθ Rθ C₀ N : ℝ}
    (hN : 0 < N)
    (hc : 0 < c) (hCk : 0 ≤ Ck) (hK : 0 ≤ K) (hCf : 0 ≤ Cflow) (hCm : 0 ≤ Cmean)
    (hRf : 256 ≤ Rflow) (hRθ : 0 < Rθ)
    (hlower : c * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)) ≤ κprev)
    (hupper : κprev ≤ Ck * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)))
    (hC₀ : iterateSourceConstant
      (iterateBudgetUniversalConstant K Ck c ((2 : ℝ) ^ (-25 : ℤ)) Cflow Cmean) Rflow Cθ ≤ C₀)
    (hsmall : C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) ≤ 1)
    (hKm : ∀ t j k, |I.Kmat κm m t j k| ≤ K * κprev)
    (hmean : ∀ j k, |(timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      κprev * Cmean * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * (Rflow / epsilon β I.Λ (m - 1)) ^ p.length)
    (hκscale : |κm| ≤ κprev)
    (hbase : iterateCoordinateEnergyProfile θprev κprev N
      (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) 0) :
    ∀ i, 1 ≤ i → i ≤ Nstar β → ∀ v w : List (Fin 2), v.length = w.length →
      ∀ s, 0 ≤ s → s ≤ 1 →
      Real.sqrt (l2NormSq (iterateSpatialWord v (iterateIncrement T i s))) +
        Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
          (fun t => spaceGrad (iterateSpatialWord w (iterateIncrement T i t)))) ≤
      N * iterateAmplitude
        (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
          max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))) i *
        iterateAnalyticWeight v.length i
          (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) := by
  let E := epsilon β I.Λ (m - 1)
  let ρ := E ^ (2 * delta β)
  let H : ℝ := (2 : ℝ) ^ (-25 : ℤ)
  let F := C₀ * max 1 (E ^ (1 + gamma β / 2) / Rθ)
  let L := max (C₀ * E ^ (-1 - gamma β / 2)) (C₀ / Rθ)
  let r := 2 * ((Rflow / E) / ρ)
  let D := 2 * tauPP β I.Λ m * K * κprev
  let Bvel := ((2 : ℝ) ^ 21 * a β I.Λ (m - 1)) / r
  let Cs := iterateBudgetScaleConstant K Ck c H
  let Ccoef := iterateBudgetCoefficientConstant K Cflow Cmean
  let C := iterateBudgetUniversalConstant K Ck c H Cflow Cmean
  have hE : 0 < E := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hδ := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hE _
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one hE.le hE1 (by positivity)
  have hH : 0 ≤ H := by positivity
  have hκ : 0 < κprev := (mul_pos hc (mul_pos ha (Real.rpow_pos_of_pos hE _))).trans_le hlower
  have hτ := I.tauPP_pos' m
  have hconst := iterate_source_constant_bounds C Rflow Cθ
  have hC₀one := hconst.1.trans hC₀
  have hC₀pos : 0 < C₀ := by linarith only [hC₀one]
  have hlarge := hconst.2.1.trans hC₀
  have hRlarge := (iterate_source_constant_doubled_radius C Rflow Cθ).trans hC₀
  have hF : C₀ ≤ F := by
    have ht := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) (E ^ (1 + gamma β / 2) / Rθ))
        hC₀pos.le
    simpa only [mul_one] using ht
  have hFp : 0 < F := hC₀pos.trans_le hF
  have hL : 0 < L := (mul_pos hC₀pos (Real.rpow_pos_of_pos hE _)).trans_le (le_max_left _ _)
  have hFid : F = E ^ (1 + gamma β / 2) * L := iterate_source_radius_identity hE hRθ hC₀pos.le
  have hηid : C₀ * (ρ * F ^ 2) = C₀ ^ 3 * E ^ (2 * delta β) *
      max 1 (E ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) := iterate_source_amplitude_parameter hE hRθ
  have hsmall' : C₀ * (ρ * F ^ 2) ≤ 1 := by rw [hηid]; exact hsmall
  have hF1 : 1 ≤ F := hC₀one.trans hF
  have hρq : ρ ≤ ρ * F ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ F ^ 2 by nlinarith only [hF1]) hρ.le
    simpa only [mul_one] using ht
  have hRf0 : 0 ≤ Rflow := by linarith only [hRf]
  have hRfpos : 0 < Rflow := by linarith only [hRf]
  have hr : 0 < r := by positivity
  have hrvel : 256 * E⁻¹ ≤ r := by
    have h0 : 256 * E⁻¹ ≤ Rflow / E := by
      simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hRf hE.le
    have h1 : Rflow / E ≤ (Rflow / E) / ρ := (le_div_iff₀ hρ).mpr
      (mul_le_of_le_one_right (by positivity : 0 ≤ Rflow / E) hρ1)
    exact (h0.trans h1).trans (by
      dsimp [r]
      have hn : 0 ≤ (Rflow / E) / ρ := by positivity
      linarith only [hn])
  have hrscale0 := iterate_inflated_radius_ratio hE hE1 hL hFp hRf0
    (section4_exponent_budgets I.one_lt_beta I.beta_lt).1 hFid
  have hrscale : r / L ≤ (2 * Rflow) / F := by
    have hb := mul_le_mul_of_nonneg_left hrscale0 (by norm_num : (0 : ℝ) ≤ 2)
    convert hb using 1 <;> ring
  have hgeom := iterate_inflated_radius_geometric_conditions hL hr.le
    (by positivity : 0 ≤ 256 * E⁻¹) (by positivity : 0 ≤ 2 * Rflow) hC₀pos hF hRlarge hrscale hrvel
  have htime : tauPP β I.Λ m * a β I.Λ (m - 1) ≤ H * ρ := by
    have ht := (amplitude_tauPP_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le (by omega : 1 ≤
        m)).2
    change tauPP β I.Λ m * a β I.Λ (m - 1) ≤
      (2 : ℝ) ^ (-25 : ℤ) * epsilon β I.Λ (m - 1) ^ (2 * delta β)
    calc
      _ = a β I.Λ (m - 1) * tauPP β I.Λ m := by ring
      _ ≤ _ := ht
  have hphys := iterate_physical_coefficient_bundle (Cflow := Cflow) (Cmean := Cmean)
    ha.le hE hκ hc hCk hτ.le hK hH hρ.le hL hF1 hlower hupper htime hFid
  have hCs := iterate_budget_scale_constant_bounds hK hCk hc hH
  have hC := iterate_budget_universal_constant_bounds (Ck := Ck) (Cflow := Cflow) (Cmean := Cmean)
      hK hc hH
  dsimp only at hC
  have hQ : ∀ t j k, |iterateKmatPrimitive I κm m t j k| ≤ D := by
    intro t j k
    have ht := (iterateKmatPrimitive_properties I hκm (by omega : 1 ≤ m)
      (mul_nonneg hK hκ.le) hKm).2.2.2 t j k
    convert ht using 1
    ring
  have hBr : Bvel * r = (8192 * a β I.Λ (m - 1) * E) * (256 * E⁻¹) := by
    rw [iterate_velocity_first_jet_scale hE.ne']
    dsimp only [Bvel]
    field_simp
  have hjet := iterate_velocity_extended_profile_of_A3 I hΦ hm hA3 hr hrvel
  have hvGrad := iterate_velocity_gradMatrix_bound_of_A3 I hΦ hm hA3
  have hfs t l : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) :=
    (hflow l).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hprofiles := iterate_TForcing_profiles_from_flow I hΦ (by omega : 1 ≤ m)
    hκ.le hK hCf hCm (by positivity : 0 ≤ Rflow / E) hρ hρ1 hfs hKm hmean hzero hpositive hκscale
    (by
      have hbase : 1 ≤ (Rflow / E) / ρ := by
        have h256 : 256 ≤ 256 * E⁻¹ := by
          have hinv : (1 : ℝ) ≤ E⁻¹ := (one_le_inv₀ hE).2 hE1
          linarith only [hinv]
        have h0 : 256 * E⁻¹ ≤ Rflow / E := by
          simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hRf hE.le
        have h01 : 256 * E⁻¹ ≤ (Rflow / E) / ρ := h0.trans
          ((le_div_iff₀ hρ).2 (mul_le_of_le_one_right (by positivity) hρ1))
        linarith only [h256, h01]
      exact hbase)
  have hnorm := iterate_actual_independent_coordinate_norms_of_scales I hΦ hT hθ hm hκm hκ
    hflow hflowp hA3 (Ccoef := Ccoef) (Cs := Cs) (C := C) (C₀ := C₀)
    (N := N) (B := Bvel) (r := r) (L := L) (D := D)
    (Bflow := (2 : ℝ) ^ 21 * a β I.Λ (m - 1)) (ρ := ρ) (F := F)
    hL hgeom.1 hgeom.2 (by positivity : 0 ≤ D) hCs.1 hC.1 hN.le
    (by positivity : 0 ≤ Bvel) hr.le hρ hρq hC₀one hF hlarge hsmall' hQ hphys.1
    (by rw [iterate_velocity_first_jet_scale hE.ne']; exact hphys.2.1)
    hBr hjet hvGrad hphys.2.2.1 hprofiles.1 hprofiles.2 hbase hC.2.1 hC.2.2.1
    hphys.2.2.2.1 hphys.2.2.2.2.1 hphys.2.2.2.2.2
  intro i hi0 hi v w hvw s hs hs1
  rw [← hηid]
  exact hnorm i hi0 hi v w hvw s hs hs1

end AVenhance.Infra.Section4
