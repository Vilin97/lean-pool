/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TMaterialSpatialStep
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.MaterialMixedJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorHEuclid
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Derivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2

/-! Exact `TMaterialContract` adapter retaining the small material rate. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory

namespace AVenhance.Infra.Section5.Contracts

open AVenhance.Infra.Section5.Integration
open AVenhance.Infra.Section4
open AVenhance.Infra.Section5.RelativeError

theorem TMaterialProfiles.terminal_materialGrad_aestronglyMeasurable {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} {κm κprev : ℝ}
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    AEStronglyMeasurable
      (fun z : AmnrSpace => AVenhance.Infra.Section5.LeftToShow.materialGrad
        (streamVel (Φ (m - 1))) (T (Nstar β)) z.1 z.2)
    (volume.restrict timeCube) := by
  let b : ℝ → Vec 2 → Vec 2 := fun t x => streamVel (Φ (m - 1)) t x
  let u : ℝ → Vec 2 → ℝ := T (Nstar β)
  obtain ⟨_, hu⟩ := amnr_tIterates_classical_family I hΦ hθprev hT
    (Nstar β) le_rfl
  have hb : Infra.Flow.SmoothPeriodicField b :=
    Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  have hsub : (timeCube : Set AmnrSpace) ⊆
      AVenhance.Infra.Section5.LeftToShow.halfSpace := by
    intro z hz
    exact ⟨hz.1.1.le, Set.mem_univ _⟩
  have hcoord (p : Fin 2) : ContinuousOn
      (fun z : AmnrSpace => AVenhance.Infra.Section5.LeftToShow.materialGrad b u z.1 z.2 p)
      timeCube := by
    have hext := AVenhance.Infra.Section5.LeftToShow.matGradExt_continuousOn
      hb hu.1 p
    have heq : Set.EqOn
        (fun z : AmnrSpace => AVenhance.Infra.Section5.LeftToShow.matGradExt b u p z)
        (fun z : AmnrSpace => AVenhance.Infra.Section5.LeftToShow.materialGrad b u z.1 z.2 p)
        timeCube := by
      intro z hz
      exact AVenhance.Infra.Section5.LeftToShow.matGradExt_eq_materialGrad
        (b := b) (T := u) hz.1.1 z.2 p
    exact (hext.mono hsub).congr heq.symm
  have hcont : ContinuousOn
      (fun z : AmnrSpace => AVenhance.Infra.Section5.LeftToShow.materialGrad b u z.1 z.2)
      timeCube := continuousOn_pi.2 hcoord
  change AEStronglyMeasurable
    (fun z : AmnrSpace => AVenhance.Infra.Section5.LeftToShow.materialGrad b u z.1 z.2)
    (volume.restrict timeCube)
  exact hcont.aestronglyMeasurable
    AVenhance.Infra.Section5.RelativeError.measurableSet_timeCube

/-- The source-rate form of the first material estimate before the rate conversion. -/
def TMaterialRateProfile {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) (κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (S C : ℝ) : Prop :=
  Real.sqrt (spaceTimeGradNormSq
    (AVenhance.Infra.Section5.LeftToShow.materialGrad
      (streamVel (Φ (m - 1))) (T (Nstar β)))) ≤
    C * a β I.Λ (m - 1) * (Real.sqrt κprev)⁻¹ * S

theorem TMaterialProfiles.eLpNorm_vec2_le_of_component_bounds {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → Vec 2} {B : ℝ} (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f μ)
    (h0 : eLpNorm (fun z => f z 0) 2 μ ≤ ENNReal.ofReal B)
    (h1 : eLpNorm (fun z => f z 1) 2 μ ≤ ENNReal.ofReal B) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (2 * B) := by
  have hf0 : AEStronglyMeasurable (fun z => f z 0) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h0)
  have hf1 : AEStronglyMeasurable (fun z => f z 1) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1)
  have h0abs : eLpNorm (fun z => |f z 0|) 2 μ = eLpNorm (fun z => f z 0) 2 μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun z => f z 0) hf0
  have h1abs : eLpNorm (fun z => |f z 1|) 2 μ = eLpNorm (fun z => f z 1) 2 μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun z => f z 1) hf1
  have hpoint : ∀ z, ‖f z‖ ≤ |f z 0| + |f z 1| := by
    intro z
    rw [pi_norm_le_iff_of_nonempty]
    intro i
    fin_cases i
    · change |f z 0| ≤ |f z 0| + |f z 1|
      exact le_add_of_nonneg_right (abs_nonneg _)
    · change |f z 1| ≤ |f z 0| + |f z 1|
      exact le_add_of_nonneg_left (abs_nonneg _)
  have hpoint' : ∀ z, ‖f z‖ ≤ ‖(|f z 0| + |f z 1| : ℝ)‖ := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hpoint z
  have hmono := eLpNorm_mono_ae (p := (2 : ENNReal)) hf
    (Filter.Eventually.of_forall hpoint')
  have htri : eLpNorm (fun z : α => |f z 0| + |f z 1|) 2 μ ≤
      eLpNorm (fun z => |f z 0|) 2 μ + eLpNorm (fun z => |f z 1|) 2 μ :=
    eLpNorm_add_le (p := (2 : ENNReal)) (μ := μ)
      (by norm_num : (1 : ENNReal) ≤ 2)
  have hsum : eLpNorm (fun z => |f z 0| + |f z 1|) 2 μ ≤
      ENNReal.ofReal B + ENNReal.ofReal B := by
    calc
      _ ≤ eLpNorm (fun z => |f z 0|) 2 μ + eLpNorm (fun z => |f z 1|) 2 μ := by
        simpa only [Pi.add_apply] using htri
      _ ≤ _ := add_le_add (by rw [h0abs]; exact h0) (by rw [h1abs]; exact h1)
  calc
    _ ≤ eLpNorm (fun z => |f z 0| + |f z 1|) 2 μ := hmono
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := hsum
    _ = ENNReal.ofReal (2 * B) := by rw [← ENNReal.ofReal_add hB hB]; congr 1; ring

/-- The minimal source-rate estimate. Only spatial words of lengths zero,
one and two are consumed; the material-rate coefficient premise is absent. -/
theorem tMaterial_rate_profile_of_spatial_profiles {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm ν : ℝ} (hκm : 0 < κm) (hν : 0 < ν)
    {g : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κm ν g θprev T)
    {L G CA Cb Cd Cg S : ℝ} (hL : 0 < L) (hG : 0 ≤ G)
    (hCA : 0 ≤ CA) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hGscale : G ≤ Cg * (Real.sqrt ν)⁻¹ * S)
    (hRate : ν * L ^ 2 ≤ Cd * a β I.Λ (m - 1))
    (hCoefficient : ∀ j p (α : List (Fin 2)), α.length ≤ 2 → ∀ z,
      |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
        (amnrTemperatureCoefficient I hΦ m κm ν j p) z| ≤ CA * ν * L ^ α.length)
    (hVelocity : ∀ q p z, |amnrVelocityGradient
      (fun y => streamVel (Φ (m - 1)) y.1 y.2) q p z| ≤ Cb * a β I.Λ (m - 1))
    (hSpatial : ∀ i, i ≤ Nstar β → ∀ p (α : List (Fin 2)), α.length ≤ 2 →
      eLpNorm (amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2)
        (α.map some) (amnrTGradient (T i) p)) 2 (volume.restrict timeCube) ≤
        ENNReal.ofReal (G * L ^ α.length)) :
    TMaterialRateProfile I Φ m ν T S (2 * Real.sqrt 2 *
      tMaterialSpatialStepConstant Cb CA Cd * Cg) := by
  let Cstep := tMaterialSpatialStepConstant Cb CA Cd
  let D : ℝ → Vec 2 → Vec 2 :=
    AVenhance.Infra.Section5.LeftToShow.materialGrad (streamVel (Φ (m - 1))) (T (Nstar β))
  have hK : 0 ≤ amnrNormalOrderConstant 2 Cb 2 * (amnrCanonicalSamples 2 2).card :=
    mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (amnrNormalOrderConstant_one_le hCb 2))
        (Nat.cast_nonneg _)
  have hCstep : 0 ≤ Cstep := by dsimp [Cstep, tMaterialSpatialStepConstant]; positivity
  have ha : 0 ≤ a β I.Λ (m - 1) :=
    (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hB : 0 ≤ Cstep * a β I.Λ (m - 1) * G := by positivity
  have hcomponent (p : Fin 2) : eLpNorm (fun z => D z.1 z.2 p) 2 (volume.restrict timeCube) ≤
      ENNReal.ofReal (Cstep * a β I.Λ (m - 1) * G) :=
    tMaterial_component_of_spatial_profiles I hΦ hm hκm hν hθ hT hL hG hCA hCb
      hRate hCoefficient hVelocity hSpatial p
  have hvec := TMaterialProfiles.eLpNorm_vec2_le_of_component_bounds hB
    (TMaterialProfiles.terminal_materialGrad_aestronglyMeasurable I hΦ hθ hT) (hcomponent 0)
        (hcomponent 1)
  have hspace := sqrt_spaceTimeGradNormSq_le_of_eLpNorm_le D (by positivity) hvec
  have hscaled := mul_le_mul_of_nonneg_left hGscale (mul_nonneg hCstep ha)
  change Real.sqrt (spaceTimeGradNormSq D) ≤ _
  calc
    _ ≤ Real.sqrt 2 * (2 * (Cstep * a β I.Λ (m - 1) * G)) := hspace
    _ = (2 * Real.sqrt 2) * ((Cstep * a β I.Λ (m - 1)) * G) := by ring
    _ ≤ (2 * Real.sqrt 2) * ((Cstep * a β I.Λ (m - 1)) * (Cg * (Real.sqrt ν)⁻¹ * S)) :=
      mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ = _ := by dsimp [Cstep]; ring

/-- Convert a material-rate estimate into the exact hDt contract.

The hypothesis is the first-material-level estimate at the actual source rate
`a β Λ (m - 1)`.  The proved rate lemma supplies
`a ≤ 2^(-27) ε^(3δ) / τP`, so this conversion retains the required small factor. -/
theorem tMaterial_contract_of_material_rate {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {m : ℕ} {κprev : ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} {S C : ℝ}
    (hm : 1 ≤ m) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hmaterial : TMaterialRateProfile I Φ m κprev T S C) :
    TMaterialContract I Φ m κprev T (C * (2 : ℝ) ^ (-27 : ℤ)) S := by
  rw [TMaterialContract]
  have hrate := Infra.Section4.amnr_material_rate_small I hm
  have hκinv : 0 ≤ (Real.sqrt κprev)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hτinv : 0 ≤ (tauP β I.Λ m)⁻¹ := inv_nonneg.mpr
    (Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hε : 0 ≤ epsilon β I.Λ (m - 1) ^ (3 * delta β) := by
    exact Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le).le _
  have hrate' : a β I.Λ (m - 1) ≤
      (2 : ℝ) ^ (-27 : ℤ) * epsilon β I.Λ (m - 1) ^ (3 * delta β) *
        (tauP β I.Λ m)⁻¹ := hrate
  calc
    _ ≤ C * a β I.Λ (m - 1) * (Real.sqrt κprev)⁻¹ * S := hmaterial
    _ ≤ C * ((2 : ℝ) ^ (-27 : ℤ) *
        epsilon β I.Λ (m - 1) ^ (3 * delta β) * (tauP β I.Λ m)⁻¹) *
          (Real.sqrt κprev)⁻¹ * S := by
      have hcoeff := mul_le_mul_of_nonneg_left hrate' hC
      have hscaled := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hκinv hS)
      simpa only [mul_assoc] using hscaled
    _ = C * (2 : ℝ) ^ (-27 : ℤ) * epsilon β I.Λ (m - 1) ^
        (3 * delta β) * (Real.sqrt κprev)⁻¹ * S * (tauP β I.Λ m)⁻¹ := by ring

end AVenhance.Infra.Section5.Contracts
