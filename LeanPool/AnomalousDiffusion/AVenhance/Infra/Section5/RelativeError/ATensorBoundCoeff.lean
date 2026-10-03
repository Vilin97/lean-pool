/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorBoundLevels
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientTopSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SeedMultiplierSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceSmallnessThreshold

/-! # Uniform primitive coefficient constants for the S-amplitude AMNR Hessian

`I`-uniform versions (constants depending only on `β` and the common bound `C₀`) of the mixed
velocity-gradient, flow-gradient, flow-average, seed-multiplier and temperature-coefficient bounds
proved upstream with constants chosen after `I`.  The proofs follow the upstream ones verbatim,
substituting the uniform source jet levels of `ATensorBoundLevels`. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
open AVenhance.Infra.Section4

namespace AVenhance.Infra.Section5.RelativeError

/-- Uniform velocity-gradient constant. -/
def uniCb (β C₀ : ℝ) : ℝ := uniLevelConst β C₀ (AVenhance.Nstar β)

theorem one_le_uniCb (β C₀ : ℝ) : 1 ≤ uniCb β C₀ := uniLevelConst_one_le β C₀ _

/-- Uniform flow-gradient constant. -/
def uniFlowGrad (β C₀ : ℝ) : ℝ :=
  (2 : ℝ) ^ (AVenhance.Nstar β + 1) * amnrFlowGradientSpatialConstant (AVenhance.Nstar β) *
    (1 + (2 : ℝ) ^ (AVenhance.Nstar β + 1) * uniCb β C₀) ^ AVenhance.Nstar β

/-- Uniform flow-average constant. -/
def uniFlowAvg (β C₀ : ℝ) : ℝ :=
  3 * (2 : ℝ) ^ (AVenhance.Nstar β) * C₀ * uniFlowGrad β C₀

/-- Uniform corrected-form flow-average constant, with the extra cutoff-flow
factor estimated by the mixed product rule. -/
def uniFlowAvgA0Plus (β C₀ : ℝ) : ℝ :=
  3 * (2 : ℝ) ^ (AVenhance.Nstar β) * C₀ *
    (2 ^ AVenhance.Nstar β * uniFlowGrad β C₀ * uniFlowGrad β C₀)

/-- Uniform corrected-form seed constant: the old memory factor multiplies the
two-flow cutoff average. -/
def uniSeedA0Plus (β C₀ : ℝ) : ℝ :=
  (2 : ℝ) ^ AVenhance.Nstar β * amnrMemoryConstant β C₀ *
    uniFlowAvgA0Plus β C₀

/-- Uniform temperature-coefficient constant. -/
def uniCoeff (β C₀ : ℝ) : ℝ :=
  2 * (2 : ℝ) ^ AVenhance.Nstar β * amnrKmatStepConstant β C₀ * uniFlowAvg β C₀ + 1 +
    4 * (2 : ℝ) ^ AVenhance.Nstar β *
      (amnrKmatStepConstant β C₀ + 160 / 9) *
        (uniFlowAvgA0Plus β C₀ + uniFlowAvg β C₀)

theorem uniFlowGrad_nonneg (β C₀ : ℝ) : 0 ≤ uniFlowGrad β C₀ := by
  have := one_le_uniCb β C₀
  have := amnrFlowGradientSpatialConstant_pos (AVenhance.Nstar β)
  unfold uniFlowGrad
  positivity

/-- Uniform mixed velocity-gradient bounds. -/
theorem uni_velocityGradient_mixed_bounds {β C C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ) :
    ∀ m, 1 ≤ m → ∀ i p w, IsAmnrMixedWord w →
      amnrBudget w + 2 ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) i p) z| ≤
        uniCb β C₀ * (AVenhance.tauP β I.Λ m)⁻¹ *
          amnrWeight (AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2)))
            (AVenhance.tauP β I.Λ m)⁻¹ w := by
  have hlevels := uniLevelConst_spec I hz hh hΦ hreg (AVenhance.Nstar β)
  intro m hm i p w hw hbudget z
  obtain ⟨α, r, rfl⟩ := IsAmnrMixedWord.normalForm hw
  rw [amnrMixedWord_budget] at hbudget
  rw [amnrMixedWord_weight]
  have hh := hlevels.gradient (m - 1) α r (by omega) hbudget i p z
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m
      - 1)
  have hA := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  obtain ⟨hS, hH⟩ := amnr_physical_rates I hm
  have hHp : 0 ≤ (AVenhance.tauP β I.Λ m)⁻¹ := hA.le.trans hH
  have hCb0 : 0 ≤ uniLevelConst β C₀ (AVenhance.Nstar β) := by
    linarith [uniLevelConst_one_le β C₀ (AVenhance.Nstar β)]
  refine hh.trans ?_
  calc
    _ ≤ uniLevelConst β C₀ (AVenhance.Nstar β) * (AVenhance.tauP β I.Λ m)⁻¹ *
        (AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2))) ^ α.length *
          (AVenhance.tauP β I.Λ m)⁻¹ ^ r := by gcongr
    _ = _ := by unfold uniCb; ring

/-- Uniform mixed flow-gradient bounds. -/
theorem uni_flowGrad_mixed_bounds {β C C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ) :
    ∀ m, 1 ≤ m → ∀ (l : ℤ) (α : List (Fin 2)) n,
      α.length + 2 * n ≤ AVenhance.Nstar β → ∀ z : AmnrSpace,
      |z.1 - (l : ℝ) * AVenhance.tauPP β I.Λ m| ≤
        AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m → ∀ i p,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (amnrMixedWord α n)
        (fun y => I.flowGrad hΦ m l y.1 y.2 i p) z| ≤
        uniFlowGrad β C₀ *
          (AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2))) ^ α.length *
          (AVenhance.tauP β I.Λ m)⁻¹ ^ n := by
  have hB := uni_velocityGradient_mixed_bounds I hz hh hΦ hreg
  have hCb := one_le_uniCb β C₀
  let N := AVenhance.Nstar β
  let Cg := amnrFlowGradientSpatialConstant N
  let Cb := uniCb β C₀
  let R := 1 + (2 : ℝ) ^ (N + 1) * Cb
  have hCg : 0 ≤ Cg := (amnrFlowGradientSpatialConstant_pos N).le
  have hR : 1 ≤ R := by
    have hh : 0 ≤ (2 : ℝ) ^ (N + 1) * Cb := by positivity
    dsimp [R]
    linarith
  intro m hm l α n hbudget z ht i p
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let G := fun q => fun y : AmnrSpace => I.flowGrad hΦ m l y.1 y.2 i q
  let S := AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2))
  let H := (AVenhance.tauP β I.Λ m)⁻¹
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  have hG (q : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (G q) :=
    amnr_flowGrad_joint_contDiff_infty I hΦ m l i q
  have hS : 0 ≤ S := Real.rpow_nonneg
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hH : 0 ≤ H := inv_nonneg.mpr
    (AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  obtain ⟨hSp, _⟩ := amnr_physical_rates I hm
  have hh := amnr_flow_mixed_abs_le_of_primitive_jets hb G hG
    (fun q y => amnr_flowGrad_material_equation I hΦ m l i q y)
    hS hH hCg (show 0 ≤ Cb by linarith) z
    (fun q η hη => by
      have hh := amnr_flowGrad_spatialWord_abs_le_of_A3 I hΦ hreg hm l z ht η hη i q
      have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m
          := m - 1)
      exact hh.trans (by gcongr))
    (fun j q w hw hbudget => hB m hm j q w hw hbudget z) α n hbudget p
  have hp2 : (2 : ℝ) ^ (α.length + 1) ≤ (2 : ℝ) ^ (N + 1) :=
    pow_le_pow_right₀ (by norm_num) (by dsimp [N]; omega)
  have hpR : R ^ n ≤ R ^ N := pow_le_pow_right₀ hR (by dsimp [N]; omega)
  exact hh.trans (by unfold uniFlowGrad; gcongr)

/-- Uniform mixed flow-average bounds. -/
theorem uni_flowAverage_mixed_bounds {β C C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ) :
    ∀ m, 1 ≤ m → ∀ k p w, IsAmnrMixedWord w →
      amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrFlowAverage I hΦ m k p) z| ≤
        uniFlowAvg β C₀ *
          amnrWeight (AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2)))
            (AVenhance.tauP β I.Λ m)⁻¹ w := by
  have hX := uniFlowGrad_nonneg β C₀
  have hflow := uni_flowGrad_mixed_bounds I hz hh hΦ hreg
  have hChat : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  intro m hm k p w hw hbudget z
  have hmain := amnr_cutoff_word_abs_le I hm isOpen_univ
    (amnr_previous_velocity_contDiff I hΦ hm (AVenhance.Nstar β)).contDiffOn
    (fun l y => I.flowGrad hΦ m l y.1 y.2 k p)
    (fun l => ((amnr_flowGrad_joint_contDiff_infty I hΦ m l k p).of_le (by simp)).contDiffOn)
    (Real.rpow_nonneg
      (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _) hX
    (fun l v hv hbudget y _ ht => by
      obtain ⟨α, r, rfl⟩ := IsAmnrMixedWord.normalForm hv
      rw [amnrMixedWord_budget] at hbudget
      rw [amnrMixedWord_weight]
      exact (hflow m hm l α r hbudget y ht k p).trans_eq (by ring))
    w hw hbudget (mem_univ z)
  refine hmain.trans ?_
  have hW := amnrWeight_nonneg (S := AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β /
      2)))
    (H := (AVenhance.tauP β I.Λ m)⁻¹)
    (Real.rpow_nonneg
      (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _)
    (inv_nonneg.mpr (AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le).le) w
  unfold uniFlowAvg
  gcongr

/-- Uniform mixed bounds for the corrected-form candidate seed multiplier. The
constants depend only on `(β,C₀)` and precede the instance `I`. -/
theorem uni_seedMultiplierA0Plus_mixed_bounds {β C C₀ : ℝ}
    (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) :
    ∀ m, 1 ≤ m → ∀ κ, 0 < κ → ∀ n,
      n ≤ AVenhance.Nstar β → ∀ j k i p w, IsAmnrMixedWord w →
      amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrSeedMultiplierA0Plus I hΦ m κ n j k i p) z| ≤
        (uniSeedA0Plus β C₀ * (AVenhance.epsilon β I.Λ m ^ 2 / κ)) *
          amnrWeight (AVenhance.epsilon β I.Λ (m - 1) ^
            (-(1 + AVenhance.gamma β / 2)))
            (AVenhance.tauP β I.Λ m)⁻¹ w := by
  have hflow := uni_flowGrad_mixed_bounds I hz hh hΦ hreg
  have hX := uniFlowGrad_nonneg β C₀
  have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Chat, hh]
  have hChat : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hMem : 0 ≤ amnrMemoryConstant β C₀ := by
    unfold amnrMemoryConstant
    positivity
  have hAvgConst : 0 ≤ uniFlowAvgA0Plus β C₀ := by
    unfold uniFlowAvgA0Plus
    positivity
  have hSeedConst : 0 ≤ uniSeedA0Plus β C₀ := by
    unfold uniSeedA0Plus
    positivity
  intro m hm κ hκ n hn j k i p w hw hbudget z
  let S := AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2))
  let H := (AVenhance.tauP β I.Λ m)⁻¹
  have hS : 0 ≤ S := Real.rpow_nonneg
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hH : 0 ≤ H := inv_nonneg.mpr
    (AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have havgGen := amnr_flowAverageA0Plus_mixed_of_flow_bounds I hΦ hX hflow
  have havgBound : ∀ v, IsAmnrMixedWord v → amnrBudget v ≤ AVenhance.Nstar β →
      ∀ y, |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) v
        (amnrFlowAverageA0Plus I hΦ m j k i p) y| ≤
        uniFlowAvgA0Plus β C₀ * amnrWeight S H v := by
    intro v hv hvb y
    have hraw := havgGen m hm j k i p v hv hvb y
    have hW := amnrWeight_nonneg hS hH v
    have hcoeff : 3 * (2 : ℝ) ^ AVenhance.Nstar β * I.Chat *
        (2 ^ AVenhance.Nstar β * uniFlowGrad β C₀ * uniFlowGrad β C₀) ≤
      uniFlowAvgA0Plus β C₀ := by
      unfold uniFlowAvgA0Plus
      gcongr
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hW)
  have hAvgReg : ContDiffOn ℝ (AVenhance.Nstar β)
      (amnrFlowAverageA0Plus I hΦ m j k i p) Set.univ :=
    amnrFlowAverageA0Plus_contDiffOn (N := AVenhance.Nstar β)
      I hΦ hm isOpen_univ j k i p
      (fun l => (amnr_flowGrad_joint_contDiff_infty I hΦ m l j i).of_le (by simp) |>.contDiffOn)
      (fun l => (amnr_flowGrad_joint_contDiff_infty I hΦ m l k p).of_le (by simp) |>.contDiffOn)
  have hmain := amnrLMN_mul_mixed_le I hh hΦ hm hκ hn isOpen_univ
    hAvgReg hS hAvgConst
    (fun v hv hvb y _ => havgBound v hv hvb y)
    w hw hbudget (mem_univ z)
  change |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
      (fun y => -(I.LMN κ m n y.1) * amnrFlowAverageA0Plus I hΦ m j k i p y) z| ≤ _
  convert hmain using 1
  dsimp [uniSeedA0Plus, uniFlowAvgA0Plus]
  ring

/-- Uniform primitive temperature coefficient jets without an interior-scale restriction. -/
theorem uni_temperatureCoefficient_mixed_of_step_size {β C C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) (hreg : AVenhance.StreamRegularityBounds C I Φ) :
    ∀ m, 1 ≤ m → ∀ κm κprev : ℝ,
      0 < κm → 0 < κprev →
      AVenhance.epsilon β I.Λ m ^ 2 ≤ κm * AVenhance.tau β I.Λ m →
      κm + AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κm ≤
        (160 / 9) * κprev →
      ∀ i j w, IsAmnrMixedWord w → amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrTemperatureCoefficient I hΦ m κm κprev i j) z| ≤
        (uniCoeff β C₀ * κprev) *
          amnrWeight (AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2)))
            (AVenhance.tauP β I.Λ m)⁻¹ w := by
  have hGconst := uniFlowGrad_nonneg β C₀
  have hX : 0 ≤ uniFlowAvg β C₀ := by
    have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Chat]
    unfold uniFlowAvg
    positivity
  have hY : 0 ≤ uniFlowAvgA0Plus β C₀ := by
    have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Chat]
    unfold uniFlowAvgA0Plus
    positivity
  have hflowGrad := uni_flowGrad_mixed_bounds I hz hh hΦ hreg
  have hflow := uni_flowAverage_mixed_bounds I hz hh hΦ hreg
  have hAplusGen := amnr_flowAverageA0Plus_mixed_of_flow_bounds I hΦ hGconst hflowGrad
  let Q := amnrKmatStepConstant β C₀
  have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hz]
  have hQ : 0 ≤ Q := by dsimp [Q, amnrKmatStepConstant]; positivity
  intro m hm κm κprev hκm hκprev hratio hsize i j w hw hbudget z
  let S := AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2))
  let H := (AVenhance.tauP β I.Λ m)⁻¹
  have hS : 0 ≤ S := Real.rpow_nonneg
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hH : 0 ≤ H := inv_nonneg.mpr
    (AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  have hb : ContDiff ℝ (AVenhance.Nstar β) b :=
    amnr_previous_velocity_contDiff I hΦ hm (AVenhance.Nstar β)
  have hKentry (a p : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (fun y : AmnrSpace => I.Kmat κm m y.1 a p) :=
    ((contDiff_apply ℝ ℝ p).comp ((contDiff_apply ℝ (Fin 2 → ℝ) a).comp
      (Section3.Kmat_contDiff I hm hκm))).comp contDiff_fst
  have hKbound (a p : Fin 2) (v : List (Option (Fin 2)))
      (hv : v.Sublist w) (y : AmnrSpace) :
      |amnrWord b v (fun y => I.Kmat κm m y.1 a p) y| ≤
        (Q * κprev) * amnrWeight S H v := by
      obtain ⟨α, r, rfl⟩ := IsAmnrMixedWord.normalForm (hw.sublist hv)
      have hvbudget := (amnrBudget_sublist hv).trans hbudget
      rw [amnrMixedWord_budget] at hvbudget
      exact amnr_Kmat_mixed_bound_of_step_size I hz hh hm hκm hκprev.le hratio hsize
        b hS α r hvbudget a p y
  have hGbound (p : Fin 2) (v : List (Option (Fin 2)))
      (hv : v.Sublist w) (y : AmnrSpace) :
      |amnrWord b v (amnrFlowAverage I hΦ m p j) y| ≤
        uniFlowAvg β C₀ * amnrWeight S H v :=
    hflow m hm p j v (hw.sublist hv) ((amnrBudget_sublist hv).trans hbudget) y
  have hAplusBound (a p : Fin 2) (v : List (Option (Fin 2)))
      (hv : v.Sublist w) (y : AmnrSpace) :
      |amnrWord b v (amnrFlowAverageA0Plus I hΦ m a p i j) y| ≤
        uniFlowAvgA0Plus β C₀ * amnrWeight S H v := by
    have hraw := hAplusGen m hm a p i j v (hw.sublist hv)
      ((amnrBudget_sublist hv).trans hbudget) y
    have hcoeff : 3 * (2 : ℝ) ^ AVenhance.Nstar β * I.Chat *
        (2 ^ AVenhance.Nstar β * uniFlowGrad β C₀ * uniFlowGrad β C₀) ≤
          uniFlowAvgA0Plus β C₀ := by
      unfold uniFlowAvgA0Plus
      gcongr
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff (amnrWeight_nonneg hS hH v))
  have hAplusCont (a p : Fin 2) : ContDiff ℝ (AVenhance.Nstar β)
      (amnrFlowAverageA0Plus I hΦ m a p i j) := by
    have hleft (l : ℤ) : ContDiffOn ℝ (AVenhance.Nstar β)
        (fun y : AmnrSpace => I.flowGrad hΦ m l y.1 y.2 a i) Set.univ :=
      ((amnr_flowGrad_joint_contDiff_infty I hΦ m l a i).of_le (by simp)).contDiffOn
    have hright (l : ℤ) : ContDiffOn ℝ (AVenhance.Nstar β)
        (fun y : AmnrSpace => I.flowGrad hΦ m l y.1 y.2 p j) Set.univ :=
      ((amnr_flowGrad_joint_contDiff_infty I hΦ m l p j).of_le (by simp)).contDiffOn
    exact contDiffOn_univ.mp (amnrFlowAverageA0Plus_contDiffOn I hΦ hm isOpen_univ
      (N := AVenhance.Nstar β) a p i j hleft hright)
  have hκmLe : κm ≤ (160 / 9) * κprev := by
    have hcorrection : 0 ≤ AVenhance.a β I.Λ m ^ 2 * AVenhance.epsilon β I.Λ m ^ 4 / κm := by
      positivity
    nlinarith [hsize]
  have hPbound (a p : Fin 2) (v : List (Option (Fin 2)))
      (hv : v.Sublist w) (y : AmnrSpace) :
      |amnrWord b v
        (fun y => (I.Kmat κm m y.1 - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a p) y| ≤
          ((Q + 160 / 9) * κprev) * amnrWeight S H v := by
    have hdelta : |κm * (if a = p then 1 else 0)| ≤ (160 / 9) * κprev := by
      have hδ : |(if a = p then (1 : ℝ) else 0)| ≤ 1 := by
        split_ifs <;> norm_num
      calc
        |κm * (if a = p then 1 else 0)| = κm * |if a = p then 1 else 0| := by
          rw [abs_mul, abs_of_pos hκm]
        _ ≤ κm * 1 := mul_le_mul_of_nonneg_left hδ hκm.le
        _ ≤ (160 / 9) * κprev := by simpa only [mul_one] using hκmLe
    have hvbudget := (amnrBudget_sublist hv).trans hbudget
    have hraw := amnr_word_sub_const_abs_le (A := Q * κprev)
      (c := κm * (if a = p then 1 else 0)) hb (hKentry a p) hS hH
      v hvbudget y (hKbound a p v hv y)
    have hcoeff : Q * κprev + |κm * (if a = p then 1 else 0)| ≤
        (Q + 160 / 9) * κprev := by nlinarith [hdelta]
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff (amnrWeight_nonneg hS hH v))
  have hHbound (a p : Fin 2) (v : List (Option (Fin 2)))
      (hv : v.Sublist w) (y : AmnrSpace) :
      |amnrWord b v
        (fun y => amnrFlowAverageA0Plus I hΦ m a p i j y -
          (if i = a then 1 else 0) * amnrFlowAverage I hΦ m p j y) y| ≤
            (uniFlowAvgA0Plus β C₀ + uniFlowAvg β C₀) * amnrWeight S H v := by
    let δ : ℝ := if i = a then 1 else 0
    have hAreg : ContDiffOn ℝ (AVenhance.Nstar β)
        (amnrFlowAverageA0Plus I hΦ m a p i j) Set.univ := (hAplusCont a p).contDiffOn
    have hGreg : ContDiffOn ℝ (AVenhance.Nstar β)
        (amnrFlowAverage I hΦ m p j) Set.univ :=
      (amnr_flowAverage_contDiff I hΦ hm (AVenhance.Nstar β) p j).contDiffOn
    have hscaledReg : ContDiffOn ℝ (AVenhance.Nstar β)
        (fun y : AmnrSpace => δ * amnrFlowAverage I hΦ m p j y) Set.univ :=
      (contDiff_const (c := δ)).contDiffOn.mul hGreg
    have hsub := amnrWord_sub isOpen_univ hb.contDiffOn hAreg hscaledReg v
      ((amnrBudget_length_le v).trans ((amnrBudget_sublist hv).trans hbudget))
    have hδabs : |δ| ≤ 1 := by dsimp [δ]; split_ifs <;> norm_num
    have hscaledEq : amnrWord b v (fun q => δ * amnrFlowAverage I hΦ m p j q) =
        fun q => δ * amnrWord b v (amnrFlowAverage I hΦ m p j) q := by
      have hfun : (fun q => δ * amnrFlowAverage I hΦ m p j q) =
          δ • amnrFlowAverage I hΦ m p j := by
        funext q
        simp [smul_eq_mul]
      rw [hfun, amnrWord_const_smul]
      funext q
      simp [smul_eq_mul]
    have hscaled (q : AmnrSpace) :
        |amnrWord b v (fun q => δ * amnrFlowAverage I hΦ m p j q) q| ≤
          uniFlowAvg β C₀ * amnrWeight S H v := by
      rw [hscaledEq]
      change |δ * amnrWord b v (amnrFlowAverage I hΦ m p j) q| ≤ _
      calc
        _ = |δ| * |amnrWord b v (amnrFlowAverage I hΦ m p j) q| := abs_mul _ _
        _ ≤ 1 * |amnrWord b v (amnrFlowAverage I hΦ m p j) q| :=
          mul_le_mul_of_nonneg_right hδabs (abs_nonneg _)
        _ ≤ 1 * (uniFlowAvg β C₀ * amnrWeight S H v) :=
          mul_le_mul_of_nonneg_left (hGbound p v hv q) (by norm_num)
        _ = _ := by ring
    change |amnrWord b v (amnrFlowAverageA0Plus I hΦ m a p i j -
      (fun q => δ * amnrFlowAverage I hΦ m p j q)) y| ≤ _
    rw [hsub (mem_univ y)]
    calc
      |amnrWord b v (amnrFlowAverageA0Plus I hΦ m a p i j) y -
          amnrWord b v (fun q => δ * amnrFlowAverage I hΦ m p j q) y| ≤
        |amnrWord b v (amnrFlowAverageA0Plus I hΦ m a p i j) y| +
          |amnrWord b v (fun q => δ * amnrFlowAverage I hΦ m p j q) y| := abs_sub _ _
      _ ≤ uniFlowAvgA0Plus β C₀ * amnrWeight S H v +
          uniFlowAvg β C₀ * amnrWeight S H v :=
        add_le_add (hAplusBound a p v hv y) (hscaled y)
      _ = _ := by ring
  have hd : |κprev * (if i = j then 1 else 0)| ≤ κprev := by
    split_ifs <;> simp [abs_of_pos hκprev, hκprev.le]
  have hcomponents := amnr_temperatureCoefficient_mixed_bound_of_components
    I hΦ (m := m) (hm := hm) (κm := κm) (κprev := κprev) hκm i j
    (S := S) (T := H) (A := Q * κprev) (B := uniFlowAvg β C₀)
    (C := (Q + 160 / 9) * κprev)
    (D := uniFlowAvgA0Plus β C₀ + uniFlowAvg β C₀)
    hS hH (mul_nonneg hQ hκprev.le) hX
    (mul_nonneg (by positivity) hκprev.le) (add_nonneg hY hX)
    w hbudget z (fun p v hv y => hKbound i p v hv y)
    hGbound hPbound hHbound
  have hweight : 0 ≤ amnrWeight S H w := amnrWeight_nonneg hS hH w
  have hcoeff :
      2 * (2 : ℝ) ^ AVenhance.Nstar β * (Q * κprev) * uniFlowAvg β C₀ +
        |κprev * (if i = j then 1 else 0)| +
        4 * (2 : ℝ) ^ AVenhance.Nstar β *
          ((Q + 160 / 9) * κprev) *
          (uniFlowAvgA0Plus β C₀ + uniFlowAvg β C₀) ≤
        uniCoeff β C₀ * κprev := by
    dsimp [uniCoeff]
    nlinarith [hd]
  exact hcomponents.trans (mul_le_mul_of_nonneg_right hcoeff hweight)

/-- Uniform literal-source coefficient bounds through the terminal permitted scale. -/
theorem uni_temperatureCoefficient_mixed_bounds_through_top
    {β Creg C₀ c C : ℝ} (I : AVenhance.Ingredients β)
    (hz : I.Czeta ≤ C₀) (hh : I.Chat ≤ C₀) (hc : 0 < c) (hcC : c < C)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds Creg I Φ) :
    ∀ (κ : ℝ) (M : ℕ), 0 < κ →
      κ ∈ AVenhance.permittedInterval β I.Λ M →
      (
      (∀ m : ℕ, 1 ≤ m → m < M →
        c * (AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ (2 + AVenhance.gamma β)) ≤
          I.kappaAt κ m (M - m) ∧
        I.kappaAt κ m (M - m) ≤
          C * (AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ (2 + AVenhance.gamma β))) ∧
      (∀ m : ℕ, 2 ≤ m → m < M →
        c * AVenhance.epsilon β I.Λ (m - 1) ^ (4 * AVenhance.delta β) ≤
          AVenhance.epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * AVenhance.tau β I.Λ m) ∧
        AVenhance.epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * AVenhance.tau β I.Λ m) ≤
          C * AVenhance.epsilon β I.Λ (m - 1) ^ (4 * AVenhance.delta β))) → ∀ m, 2 ≤ m → m ≤ M →
      amnrSourceRatioConstant β C * AVenhance.epsilon β I.Λ (m - 1) ^ (2 * AVenhance.delta β) ≤ 1
          / 2 →
      Section3.lAmtOneStepConstant β C₀ *
        (amnrSourceRatioConstant β C * AVenhance.epsilon β I.Λ (m - 1) ^ (2 * AVenhance.delta β) +
          AVenhance.epsilon β I.Λ (m - 1) ^ AVenhance.delta β) ≤ 9 / 160 →
      ∀ i j w, IsAmnrMixedWord w → amnrBudget w ≤ AVenhance.Nstar β → ∀ z,
      |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) w
        (amnrTemperatureCoefficient I hΦ m (I.kappaAt κ m (M - m))
          (I.kappaAt κ (m - 1) (M - (m - 1))) i j) z| ≤
        (uniCoeff β C₀ * I.kappaAt κ (m - 1) (M - (m - 1))) *
          amnrWeight (AVenhance.epsilon β I.Λ (m - 1) ^ (-(1 + AVenhance.gamma β / 2)))
            (AVenhance.tauP β I.Λ m)⁻¹ w := by
  have hbound := uni_temperatureCoefficient_mixed_of_step_size I hz hh hΦ hreg
  intro κ M hκ hPerm hA5 m hm hmM hsmall hAvg i j w hw hbudget z
  have hκm := Section3.kappaAt_pos I hκ m (M - m)
  have hκprev := Section3.kappaAt_pos I hκ (m - 1) (M - (m - 1))
  have hC : 0 < C := hc.trans hcC
  have ht : 0 ≤ Section3.kappaPrimeEndpointExpratConstant β := by
    have hq : 0 ≤ AVenhance.q β := le_trans (by norm_num)
      (AVenhance.Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt).le
    unfold Section3.kappaPrimeEndpointExpratConstant
    have hs : 0 ≤ AVenhance.Infra.Ingredients.supergeoConstant β := by
      unfold AVenhance.Infra.Ingredients.supergeoConstant
      positivity
    have hb : 0 ≤ 1 + AVenhance.Infra.Ingredients.supergeoConstant β / 128 := by positivity
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hb _)
  have hUpper : AVenhance.epsilon β I.Λ m ^ 2 /
      (I.kappaAt κ m (M - m) * AVenhance.tau β I.Λ m) ≤
      amnrSourceRatioConstant β C * AVenhance.epsilon β I.Λ (m - 1) ^ (2 * AVenhance.delta β) := by
    by_cases hmi : m < M
    · have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m
        := m - 1)
      have he1 := AVenhance.Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
          I.two_pow_seven_le (m := m - 1)
      have hd := AVenhance.Infra.Cutoff.delta_pos I.one_lt_beta I.beta_lt
      have hp := Real.rpow_le_rpow_of_exponent_ge he he1 (show 2 * AVenhance.delta β ≤ 4 *
          AVenhance.delta β by linarith)
      refine (hA5.2 m hm hmi).2.trans ((mul_le_mul_of_nonneg_left hp hC.le).trans ?_)
      exact mul_le_mul_of_nonneg_right (by dsimp [amnrSourceRatioConstant]; linarith only [ht])
        (Real.rpow_nonneg he.le _)
    · have heq : m = M := by omega
      subst m
      have hh := (Section3.l_recurse_top I.one_lt_beta I.beta_lt I.two_pow_seven_le hκ hPerm (by
          omega)).2
      simp only [Nat.sub_self, AVenhance.Ingredients.kappaAt]
      refine hh.trans ?_
      exact mul_le_mul_of_nonneg_right (by dsimp [amnrSourceRatioConstant]; linarith only [hC.le])
        (Real.rpow_nonneg (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
            I.two_pow_seven_le).le _)
  have hτ := AVenhance.Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hratio := condition_of_exprat_upper hκm hτ hUpper hsmall
  have hratio' : AVenhance.epsilon β I.Λ m ^ 2 ≤ I.kappaAt κ m (M - m) * AVenhance.tau β I.Λ m := by
    refine hratio.trans ?_
    nlinarith only [(mul_pos hκm hτ).le]
  have hL : 0 ≤ Section3.lAmtOneStepConstant β C₀ := by
    have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hz]
    unfold Section3.lAmtOneStepConstant
    positivity
  have hAvg' := (mul_le_mul_of_nonneg_left (add_le_add_left hUpper _) hL).trans hAvg
  have hsize := amnr_kappa_step_size_of_averaging I hz hh (by omega) hκm hAvg'
  rw [← amnr_kappa_previous_eq_step I (by omega) hmM] at hsize
  exact hbound m (by omega) _ _ hκm hκprev hratio' hsize i j w hw hbudget z

end AVenhance.Infra.Section5.RelativeError
