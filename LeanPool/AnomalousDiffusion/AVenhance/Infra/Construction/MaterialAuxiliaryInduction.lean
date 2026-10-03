/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.MaterialAuxiliaryWords
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.BoundedGradientInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HigherGradientStep
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityHigherStep
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityHigherOrders
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.GradientScaleChange
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HigherMaterialScaling

/-! All-order material jets with a separate auxiliary spatial/word budget. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Construction
open AVenhance.Infra.Section4

/-- Source material/spatial jets through `cut`, using auxiliary budget `N`.
The material range remains finite because time-cutoff data are only used
through `Nstar`; spatial orders can exceed that cutoff. -/
structure MaterialAuxJetLevels {β : ℝ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (N : ℕ) (K : ℝ) (cut : ℕ) : Prop where
  velocity : ∀ m α r, r ≤ cut → amnrMixedWord α r ≠ [] →
    α.length + 2 * r + 1 ≤ N → ∀ i z,
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α r)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
        K * AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r
  gradient : ∀ m α r, r ≤ cut →
    α.length + 2 * r + 2 ≤ N → ∀ i p z,
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (amnrMixedWord α r)
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ m) y.1 y.2) i p) z| ≤
        K * AVenhance.a β I.Λ m *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r

/-- Spatial velocity jets at arbitrary finite auxiliary order follow from
the all-order spatial displays of the stream-regularity estimates, with no bound on the velocity
    value. -/
theorem material_aux_velocity_nonempty_spatial_abs_le_of_A3
    {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (hne : α ≠ []) {N : ℕ}
    (hbudget : α.length + 1 ≤ N) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2) (α.map some)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      amnrSpatialVelocityConstant N * AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
  rcases List.eq_nil_or_concat α with hnil | ⟨η, p, hα⟩
  · exact (hne hnil).elim
  · have hα' : α = η ++ [p] := by simpa only [List.concat_eq_append] using hα
    rw [hα'] at hbudget ⊢
    simp only [List.length_append, List.length_singleton] at hbudget
    let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
    have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (AVenhance.streamSeq_isAdmissible hΦ m)).smooth
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y => b y i) := (contDiff_apply ℝ ℝ i).comp hb
    have heq : amnrWord b [some p] (fun y => b y i) = amnrVelocityGradient b i p := by
      funext y
      exact amnrOp_space (hf.differentiable (by simp) y) p
    simp only [List.map_append, List.map_singleton, List.length_append,
      List.length_singleton]
    rw [amnrWord_append, heq]
    have hh := amnr_velocityGradient_spatial_le_of_A3_auxiliary_budget
      I hΦ hreg hm η N (by omega) i p z
    have hE := AVenhance.Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hscale : AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ = AVenhance.a β I.Λ m := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
      unfold AVenhance.a
      congr 1
      ring
    rw [pow_succ]
    calc
      _ ≤ amnrSpatialVelocityConstant N * AVenhance.a β I.Λ m *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ η.length := hh
      _ = amnrSpatialVelocityConstant N *
            (AVenhance.epsilon β I.Λ m ^ (β - 1) *
              (AVenhance.epsilon β I.Λ m)⁻¹) *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ η.length := by rw [hscale]
      _ = amnrSpatialVelocityConstant N * AVenhance.epsilon β I.Λ m ^ (β - 1) *
            ((AVenhance.epsilon β I.Λ m)⁻¹ ^ η.length *
              (AVenhance.epsilon β I.Λ m)⁻¹) := by ring

/-- The zero material level is precisely the source spatial stream-regularity estimate. -/
theorem material_aux_jet_levels_spatial {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) {N : ℕ} :
    ∃ K : ℝ, 1 ≤ K ∧ MaterialAuxJetLevels I Φ N K 0 := by
  let K := max 1 (amnrSpatialVelocityConstant N)
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨K, hK, ?_⟩
  constructor
  · intro m α r hr hne hbudget i z
    have hr0 : r = 0 := by omega
    subst r
    have hα : α ≠ [] := by
      intro hnil
      apply hne
      simp [hnil, amnrMixedWord]
    simp only [amnrMixedWord, List.replicate_zero, List.append_nil,
      pow_zero, mul_one, Nat.mul_zero, Nat.add_zero] at *
    by_cases hm : m = 0
    · subst m
      rw [amnr_streamVelocity_zero_word I hΦ]
      simp only [Pi.zero_apply, abs_zero]
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := 0)
      have hA := AVenhance.Infra.Cutoff.a_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := 0)
      positivity
    · have hh := material_aux_velocity_nonempty_spatial_abs_le_of_A3
        I hΦ hreg (by omega : 1 ≤ m) α hα hbudget i z
      have hle : amnrSpatialVelocityConstant N ≤ K := le_max_right _ _
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hInv : 0 ≤ (AVenhance.epsilon β I.Λ m)⁻¹ := inv_nonneg.mpr hE.le
      have hV : 0 ≤ AVenhance.epsilon β I.Λ m ^ (β - 1) :=
        Real.rpow_nonneg hE.le _
      calc
        _ ≤ amnrSpatialVelocityConstant N *
            (AVenhance.epsilon β I.Λ m ^ (β - 1) *
              (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) := by
          simpa [mul_assoc] using hh
        _ ≤ K * (AVenhance.epsilon β I.Λ m ^ (β - 1) *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hV (pow_nonneg hInv _))
        _ = _ := by ring
  · intro m α r hr hbudget i p z
    have hr0 : r = 0 := by omega
    subst r
    simp only [amnrMixedWord, List.replicate_zero, List.append_nil,
      pow_zero, mul_one, Nat.mul_zero, Nat.add_zero] at *
    by_cases hm : m = 0
    · subst m
      rw [amnr_streamGradient_zero_word I hΦ]
      simp only [Pi.zero_apply, abs_zero]
      have hA := AVenhance.Infra.Cutoff.a_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := 0)
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := 0)
      positivity
    · have hh := amnr_velocityGradient_spatial_le_of_A3_auxiliary_budget
        I hΦ hreg (by omega : 1 ≤ m) α N (by omega : α.length ≤ N) i p z
      have hle : amnrSpatialVelocityConstant N ≤ K := le_max_right _ _
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hA := AVenhance.Infra.Cutoff.a_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hInv : 0 ≤ (AVenhance.epsilon β I.Λ m)⁻¹ := inv_nonneg.mpr hE.le
      calc
        _ ≤ amnrSpatialVelocityConstant N * AVenhance.a β I.Λ m *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := hh
        _ ≤ K * AVenhance.a β I.Λ m *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length := by
          have h1 := mul_le_mul_of_nonneg_right hle hA.le
          exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hInv α.length)
        _ = _ := by ring

/-- Fast velocity mixed jets use the differentiated recursion and lower
material-gradient jets, with the source material order kept at `Nstar`. -/
theorem material_aux_fastVelocity_mixed_abs_le_of_lower_gradient_bounds
    {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {K : ℝ} {Nspace cut : ℕ}
    (hlevels : MaterialAuxJetLevels I Φ Nspace K cut)
    (hK : 0 ≤ K) {m : ℕ} (hm : 1 ≤ m)
    (α : List (Fin 2)) (n : ℕ)
    (hn : n ≤ cut + 1) (hcutN : cut + 1 ≤ AVenhance.Nstar β)
    (hbudget : α.length + 1 + 2 * n ≤ Nspace)
    (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
      (amnrMixedWord α n)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i -
        AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i) z| ≤
      ((1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ n *
        materialAuxStreamMixedCurrentConstant I Nspace) *
        AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ n := by
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let f := fun y : AmnrSpace => Φ m y.1 y.2 - Φ (m - 1) y.1 y.2
  let q : Fin 2 := if i = 0 then 1 else 0
  let S := (AVenhance.epsilon β I.Λ m)⁻¹
  let H := AVenhance.a β I.Λ m
  let F := materialAuxStreamMixedCurrentConstant I Nspace * H * AVenhance.epsilon β I.Λ m ^ 2
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  have hf := amnr_streamIncrement_contDiff I hΦ m
  have hE := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hH := AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hS : 0 ≤ S := inv_nonneg.mpr hE.le
  have hH0 : 0 ≤ H := hH.le
  have hF : 0 ≤ F := by
    dsimp [F]
    have hCurrent := materialAuxStreamMixedCurrentConstant_nonneg I Nspace
    positivity
  have hfb : ∀ η r, r ≤ n → η.length + 2 * r ≤ Nspace →
      |amnrWord b (amnrMixedWord η r) f z| ≤ F * S ^ η.length * H ^ r := by
    intro η r hr hη
    have hη' : η.length ≤ Nspace := by omega
    have hr' : r ≤ AVenhance.Nstar β := (hr.trans hn).trans hcutN
    have hs := material_aux_streamIncrement_mixed_current_abs_le_of_A3
      I hΦ hreg hm η r hη' hr' z
    simpa [b, f, S, H, F, mul_assoc, mul_left_comm, mul_comm] using hs
  have hBb : ∀ p q' η r, r < n → η.length + 2 * r + 2 ≤ Nspace →
      |amnrWord b (amnrMixedWord η r) (amnrVelocityGradient b p q') z| ≤
        K * H * S ^ η.length * H ^ r := by
    intro p q' η r hr hη
    have hr' : r ≤ cut := by omega
    have hs := hlevels.gradient (m - 1) η r hr' hη p q' z
    have hEF := amnr_epsilon_current_le_prev I hm
    have hPrev := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
    have hscale := amnr_gradient_material_scale_antitone hE hPrev hEF I.beta_lt η.length r
    have hscaled := mul_le_mul_of_nonneg_left hscale hK
    calc
      _ ≤ K * (AVenhance.a β I.Λ (m - 1) *
          (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ η.length *
          AVenhance.a β I.Λ (m - 1) ^ r) := by
        convert hs using 1; ring
      _ ≤ K * (H * S ^ η.length * H ^ r) := by
        simpa [H, S, AVenhance.a, mul_assoc, mul_left_comm, mul_comm] using hscaled
      _ = _ := by ring
  have hh := amnr_material_gradient_mixed_abs_le_of_bounded_lower_gradient_bounds hb hf
    (N := Nspace) (cut := n) hS hH0 hF hK z hfb hBb
    n le_rfl α 0 (by omega) (by omega) q
  simp only [List.replicate_zero, amnrWord, Nat.add_zero] at hh
  rw [amnr_fastVelocity_component I hΦ m i, amnrWord_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  rw [show |if i = 0 then (-1 : ℝ) else 1| = 1 by split_ifs <;> norm_num, one_mul]
  change |amnrWord b (amnrMixedWord α n) (amnrOp b (some q) f) z| ≤ _
  have hcancel := amnr_stream_amplitude_spatial_cancel (A := H) (β := β) hE
    (amnr_amplitude_gradient_scale (β := β) hE) α.length
  refine hh.trans_eq ?_
  dsimp [F, H, S]
  calc
    _ = ((1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ n *
        materialAuxStreamMixedCurrentConstant I Nspace) *
        (AVenhance.a β I.Λ m * AVenhance.epsilon β I.Λ m ^ 2 *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ (α.length + 1)) *
          AVenhance.a β I.Λ m ^ n := by ring
    _ = _ := by rw [hcancel]; ring

/-- Uniform fast-velocity constant for the auxiliary material word budget. -/
def materialAuxHigherFastConstant {β : ℝ} (I : AVenhance.Ingredients β)
    (K : ℝ) (N : ℕ) : ℝ :=
  max 1 ((1 + (2 : ℝ) ^ (N + 1) * K) ^ N *
    materialAuxStreamMixedCurrentConstant I N)

theorem materialAuxHigherFastConstant_one_le {β K : ℝ}
    (I : AVenhance.Ingredients β) (N : ℕ) :
    1 ≤ materialAuxHigherFastConstant I K N := le_max_left _ _

/-- Scale-step constant for changing the velocity in a material word. -/
def materialAuxHigherVelocityStepConstant {β : ℝ} (I : AVenhance.Ingredients β)
    (K : ℝ) (N n k : ℕ) : ℝ :=
  let D := materialAuxHigherFastConstant I K N
  let R := amnrNormalOrderConstant (N - 1) K (N - 1)
  D + ((amnrMaterialErrorCardinality n * (n + 1) ^ k : ℕ) : ℝ) *
    (R * D) ^ n * (R * (K + D))

theorem materialAuxHigherVelocityStepConstant_nonneg {β K : ℝ}
    (I : AVenhance.Ingredients β) (hK : 0 ≤ K) (N n k : ℕ) :
    0 ≤ materialAuxHigherVelocityStepConstant I K N n k := by
  have hD : 0 ≤ materialAuxHigherFastConstant I K N :=
    le_trans (by norm_num) (materialAuxHigherFastConstant_one_le (K := K) I N)
  have hR : 0 ≤ amnrNormalOrderConstant (N - 1) K (N - 1) :=
    le_trans (by norm_num) (amnrNormalOrderConstant_one_le hK (N - 1))
  unfold materialAuxHigherVelocityStepConstant
  dsimp
  positivity

/-- One higher source material order follows from strictly lower velocity
and gradient levels plus the all-order transported fast increment. -/
theorem material_aux_velocity_higher_source_step {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {Nspace n m : ℕ} {K : ℝ} (hn : 1 ≤ n)
    (hnN : n ≤ AVenhance.Nstar β)
    (hlevels : MaterialAuxJetLevels I Φ Nspace K (n - 1))
    (hK : 1 ≤ K) (α : List (Fin 2))
    (hbudget : α.length + 2 * n + 1 ≤ Nspace)
    (hm : 1 ≤ m) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
      (amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2)
          (List.replicate n none) (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) -
        amnrWord (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2)
          (List.replicate n none) (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2 i)) z|
      ≤ materialAuxHigherVelocityStepConstant I K Nspace n α.length *
        AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ n := by
  let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
  let c := fun y : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) y.1 y.2
  let S := (AVenhance.epsilon β I.Λ m)⁻¹
  let H := AVenhance.a β I.Λ m
  let V := AVenhance.epsilon β I.Λ m ^ (β - 1)
  let D := materialAuxHigherFastConstant I K Nspace
  let R := amnrNormalOrderConstant (Nspace - 1) K (Nspace - 1)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVenhance.streamSeq_isAdmissible hΦ m)).smooth
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)).smooth
  have hE := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  have hH : 0 ≤ H :=
    (AVenhance.Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)).le
  have hVS : V * S = H := by
    dsimp [V, S, H, AVenhance.a]
    rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
    congr 1
    ring
  have hFastBase : 1 ≤ 1 + (2 : ℝ) ^ (Nspace + 1) * K := by
    have hpow : 0 ≤ (2 : ℝ) ^ (Nspace + 1) := by positivity
    have hK0 : 0 ≤ K := by linarith
    have hmul : 0 ≤ (2 : ℝ) ^ (Nspace + 1) * K := mul_nonneg hpow hK0
    linarith
  have hFastCoeff (r : ℕ) (hrN : r ≤ Nspace) :
      (1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ r *
        materialAuxStreamMixedCurrentConstant I Nspace ≤ D := by
    have hAux := materialAuxStreamMixedCurrentConstant_nonneg I Nspace
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hFastBase hrN) hAux
    dsimp [D, materialAuxHigherFastConstant]
    exact hp.trans (le_max_right _ _)
  have hfast (p : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hη : η.length + 2 * r + 1 ≤ Nspace) (hr : r < n) :
      |amnrWord c (amnrMixedWord η r) (amnrAdvectionVelocity b c p) z| ≤
        (D * V) * amnrWeight S H (amnrMixedWord η r) := by
    change |amnrWord c (amnrMixedWord η r) (fun y => b y p - c y p) z| ≤ _
    have hh := material_aux_fastVelocity_mixed_abs_le_of_lower_gradient_bounds
      I hΦ hreg hlevels (by linarith) hm η r
      (by omega) (by omega) (by omega) p z
    have hrate : 0 ≤ V * S ^ η.length * H ^ r := by positivity
    have hmul := mul_le_mul_of_nonneg_right (hFastCoeff r (by omega)) hrate
    calc
      _ ≤ (1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ r *
          materialAuxStreamMixedCurrentConstant I Nspace * V * S ^ η.length * H ^ r := by
        simpa [b, c, V, S, H, amnrAdvectionVelocity, mul_assoc, mul_left_comm,
          mul_comm] using hh
      _ ≤ D * V * S ^ η.length * H ^ r := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = (D * V) * amnrWeight S H (amnrMixedWord η r) := by
        rw [amnrMixedWord_weight]
        ring
  have hcoarse (p : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hne : amnrMixedWord η r ≠ [])
      (hη : η.length + 2 * r + 1 ≤ Nspace) (hr : r < n) :
      |amnrWord c (amnrMixedWord η r) (fun y => c y p) z| ≤
        (K * V) * amnrWeight S H (amnrMixedWord η r) := by
    have hh := hlevels.velocity (m - 1) η r (by omega) hne hη p z
    have hkr : 1 ≤ η.length + r := by
      by_contra hh0
      have hη0 : η = [] := List.length_eq_zero_iff.mp (by omega)
      have hr0 : r = 0 := by omega
      apply hne
      simp [hη0, hr0, amnrMixedWord]
    have hscale := amnr_higher_velocity_scale_antitone hE
      (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := m - 1))
      (amnr_epsilon_current_le_prev I hm) I.beta_lt η.length r hkr
    have hh' := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ K)
    calc
      _ ≤ K * (AVenhance.epsilon β I.Λ (m - 1) ^ (β - 1) *
          (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ η.length *
          AVenhance.a β I.Λ (m - 1) ^ r) := by
        convert hh using 1; ring
      _ ≤ K * (V * S ^ η.length * H ^ r) := by
        simpa [V, S, H, AVenhance.a, mul_assoc, mul_left_comm, mul_comm] using hh'
      _ = (K * V) * amnrWeight S H (amnrMixedWord η r) := by
        rw [amnrMixedWord_weight]
        ring
  have hB (p q : Fin 2) (η : List (Fin 2)) (r : ℕ)
      (hr : r < n) (hη : η.length + 2 * r + 2 ≤ Nspace) :
      |amnrWord c (amnrMixedWord η r) (amnrVelocityGradient c p q) z| ≤
        (K * H) * amnrWeight S H (amnrMixedWord η r) := by
    have hh := hlevels.gradient (m - 1) η r (by omega) hη p q z
    have hscale := amnr_gradient_material_scale_antitone
      (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := m))
      (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := m - 1))
      (amnr_epsilon_current_le_prev I hm) I.beta_lt η.length r
    have hh' := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ K)
    calc
      _ ≤ K * (AVenhance.a β I.Λ (m - 1) *
          (AVenhance.epsilon β I.Λ (m - 1))⁻¹ ^ η.length *
          AVenhance.a β I.Λ (m - 1) ^ r) := by
        convert hh using 1; ring
      _ ≤ K * (H * S ^ η.length * H ^ r) := by
        simpa [H, S, AVenhance.a, mul_assoc, mul_left_comm, mul_comm] using hh'
      _ = (K * H) * amnrWeight S H (amnrMixedWord η r) := by
        rw [amnrMixedWord_weight]
        ring
  have htop := material_aux_fastVelocity_mixed_abs_le_of_lower_gradient_bounds
    I hΦ hreg hlevels (by linarith) hm α n (by omega) (by omega) (by omega) i z
  have htopRate : 0 ≤ V * S ^ α.length * H ^ n := by positivity
  have htopMul := mul_le_mul_of_nonneg_right (hFastCoeff n (by omega)) htopRate
  have htop' : |amnrWord c (amnrMixedWord α n) (amnrAdvectionVelocity b c i) z| ≤
      D * V * S ^ α.length * H ^ n := by
    change |amnrWord c (amnrMixedWord α n) (fun y => b y i - c y i) z| ≤ _
    calc
      _ ≤ (1 + (2 : ℝ) ^ (Nspace + 1) * K) ^ n *
          materialAuxStreamMixedCurrentConstant I Nspace * V * S ^ α.length * H ^ n := by
        simpa [b, c, V, S, H, amnrAdvectionVelocity, mul_assoc, mul_left_comm,
          mul_comm] using htop
      _ ≤ D * V * S ^ α.length * H ^ n := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using htopMul
  have hstep := amnr_velocity_higher_step_abs_le_of_lower_bounds hb hc
    (inv_nonneg.mpr hE.le) hH (Real.rpow_nonneg hE.le _)
    (materialAuxHigherFastConstant_one_le (K := K) I Nspace)
    (by linarith) (by linarith) hVS α n hn (by omega) i z hfast hcoarse hB htop'
  simpa [amnrMixedWord, amnrWord_append, D, R, V, S, H,
    materialAuxHigherVelocityStepConstant, materialAuxHigherFastConstant] using hstep

/-- The higher material velocity jets telescope over scales. Their exponent
is uniformly negative, so the new constant is independent of the scale. -/
theorem material_aux_velocity_higher_material_abs_le_of_source_lower_levels
    {β C : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {Nspace n : ℕ} {K : ℝ} (hn : 1 ≤ n)
    (hnN : n ≤ AVenhance.Nstar β)
    (hlevels : MaterialAuxJetLevels I Φ Nspace K (n - 1))
    (hK : 1 ≤ K) (m : ℕ) (α : List (Fin 2))
    (hbudget : α.length + 2 * n + 1 ≤ Nspace) (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2)
      (amnrMixedWord α n) (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      (2 * materialAuxHigherVelocityStepConstant I K Nspace n α.length) *
        AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ n := by
  let b (j : ℕ) := fun y : AmnrSpace => AVenhance.streamVel (Φ j) y.1 y.2
  let F (j : ℕ) := amnrWord (b j) (List.replicate n none) (fun y => b j y i)
  let q := β - 1 + (β - 2) * (n : ℝ) - (α.length : ℝ)
  let v (j : ℕ) := amnrWord (fun _ => (0 : Vec 2)) (α.map some) (F j) z
  let u (j : ℕ) := AVenhance.epsilon β I.Λ j ^ q
  let S := materialAuxHigherVelocityStepConstant I K Nspace n α.length
  have hS : 0 ≤ S := materialAuxHigherVelocityStepConstant_nonneg I (by linarith) Nspace n α.length
  have hF (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (F j) := by
    have hb :=
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (AVenhance.streamSeq_isAdmissible hΦ j)).smooth
    exact contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
      ((contDiff_apply ℝ ℝ i).comp hb).contDiffOn (List.replicate n none))
  have hzero : v 0 = 0 := by
    have hFb : F 0 = 0 := amnr_streamVelocity_zero_word I hΦ _ i
    simp [v, hFb, amnrWord_zero]
  have hstep (j : ℕ) : |v (j + 1) - v j| ≤ S * u (j + 1) := by
    have hh := material_aux_velocity_higher_source_step (m := j + 1) I hΦ hreg
      hn hnN hlevels hK α hbudget (by omega) i z
    have hs := amnrWord_sub_global
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : AmnrSpace => (0 : Vec 2)))
      (hF (j + 1)) (hF j) (α.map some)
    have hscale := amnr_higher_material_spatial_scale (β := β)
      (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := j + 1)) α.length n
    rw [amnrWord_spatial_independent _ (fun _ => (0 : Vec 2))] at hh
    change |amnrWord (fun _ => (0 : Vec 2)) (α.map some) (F (j + 1) - F j) z| ≤ _ at hh
    rw [hs] at hh
    refine hh.trans_eq ?_
    change materialAuxHigherVelocityStepConstant I K Nspace n α.length *
        AVenhance.epsilon β I.Λ (j + 1) ^ (β - 1) *
        (AVenhance.epsilon β I.Λ (j + 1))⁻¹ ^ α.length *
        AVenhance.a β I.Λ (j + 1) ^ n =
      S * AVenhance.epsilon β I.Λ (j + 1) ^ q
    rw [show q = β - 1 + (β - 2) * (n : ℝ) - (α.length : ℝ) by rfl]
    dsimp [S]
    rw [← hscale]
    dsimp [AVenhance.a]
    ring_nf
  have hh := amnr_abs_recursion_sum v u hS
    (fun j => Real.rpow_nonneg (AVenhance.Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := j)).le _)
    hzero hstep m
  have hq := amnr_higher_material_exponent_le I.beta_lt α.length n hn
  have hsum := amnr_negative_power_sum I hq m
  have hb := hh.trans (mul_le_mul_of_nonneg_left hsum hS)
  rw [amnrMixedWord, amnrWord_append,
    amnrWord_spatial_independent _ (fun _ => (0 : Vec 2))]
  refine hb.trans_eq ?_
  have hscale := amnr_higher_material_spatial_scale (β := β)
    (AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)) α.length n
  change S * (2 * AVenhance.epsilon β I.Λ m ^ q) = _
  rw [← hscale]
  dsimp [S, AVenhance.a]
  ring_nf

/-- The source constant after one auxiliary material induction level. -/
def materialAuxVelocityAdvanceConstant {β : ℝ} (I : AVenhance.Ingredients β)
    (K : ℝ) (N cut : ℕ) : ℝ :=
  K + 2 * materialAuxHigherVelocityStepConstant I K N (cut + 1) N

theorem materialAuxVelocityAdvanceConstant_nonneg {β K : ℝ}
    (I : AVenhance.Ingredients β) (hK : 0 ≤ K) (N cut : ℕ) :
    0 ≤ materialAuxVelocityAdvanceConstant I K N cut := by
  have hstep := materialAuxHigherVelocityStepConstant_nonneg I hK N (cut + 1) N
  unfold materialAuxVelocityAdvanceConstant
  exact add_nonneg hK (mul_nonneg (by norm_num) hstep)

theorem materialAuxHigherVelocityStepConstant_mono_spatial {β K : ℝ}
    (I : AVenhance.Ingredients β) (hK : 0 ≤ K) (N n : ℕ)
    {k l : ℕ} (hkl : k ≤ l) :
    materialAuxHigherVelocityStepConstant I K N n k ≤
      materialAuxHigherVelocityStepConstant I K N n l := by
  have hD : 1 ≤ materialAuxHigherFastConstant I K N :=
    materialAuxHigherFastConstant_one_le (K := K) I N
  have hR := amnrNormalOrderConstant_one_le (N := N - 1) hK (N - 1)
  dsimp [materialAuxHigherVelocityStepConstant]
  simp only [Nat.cast_mul, Nat.cast_pow]
  gcongr
  exact_mod_cast (show 1 ≤ n + 1 by omega)

/-- Extend the velocity part of the source invariant through its next
material order, summing the actual scale increments. -/
theorem material_aux_velocity_advance {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {N cut : ℕ} {K : ℝ}
    (hlevels : MaterialAuxJetLevels I Φ N K cut) (hK : 1 ≤ K)
    (hcutN : cut + 1 ≤ AVenhance.Nstar β)
    (m : ℕ) (α : List (Fin 2)) (r : ℕ)
    (hr : r ≤ cut + 1) (hne : amnrMixedWord α r ≠ [])
    (hbudget : α.length + 2 * r + 1 ≤ N)
    (i : Fin 2) (z : AmnrSpace) :
    |amnrWord (fun y => AVenhance.streamVel (Φ m) y.1 y.2)
      (amnrMixedWord α r)
      (fun y => AVenhance.streamVel (Φ m) y.1 y.2 i) z| ≤
      materialAuxVelocityAdvanceConstant I K N cut *
        AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r := by
  let Knew := materialAuxVelocityAdvanceConstant I K N cut
  have hK0 : 0 ≤ K := by linarith
  have hKle : K ≤ Knew := by
    have hstep := materialAuxHigherVelocityStepConstant_nonneg I hK0 N (cut + 1) N
    dsimp [Knew, materialAuxVelocityAdvanceConstant]
    linarith
  by_cases hrc : r ≤ cut
  · have hh := hlevels.velocity m α r hrc hne hbudget i z
    have hE := AVenhance.Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hA := AVenhance.Infra.Cutoff.a_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hscale : 0 ≤ AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r := by
      positivity
    calc
      _ ≤ K * (AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ Knew * (AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r) :=
        mul_le_mul_of_nonneg_right hKle hscale
      _ = _ := by ring
  · have hrEq : r = cut + 1 := by omega
    subst r
    have hlevels' : MaterialAuxJetLevels I Φ N K (cut + 1 - 1) := by
      simpa using hlevels
    have hh := material_aux_velocity_higher_material_abs_le_of_source_lower_levels
      I hΦ hreg (by omega) hcutN hlevels' hK m α hbudget i z
    have hlen : α.length ≤ N := by omega
    have hmono := materialAuxHigherVelocityStepConstant_mono_spatial
      I hK0 N (cut + 1) hlen
    have hcoef : 2 * materialAuxHigherVelocityStepConstant I K N (cut + 1) α.length ≤ Knew := by
      dsimp [Knew, materialAuxVelocityAdvanceConstant]
      nlinarith
    have hE := AVenhance.Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hA := AVenhance.Infra.Cutoff.a_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    have hscale : 0 ≤ AVenhance.epsilon β I.Λ m ^ (β - 1) *
        (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ (cut + 1) := by
      positivity
    calc
      _ ≤ (2 * materialAuxHigherVelocityStepConstant I K N (cut + 1) α.length) *
          (AVenhance.epsilon β I.Λ m ^ (β - 1) *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ (cut + 1)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ Knew * (AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ (cut + 1)) :=
        mul_le_mul_of_nonneg_right hcoef hscale
      _ = _ := by ring

/-- Advancing one material level closes the gradient estimates from the
velocity estimates at that same level and the previous gradient level. -/
def materialAuxJetAdvanceConstant {β : ℝ} (I : AVenhance.Ingredients β)
    (K : ℝ) (N cut : ℕ) : ℝ :=
  let Kv := materialAuxVelocityAdvanceConstant I K N cut
  max Kv ((1 + (2 : ℝ) ^ N * K) ^ (cut + 1) * Kv)

theorem material_aux_jet_levels_advance {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ)
    {N cut : ℕ} {K : ℝ}
    (hlevels : MaterialAuxJetLevels I Φ N K cut) (hK : 1 ≤ K)
    (hcutN : cut + 1 ≤ AVenhance.Nstar β) :
    ∃ Knew : ℝ, 1 ≤ Knew ∧ MaterialAuxJetLevels I Φ N Knew (cut + 1) := by
  let Kv := materialAuxVelocityAdvanceConstant I K N cut
  let Kg := (1 + (2 : ℝ) ^ N * K) ^ (cut + 1) * Kv
  let Knew := materialAuxJetAdvanceConstant I K N cut
  have hK0 : 0 ≤ K := by linarith
  have hKvge : K ≤ Kv := by
    have hstep := materialAuxHigherVelocityStepConstant_nonneg I hK0 N (cut + 1) N
    dsimp [Kv, materialAuxVelocityAdvanceConstant]
    linarith
  have hKv : 1 ≤ Kv := hK.trans hKvge
  have hKgv : 0 ≤ Kg := by
    have hbase : 0 ≤ 1 + (2 : ℝ) ^ N * K := by positivity
    have hKv0 := materialAuxVelocityAdvanceConstant_nonneg I hK0 N cut
    dsimp [Kg]
    exact mul_nonneg (pow_nonneg hbase _) hKv0
  have hKnewgeKv : Kv ≤ Knew := by
    dsimp [Knew, materialAuxJetAdvanceConstant, Kv]
    exact le_max_left _ _
  have hKnewgeKg : Kg ≤ Knew := by
    dsimp [Knew, materialAuxJetAdvanceConstant, Kg, Kv]
    exact le_max_right _ _
  have hKnew : 1 ≤ Knew := by
    dsimp [Knew, materialAuxJetAdvanceConstant, Kv]
    have hleft : 1 ≤ materialAuxVelocityAdvanceConstant I K N cut := hKv
    exact le_trans hleft (le_max_left _ _)
  refine ⟨Knew, hKnew, ?_⟩
  constructor
  · intro m α r hr hne hbudget i z
    by_cases hro : r ≤ cut
    · have hh := hlevels.velocity m α r hro hne hbudget i z
      have hcoeff : K ≤ Knew := le_trans hKvge hKnewgeKv
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hA := AVenhance.Infra.Cutoff.a_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hscale : 0 ≤ AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length *
          AVenhance.a β I.Λ m ^ r := by positivity
      calc
        _ ≤ K * (AVenhance.epsilon β I.Λ m ^ (β - 1) *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hh
        _ ≤ Knew * (AVenhance.epsilon β I.Λ m ^ (β - 1) *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r) :=
          mul_le_mul_of_nonneg_right hcoeff hscale
        _ = _ := by ring
    · have hr' : r = cut + 1 := by omega
      subst r
      have hh := material_aux_velocity_advance I hΦ hreg hlevels hK hcutN
        m α (cut + 1) (by omega) hne hbudget i z
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hA := AVenhance.Infra.Cutoff.a_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hscale : 0 ≤ AVenhance.epsilon β I.Λ m ^ (β - 1) *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length *
          AVenhance.a β I.Λ m ^ (cut + 1) := by positivity
      calc
        _ ≤ materialAuxVelocityAdvanceConstant I K N cut *
            (AVenhance.epsilon β I.Λ m ^ (β - 1) *
              (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ (cut + 1)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hh
        _ ≤ Knew * (AVenhance.epsilon β I.Λ m ^ (β - 1) *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ (cut + 1)) :=
          mul_le_mul_of_nonneg_right hKnewgeKv hscale
        _ = _ := by ring
  · intro m α r hr hbudget i p z
    by_cases hro : r ≤ cut
    · have hh := hlevels.gradient m α r hro hbudget i p z
      have hcoeff : K ≤ Knew := le_trans hKvge hKnewgeKv
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hA := AVenhance.Infra.Cutoff.a_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hscale : 0 ≤ AVenhance.a β I.Λ m *
          (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length *
          AVenhance.a β I.Λ m ^ r := by positivity
      calc
        _ ≤ K * (AVenhance.a β I.Λ m *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hh
        _ ≤ Knew * (AVenhance.a β I.Λ m *
            (AVenhance.epsilon β I.Λ m)⁻¹ ^ α.length * AVenhance.a β I.Λ m ^ r) :=
          mul_le_mul_of_nonneg_right hcoeff hscale
        _ = _ := by ring
    · have hr' : r = cut + 1 := by omega
      subst r
      let b := fun y : AmnrSpace => AVenhance.streamVel (Φ m) y.1 y.2
      let S := (AVenhance.epsilon β I.Λ m)⁻¹
      let H := AVenhance.a β I.Λ m
      let V := AVenhance.epsilon β I.Λ m ^ (β - 1)
      have hb : ContDiff ℝ (⊤ : ℕ∞) b :=
        (AVenhance.Infra.Construction.smoothPeriodic_streamVel
          (AVenhance.streamSeq_isAdmissible hΦ m)).smooth
      have hE := AVenhance.Infra.Cutoff.epsilon_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hH := AVenhance.Infra.Cutoff.a_pos
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
      have hVS : V * S = H := by
        dsimp [V, S, H, AVenhance.a]
        rw [← Real.rpow_neg_one, ← Real.rpow_add hE]
        congr 1
        ring
      have hgrad := amnr_velocityGradient_mixed_abs_le_of_bounded_velocity_jets hb
        (inv_nonneg.mpr hE.le) hH.le (Real.rpow_nonneg hE.le _)
        (materialAuxVelocityAdvanceConstant_nonneg (K := K) I hK0 N cut)
        hK0 hVS α (cut + 1) hbudget i p z
        (fun η r' hr' hne' hbudget' => by
          exact material_aux_velocity_advance I hΦ hreg hlevels hK hcutN
            m η r' hr' hne' hbudget' i z)
        (fun j q η r' hlt hbudget' => by
          exact hlevels.gradient m η r' (by omega) hbudget' j q z)
      have hgrad' : |amnrWord b (amnrMixedWord α (cut + 1))
          (amnrVelocityGradient b i p) z| ≤ Kg * H * S ^ α.length * H ^ (cut + 1) := by
        simpa [Kg, H, S, Kv, materialAuxVelocityAdvanceConstant] using hgrad
      have hcoef : Kg ≤ Knew := hKnewgeKg
      have hscale : 0 ≤ H * S ^ α.length * H ^ (cut + 1) := by positivity
      calc
        _ ≤ Kg * (H * S ^ α.length * H ^ (cut + 1)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hgrad'
        _ ≤ Knew * (H * S ^ α.length * H ^ (cut + 1)) :=
          mul_le_mul_of_nonneg_right hcoef hscale
        _ = _ := by ring

/-- The differentiated recursion and the actual stream-regularity spatial estimates give
all source word bounds through the paper's material cutoff. The auxiliary
word budget is `2*Nstar+1`; time derivatives of recursion cutoffs never
exceed the literal `Nstar`. -/
theorem material_aux_jet_levels_all_orders_of_A3 {β C : ℝ}
    (I : AVenhance.Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ)
    (hreg : AVenhance.StreamRegularityBounds C I Φ) :
    ∃ K : ℝ, 1 ≤ K ∧
      MaterialAuxJetLevels I Φ (2 * AVenhance.Nstar β + 1) K
        (AVenhance.Nstar β) := by
  have hlevels : ∀ n : ℕ, n ≤ AVenhance.Nstar β →
      ∃ K : ℝ, 1 ≤ K ∧
        MaterialAuxJetLevels I Φ (2 * AVenhance.Nstar β + 1) K n := by
    intro n
    induction n with
    | zero =>
        intro _
        exact material_aux_jet_levels_spatial I hΦ hreg
    | succ n ih =>
        intro hn
        obtain ⟨K, hK, hbase⟩ := ih (by omega)
        exact material_aux_jet_levels_advance I hΦ hreg hbase hK (by omega)
  exact hlevels (AVenhance.Nstar β) le_rfl

end AVenhance.Infra.Construction

end
