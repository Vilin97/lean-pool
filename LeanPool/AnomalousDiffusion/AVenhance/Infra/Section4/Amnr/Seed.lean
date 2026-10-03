/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Memory

/-! Generic seed multipliers and AMNR seed infrastructure. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnr_abs_list_sum_le (L : List ℝ) :
    |L.sum| ≤ (L.map abs).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le a L.sum).trans (add_le_add le_rfl ih)

/-- The pointwise counterpart of the mixed L2 multiplier estimate. It is used
for the memory coefficient times the pulled-back flow multiplier in the seed. -/
theorem amnrWord_mul_abs_le {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ} {N : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U)
    (hg : ContDiffOn ℝ N g U) {S H F G : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hF : 0 ≤ F) (_hG : 0 ≤ G)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N)
    (hfb : ∀ v, v.Sublist w → ∀ z ∈ U,
      |amnrWord b v f z| ≤ F * amnrWeight S H v)
    (hgb : ∀ v, v.Sublist w → ∀ z ∈ U,
      |amnrWord b v g z| ≤ G * amnrWeight S H v) {z : AmnrSpace} (hz : z ∈ U) :
    |amnrWord b w (f * g) z| ≤ (2 : ℝ) ^ w.length * F * G * amnrWeight S H w := by
  rw [amnrWord_mul hU hb hf hg w ((amnrBudget_length_le w).trans hw) hz]
  let L := (amnrSplits w).map (fun q => amnrWord b q.1 f z * amnrWord b q.2 g z)
  change |L.sum| ≤ _
  have hterm (q) (hq : q ∈ amnrSplits w) :
      |amnrWord b q.1 f z * amnrWord b q.2 g z| ≤ F * G * amnrWeight S H w := by
    have hs := amnrSplits_sublist w q hq
    rw [abs_mul]
    have hh := mul_le_mul (hfb q.1 hs.1 z hz) (hgb q.2 hs.2.1 z hz)
      (abs_nonneg _) (mul_nonneg hF (amnrWeight_nonneg hS hH q.1))
    refine hh.trans_eq ?_
    rw [mul_mul_mul_comm, amnrWeight_split S H w q hq]
  have hsum : (L.map abs).sum ≤
      ((amnrSplits w).map (fun _ => F * G * amnrWeight S H w)).sum := by
    simp only [L, List.map_map]
    exact List.sum_le_sum hterm
  refine (amnr_abs_list_sum_le L).trans (hsum.trans_eq ?_)
  simp only [List.map_const', List.sum_replicate, amnrSplits_length, nsmul_eq_mul]
  push_cast
  ring

/-- Every ordered mixed word has the source's spatial-then-material form. -/
theorem IsAmnrMixedWord.normalForm {w : List (Option (Fin 2))} (hw : IsAmnrMixedWord w) :
    ∃ α : List (Fin 2), ∃ ℓ : ℕ, w = amnrMixedWord α ℓ := by
  induction w with
  | nil => exact ⟨[], 0, rfl⟩
  | cons d w ih =>
    have hp := List.pairwise_cons.mp hw
    cases d with
    | none =>
      have hall : ∀ a ∈ w, a = none := fun a ha => hp.1 a ha rfl
      have heq := List.eq_replicate_length.mpr hall
      refine ⟨[], w.length + 1, ?_⟩
      simp only [amnrMixedWord, List.map_nil, List.nil_append, List.replicate_succ]
      rw [heq]
      simp only [List.length_replicate]
    | some i =>
      obtain ⟨α, ℓ, hα⟩ := ih hp.2
      exact ⟨i :: α, ℓ, by simp only [amnrMixedWord, List.map_cons, List.cons_append] at *; rw [hα]⟩

/-- The source cell is open, so the directional calculus and L2 norms
apply to the precise paper domain without endpoint extension assumptions. -/
theorem amnr_timeCube_isOpen : IsOpen AVenhance.timeCube := by
  unfold AVenhance.timeCube AVenhance.unitCube
  exact isOpen_Ioo.prod (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))

/-- Joint smoothness of the actual previous velocity follows from the defining
previous-stream witness; it is not an extra induction hypothesis. -/
theorem amnr_previous_velocity_contDiff {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ContDiff ℝ N (fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) := by
  obtain ⟨hprev, _⟩ := hΦ.2 m hm
  exact (AVenhance.Infra.Construction.smoothPeriodic_streamVel hprev).smooth.of_le (by simp)

/-- Constant scalar multiplication commutes with a differential word even
when an intermediate derivative is defined by the total fderiv convention. -/
theorem amnrWord_const_smul (b : AmnrSpace → Vec 2) (c : ℝ)
    (w : List (Option (Fin 2))) (f : AmnrSpace → ℝ) :
    amnrWord b w (c • f) = c • amnrWord b w f := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    simp only [amnrWord, ih]
    funext z
    unfold amnrOp
    rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := amnrWord b w f) c) z]
    rfl

/-- The cutoff-weighted flow factor before multiplication by the memory. -/
def amnrFlowAverage {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (k p : Fin 2) (z : AmnrSpace) : ℝ :=
  ∑' l : ℤ, I.hatXiML m l z.1 * I.flowGrad hΦ m l z.1 z.2 k p

/-- Unfolded product formula for the left-Jacobian base. -/
theorem amnrSeedMultiplierA0Plus_eq {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (n : ℕ) (j k i p : Fin 2) :
    amnrSeedMultiplierA0Plus I hΦ m κ n j k i p =
      fun z => -(I.LMN κ m n z.1) * amnrFlowAverageA0Plus I hΦ m j k i p z := by
  funext z
  rfl

/-- Generic memory-times-average estimate. The cutoff-flow factor may already
contain additional factors inside its summands; only its own smoothness and
mixed bound enter this multiplication step. -/
theorem amnrLMN_mul_mixed_le {β C₀ : ℝ} (I : AVenhance.Ingredients β)
    (hcutoff : I.Chat ≤ C₀) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : AVenhance.IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ}
    (hκ : 0 < κ) {n : ℕ} (hn : n ≤ AVenhance.Nstar β)
    {U : Set AmnrSpace} (hU : IsOpen U) {A : AmnrSpace → ℝ}
    (hA : ContDiffOn ℝ (AVenhance.Nstar β) A U)
    {S X : ℝ} (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hAbound : ∀ w, IsAmnrMixedWord w → amnrBudget w ≤ AVenhance.Nstar β →
      ∀ z ∈ U, |amnrWord
        (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) w A z| ≤
        X * amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ w)
    (w : List (Option (Fin 2))) (hw : IsAmnrMixedWord w)
    (hbudget : amnrBudget w ≤ AVenhance.Nstar β) {z : AmnrSpace} (hz : z ∈ U) :
    |amnrWord (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) w
      (fun z => -(I.LMN κ m n z.1) * A z) z| ≤
      ((2 : ℝ) ^ AVenhance.Nstar β * amnrMemoryConstant β C₀ *
        (AVenhance.epsilon β I.Λ m ^ 2 / κ) * X) *
          amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ w := by
  let b := fun z : AmnrSpace => AVenhance.streamVel (Φ (m - 1)) z.1 z.2
  let L := fun z : AmnrSpace => I.LMN κ m n z.1
  let F := amnrMemoryConstant β C₀ * (AVenhance.epsilon β I.Λ m ^ 2 / κ)
  have hF : 0 ≤ F := by dsimp [F, amnrMemoryConstant]; positivity
  have hτ : 0 < AVenhance.tauP β I.Λ m :=
    AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hL : ContDiffOn ℝ (AVenhance.Nstar β) L U :=
    (((Infra.Section3.LMN_contDiff I hm hκ n).of_le (by norm_cast)).comp
      contDiff_fst).contDiffOn
  have hLb (v) (hv : v.Sublist w) : ∀ z ∈ U,
      |amnrWord b v L z| ≤ F * amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ v := by
    obtain ⟨α, ℓ, rfl⟩ := IsAmnrMixedWord.normalForm (hw.sublist hv)
    have hbud := (amnrBudget_sublist hv).trans hbudget
    rw [amnrMixedWord_budget] at hbud
    intro y _
    have hh := LMN_mixed_word_abs_le I hcutoff hm hκ hn (b := b) hS α ℓ hbud y
    simpa only [amnrMixedWord_weight, mul_assoc, L, F] using hh
  have hneg : ContDiffOn ℝ (AVenhance.Nstar β) (fun y => -(L y)) U := hL.neg
  have hnegb (v) (hv : v.Sublist w) : ∀ z ∈ U,
      |amnrWord b v (fun y => -(L y)) z| ≤ F *
        amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ v := by
    intro y hy
    have hmul := amnrWord_const_smul b (-1) v L
    have heq : (fun y => -(L y)) = (-1 : ℝ) • L := by
      funext y
      simp [Pi.smul_apply, smul_eq_mul]
    rw [heq, hmul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_one, one_mul]
    exact hLb v hv y hy
  have hh := amnrWord_mul_abs_le hU
    (amnr_previous_velocity_contDiff I hΦ hm (AVenhance.Nstar β)).contDiffOn
    hneg hA hS (inv_nonneg.mpr hτ.le) hF hX w hbudget hnegb
    (fun v hv => hAbound v (hw.sublist hv) ((amnrBudget_sublist hv).trans hbudget)) hz
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    ((amnrBudget_length_le w).trans hbudget)
  refine hh.trans ?_
  have hW := amnrWeight_nonneg hS (inv_nonneg.mpr hτ.le) w
  have hx := mul_le_mul_of_nonneg_right hpow (mul_nonneg (mul_nonneg hF hX) hW)
  convert hx using 1 <;> dsimp [F] <;> ring

end AVenhance.Infra.Section4
