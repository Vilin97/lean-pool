/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Cutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Seed

/-! Differentiation and estimates for the actual locally finite cutoff-flow sum. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A finite local representation of every ordered derivative of a cutoff sum. -/
theorem amnr_cutoff_word_sum {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {U : Set AmnrSpace} (hU : IsOpen U)
    {N : ℕ} {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ N b U)
    (F : ℤ → AmnrSpace → ℝ) (hF : ∀ l, ContDiffOn ℝ N (F l) U)
    (w : List (Option (Fin 2))) (hw : w.length ≤ N) {z : AmnrSpace} (hz : z ∈ U) :
    ∃ s : Finset ℤ, s.card ≤ 3 ∧
      amnrWord b w (fun y => ∑' l : ℤ, I.hatXiML m l y.1 * F l y) z =
        ∑ l ∈ s, amnrWord b w ((fun y => I.hatXiML m l y.1) * F l) z := by
  classical
  obtain ⟨s, hcard, hs⟩ := amnr_hatXi_local_finite I hm z.1
  let V := U ∩ {y : AmnrSpace | |y.1 - z.1| < AVenhance.tauPP β I.Λ m / 8}
  have hV : IsOpen V := hU.inter (isOpen_lt (by fun_prop) continuous_const)
  have hzV : z ∈ V := ⟨hz, by
    change |z.1 - z.1| < AVenhance.tauPP β I.Λ m / 8
    simp only [sub_self, abs_zero]
    exact div_pos (I.tauPP_pos' m) (by norm_num)⟩
  have hVU : V ⊆ U := Set.inter_subset_left
  have hcut (l : ℤ) : ContDiffOn ℝ N (fun y : AmnrSpace => I.hatXiML m l y.1) V := by
    have hh : ContDiff ℝ N (I.hatXiML m l) := by
      unfold AVenhance.Ingredients.hatXiML AVenhance.shiftCutoff
      exact ((I.hatXi_smooth m).comp (by fun_prop)).of_le (by simp)
    exact (hh.comp contDiff_fst).contDiffOn
  have heq : Set.EqOn (fun y => ∑' l : ℤ, I.hatXiML m l y.1 * F l y)
      (∑ l ∈ s, (fun y => I.hatXiML m l y.1) * F l) V := by
    intro y hy
    rw [Finset.sum_apply]
    exact tsum_eq_sum (fun l hl => by
      simp only [hs y.1 hy.2 l hl, zero_mul])
  refine ⟨s, hcard, ?_⟩
  rw [amnrWord_congr hV (b := b) heq w hzV]
  simpa only [Finset.sum_apply] using amnrWord_sum hV (hb.mono hVU) s
    (fun l => (fun y => I.hatXiML m l y.1) * F l)
    (fun l _ => (hcut l).mul ((hF l).mono hVU)) w hw hzV

/-- Local finite sums inherit the regularity of the actual summands. -/
theorem amnr_cutoff_tsum_contDiffOn {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {U : Set AmnrSpace} (hU : IsOpen U) {N : ℕ}
    (F : ℤ → AmnrSpace → ℝ) (hF : ∀ l, ContDiffOn ℝ N (F l) U) :
    ContDiffOn ℝ N (fun y => ∑' l : ℤ, I.hatXiML m l y.1 * F l y) U := by
  classical
  intro z hz
  obtain ⟨s, _, hs⟩ := amnr_hatXi_local_finite I hm z.1
  let V := U ∩ {y : AmnrSpace | |y.1 - z.1| < AVenhance.tauPP β I.Λ m / 8}
  have hV : IsOpen V := hU.inter (isOpen_lt (by fun_prop) continuous_const)
  have hzV : z ∈ V := ⟨hz, by
    change |z.1 - z.1| < AVenhance.tauPP β I.Λ m / 8
    simp only [sub_self, abs_zero]
    exact div_pos (I.tauPP_pos' m) (by norm_num)⟩
  have hreg : ContDiffOn ℝ N (fun y => ∑ l ∈ s, I.hatXiML m l y.1 * F l y) U := by
    apply ContDiffOn.sum
    intro l _
    have hh : ContDiff ℝ N (I.hatXiML m l) := by
      unfold AVenhance.Ingredients.hatXiML AVenhance.shiftCutoff
      exact ((I.hatXi_smooth m).comp (by fun_prop)).of_le (by simp)
    exact (hh.comp contDiff_fst).contDiffOn.mul (hF l)
  have hnear : (fun y => ∑' l : ℤ, I.hatXiML m l y.1 * F l y) =ᶠ[nhds z]
      (fun y => ∑ l ∈ s, I.hatXiML m l y.1 * F l y) := by
    apply Filter.eventuallyEq_of_mem (hV.mem_nhds hzV)
    intro y hy
    exact tsum_eq_sum (fun l hl => by rw [hs y.1 hy.2 l hl, zero_mul])
  exact ((hreg.contDiffAt (hU.mem_nhds hz)).congr_of_eventuallyEq hnear).contDiffWithinAt

/-- Joint smoothness of the actual left-Jacobian flow-product average. -/
theorem amnrFlowAverageA0Plus_contDiffOn {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {U : Set AmnrSpace} (hU : IsOpen U) {N : ℕ}
    (j k i p : Fin 2)
    (hleft : ∀ l, ContDiffOn ℝ N
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 j i) U)
    (hright : ∀ l, ContDiffOn ℝ N
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 k p) U)
    :
    ContDiffOn ℝ N (amnrFlowAverageA0Plus I hΦ m j k i p) U := by
  unfold amnrFlowAverageA0Plus amnrFlowAverageGen
  apply amnr_cutoff_tsum_contDiffOn I hm hU
  intro l
  exact (hleft l).mul (hright l)

/-- Pointwise mixed Leibniz bounds require quantitative hypotheses only at
that point; regularity is local on the surrounding open set. -/
theorem amnrWord_mul_abs_le_at {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ} {N : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U)
    (hg : ContDiffOn ℝ N g U) {S H F G : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hF : 0 ≤ F) (_hG : 0 ≤ G)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N)
    {z : AmnrSpace} (hz : z ∈ U)
    (hfb : ∀ v, v.Sublist w →
      |amnrWord b v f z| ≤ F * amnrWeight S H v)
    (hgb : ∀ v, v.Sublist w →
      |amnrWord b v g z| ≤ G * amnrWeight S H v) :
    |amnrWord b w (f * g) z| ≤ (2 : ℝ) ^ w.length * F * G * amnrWeight S H w := by
  rw [amnrWord_mul hU hb hf hg w ((amnrBudget_length_le w).trans hw) hz]
  let L := (amnrSplits w).map (fun q => amnrWord b q.1 f z * amnrWord b q.2 g z)
  change |L.sum| ≤ _
  have hterm (q) (hq : q ∈ amnrSplits w) :
      |amnrWord b q.1 f z * amnrWord b q.2 g z| ≤ F * G * amnrWeight S H w := by
    have hs := amnrSplits_sublist w q hq
    rw [abs_mul]
    have hh := mul_le_mul (hfb q.1 hs.1) (hgb q.2 hs.2.1)
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

/-- Higher cutoff-sum bound from localized bounds on its primitive factors.
The actual cutoff jets and their support are proved, rather than assumed. -/
theorem amnr_cutoff_word_abs_le {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ (AVenhance.Nstar β) b U)
    (F : ℤ → AmnrSpace → ℝ) (hF : ∀ l, ContDiffOn ℝ (AVenhance.Nstar β) (F l) U)
    {S X : ℝ} (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hbound : ∀ (l : ℤ) v, IsAmnrMixedWord v → amnrBudget v ≤ AVenhance.Nstar β → ∀ z ∈ U,
      |z.1 - l * AVenhance.tauPP β I.Λ m| ≤
        AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m →
      |amnrWord b v (F l) z| ≤ X * amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ v)
    (w : List (Option (Fin 2))) (hw : IsAmnrMixedWord w)
    (hbudget : amnrBudget w ≤ AVenhance.Nstar β) {z : AmnrSpace} (hz : z ∈ U) :
    |amnrWord b w (fun y => ∑' l : ℤ, I.hatXiML m l y.1 * F l y) z| ≤
      3 * (2 : ℝ) ^ AVenhance.Nstar β * I.Chat * X *
        amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ w := by
  classical
  have hτ : 0 < AVenhance.tauP β I.Λ m :=
    AVenhance.Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hC : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hW := amnrWeight_nonneg hS (inv_nonneg.mpr hτ.le) w
  obtain ⟨s, hcard, heq⟩ := amnr_cutoff_word_sum I hm hU hb F hF w
    ((amnrBudget_length_le w).trans hbudget) hz
  rw [heq]
  have hterm (l : ℤ) :
      |amnrWord b w ((fun y => I.hatXiML m l y.1) * F l) z| ≤
        (2 : ℝ) ^ w.length * I.Chat * X * amnrWeight S (AVenhance.tauP β I.Λ m)⁻¹ w := by
    by_cases hnear : |z.1 - l * AVenhance.tauPP β I.Λ m| ≤
      AVenhance.tauPP β I.Λ m / 2 + AVenhance.tauP β I.Λ m
    · have hc : ContDiffOn ℝ (AVenhance.Nstar β)
          (fun y : AmnrSpace => I.hatXiML m l y.1) U := by
        have ht : ContDiff ℝ (AVenhance.Nstar β) (I.hatXiML m l) := by
          unfold AVenhance.Ingredients.hatXiML AVenhance.shiftCutoff
          exact ((I.hatXi_smooth m).comp (by fun_prop)).of_le (by simp)
        exact (ht.comp contDiff_fst).contDiffOn
      exact amnrWord_mul_abs_le_at hU hb hc (hF l) hS (inv_nonneg.mpr hτ.le) hC hX w hbudget hz
        (fun v hv => amnr_hatXi_mixed_abs_le I hm l hS v (hw.sublist hv)
          ((amnrBudget_sublist hv).trans hbudget) z)
        (fun v hv => hbound l v (hw.sublist hv) ((amnrBudget_sublist hv).trans hbudget) z hz hnear)
    · rw [amnr_hatXi_product_word_zero I hm l (F l) b w z (lt_of_not_ge hnear), abs_zero]
      positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun l _ => hterm l)).trans ?_)
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    ((amnrBudget_length_le w).trans hbudget)
  have hcardR : (s.card : ℝ) ≤ 3 := by exact_mod_cast hcard
  have hh := mul_le_mul hcardR hpow (by positivity : (0 : ℝ) ≤ 2 ^ w.length) (by norm_num : (0 :
      ℝ) ≤ 3)
  have hm := mul_le_mul_of_nonneg_right hh (mul_nonneg (mul_nonneg hC hX) hW)
  convert hm using 1 <;> ring

end AVenhance.Infra.Section4
