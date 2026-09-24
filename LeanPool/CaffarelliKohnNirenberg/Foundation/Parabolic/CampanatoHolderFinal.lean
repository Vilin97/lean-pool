/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.CampanatoHolder

/-!
# Campanato Holder Final

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Parabolic

private lemma ballRepresentative_eq_hbound_1 :
    ∀ {f : ParabolicPoint → ℝ} {z : ParabolicPoint} {m M α K p : ℝ},
      0 < m →
        0 < M →
          0 < α →
            1 ≤ p →
              0 ≤ K →
                GlobalParabolicBallCampanatoBound f α K p →
                  GlobalParabolicBallLpData f p →
                    (∀ (n : ℕ),
                        |parabolicBallRepresentative f M z - ParabolicBallMeanSeq f M z n| ≤
                          parabolicCampanatoTailConstant α * 2 ^ (5 / p) *
                            (K * (M / 2 ^ n) ^ α)) →
                      (∀ (n : ℕ),
                          |parabolicBallRepresentative f m z - ParabolicBallMeanSeq f m z n| ≤
                            parabolicCampanatoTailConstant α * 2 ^ (5 / p) *
                              (K * (m / 2 ^ n) ^ α)) →
                        ∀ (hex : ∃ n, M / m ≤ 2 ^ n),
                          let k : ℕ := Nat.find (p := fun n => M / m ≤ 2 ^ n) hex;
                          m ≤ 2 * (M / 2 ^ k) →
                            M / 2 ^ k ≤ m →
                              ∀ (n : ℕ),
                                dist (parabolicBallRepresentative f M z)
                                    (parabolicBallRepresentative f m z) ≤
                                  (2 * parabolicCampanatoTailConstant α + 1) * 2 ^ (5 / p) *
                                    (K * (m / 2 ^ n) ^ α)
    := by
  intro f z m M α K p hm hM hα hp hK hcamp hdata htailM htailm hex k hklo hbase n
  let r₁ : ℝ := M / (2 : ℝ) ^ (n + k)
  let r₂ : ℝ := m / (2 : ℝ) ^ n
  have hr₁ : 0 < r₁ := by dsimp [r₁]; positivity
  have hr₂ : 0 < r₂ := by dsimp [r₂]; positivity
  have hrewrite : r₁ = (M / (2 : ℝ) ^ k) / (2 : ℝ) ^ n := by
    dsimp [r₁]
    rw [show n + k = k + n by omega, pow_add]
    ring
  have hsmall : r₁ ≤ r₂ := by
    rw [hrewrite]
    exact div_le_div_of_nonneg_right hbase (by positivity)
  have hlarge : r₂ ≤ 2 * r₁ := by
    rw [hrewrite]
    calc
      _ ≤ (2 * (M / (2 : ℝ) ^ k)) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_right hklo (by positivity)
      _ = _ := by ring
  have hsubset :
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₁ ⊆
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₂ :=
    Metric.closedBall_subset_closedBall hsmall
  have hd₂ := hdata z hr₂
  have hcomp := abs_setAverage_sub_setAverage_le hsubset
    (parabolicBall_closedBall_pos hr₂) (parabolicBall_closedBall_top hr₂)
    (parabolicBall_closedBall_pos hr₁) (parabolicBall_closedBall_top hr₁)
    hd₂.1 hd₂.2 hp
    (parabolicBall_volume_ratio_le_two hr₁ hr₂ hlarge)
  have hcamp₂ := hcamp z hr₂
  have hcomp' :
      |(⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₁, f x) -
          ⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₂, f x| ≤
        (2 : ℝ) ^ (5 / p) *
          (⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₂,
            |f x - ⨍ y in
              @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₂, f y| ^ p) ^
            (1 / p) := by
    have hpow : ((2 : ℝ) ^ 5) ^ (1 / p) = (2 : ℝ) ^ (5 / p) := by
      rw [show (2 : ℝ) ^ 5 = (2 : ℝ) ^ (5 : ℝ) by norm_num,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hpow] at hcomp
    exact hcomp
  have hmean :
      |ParabolicBallMeanSeq f M z (n + k) - ParabolicBallMeanSeq f m z n| ≤
        (2 : ℝ) ^ (5 / p) * (K * r₂ ^ α) := by
    calc
      _ ≤ (2 : ℝ) ^ (5 / p) *
          (⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₂,
            |f x - ⨍ y in
              @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r₂, f y| ^ p) ^
            (1 / p) := by
        simpa [ParabolicBallMeanSeq, r₁, r₂] using hcomp'
      _ ≤ _ := mul_le_mul_of_nonneg_left hcamp₂ (by positivity)
  have htail₁ := htailM (n + k)
  have htail₂ := htailm n
  have htail₁' :
      |parabolicBallRepresentative f M z - ParabolicBallMeanSeq f M z (n + k)| ≤
        parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) * (K * r₂ ^ α) := by
    have htail₁r :
        |parabolicBallRepresentative f M z - ParabolicBallMeanSeq f M z (n + k)| ≤
          parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) * (K * r₁ ^ α) := by
      simpa [r₁] using htail₁
    exact htail₁r.trans (by
      have hp : r₁ ^ α ≤ r₂ ^ α := Real.rpow_le_rpow (by positivity) hsmall hα.le
      have hT : 0 ≤ parabolicCampanatoTailConstant α := by
        unfold parabolicCampanatoTailConstant
        exact one_div_nonneg.mpr (sub_nonneg.mpr
          (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])).le)
      have hD : 0 ≤ (2 : ℝ) ^ (5 / p) := Real.rpow_nonneg (by norm_num) _
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hK)
        (mul_nonneg hT hD))
  have htail₂' := htail₂
  have hsum :
      |parabolicBallRepresentative f M z - parabolicBallRepresentative f m z| ≤
        (2 * parabolicCampanatoTailConstant α + 1) * (2 : ℝ) ^ (5 / p) *
          (K * r₂ ^ α) := by
    have hmean' := hmean
    have htail₂''' :
        |ParabolicBallMeanSeq f m z n - parabolicBallRepresentative f m z| ≤
          parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) * (K * r₂ ^ α) := by
      simpa only [abs_sub_comm] using htail₂'
    calc
      _ ≤ |parabolicBallRepresentative f M z - ParabolicBallMeanSeq f M z (n + k)| +
          |ParabolicBallMeanSeq f M z (n + k) - parabolicBallRepresentative f m z| :=
        abs_sub_le _ _ _
      _ ≤ |parabolicBallRepresentative f M z - ParabolicBallMeanSeq f M z (n + k)| +
          (|ParabolicBallMeanSeq f M z (n + k) - ParabolicBallMeanSeq f m z n| +
            |ParabolicBallMeanSeq f m z n - parabolicBallRepresentative f m z|) := by
        have hmid := abs_sub_le
          (ParabolicBallMeanSeq f M z (n + k))
          (ParabolicBallMeanSeq f m z n)
          (parabolicBallRepresentative f m z)
        exact add_le_add (le_refl _) hmid
      _ ≤ _ := by
        have hT : 0 ≤ parabolicCampanatoTailConstant α := by
          unfold parabolicCampanatoTailConstant
          exact one_div_nonneg.mpr (sub_nonneg.mpr
            (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])).le)
        have hD : 0 ≤ (2 : ℝ) ^ (5 / p) := Real.rpow_nonneg (by norm_num) _
        calc
          _ ≤ parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) * (K * r₂ ^ α) +
              (((2 : ℝ) ^ (5 / p) * (K * r₂ ^ α)) +
                parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
                  (K * r₂ ^ α)) := by
            have hineq := add_le_add (add_le_add htail₁' hmean') htail₂'''
            simpa only [add_assoc] using hineq
          _ = (2 * parabolicCampanatoTailConstant α + 1) *
              (2 : ℝ) ^ (5 / p) * (K * r₂ ^ α) := by ring
  exact hsum

private lemma parabolicBallRepresentative_eq_of_global_of_le
    {f : ParabolicPoint → ℝ} {z : ParabolicPoint}
    {m M α K p : ℝ} (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M)
    (hα : 0 < α) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hcamp : GlobalParabolicBallCampanatoBound f α K p)
    (hdata : GlobalParabolicBallLpData f p) :
    parabolicBallRepresentative f m z = parabolicBallRepresentative f M z := by
  have hcampM : ParabolicBallCampanatoBoundOn f Set.univ M α K p := by
    intro w _ r hr _
    exact hcamp w hr
  have hcampm : ParabolicBallCampanatoBoundOn f Set.univ m α K p := by
    intro w _ r hr _
    exact hcamp w hr
  have hdataM : ParabolicBallLpDataOn f Set.univ M p := by
    intro w _ r hr _
    exact hdata w hr
  have hdatam : ParabolicBallLpDataOn f Set.univ m p := by
    intro w _ r hr _
    exact hdata w hr
  have hstepM : ∀ n : ℕ,
      dist (ParabolicBallMeanSeq f M z n)
          (ParabolicBallMeanSeq f M z (n + 1)) ≤
        ((2 : ℝ) ^ (5 / p) * (K * M ^ α)) *
          ((2 : ℝ) ^ (-α)) ^ n := by
    intro n
    have hrn : 0 < M / (2 : ℝ) ^ n := parabolicBall_dyadic_pos hM n
    have hrn1 : 0 < M / (2 : ℝ) ^ (n + 1) := parabolicBall_dyadic_pos hM (n + 1)
    have heq : 2 * (M / (2 : ℝ) ^ (n + 1)) = M / (2 : ℝ) ^ n := by
      rw [pow_succ]
      ring
    have hratio :
        (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
          (M / (2 : ℝ) ^ n))).toReal /
            (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
              (M / (2 : ℝ) ^ (n + 1)))).toReal ≤ (2 : ℝ) ^ 5 := by
      rw [← heq]
      exact le_of_eq (parabolicBall_volume_ratio_two (z := z) (w := z) hrn1)
    have hd := hdataM z (by simp) hrn (parabolicBall_dyadic_le hM n)
    have h := abs_parabolicBallMeanSeq_succ_le hM hp (by positivity)
      hcampM (by simp) n hratio hd.1 hd.2
    rw [Real.dist_eq]
    calc
      _ ≤ (2 : ℝ) ^ (5 / p) * (K * (M / (2 : ℝ) ^ n) ^ α) := by
        have hpow : ((2 : ℝ) ^ 5) ^ p⁻¹ = (2 : ℝ) ^ (5 / p) := by
          rw [show (2 : ℝ) ^ 5 = (2 : ℝ) ^ (5 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
        simpa only [one_mul, one_div, hpow] using h
      _ = ((2 : ℝ) ^ (5 / p) * (K * M ^ α)) *
            ((2 : ℝ) ^ (-α)) ^ n := by
        rw [parabolicBall_dyadic_rpow hM.le α n]
        ring
  have hstepm : ∀ n : ℕ,
      dist (ParabolicBallMeanSeq f m z n)
          (ParabolicBallMeanSeq f m z (n + 1)) ≤
        ((2 : ℝ) ^ (5 / p) * (K * m ^ α)) *
          ((2 : ℝ) ^ (-α)) ^ n := by
    intro n
    have hrn : 0 < m / (2 : ℝ) ^ n := parabolicBall_dyadic_pos hm n
    have hrn1 : 0 < m / (2 : ℝ) ^ (n + 1) := parabolicBall_dyadic_pos hm (n + 1)
    have heq : 2 * (m / (2 : ℝ) ^ (n + 1)) = m / (2 : ℝ) ^ n := by
      rw [pow_succ]
      ring
    have hratio :
        (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
          (m / (2 : ℝ) ^ n))).toReal /
            (volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z
              (m / (2 : ℝ) ^ (n + 1)))).toReal ≤ (2 : ℝ) ^ 5 := by
      rw [← heq]
      exact le_of_eq (parabolicBall_volume_ratio_two (z := z) (w := z) hrn1)
    have hd := hdatam z (by simp) hrn (parabolicBall_dyadic_le hm n)
    have h := abs_parabolicBallMeanSeq_succ_le hm hp (by positivity)
      hcampm (by simp) n hratio hd.1 hd.2
    rw [Real.dist_eq]
    calc
      _ ≤ (2 : ℝ) ^ (5 / p) * (K * (m / (2 : ℝ) ^ n) ^ α) := by
        have hpow : ((2 : ℝ) ^ 5) ^ p⁻¹ = (2 : ℝ) ^ (5 / p) := by
          rw [show (2 : ℝ) ^ 5 = (2 : ℝ) ^ (5 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
        simpa only [one_mul, one_div, hpow] using h
      _ = ((2 : ℝ) ^ (5 / p) * (K * m ^ α)) *
            ((2 : ℝ) ^ (-α)) ^ n := by
        rw [parabolicBall_dyadic_rpow hm.le α n]
        ring
  have htailM : ∀ n : ℕ,
      |parabolicBallRepresentative f M z - ParabolicBallMeanSeq f M z n| ≤
        parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
          (K * (M / (2 : ℝ) ^ n) ^ α) := by
    intro n
    have h := abs_parabolicBallRepresentative_sub_meanSeq_le hα (hstepM) n
    calc
      _ ≤ parabolicCampanatoTailConstant α *
          ((2 : ℝ) ^ (5 / p) * (K * M ^ α)) *
            ((2 : ℝ) ^ (-α)) ^ n := h
      _ = _ := by rw [parabolicBall_dyadic_rpow hM.le α n]; ring
  have htailm : ∀ n : ℕ,
      |parabolicBallRepresentative f m z - ParabolicBallMeanSeq f m z n| ≤
        parabolicCampanatoTailConstant α * (2 : ℝ) ^ (5 / p) *
          (K * (m / (2 : ℝ) ^ n) ^ α) := by
    intro n
    have h := abs_parabolicBallRepresentative_sub_meanSeq_le hα (hstepm) n
    calc
      _ ≤ parabolicCampanatoTailConstant α *
          ((2 : ℝ) ^ (5 / p) * (K * m ^ α)) *
            ((2 : ℝ) ^ (-α)) ^ n := h
      _ = _ := by rw [parabolicBall_dyadic_rpow hm.le α n]; ring
  have hq : 0 < M / m := div_pos hM hm
  have hex : ∃ n : ℕ, M / m ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / m) one_lt_two
    exact ⟨n, le_of_lt hn⟩
  let k : ℕ := Nat.find hex
  have hkhi : M / m ≤ (2 : ℝ) ^ k := Nat.find_spec hex
  have hklo : m ≤ 2 * (M / (2 : ℝ) ^ k) := by
    cases hk : k with
    | zero =>
        simp only [pow_zero, div_one]
        nlinarith only [hmM, hM]
    | succ j =>
        have hnot : ¬ M / m ≤ (2 : ℝ) ^ j := by
          intro h
          have hmin := Nat.find_min' hex h
          have hmin' : k ≤ j := by simpa [k] using hmin
          omega
        have hlt : (2 : ℝ) ^ j < M / m := by
          simpa [hk] using (lt_of_not_ge hnot)
        have hmul := (lt_div_iff₀ hm).mp hlt
        have hmle : m ≤ M / (2 : ℝ) ^ j := by
          apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)).2
          simpa [mul_comm] using hmul.le
        rw [pow_succ]
        convert hmle using 1
        ring
  have hbase : M / (2 : ℝ) ^ k ≤ m := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).2
    simpa [mul_comm] using (div_le_iff₀ hm).mp hkhi
  have hbound := @ballRepresentative_eq_hbound_1 f z m M α K p hm hM hα hp hK hcamp hdata htailM
    htailm hex hklo hbase
  have hqα : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])
  have hlimbase : Tendsto (fun n : ℕ => (m / (2 : ℝ) ^ n) ^ α) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ)
      (Real.rpow_nonneg (by norm_num) _) hqα
    have hmul := hpow.const_mul (m ^ α)
    convert hmul using 1
    · funext n
      exact parabolicBall_dyadic_rpow hm.le α n
    · simp
  have hlim : Tendsto (fun n : ℕ =>
      (2 * parabolicCampanatoTailConstant α + 1) * (2 : ℝ) ^ (5 / p) *
        (K * (m / (2 : ℝ) ^ n) ^ α)) atTop (𝓝 0) := by
    convert hlimbase.const_mul
      ((2 * parabolicCampanatoTailConstant α + 1) * (2 : ℝ) ^ (5 / p) * K) using 1
    · funext n
      ring
    · simp
  have hdist0 : dist (parabolicBallRepresentative f M z)
      (parabolicBallRepresentative f m z) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun n => hbound n)
  exact (dist_eq_zero.mp (le_antisymm hdist0 dist_nonneg)).symm

private lemma parabolicBallRepresentative_eq_of_global
    {f : ParabolicPoint → ℝ} {z : ParabolicPoint}
    {R S α K p : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hα : 0 < α) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hcamp : GlobalParabolicBallCampanatoBound f α K p)
    (hdata : GlobalParabolicBallLpData f p) :
    parabolicBallRepresentative f R z = parabolicBallRepresentative f S z := by
  rcases le_total R S with hRS | hSR
  · exact parabolicBallRepresentative_eq_of_global_of_le hR hS hRS hα hp hK hcamp hdata
  · exact (parabolicBallRepresentative_eq_of_global_of_le hS hR hSR hα hp hK hcamp hdata).symm

theorem campanato_holder
    {f : ParabolicPoint → ℝ} {α K p : ℝ}
    (hα : 0 < α) (_ : α < 1) (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hf : LocallyIntegrable f volume)
    (hdata : GlobalParabolicBallLpData f p)
    (hcamp : GlobalParabolicBallCampanatoBound f α K p) :
    ∃ g : ParabolicPoint → ℝ,
      g =ᵐ[volume] f ∧
      ParabolicHolderSeminormLE Set.univ g α
        (parabolicCampanatoHolderConstant α p * K) := by
  let g : ParabolicPoint → ℝ := parabolicBallRepresentative f 1
  have hg_ae : g =ᵐ[volume] f := by
    exact parabolicBallRepresentative_ae_eq_of_locallyIntegrable one_pos hf
  have hsmall : ∀ z z' : ParabolicPoint, dist z z' < 1 / 4 →
      |g z - g z'| ≤ parabolicCampanatoHolderConstant α p * K *
        parabolicDist z z' ^ α := by
    intro z z' hdist
    exact parabolicBallRepresentative_holder_at_scale hα one_pos hp hK
      (fun w _ r hr _ => hcamp w hr) (fun w _ r hr _ => hdata w hr) z
      (Set.mem_univ z) z' (Set.mem_univ z') hdist
  refine ⟨g, hg_ae, ?_⟩
  intro z hz z' hz'
  by_cases hzz' : z = z'
  · subst z'
    simp [parabolicDist, vec3EuclideanNorm_zero, hα.ne']
  · let ρ : ℝ := dist z z'
    have hρ : 0 < ρ := dist_pos.mpr hzz'
    let R : ℝ := 8 * ρ
    have hR : 0 < R := by dsimp [R]; positivity
    have hscale := parabolicBallRepresentative_holder_at_scale hα hR hp hK
      (fun w _ r hr _ => hcamp w hr) (fun w _ r hr _ => hdata w hr)
      z (Set.mem_univ z) z' (Set.mem_univ z') (by
        dsimp [R]
        linarith only [hρ])
    have hrepz := parabolicBallRepresentative_eq_of_global (z := z)
      hR one_pos hα hp hK hcamp hdata
    have hrepz' := parabolicBallRepresentative_eq_of_global (z := z')
      hR one_pos hα hp hK hcamp hdata
    simpa [g, hrepz, hrepz', R, ρ] using hscale

end CKN.Foundation.Parabolic
