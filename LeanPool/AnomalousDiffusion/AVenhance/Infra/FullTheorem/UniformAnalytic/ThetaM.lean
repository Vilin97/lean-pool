/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.Chain

/-! # Hölder bound of the top iterate `θ_M` (analytic case of `r.LeBron.2`)

`θ_M = θ_{m₀-1} + ∑_{m=m₀}^{M} (θ_m − θ_{m-1})`: Lemma U for the base level `m₀ - 1`
(`κ_{m₀-1} ≥ c₁ ε_{m₀-1}^P`), Lemma r.LeBron for the increments, and the telescoping chain lemma. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem thetaM_holder {β C₀ CU μB CB c₁ Λ₁ : ℝ} (hU : LemmaUWith CU) (hCU : 0 < CU)
    (hμB : 0 < μB) (hB : LebronWith β C₀ μB CB) (hc₁ : 0 < c₁) (hW : WindowWith β C₀ c₁ Λ₁)
    {I : Ingredients β} (hz : I.Czeta ≤ C₀) (hx : I.Cxi ≤ C₀) (hh : I.Chat ≤ C₀)
    (hCB : CB ≤ (I.Λ : ℝ)) (hΛ₁ : Λ₁ ≤ (I.Λ : ℝ)) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {κ : ℝ} (hκ : κ ∈ permissibleSet β I.Λ) {M : ℕ} (hM : 1 ≤ M)
    (hκM : κ ∈ permittedInterval β I.Λ M) {R : ℝ} (hR : 0 < R) {θ₀ : Vec 2 → ℝ}
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀) (hmean : MeanZeroOn unitCube θ₀)
    (han : IsThetaAnalytic R θ₀) (hm₀M : mTheta0 β I.Λ R ≤ M) {θs : ℕ → ℝ → Vec 2 → ℝ}
    (hθs : ∀ j, mTheta0 β I.Λ R - 1 ≤ j → j ≤ M →
      IsClassicalSol (streamVel (Φ j)) (I.kappaSeq κ M j) (fun _ _ => 0) θ₀ (θs j)) :
    IsHolderTimeL2 (min (1 / 4) μB)
      (CU * (1 + velBound β) * (1 / Real.sqrt c₁) *
          epsilon β I.Λ (mTheta0 β I.Λ R - 1) ^ (-(lebronP β / 2)) *
          Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) +
        |CB| * Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) *
          (1 / (1 - (128 : ℝ) ^ (-(delta β / 2)))))
      (θs M) := by
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ1 hβ2
  have hm2 : 2 ≤ mTheta0 β I.Λ R := (mTheta0_isLeast hβ1 hβ2 hΛ7 hR).1.1
  set m₀ := mTheta0 β I.Λ R with hm₀
  set N := Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hE : 0 < epsilon β I.Λ (m₀ - 1) := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hBv : 0 ≤ velBound β := velBound_nonneg hβ1
  have hμ₁ : 0 < min (1 / 4 : ℝ) μB := lt_min (by norm_num) hμB
  -- base level
  obtain ⟨hκlo, hκ1⟩ := hW I hz hx hh hΛ₁ κ hκ M hM hκM m₀ hm2 hm₀M (m₀ - 1) (Or.inl rfl)
  have hκpos : 0 < I.kappaSeq κ M (m₀ - 1) := lt_of_lt_of_le (by positivity) hκlo
  have hbase4 : IsHolderTimeL2 (1 / 4)
      (CU * (1 + velBound β) * (1 / Real.sqrt c₁) *
          epsilon β I.Λ (m₀ - 1) ^ (-(lebronP β / 2)) * N) (θs (m₀ - 1)) := by
    intro s hs t ht
    have h1 := classical_quarter hU hΦ (m₀ - 1) hκpos hκ1 hθ₀ hper
      (hθs (m₀ - 1) le_rfl (by omega)) s hs t ht
    have h2 := one_div_sqrt_le hc₁ hE hκlo
    have hh0 : 0 ≤ |t - s| ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
    refine h1.trans ?_
    calc CU * (1 + velBound β) / Real.sqrt (I.kappaSeq κ M (m₀ - 1)) *
          |t - s| ^ ((1 : ℝ) / 4) * N
        = CU * (1 + velBound β) * (1 / Real.sqrt (I.kappaSeq κ M (m₀ - 1))) *
          N * |t - s| ^ ((1 : ℝ) / 4) := by ring
      _ ≤ CU * (1 + velBound β) * ((1 / Real.sqrt c₁) *
          epsilon β I.Λ (m₀ - 1) ^ (-(lebronP β / 2))) * N * |t - s| ^ ((1 : ℝ) / 4) := by
          gcongr
      _ = _ := by ring
  have hA0 : 0 ≤ CU * (1 + velBound β) * (1 / Real.sqrt c₁) *
      epsilon β I.Λ (m₀ - 1) ^ (-(lebronP β / 2)) * N := by
    have := Real.rpow_nonneg hE.le (-(lebronP β / 2))
    positivity
  have hbase := IsHolderTimeL2.mono_exp hμ₁ (min_le_left _ _) hA0 hbase4
  have hchain := chain_holder (f := θs) (c := fun n => |CB| * epsilon β I.Λ (n - 1) ^ (delta β /
      2) * N)
    (n₀ := m₀ - 1) hbase M (by omega)
    (fun n h1 h2 t ht => IsClassicalSol.continuous_slice (hθs n h1 h2) ht.1)
    (by
      intro n hn1 hn2
      have hb := hB I hz hx hh hCB Φ hΦ κ hκ M hM hκM R hR θ₀ hθ₀ hper hmean han n
        (by omega) hn2 (θs n) (θs (n - 1)) (hθs n (by omega) hn2)
        (hθs (n - 1) (by omega) (by omega))
      have hε' : 0 ≤ epsilon β I.Λ (n - 1) ^ (delta β / 2) :=
        Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7).le _
      have hnn : 0 ≤ |CB| * epsilon β I.Λ (n - 1) ^ (delta β / 2) * N := by positivity
      refine IsHolderTimeL2.mono_exp hμ₁ (min_le_right _ _) hnn ?_
      refine IsHolderTimeL2.mono_const (holderTimeL2Le_isHolder hb) ?_
      have : CB * epsilon β I.Λ (n - 1) ^ (delta β / 2) ≤ |CB| * epsilon β I.Λ (n - 1) ^ (delta β
          / 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hε'
      exact mul_le_mul_of_nonneg_right this hN0)
  refine IsHolderTimeL2.mono_const hchain ?_
  have hsum := eps_sum_Ioc_le I (by linarith : 0 < delta β / 2) m₀ M hm2
  have e : ∑ n ∈ Finset.Ioc (m₀ - 1) M, |CB| * epsilon β I.Λ (n - 1) ^ (delta β / 2) * N =
      |CB| * N * ∑ n ∈ Finset.Ioc (m₀ - 1) M, epsilon β I.Λ (n - 1) ^ (delta β / 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e]
  have : |CB| * N * ∑ n ∈ Finset.Ioc (m₀ - 1) M, epsilon β I.Λ (n - 1) ^ (delta β / 2) ≤
      |CB| * N * (1 / (1 - (128 : ℝ) ^ (-(delta β / 2)))) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith

end AVenhance.Infra.FullTheorem
