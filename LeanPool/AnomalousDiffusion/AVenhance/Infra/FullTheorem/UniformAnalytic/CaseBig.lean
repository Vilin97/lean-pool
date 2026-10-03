/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.CaseSmall
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.ThetaM

/-! # Case `M ≥ m₀` of the analytic case of `r.LeBron.2`

`θ = θ_M + (θ − θ_M)`: the chain bound for `θ_M` (`ThetaM`) plus the tail piece (`TailHolder`). -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem kappaSeq_top {β : ℝ} (I : Ingredients β) (κ : ℝ) (M : ℕ) : I.kappaSeq κ M M = κ := by
  simp [Ingredients.kappaSeq, Ingredients.kappaAt]

theorem case_big {β C₀ CU μB CB c₁ Λ₁ Ct Bφ : ℝ} (hU : LemmaUWith CU) (hCU : 0 < CU)
    (hμB : 0 < μB) (hB : LebronWith β C₀ μB CB) (hc₁ : 0 < c₁) (hW : WindowWith β C₀ c₁ Λ₁)
    (hCt : 0 ≤ Ct) (hBφ : 0 ≤ Bφ)
    {I : Ingredients β} (hz : I.Czeta ≤ C₀) (hx : I.Cxi ≤ C₀) (hh : I.Chat ≤ C₀)
    (hCB : CB ≤ (I.Λ : ℝ)) (hΛ₁ : Λ₁ ≤ (I.Λ : ℝ))
    (hΛs : (2 : ℝ) ^ (1 / (β - gamma β)) ≤ (I.Λ : ℝ))
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {φ : ℝ → Vec 2 → ℝ}
    (htail : ∀ (M : ℕ) (t : ℝ) (x : Vec 2),
      |φ t x - Φ M t x| ≤ Ct * epsilon β I.Λ (M + 1) ^ β)
    (hφ_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hφ_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ t))
    (hφ_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t))
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (streamVel φ t))
    (hdiv : IsDivFree (streamVel φ))
    (hb_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ t x‖ ≤ Bφ)
    {κ : ℝ} (hκ : κ ∈ permissibleSet β I.Λ) {M : ℕ} (hM : 1 ≤ M)
    (hκM : κ ∈ permittedInterval β I.Λ M) {R : ℝ} (hR : 0 < R) {θ₀ : Vec 2 → ℝ}
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀) (hmean : MeanZeroOn unitCube θ₀)
    (han : IsThetaAnalytic R θ₀) {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsWeakSolution (streamVel φ) κ θ₀ θ) (hMm : mTheta0 β I.Λ R ≤ M) :
    IsHolderTimeL2 (min (min (1 / 4) μB) (tailMu β))
      ((CU * (1 + velBound β) * (1 / Real.sqrt c₁) *
          epsilon β I.Λ (mTheta0 β I.Λ R - 1) ^ (-unifE β) +
        |CB| * (1 / (1 - (128 : ℝ) ^ (-(delta β / 2)))) +
        tailK β CU Ct (max Bφ (velBound β))) *
        Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀))) θ := by
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ1 hβ2
  have hγ := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hm2 : 2 ≤ mTheta0 β I.Λ R := (mTheta0_isLeast hβ1 hβ2 hΛ7 hR).1.1
  set m₀ := mTheta0 β I.Λ R with hm₀
  set N := Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  set E := epsilon β I.Λ (m₀ - 1) with hEdef
  have hE : 0 < E := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one hβ1 hβ2 hΛ7
  have hμt : 0 < tailMu β := lebronMu_pos (tailExp_pos hβ1 hβ2)
    (by linarith [gamma_lt_beta hβ1 hβ2])
  have hμ' : 0 < min (min (1 / 4 : ℝ) μB) (tailMu β) :=
    lt_min (lt_min (by norm_num) hμB) hμt
  have hBv : 0 ≤ velBound β := velBound_nonneg hβ1
  -- positivity of the chain diffusivities
  have hpos : ∀ j, m₀ - 1 ≤ j → j ≤ M → 0 < I.kappaSeq κ M j := by
    intro j hj1 hj2
    by_cases hj : j = m₀ - 1
    · subst hj
      have := (hW I hz hx hh hΛ₁ κ hκ M hM hκM m₀ hm2 hMm (m₀ - 1) (Or.inl rfl)).1
      exact lt_of_lt_of_le (by positivity) this
    · have := (hW I hz hx hh hΛ₁ κ hκ M hM hκM j (by omega) hj2 j (Or.inr rfl)).1
      exact lt_of_lt_of_le (by
        have := Infra.Cutoff.epsilon_pos (Λ := I.Λ) (m := j - 1) hβ1 hβ2 hΛ7
        positivity) this
  obtain ⟨θs, hθs⟩ := exists_classical_chain hΦ hpos hθ₀ hper
  have hθM : IsClassicalSol (streamVel (Φ M)) κ (fun _ _ => 0) θ₀ (θs M) := by
    have := hθs M (by omega) le_rfl
    rwa [kappaSeq_top] at this
  -- the two pieces
  have h1 := thetaM_holder hU hCU hμB hB hc₁ hW hz hx hh hCB hΛ₁ hΦ hκ hM hκM hR hθ₀ hper hmean
    han hMm hθs
  obtain ⟨hκlo, hκ1⟩ := permitted_bounds hβ1 hβ2 hΛ7 hΛs hM hκM
  have h2 := w_holder hU hCU hCt hBφ hΦ htail hφ_meas hφ_per hφ_diff hb_meas hb_per hdiv hb_bdd
    hM hκlo hκ1 hθ₀ hper hθ hθM
  -- exponent unification
  have hexp : E ^ (-(lebronP β / 2)) ≤ E ^ (-unifE β) := by
    refine Real.rpow_le_rpow_of_exponent_ge hE hE1 ?_
    have : lebronP β / 2 ≤ unifE β := by
      unfold unifE
      have := le_max_left (lebronP β) (β - gamma β)
      linarith
    linarith
  have hA₀ : 0 ≤ CU * (1 + velBound β) * (1 / Real.sqrt c₁) := by positivity
  have hS : 0 ≤ 1 / (1 - (128 : ℝ) ^ (-(delta β / 2))) := by
    have h1 : (128 : ℝ) ^ (-(delta β / 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact one_div_nonneg.2 (by linarith)
  have hK₂ : 0 ≤ tailK β CU Ct (max Bφ (velBound β)) :=
    tailK_nonneg hβ1 hβ2 hCU.le hCt (hBφ.trans (le_max_left _ _))
  have hH₁ : 0 ≤ CU * (1 + velBound β) * (1 / Real.sqrt c₁) *
          E ^ (-(lebronP β / 2)) * N +
        |CB| * N * (1 / (1 - (128 : ℝ) ^ (-(delta β / 2)))) := by
    have := Real.rpow_nonneg hE.le (-(lebronP β / 2))
    positivity
  have h1' := IsHolderTimeL2.mono_exp hμ' (min_le_left _ _) hH₁ h1
  have h2' := IsHolderTimeL2.mono_exp hμ' (min_le_right _ _)
    (by positivity : 0 ≤ tailK β CU Ct (max Bφ (velBound β)) * N) h2
  -- memberships
  obtain ⟨Dθ, hDθ⟩ := hθ
  have hmθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ t) := fun t ht => (hDθ.1 t ht).2
  have hmM : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θs M t) := fun t ht =>
    Infra.Section5.Integration.memL2On_unitCube_of_continuous
      (IsClassicalSol.continuous_slice hθM ht.1)
  have hsp := holder_split hmθ hmM h1' h2'
  refine IsHolderTimeL2.mono_const hsp ?_
  have hsmall : CU * (1 + velBound β) * (1 / Real.sqrt c₁) * E ^ (-(lebronP β / 2)) * N ≤
      CU * (1 + velBound β) * (1 / Real.sqrt c₁) * E ^ (-unifE β) * N := by
    gcongr
  linarith [hsmall]

end AVenhance.Infra.FullTheorem
