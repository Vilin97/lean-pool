/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.AnalyticUniformContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.LemmaU
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.LebronStepAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.CaseBig
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.LimitFieldRegular

/-! # The analytic case of `r.LeBron.2`, proved

`analyticUniform_contract`: assembly of the two cases `M ≤ m₀ − 1` (`case_small`) and `M ≥ m₀`
(`case_big`), with the scale `ε_{m₀-1}` converted to a power of the analytic radius `R`
(`epsilon_mTheta0_lower`, `inv_rpow_le`). -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem

/-- The exponent of `R^{-p}`: `p = q/(1+γ/2) · e`. -/
def unifP (β : ℝ) : ℝ := q β / (1 + gamma β / 2) * unifE β

theorem AnalyticUniform.limit_periodic' {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hΦ : ∀ M, IsAdmissibleStream (Φ M))
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) (t : ℝ) :
    IsZ2Periodic (φ t) := by
  intro n x
  refine tendsto_nhds_unique (htend t (x + latticeShift n)) ?_
  have h := htend t x
  refine h.congr fun M => ?_
  have := (hΦ M).2 0 n t x
  simpa using this.symm

theorem AnalyticUniform.limit_meas' {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hΦ : ∀ M, IsAdmissibleStream (Φ M))
    (htend : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (μ : Measure (ℝ × Vec 2)) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2) μ := by
  have hm : Measurable (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    measurable_of_tendsto_metrizable (f := fun M (p : ℝ × Vec 2) => Φ M p.1 p.2)
      (fun M => (hΦ M).1.continuous.measurable)
      (tendsto_pi_nhds.2 fun p => htend p.1 p.2)
  exact hm.aestronglyMeasurable

theorem analyticUniform_contract (β C₀ : ℝ) : AnalyticUniformContract β C₀ := by
  by_cases hβr : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨1, 0, 0, one_pos, le_rfl, fun I => ?_⟩
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hβr
  obtain ⟨hβ1, hβ2⟩ := hβr
  obtain ⟨CU, hCU, hUc⟩ := lemmaU_with_of_contract lemmaU_contract
  obtain ⟨μB, CB, hμB, hB⟩ := lebron_with_of_statement
    (lebron_step_of_lemmaU lemmaU_contract β C₀)
  obtain ⟨c₁, Λ₁, hc₁, hW⟩ := window_with β C₀
  obtain ⟨Ct, hCt1, hlim⟩ := AVenhance.limit_field_regular β
  have hγ := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hγβ := gamma_lt_beta hβ1 hβ2
  have hμt : 0 < tailMu β := lebronMu_pos (tailExp_pos hβ1 hβ2) (by linarith)
  have hμ : 0 < min (min (1 / 4 : ℝ) μB) (tailMu β) :=
    lt_min (lt_min (by norm_num) hμB) hμt
  have he := unifE_nonneg hβ1 hβ2
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ1 hβ2
  have hr : 0 ≤ q β / (1 + gamma β / 2) := by positivity
  refine ⟨min (min (1 / 4 : ℝ) μB) (tailMu β), unifP β,
    max (max CB Λ₁) ((2 : ℝ) ^ (1 / (β - gamma β))), hμ, mul_nonneg hr he, ?_⟩
  intro I hz hx hh hΛ Φ hΦ φ htend
  have hCB : CB ≤ (I.Λ : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hΛ
  have hΛ₁ : Λ₁ ≤ (I.Λ : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hΛ
  have hΛs : (2 : ℝ) ^ (1 / (β - gamma β)) ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ
  have hΛ7 := I.two_pow_seven_le
  have hadm : ∀ M, IsAdmissibleStream (Φ M) := streamSeq_isAdmissible hΦ
  -- the limit field
  obtain ⟨φ', htend', htail', hdiff', -, hhol'⟩ := hlim I Φ hΦ
  have hφφ : φ' = φ := by
    funext t x
    exact tendsto_nhds_unique (htend' t x) (htend t x)
  subst hφφ
  have hα0 : 0 < (β - 1) / 2 := by linarith
  have hα1 : (β - 1) / 2 < β - 1 := by linarith
  obtain ⟨hHolder, hdiv⟩ := hhol' _ hα0 hα1
  obtain ⟨Cb, hCb⟩ := hHolder.2.2.1
  have hBφ : 0 ≤ max Cb 0 := le_max_right _ _
  have hb_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ' t x‖ ≤ max Cb 0 :=
    fun t ht x => (hCb t ht x).trans (le_max_left _ _)
  have hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ' p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :=
    hHolder.2.1.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
  have hφ_meas := AnalyticUniform.limit_meas' hadm htend (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ
      Set.univ))
  have hφ_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ' t) :=
    fun t _ => AnalyticUniform.limit_periodic' hadm htend t
  have hφ_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ' t) := fun t _ => hdiff' t
  -- the constants
  have hε1 : 0 < epsilon β I.Λ 1 := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  set c := min (epsilon β I.Λ 1) (1 / 2) with hc
  have hc0 : 0 < c := lt_min hε1 (by norm_num)
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hce : 1 ≤ c ^ (-unifE β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc0 hc1 (by linarith)
  have hce0 : 0 ≤ c ^ (-unifE β) := Real.rpow_nonneg hc0.le _
  have hBv : 0 ≤ velBound β := velBound_nonneg hβ1
  have hS : 0 ≤ 1 / (1 - (128 : ℝ) ^ (-(delta β / 2))) := by
    have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ1 hβ2
    have h1 : (128 : ℝ) ^ (-(delta β / 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact one_div_nonneg.2 (by linarith)
  have hK₂ : 0 ≤ tailK β CU Ct (max (max Cb 0) (velBound β)) :=
    tailK_nonneg hβ1 hβ2 hCU.le (by linarith) (hBφ.trans (le_max_left _ _))
  set B₀ := CU * (1 + max Cb 0) * (1 / Real.sqrt (1 / 2)) with hB₀
  set A₀ := CU * (1 + velBound β) * (1 / Real.sqrt c₁) with hA₀
  set T := |CB| * (1 / (1 - (128 : ℝ) ^ (-(delta β / 2)))) +
    tailK β CU Ct (max (max Cb 0) (velBound β)) with hT
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hT0 : 0 ≤ T := by positivity
  refine ⟨(B₀ + A₀ + T) * c ^ (-unifE β), by positivity, ?_⟩
  intro κ hκ R hR θ₀ hθ₀ hper hmean han θ hθ
  obtain ⟨M, hM, hκM⟩ := Set.mem_iUnion₂.1 hκ
  -- the scale `ε_{m₀-1}`
  have hm2 : 2 ≤ mTheta0 β I.Λ R := (mTheta0_isLeast hβ1 hβ2 hΛ7 hR).1.1
  set E := epsilon β I.Λ (mTheta0 β I.Λ R - 1) with hEdef
  have hE : 0 < E := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hX : E ^ (-unifE β) ≤ c ^ (-unifE β) * (1 + R ^ (-unifP β)) :=
    inv_rpow_le hc0 hR he (epsilon_mTheta0_lower hβ1 hβ2 hΛ7 hR)
  have hRp : 0 ≤ R ^ (-unifP β) := Real.rpow_nonneg hR.le _
  have hY : 1 ≤ c ^ (-unifE β) * (1 + R ^ (-unifP β)) := by nlinarith
  set N := Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  set μ := min (min (1 / 4 : ℝ) μB) (tailMu β) with hμdef
  rcases Nat.lt_or_ge M (mTheta0 β I.Λ R) with hMm | hMm
  · -- `M ≤ m₀ - 1`
    have h1 := case_small hUc hCU hBφ hΛs hb_meas
      (fun t ht => hHolder.1 t ht) hdiv hb_bdd hM hκM (R := R) hθ₀ hper hθ (by omega)
    have hnn : 0 ≤ B₀ * E ^ (-unifE β) * N := by
      have := Real.rpow_nonneg hE.le (-unifE β)
      positivity
    have h2 := IsHolderTimeL2.mono_exp hμ (le_trans (min_le_left _ _) (min_le_left _ _)) hnn h1
    refine IsHolderTimeL2.mono_const h2 ?_
    calc B₀ * E ^ (-unifE β) * N ≤ B₀ * (c ^ (-unifE β) * (1 + R ^ (-unifP β))) * N := by
          gcongr
      _ ≤ ((B₀ + A₀ + T) * c ^ (-unifE β)) * (1 + R ^ (-unifP β)) * N := by
          have : B₀ * c ^ (-unifE β) ≤ (B₀ + A₀ + T) * c ^ (-unifE β) :=
            mul_le_mul_of_nonneg_right (by linarith) hce0
          have h3 : B₀ * (c ^ (-unifE β) * (1 + R ^ (-unifP β))) =
              (B₀ * c ^ (-unifE β)) * (1 + R ^ (-unifP β)) := by ring
          rw [h3]
          gcongr
  · -- `m₀ ≤ M`
    have h1 := case_big hUc hCU hμB hB hc₁ hW (by linarith) hBφ hz hx hh hCB hΛ₁ hΛs hΦ
      htail' hφ_meas hφ_per hφ_diff hb_meas (fun t ht => hHolder.1 t ht) hdiv hb_bdd hκ hM hκM
      hR hθ₀ hper hmean han hθ hMm
    refine IsHolderTimeL2.mono_const h1 ?_
    have hEnn := Real.rpow_nonneg hE.le (-unifE β)
    have hTY : T ≤ T * (c ^ (-unifE β) * (1 + R ^ (-unifP β))) := by
      calc T = T * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hY hT0
    calc (A₀ * E ^ (-unifE β) + |CB| * (1 / (1 - (128 : ℝ) ^ (-(delta β / 2)))) +
          tailK β CU Ct (max (max Cb 0) (velBound β))) * N
        = (A₀ * E ^ (-unifE β) + T) * N := by rw [hT]; ring
      _ ≤ (A₀ * (c ^ (-unifE β) * (1 + R ^ (-unifP β))) +
            T * (c ^ (-unifE β) * (1 + R ^ (-unifP β)))) * N := by
          gcongr
      _ = (A₀ + T) * c ^ (-unifE β) * (1 + R ^ (-unifP β)) * N := by ring
      _ ≤ ((B₀ + A₀ + T) * c ^ (-unifE β)) * (1 + R ^ (-unifP β)) * N := by
          gcongr
          linarith

end AVenhance.Infra.FullTheorem.Contracts
