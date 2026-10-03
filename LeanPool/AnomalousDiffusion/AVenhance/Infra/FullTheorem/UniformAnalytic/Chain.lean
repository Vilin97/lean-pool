/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.Defs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.Holder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.Interpolation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.VelocityBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergySmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ForcedEnergyClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.ClassicalWellposed
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds

/-! # The classical chain `θ_{m₀-1}, …, θ_M` and the Hölder bound of `θ_M`

* Lemma U for the classical iterates (uniform drift bound `velBound β`);
* existence of the classical chain (classical well-posedness);
* the series `∑ ε_{n-1}^s` is bounded by `1/(1-128^{-s})`;
* `θ_M` is `μ₁`-Hölder in `L²` with constant `S₁ ε_{m₀-1}^{-P/2} ‖θ₀‖_{H¹}` (Lemma U at the base
  level and Lemma r.LeBron for the increments). -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Lemma U for a classical iterate. -/
theorem classical_quarter {CU : ℝ} (hU : LemmaUWith CU) {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (j : ℕ) {κj : ℝ} (h0 : 0 < κj)
    (h1 : κj ≤ 1) {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀)
    {θ : ℝ → Vec 2 → ℝ} (hθ : IsClassicalSol (streamVel (Φ j)) κj (fun _ _ => 0) θ₀ θ) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤
        CU * (1 + velBound β) / Real.sqrt κj * |t - s| ^ ((1 : ℝ) / 4) *
          Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) := by
  intro s hs t ht
  have hadm := streamSeq_isAdmissible hΦ j
  have hcont := hadm.vel_continuous
  have hweakθ := Infra.Section5.RelativeError.classical_isWeakSolutionGrad hcont hθ
  exact hU (streamVel (Φ j)) (hcont.aestronglyMeasurable)
    (fun t _ => streamVel_isZ2Periodic hadm t) (isDivFree_streamVel hadm) (velBound β)
    (velBound_nonneg I.one_lt_beta)
    (fun t _ x => streamVel_norm_le hΦ j t x) κj h0 h1 θ₀ (fun x => spaceGrad θ₀ x)
    (Infra.Section5.RelativeError.isPeriodicH1With_of_contDiff
      (hθ₀.of_le (by exact_mod_cast le_top)) hper) θ (fun t x => spaceGrad (θ t) x)
    hweakθ s hs t ht

/-- The series bound `∑_{n ∈ (n₀-1, M]} ε_{n-1}^s ≤ 1/(1-128^{-s})` for `n₀ ≥ 2`. -/
theorem eps_sum_Ioc_le {β s : ℝ} (I : Ingredients β) (hs : 0 < s) (n₀ M : ℕ) (hn₀ : 2 ≤ n₀) :
    ∑ n ∈ Finset.Ioc (n₀ - 1) M, epsilon β I.Λ (n - 1) ^ s ≤ 1 / (1 - (128 : ℝ) ^ (-s)) := by
  have hε : ∀ n, 0 < epsilon β I.Λ n := fun n =>
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hsub : Finset.Ioc (n₀ - 1) M ⊆ Finset.Ico 2 (M + 1) := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hn ⊢
    omega
  have h1 : ∑ n ∈ Finset.Ioc (n₀ - 1) M, epsilon β I.Λ (n - 1) ^ s ≤
      ∑ n ∈ Finset.Ico 2 (M + 1), epsilon β I.Λ (n - 1) ^ s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => Real.rpow_nonneg (hε _).le _
  have h2 : ∑ n ∈ Finset.Ico 2 (M + 1), epsilon β I.Λ (n - 1) ^ s =
      ∑ k ∈ Finset.range (M + 1 - 2), epsilon β I.Λ (1 + k) ^ s := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    omega
  have hsum := Infra.Construction.epsilon_rpow_sum_bound I hs 1 (M + 1 - 2)
  have he1 : epsilon β I.Λ 1 ^ s ≤ 1 :=
    Real.rpow_le_one (hε 1).le (Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      I.two_pow_seven_le) hs.le
  have hΛ : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
  have hden : (1 : ℝ) - (128 : ℝ) ^ (-s) ≤ 1 - (I.Λ : ℝ) ^ (-s) := by
    have : (I.Λ : ℝ) ^ (-s) ≤ (128 : ℝ) ^ (-s) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num)]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hΛ hs.le)
    linarith
  have hden0 : 0 < (1 : ℝ) - (128 : ℝ) ^ (-s) := by
    have h1 : (128 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  rw [h2] at h1
  refine h1.trans (hsum.trans ?_)
  calc epsilon β I.Λ 1 ^ s / (1 - (I.Λ : ℝ) ^ (-s))
      ≤ 1 / (1 - (I.Λ : ℝ) ^ (-s)) := div_le_div_of_nonneg_right he1 (by linarith)
    _ ≤ 1 / (1 - (128 : ℝ) ^ (-s)) := one_div_le_one_div_of_le hden0 hden

/-- The classical chain exists (classical well-posedness), at every level with positive
    diffusivity. -/
theorem exists_classical_chain {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {κ : ℝ} {M n₀ : ℕ}
    (hpos : ∀ j, n₀ ≤ j → j ≤ M → 0 < I.kappaSeq κ M j) {θ₀ : Vec 2 → ℝ}
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀) :
    ∃ θs : ℕ → ℝ → Vec 2 → ℝ, ∀ j, n₀ ≤ j → j ≤ M →
      IsClassicalSol (streamVel (Φ j)) (I.kappaSeq κ M j) (fun _ _ => 0) θ₀ (θs j) := by
  have h : ∀ j : ℕ, ∃ θ : ℝ → Vec 2 → ℝ, n₀ ≤ j → j ≤ M →
      IsClassicalSol (streamVel (Φ j)) (I.kappaSeq κ M j) (fun _ _ => 0) θ₀ θ := by
    intro j
    by_cases hj : n₀ ≤ j ∧ j ≤ M
    · obtain ⟨θ, hθ, -⟩ := AVenhance.classical_wellposed (Φ j) (streamSeq_isAdmissible hΦ j)
        (I.kappaSeq κ M j) (hpos j hj.1 hj.2) (fun _ _ => 0)
        (contDiffOn_const) (fun _ _ => by intro n x; rfl) θ₀ hθ₀ hper
      exact ⟨θ, fun _ _ => hθ⟩
    · exact ⟨fun _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose θs hθs using h
  exact ⟨θs, hθs⟩

end AVenhance.Infra.FullTheorem
