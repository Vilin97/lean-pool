/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.FullStatement
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.NoSelectionContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.UniformHolderContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.NoSelectionInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.UniformHolder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Full.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Nonempty
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.ExistsIsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.LimitFieldRegular

/-! # The combined main theorem from the no-selection statement

`anomalous_dissipation_full_of_noSelection`: for `α < 1/3` choose `β`, the ingredients `I` with a
large `Λ`, the stream sequence and its limit `φ`, and `κ_j = ε_{j+1}^p`; then the three
parts follow from `a0Core_contract`, `uniformHolder_contract` and the no-selection statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Numerical choice of the exponent `β`. -/
theorem FullAssembly.exists_beta (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ β : ℝ, 6 / 5 ≤ β ∧ α < β - 1 ∧ β < 4 / 3 ∧ 1 < β := by
  have h1 := le_max_left (6 / 5 : ℝ) (1 + α)
  have h2 := le_max_right (6 / 5 : ℝ) (1 + α)
  have h3 : max (6 / 5 : ℝ) (1 + α) < 4 / 3 := max_lt (by norm_num) (by linarith)
  refine ⟨(max (6 / 5) (1 + α) + 4 / 3) / 2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The combined main theorem** from the no-selection input. -/
theorem anomalous_dissipation_full_of_noSelection
    (hNS : ∀ β C₀ : ℝ, NoSelectionContract β C₀) : AnomalousDissipationFullStatement := by
  intro α hα₀ hα₁
  obtain ⟨β, hβ65, hαβ, hβ43, hβ1⟩ := FullAssembly.exists_beta α hα₀ hα₁
  obtain ⟨C₀, -, hnon⟩ := Ingredients.nonempty β hβ1 hβ43
  obtain ⟨Λ₀, hA0⟩ := Contracts.a0Core_contract β C₀ hβ65
  obtain ⟨μ, Λ₃, hμ, hUH⟩ := Contracts.uniformHolder_contract β C₀
  obtain ⟨ν, Λ₄, hν, hNSc⟩ := hNS β C₀
  have hp : 0 < 2 * β / (q β + 1) := Full.permitted_exponent_pos hβ1 hβ43
  set p := 2 * β / (q β + 1) with hpdef
  set L : ℝ := max (max Λ₀ Λ₃) (max Λ₄ ((5 : ℝ) ^ (1 / p))) with hL
  obtain ⟨I, hIΛ, hz, hx, hh⟩ := hnon (max (2 ^ 7) ⌈L⌉₊) (le_max_left _ _)
  have hΛL : L ≤ (I.Λ : ℝ) := by
    rw [hIΛ]
    exact (Nat.le_ceil L).trans (by exact_mod_cast le_max_right _ _)
  have hΛ₀ : Λ₀ ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛL
  have hΛ₃ : Λ₃ ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛL
  have hΛ₄ : Λ₄ ≤ (I.Λ : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΛL
  have hΛ₅ : (5 : ℝ) ^ (1 / p) ≤ (I.Λ : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛL
  obtain ⟨Φ, hΦ⟩ := exists_isStreamSeq I
  obtain ⟨C, hC1, hlim⟩ := limit_field_regular β
  obtain ⟨φ, htend, -, -, -, hhol⟩ := hlim I Φ hΦ
  obtain ⟨hHolder, hdiv⟩ := hhol α hα₀ hαβ
  obtain ⟨ϱ, hϱ, hmain⟩ := hA0 I hz hx hh hΛ₀ Φ hΦ φ htend
  obtain ⟨CU, hCU0, hCU⟩ := hUH I hz hx hh hΛ₃ Φ hΦ φ htend
  obtain ⟨S, hSun, hSn1, hSmain⟩ := hNSc I hz hx hh hΛ₄ Φ hΦ φ htend
  have heps : ∀ m, 0 < epsilon β I.Λ m :=
    fun m => Infra.Cutoff.epsilon_pos (Λ := I.Λ) (m := m) I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  refine ⟨streamVel φ, hHolder, hdiv, ϱ, hϱ, fun j => epsilon β I.Λ (j + 1) ^ p,
    fun j => Real.rpow_pos_of_pos (heps _) _,
    fun j => Full.four_mul_epsilon_rpow_lt I hp hΛ₅ (j + 1), ?_,
    μ, ν, CU, hμ, hν,
    {θ₀ | ∃ n ∈ S, ∃ c : ℝ, c ≠ 0 ∧ θ₀ = fun x : Vec 2 => c * Real.cos (2 * Real.pi * (n : ℝ) * x
        0)},
    hmain, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tendsto_add_atTop_iff_nat (f := fun m => epsilon β I.Λ m ^ p) 1).2
      (Infra.Construction.epsilon_rpow_tendsto_zero I hp)
  · intro θ₀ Dθ₀ h1 h2 κ hκ θ hθ
    obtain ⟨j, hj1, hj2⟩ := Set.mem_iUnion.1 hκ
    dsimp only at hj1 hj2
    refine hCU θ₀ Dθ₀ h1 h2 κ ?_ θ hθ
    refine Set.mem_iUnion₂.2 ⟨j + 1, by omega, ?_⟩
    exact ⟨show 1 / 2 * epsilon β I.Λ (j + 1) ^ p ≤ κ by linarith,
      show κ ≤ 2 * epsilon β I.Λ (j + 1) ^ p by linarith⟩
  · rintro θ₀ ⟨n, hn, c, hc, rfl⟩
    obtain ⟨a, b, d, e, -⟩ := Contracts.cosineDatum_contract n (hSn1 n hn) c
    exact ⟨a, b, d, by rw [e]; positivity⟩
  · rintro θ₀ ⟨n, hn, c, hc, rfl⟩ c' hc'
    exact ⟨n, hn, c' * c, mul_ne_zero hc' hc, by funext x; simp only [mul_assoc]⟩
  · intro N
    obtain ⟨n, hn, hNn⟩ := hSun N
    exact ⟨n, hNn, n, hn, 1, one_ne_zero, by funext x; simp⟩
  · rintro θ₀ ⟨n, hn, c, hc, rfl⟩ θ hθ
    exact hSmain n hn c hc θ hθ

end AVenhance.Infra.FullTheorem
