/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMKCorrector
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite

/-! # Corrector decay after its forcing support (`e.corrbounds.Chi.decay`)

The explicit one-mode corrector `χ_{m,k} = -corrTime · u_{m,k}` is driven by
`ζ̂_{m,l_k} ζ_{m,k}`, supported in `[(k - 2/3) τ_m, (k + 2/3) τ_m]`.  For `t ≥ (k + 3/4) τ_m`
the memory integral `corrTime` is at most `(4/3) τ_m exp(-(4π²κ/ε_m²) τ_m / 12)`
(`enhance.tex` 2860–2900; `π²κτ_m/(3ε_m²)` is the printed exponent). -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section3

/-- `ζ_{m,k}(s)` vanishes outside `[(k - 2/3) τ_m, (k + 2/3) τ_m]`. -/
theorem sb_zetaMK_eq_zero_of_not_mem {β : ℝ} (I : Ingredients β) {m : ℕ} (k : ℤ) {s : ℝ}
    (hs : s ∉ Set.Icc (((k : ℝ) - 2 / 3) * tau β I.Λ m) (((k : ℝ) + 2 / 3) * tau β I.Λ m)) :
    I.zetaMK m k s = 0 := by
  have hτ := I.tau_pos' m
  have hnot : (s - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m ∉
      Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    intro hu
    apply hs
    obtain ⟨h1, h2⟩ := hu
    rw [le_div_iff₀ hτ] at h1
    rw [div_le_iff₀ hτ] at h2
    constructor <;> nlinarith
  have hind : indIcc (-(2 / 3 : ℝ)) (2 / 3) ((s - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) = 0 := by
    simp [indIcc, hnot]
  have hle := I.zeta_le_ind ((s - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  have hnn := I.zeta_nonneg ((s - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  change I.zeta ((s - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) = 0
  rw [hind] at hle
  exact le_antisymm hle hnn

/-- **Corrector decay** (`e.corrbounds.Chi.decay`): after `(k + 3/4) τ_m` the memory integral is
exponentially small. -/
theorem sb_corrTime_nonneg_le_decay {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ}
    (hκ : 0 ≤ κ) (k : ℤ) {t : ℝ} (ht : ((k : ℝ) + 3 / 4) * tau β I.Λ m ≤ t) :
    0 ≤ I.corrTime κ m k t ∧ I.corrTime κ m k t ≤
      4 / 3 * tau β I.Λ m *
        Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12))) := by
  have hτ := I.tau_pos' m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  set ρ : ℝ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  set a : ℝ := ((k : ℝ) - 2 / 3) * tau β I.Λ m with ha
  set b : ℝ := ((k : ℝ) + 2 / 3) * tau β I.Λ m with hb
  set E : ℝ := Real.exp (-(ρ * (tau β I.Λ m / 12))) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hab : a ≤ b := by rw [ha, hb]; nlinarith
  have hbma : b - a = 4 / 3 * tau β I.Λ m := by rw [ha, hb]; ring
  have hnn : 0 ≤ I.corrTime κ m k t := by
    unfold Ingredients.corrTime
    apply setIntegral_nonneg measurableSet_Iic
    intro s _
    exact mul_nonneg (zetaProd_mem_Icc I hm k s).1 (Real.exp_nonneg _)
  refine ⟨hnn, ?_⟩
  let g : ℝ → ℝ := (Set.Icc a b).indicator (fun _ => E)
  have hgint : Integrable g := by
    refine (integrable_indicator_iff measurableSet_Icc).2 ?_
    exact integrableOn_const (by simp)
  have hg0 : ∀ s, 0 ≤ g s := fun s => by
    by_cases hs : s ∈ Set.Icc a b <;> simp [g, hs, hE0]
  have hpoint : ∀ s, I.zetaProd m k s * Real.exp (ρ * (s - t)) ≤ g s ∨ t < s := by
    intro s
    by_cases hst : t < s
    · exact Or.inr hst
    left
    by_cases hs : s ∈ Set.Icc a b
    · have hz := (zetaProd_mem_Icc I hm k s).2
      have hexp : Real.exp (ρ * (s - t)) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.2
        have : s - t ≤ -(tau β I.Λ m / 12) := by
          have := hs.2
          rw [hb] at this
          nlinarith
        nlinarith
      simp only [g, Set.indicator_of_mem hs]
      calc I.zetaProd m k s * Real.exp (ρ * (s - t)) ≤ 1 * E :=
            mul_le_mul hz hexp (Real.exp_nonneg _) zero_le_one
        _ = E := one_mul E
    · have hz : I.zetaProd m k s = 0 := by
        unfold Ingredients.zetaProd
        rw [sb_zetaMK_eq_zero_of_not_mem I k hs, mul_zero]
      simp [g, hs, hz]
  have hle : (∫ s in Set.Iic t, I.zetaProd m k s * Real.exp (ρ * (s - t))) ≤
      ∫ s in Set.Iic t, g s := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun s =>
        mul_nonneg (zetaProd_mem_Icc I hm k s).1 (Real.exp_nonneg _)
    · exact hgint.integrableOn
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Iic]
      refine Filter.Eventually.of_forall fun s hs => ?_
      rcases hpoint s with h | h
      · exact h
      · exact absurd hs (not_le.2 h)
  have hle2 : (∫ s in Set.Iic t, g s) ≤ ∫ s, g s :=
    setIntegral_le_integral hgint (Filter.Eventually.of_forall hg0)
  have hint : (∫ s, g s) = (b - a) * E := by
    simp only [g]
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hab]
    simp
  calc I.corrTime κ m k t
      = ∫ s in Set.Iic t, I.zetaProd m k s * Real.exp (ρ * (s - t)) := rfl
    _ ≤ (b - a) * E := hle.trans (hle2.trans hint.le)
    _ = 4 / 3 * tau β I.Λ m * E := by rw [hbma]

end AVenhance.Infra.Section5.Contracts
end
