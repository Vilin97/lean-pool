/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars

/-! # Two-sided diffusivity bounds at levels `m-1` and `m` (Lemma r.LeBron, step (c))

For `2 ≤ m ≤ M` and `Λ` large, `c₁ ε_{m-1}^{q(β+γ)} ≤ κ_j ≤ 1` for `j ∈ {m-1, m}`.
Sources: the diffusivity recursion (`l_recurse`) for `j < M`, the permitted interval for `j = M`,
    and the
supergeometric comparison `ε_m ≥ ½ ε_{m-1}^q`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The exponent `P = q (β + γ)` of Lemma r.LeBron. -/
def lebronP (β : ℝ) : ℝ := q β * (β + gamma β)

section Scales

variable {β : ℝ} {Λ : ℕ}

/-- `ε_{n+1} ≥ ½ ε_n^q` for `n ≥ 1`. -/
theorem epsilon_succ_ge (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2) * epsilon β Λ n ^ q β ≤ epsilon β Λ (n + 1) := by
  have h := (Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ hn).1
  have hle : epsilon β Λ n ≤ 1 / 128 := by
    have h1 := Infra.Ingredients.epsilon_le_lambda_pow (m := n) hβ hβ' hΛ
    have hΛ' : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    have h2 : (Λ : ℝ) ^ (-(n : ℝ)) ≤ (Λ : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
    rw [Real.rpow_neg_one] at h2
    have h3 : (Λ : ℝ)⁻¹ ≤ (128 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hΛ'
    have := h1.trans (h2.trans h3)
    simpa using this
  have hpos : 0 ≤ epsilon β Λ n ^ q β :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _
  calc (1 / 2) * epsilon β Λ n ^ q β ≤ (1 - 10 * epsilon β Λ n) * epsilon β Λ n ^ q β :=
        mul_le_mul_of_nonneg_right (by linarith) hpos
    _ ≤ _ := h

/-- `ε_{n+1}^s ≥ (1/2)^s ε_n^{q s}` for `n ≥ 1`, `s ≥ 0`. -/
theorem epsilon_rpow_succ_ge (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {n : ℕ}
    (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    (1 / 2 : ℝ) ^ s * epsilon β Λ n ^ (q β * s) ≤ epsilon β Λ (n + 1) ^ s := by
  have hε := (Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := n)).le
  calc (1 / 2 : ℝ) ^ s * epsilon β Λ n ^ (q β * s)
      = ((1 / 2) * epsilon β Λ n ^ q β) ^ s := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hε _), ← Real.rpow_mul hε]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (epsilon_succ_ge hβ hβ' hΛ hn) hs

/-- `ε_n^s ≤ 1/Λ` for `n ≥ 1`, `s ≥ 1`. -/
theorem epsilon_rpow_le_inv (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {n : ℕ}
    (hn : 1 ≤ n) {s : ℝ} (hs : 1 ≤ s) : epsilon β Λ n ^ s ≤ (Λ : ℝ)⁻¹ := by
  have hε := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := n)
  have hε1 : epsilon β Λ n ≤ 1 := Infra.Construction.epsilon_le_one hβ hβ' hΛ
  have h1 := Infra.Ingredients.epsilon_le_lambda_pow (m := n) hβ hβ' hΛ
  have hΛ' : (1 : ℝ) ≤ Λ := by
    have : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    linarith
  have h2 : (Λ : ℝ) ^ (-(n : ℝ)) ≤ (Λ : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hΛ' (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
  rw [Real.rpow_neg_one] at h2
  calc epsilon β Λ n ^ s ≤ epsilon β Λ n ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hε hε1 hs
    _ = epsilon β Λ n := Real.rpow_one _
    _ ≤ _ := h1.trans h2

/-- `ε_n^s ≤ (1/Λ)^s` for `n ≥ 1`, `s ≥ 0`. -/
theorem epsilon_rpow_le_inv_rpow (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {n : ℕ}
    (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) : epsilon β Λ n ^ s ≤ ((Λ : ℝ)⁻¹) ^ s := by
  refine Real.rpow_le_rpow (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le ?_ hs
  have := epsilon_rpow_le_inv hβ hβ' hΛ hn (s := 1) le_rfl
  simpa using this

/-- `c · Λ^{-s} ≤ 1` once `Λ ≥ c^{1/s}`, in the form needed for the top level. -/
theorem two_mul_inv_rpow_le_one {s : ℝ} (hs : 0 < s) {Λ : ℝ} (hΛ0 : 0 < Λ)
    (hΛ : (2 : ℝ) ^ (1 / s) ≤ Λ) : 2 * (Λ⁻¹) ^ s ≤ 1 := by
  have h1 : (2 : ℝ) ≤ Λ ^ s := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / s)) ^ s := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
      _ ≤ Λ ^ s := Real.rpow_le_rpow (by positivity) hΛ hs.le
  have h2 : (Λ⁻¹) ^ s = (Λ ^ s)⁻¹ := Real.inv_rpow hΛ0.le s
  rw [h2]
  have h3 : 0 < Λ ^ s := Real.rpow_pos_of_pos hΛ0 s
  rw [← div_eq_mul_inv, div_le_one h3]
  exact h1

end Scales

section Levels

/-- One level `1 ≤ j ≤ M`: `min(c,½) ε_j^{β+γ} ≤ κ_j ≤ 1`, for `Λ` large. -/
theorem kappaSeq_level {β C₀ c Cl : ℝ}
    (hl : ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
        ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
        ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
          ∀ m : ℕ, 1 ≤ m → m < M →
            c * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) ≤ I.kappaAt κ m (M - m) ∧
            I.kappaAt κ m (M - m) ≤ Cl * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)))
    (I : Ingredients β) (hz : I.Czeta ≤ C₀) (hx : I.Cxi ≤ C₀) (hh : I.Chat ≤ C₀)
    (hCl : Cl ≤ (I.Λ : ℝ)) (hΛs : (2 : ℝ) ^ (1 / (β - gamma β)) ≤ (I.Λ : ℝ))
    {κ : ℝ} (hκ : κ ∈ permissibleSet β I.Λ) {M : ℕ} (hM : 1 ≤ M)
    (hκM : κ ∈ permittedInterval β I.Λ M) {j : ℕ} (hj : 1 ≤ j) (hjM : j ≤ M) :
    min c (1 / 2) * epsilon β I.Λ j ^ (β + gamma β) ≤ I.kappaSeq κ M j ∧
      I.kappaSeq κ M j ≤ 1 := by
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hεpos : 0 < epsilon β I.Λ j := Infra.Cutoff.epsilon_pos hβ hβ' hΛ7
  have hε1 : epsilon β I.Λ j ≤ 1 := Infra.Construction.epsilon_le_one hβ hβ' hΛ7
  have hΛpos : (0 : ℝ) < I.Λ := by
    have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast hΛ7
    linarith
  have hγβ : gamma β < β := by
    unfold gamma
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hs : β - gamma β = 2 * β / (q β + 1) := by
    unfold gamma
    field_simp
    ring
  have hspos : 0 < β - gamma β := by linarith
  have hE0 : 0 ≤ epsilon β I.Λ j ^ (β + gamma β) := Real.rpow_nonneg hεpos.le _
  rcases hjM.lt_or_eq with hlt | heq
  · -- level below the top: diffusivity-recursion
    obtain ⟨hlo, hup⟩ := hl I hz hx hh κ hκ M hM hκM j hj hlt
    have hprod : a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β) =
        epsilon β I.Λ j ^ (β + gamma β) := by
      unfold a
      rw [← Real.rpow_add hεpos]
      congr 1
      ring
    rw [hprod] at hlo hup
    have hkeq : I.kappaSeq κ M j = I.kappaAt κ j (M - j) := rfl
    rw [hkeq]
    refine ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hE0) hlo, ?_⟩
    refine hup.trans ?_
    have h1 : epsilon β I.Λ j ^ (β + gamma β) ≤ (I.Λ : ℝ)⁻¹ :=
      epsilon_rpow_le_inv hβ hβ' hΛ7 hj (by linarith)
    calc Cl * epsilon β I.Λ j ^ (β + gamma β) ≤ (I.Λ : ℝ) * (I.Λ : ℝ)⁻¹ := by
          exact mul_le_mul hCl h1 hE0 hΛpos.le
      _ = 1 := by field_simp
  · -- the top level: `κ_M = κ`
    subst heq
    have hkeq : I.kappaSeq κ j j = κ := by simp [Ingredients.kappaSeq, Ingredients.kappaAt]
    rw [hkeq]
    obtain ⟨hlo, hup⟩ := hκM
    rw [← hs] at hlo hup
    have hmono : epsilon β I.Λ j ^ (β + gamma β) ≤ epsilon β I.Λ j ^ (β - gamma β) :=
      Real.rpow_le_rpow_of_exponent_ge hεpos hε1 (by linarith)
    refine ⟨?_, ?_⟩
    · calc min c (1 / 2) * epsilon β I.Λ j ^ (β + gamma β)
          ≤ (1 / 2) * epsilon β I.Λ j ^ (β + gamma β) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hE0
        _ ≤ (1 / 2) * epsilon β I.Λ j ^ (β - gamma β) := by gcongr
        _ ≤ κ := hlo
    · refine hup.trans ?_
      have h1 : epsilon β I.Λ j ^ (β - gamma β) ≤ ((I.Λ : ℝ)⁻¹) ^ (β - gamma β) :=
        epsilon_rpow_le_inv_rpow hβ hβ' hΛ7 hj hspos.le
      calc 2 * epsilon β I.Λ j ^ (β - gamma β) ≤ 2 * ((I.Λ : ℝ)⁻¹) ^ (β - gamma β) := by
            gcongr
        _ ≤ 1 := two_mul_inv_rpow_le_one hspos hΛpos hΛs

end Levels

/-- **Diffusivity window** for `j ∈ {m-1, m}`: `c₁ ε_{m-1}^{P} ≤ κ_j ≤ 1`, `P = q(β+γ)`. -/
theorem kappaSeq_window (β C₀ : ℝ) :
    ∃ c₁ Λ₁ : ℝ, 0 < c₁ ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₁ ≤ (I.Λ : ℝ) → ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ j : ℕ, (j = m - 1 ∨ j = m) →
        c₁ * epsilon β I.Λ (m - 1) ^ lebronP β ≤ I.kappaSeq κ M j ∧ I.kappaSeq κ M j ≤ 1 := by
  by_cases hβr : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨1, 1, one_pos, fun I => ?_⟩
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hβr
  obtain ⟨hβ, hβ'⟩ := hβr
  obtain ⟨c, Cl, hc, -, hl⟩ := AVenhance.l_recurse β C₀
  have hl' : ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
        ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
        ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
          ∀ m : ℕ, 1 ≤ m → m < M →
            c * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) ≤ I.kappaAt κ m (M - m) ∧
            I.kappaAt κ m (M - m) ≤ Cl * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) :=
    fun I hz hx hh κ hκ M hM hκM => (hl I hz hx hh κ hκ M hM hκM).1
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hw0 : 0 < (1 / 2 : ℝ) ^ (β + gamma β) := Real.rpow_pos_of_pos (by norm_num) _
  have hw1 : (1 / 2 : ℝ) ^ (β + gamma β) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have hmin0 : 0 < min c (1 / 2) := lt_min hc (by norm_num)
  refine ⟨min c (1 / 2) * (1 / 2 : ℝ) ^ (β + gamma β),
    max Cl ((2 : ℝ) ^ (1 / (β - gamma β))), mul_pos hmin0 hw0, ?_⟩
  intro I hz hx hh hΛ κ hκ M hM hκM m hm2 hmM j hj
  have hCl : Cl ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ
  have hΛs : (2 : ℝ) ^ (1 / (β - gamma β)) ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ
  have hΛ7 := I.two_pow_seven_le
  have hεpos : 0 < epsilon β I.Λ (m - 1) := Infra.Cutoff.epsilon_pos hβ hβ' hΛ7
  have hε1 : epsilon β I.Λ (m - 1) ≤ 1 := Infra.Construction.epsilon_le_one hβ hβ' hΛ7
  have hPge : β + gamma β ≤ lebronP β := by
    unfold lebronP
    nlinarith
  have hEP : epsilon β I.Λ (m - 1) ^ lebronP β ≤ epsilon β I.Λ (m - 1) ^ (β + gamma β) :=
    Real.rpow_le_rpow_of_exponent_ge hεpos hε1 hPge
  rcases hj with rfl | rfl
  · obtain ⟨h1, h2⟩ := kappaSeq_level (c := c) (Cl := Cl) hl' I hz hx hh hCl hΛs hκ hM hκM
      (j := m - 1) (by omega) (by omega)
    refine ⟨le_trans ?_ h1, h2⟩
    calc min c (1 / 2) * (1 / 2 : ℝ) ^ (β + gamma β) * epsilon β I.Λ (m - 1) ^ lebronP β
        ≤ min c (1 / 2) * 1 * epsilon β I.Λ (m - 1) ^ (β + gamma β) := by
          gcongr
      _ = _ := by ring
  · obtain ⟨h1, h2⟩ := kappaSeq_level (c := c) (Cl := Cl) hl' I hz hx hh hCl hΛs hκ hM hκM
      (j := j) (by omega) hmM
    refine ⟨le_trans ?_ h1, h2⟩
    have hsucc := epsilon_rpow_succ_ge (β := β) (Λ := I.Λ) hβ hβ' hΛ7 (n := j - 1) (by omega)
      (s := β + gamma β) (by linarith)
    have hj1 : j - 1 + 1 = j := by omega
    rw [hj1] at hsucc
    unfold lebronP
    calc min c (1 / 2) * (1 / 2 : ℝ) ^ (β + gamma β) * epsilon β I.Λ (j - 1) ^
          (q β * (β + gamma β))
        = min c (1 / 2) * ((1 / 2 : ℝ) ^ (β + gamma β) * epsilon β I.Λ (j - 1) ^
          (q β * (β + gamma β))) := by ring
      _ ≤ min c (1 / 2) * epsilon β I.Λ j ^ (β + gamma β) :=
          mul_le_mul_of_nonneg_left hsucc hmin0.le

end AVenhance.Infra.FullTheorem
