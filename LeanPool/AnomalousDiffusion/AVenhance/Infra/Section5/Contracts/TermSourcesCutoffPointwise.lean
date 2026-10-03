/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffXi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffDecay
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2Ioi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraDefs

/-! # Pointwise bound of `cutoff1` (`e.monster.est.3`)

At fixed `(t, x)` at most three odd `k` have `ξ'_{m,k}(t) ≠ 0`; for each, `ξ'_{m,k}` is `≤ C_ξ/τ_m`,
the corrector `χTilde_{m,k}` is `≤ (4/3) τ_m e^{-π²κ τ_m/(3ε_m²)} · 2π a_m ε_m` (it vanishes before
`(k - 2/3) τ_m` and decays after `(k + 3/4) τ_m`), and `|G_{l_k}| ≤ 4 |∇T|`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section3

/-- The corrector `χTilde_{m,k}(t)` is small on the support of `ξ'_{m,k}`, entrywise. -/
theorem sb_chiTilde_abs_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 ≤ κ) (k : ℤ) {t : ℝ}
    (hsupp : ((k : ℝ) + 3 / 4) * tau β I.Λ m ≤ t ∨ t ≤ ((k : ℝ) - 3 / 4) * tau β I.Λ m)
    (x : Vec 2) (j : Fin 2) :
    |I.chiTilde hΦ m κ k t x j| ≤
      4 / 3 * tau β I.Λ m *
        Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12))) *
        (2 * Real.pi * a β I.Λ m * epsilon β I.Λ m) := by
  have hτ := I.tau_pos' m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hε _).le
  have hct : |I.corrTime κ m k t| ≤ 4 / 3 * tau β I.Λ m *
        Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12))) := by
    rcases hsupp with h | h
    · obtain ⟨h1, h2⟩ := sb_corrTime_nonneg_le_decay I hm hκ k h
      rwa [abs_of_nonneg h1]
    · have : I.corrTime κ m k t = 0 :=
        corrTime_eq_zero_before_support I κ k t (by nlinarith)
      rw [this, abs_zero]
      positivity
  have hu := uShear_component_abs_le (β := β) (Λ := I.Λ) (m := m)
    k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j
  have hpos : |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m| =
      2 * Real.pi * a β I.Λ m * epsilon β I.Λ m := abs_of_nonneg (by positivity)
  rw [hpos] at hu
  calc |I.chiTilde hΦ m κ k t x j|
      = |I.corrTime κ m k t| * |uShear β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j| := by
        simp [Ingredients.chiTilde, Ingredients.chiMK, Pi.smul_apply, smul_eq_mul, abs_mul]
    _ ≤ _ := mul_le_mul hct hu (abs_nonneg _) (by positivity)

/-- `|G_l| ≤ 4 |∇T|` when the flow is `ε^{2δ}`-close to the identity. -/
theorem sb_G_abs_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ}
    (hξ : I.xiMK m k t ≠ 0) {T : ℝ → Vec 2 → ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2)
    (j : Fin 2) :
    |G I hΦ m T (lIdx β I.Λ m k) t x j| ≤ 4 * Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
  have hT := (hTt.differentiable (by simp) x).hasFDerivAt
  have hX := ((RelativeError.contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t).differentiable (by
      simp)
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
  rw [G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x hT hX
    (RelativeError.xFlow_xFlowInv I hΦ m _ t x)]
  have hε1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le).le (Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le))
      (by have := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt; linarith)
  have hF : ∀ i j, |(I.flowGrad hΦ m (lIdx β I.Λ m k) t x) i j| ≤ 2 :=
    RelativeError.abs_le_two_of_sub_one hε1 (fun i j => RelativeError.flowGrad_sub_one_le hΦ hm k
        hξ x i j)
  have := RelativeError.abs_mulVec_le (M := I.flowGrad hΦ m (lIdx β I.Λ m k) t x) (μ := 2)
    (gT := Real.sqrt (vecNormSq (spaceGrad (T t) x))) (g := spaceGrad (T t) x) hF
    (fun p => RelativeError.abs_apply_le_sqrt_vecNormSq _ p) j
  linarith

/-- Every odd `k` with `ξ_{m,k}(t) ≠ 0` has `|t - kτ_m| ≤ 5/4 τ_m`. -/
theorem sb_xiMK_ne_zero_abs_le {β : ℝ} (I : Ingredients β) (m : ℕ) {k : ℤ} {t : ℝ}
    (hne : I.xiMK m k t ≠ 0) : |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
  have hτ := I.tau_pos' m
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
    by_contra hnot
    apply hne
    have h1 := I.xi_le_ind u
    have h2 := I.ind_le_xi u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) u
    exact le_antisymm h1 (h3.trans h2)
  have habs : |u| ≤ 5 / 4 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at habs
  linarith

/-- At most three odd indices have `ξ_{m,k}(t) ≠ 0`: they lie in a finite set of card `≤ 3`. -/
theorem sb_odd_support_card {β : ℝ} (I : Ingredients β) (m : ℕ) (t : ℝ) :
    ∃ s : Finset {k : ℤ // Odd k}, s.card ≤ 3 ∧
      ∀ q : {k : ℤ // Odd k}, I.xiMK m q.1 t ≠ 0 → q ∈ s := by
  classical
  have hτ := I.tau_pos' m
  set u : ℝ := t / tau β I.Λ m with hu
  refine ⟨(Finset.Icc ⌈u - 5 / 4⌉ ⌊u + 5 / 4⌋).subtype Odd, ?_, ?_⟩
  · rw [Finset.card_subtype]
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Int.card_Icc]
    have h1 : (⌊u + 5 / 4⌋ : ℝ) ≤ u + 5 / 4 := Int.floor_le _
    have h2 : u - 5 / 4 ≤ (⌈u - 5 / 4⌉ : ℝ) := Int.le_ceil _
    have h3 : ⌊u + 5 / 4⌋ - ⌈u - 5 / 4⌉ ≤ 2 := by
      have : ((⌊u + 5 / 4⌋ - ⌈u - 5 / 4⌉ : ℤ) : ℝ) < 3 := by push_cast; linarith
      have : ⌊u + 5 / 4⌋ - ⌈u - 5 / 4⌉ < 3 := by exact_mod_cast this
      omega
    omega
  · intro q hq
    have h := sb_xiMK_ne_zero_abs_le I m hq
    rw [abs_le] at h
    rw [Finset.mem_subtype, Finset.mem_Icc]
    have h1 : u - 5 / 4 ≤ (q.1 : ℝ) := by
      rw [hu, div_sub' hτ.ne', div_le_iff₀ hτ]; nlinarith [h.2]
    have h2 : (q.1 : ℝ) ≤ u + 5 / 4 := by
      rw [hu, div_add' _ _ _ hτ.ne', le_div_iff₀ hτ]; nlinarith [h.1]
    exact ⟨Int.ceil_le.2 h1, Int.le_floor.2 h2⟩

/-- **Pointwise bound of `cutoff1`.** -/
theorem sb_cutoff1_abs_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κ : ℝ} (hκ : 0 ≤ κ)
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2) :
    |cutoff1 I hΦ m κ T t x| ≤
      64 * Real.pi * I.Cxi * (a β I.Λ m * epsilon β I.Λ m) *
        Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12))) *
        Real.sqrt (vecNormSq (spaceGrad (T t) x)) := by
  classical
  have hτ := I.tau_pos' m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hε _).le
  set E : ℝ := Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12)))
    with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set g : ℝ := Real.sqrt (vecNormSq (spaceGrad (T t) x)) with hg
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hCxi := I.one_le_Cxi
  set Dχ : ℝ := 4 / 3 * tau β I.Λ m * E * (2 * Real.pi * a β I.Λ m * epsilon β I.Λ m) with hD
  have hD0 : 0 ≤ Dχ := by rw [hD]; positivity
  set B1 : ℝ := I.Cxi / tau β I.Λ m * (2 * (Dχ * (4 * g))) with hB1
  have hB10 : 0 ≤ B1 := by rw [hB1]; positivity
  obtain ⟨s, hcard, hs⟩ := sb_odd_support_card I m t
  have hterm : ∀ q : {k : ℤ // Odd k},
      |deriv (I.xiMK m q.1) t * vecDot (I.chiTilde hΦ m κ q.1 t x)
        (G I hΦ m T (lIdx β I.Λ m q.1) t x)| ≤ B1 := by
    intro q
    by_cases h0 : deriv (I.xiMK m q.1) t = 0
    · rw [h0, zero_mul, abs_zero]; exact hB10
    obtain ⟨hξ, hsupp, hder⟩ := sb_deriv_xiMK_facts I q.1 h0
    have hχ := fun j => sb_chiTilde_abs_le I hΦ (by omega) hκ q.1 hsupp x j
    have hG := fun j => sb_G_abs_le I hΦ hm q.1 hξ hTt x j
    have hdot : |vecDot (I.chiTilde hΦ m κ q.1 t x) (G I hΦ m T (lIdx β I.Λ m q.1) t x)| ≤
        2 * (Dχ * (4 * g)) := by
      simp only [vecDot, Fin.sum_univ_two]
      have h0' := RelativeError.abs_mul_le_of_le (hχ 0) (hG 0)
      have h1' := RelativeError.abs_mul_le_of_le (hχ 1) (hG 1)
      have := RelativeError.abs_add_le_of_le h0' h1'
      rw [hD] at *
      linarith
    rw [abs_mul]
    calc _ ≤ (I.Cxi / tau β I.Λ m) * (2 * (Dχ * (4 * g))) :=
          mul_le_mul hder hdot (abs_nonneg _) (by positivity)
      _ = B1 := rfl
  have hzero : ∀ q ∉ s, deriv (I.xiMK m q.1) t * vecDot (I.chiTilde hΦ m κ q.1 t x)
        (G I hΦ m T (lIdx β I.Λ m q.1) t x) = 0 := by
    intro q hq
    by_cases h0 : deriv (I.xiMK m q.1) t = 0
    · rw [h0, zero_mul]
    · exact absurd (hs q (sb_deriv_xiMK_facts I q.1 h0).1) hq
  unfold cutoff1
  rw [tsum_eq_sum hzero]
  calc |∑ q ∈ s, deriv (I.xiMK m q.1) t * vecDot (I.chiTilde hΦ m κ q.1 t x)
        (G I hΦ m T (lIdx β I.Λ m q.1) t x)|
      ≤ ∑ q ∈ s, |deriv (I.xiMK m q.1) t * vecDot (I.chiTilde hΦ m κ q.1 t x)
        (G I hΦ m T (lIdx β I.Λ m q.1) t x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ s, B1 := Finset.sum_le_sum fun q _ => hterm q
    _ = s.card * B1 := by simp
    _ ≤ 3 * B1 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB10
    _ = 64 * Real.pi * I.Cxi * (a β I.Λ m * epsilon β I.Λ m) * E * g := by
        rw [hB1, hD]; field_simp; ring

end AVenhance.Infra.Section5.Contracts
end
