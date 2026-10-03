/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeqPred
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.LRecurseTop
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleArithmetic

/-! # Scale arithmetic for `e.left.to.show`

Source: `enhance.tex` 7250-7320 (`e.kappam`, `e.expqunt`, `e.corrm`), 8466-8510 (flux-size
step), 8780-8830 (`τ''/τ'`), 8588-8630 (ergodic exponent).  Pure parameter lemmas: the
two-sided bounds of the `l_recurse` for `m < M` are combined with the one-sided
terminal estimate `l_recurse_top` at `m = M`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance AVenhance.Infra.Section3

section Elementary

variable {β : ℝ} {Λ : ℕ}

theorem Scales.eps_pos (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} :
    0 < epsilon β Λ m :=
  Infra.Cutoff.epsilon_pos hβ hβ' hΛ

theorem Scales.eps_le_one (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} :
    epsilon β Λ m ≤ 1 :=
  Infra.Construction.epsilon_le_one hβ hβ' hΛ

theorem Scales.supergeoConstant_nonneg (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 ≤ Infra.Ingredients.supergeoConstant β := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  unfold Infra.Ingredients.supergeoConstant
  have : 0 ≤ q β := by linarith only [hq]
  positivity

theorem Scales.gamma_lt_beta (hβ : 1 < β) (hβ' : β < 4 / 3) : gamma β < β := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hden : 0 < q β + 1 := by linarith only [hq]
  unfold gamma
  apply (div_lt_iff₀ hden).2
  have hβpos : 0 < β := by linarith only [hβ]
  nlinarith only [hβpos]

/-- `a_m ε_m^(2+γ) = ε_m^(β+γ)`. -/
theorem Scales.a_mul_rpow_eq {m : ℕ} (hx : 0 < epsilon β Λ m) (γ : ℝ) :
    a β Λ m * epsilon β Λ m ^ (2 + γ) = epsilon β Λ m ^ (β + γ) := by
  unfold a
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- `a_m ε_m² = ε_m^β`. -/
theorem Scales.a_mul_sq_eq {m : ℕ} (hx : 0 < epsilon β Λ m) :
    a β Λ m * epsilon β Λ m ^ 2 = epsilon β Λ m ^ β := by
  unfold a
  rw [← Real.rpow_natCast (epsilon β Λ m) 2, ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem Scales.amplitude_div_scale {x γ c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    (x ^ (β - 2)) ^ 2 * x ^ 4 / (c * x ^ (β + γ)) = (1 / c) * x ^ (β - γ) := by
  rw [← Real.rpow_natCast (x ^ (β - 2)) 2, ← Real.rpow_mul hx.le,
    ← Real.rpow_natCast x 4, ← Real.rpow_add hx]
  norm_num only [Nat.cast_ofNat]
  have he : (β - 2) * (2 : ℝ) + 4 = (β - γ) + (β + γ) := by ring
  rw [he, Real.rpow_add hx]
  field_simp

/-- Successive scales: `ε_m ≤ (1 + A) ε_{m-1}^q` for `m ≥ 2`. -/
theorem Scales.eps_le_const_mul_pred_pow (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {m : ℕ} (hm : 2 ≤ m) :
    epsilon β Λ m ≤
      (1 + Infra.Ingredients.supergeoConstant β) * epsilon β Λ (m - 1) ^ q β := by
  have hA := Scales.supergeoConstant_nonneg hβ hβ'
  have hscale := (Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ (m := m - 1) (by omega)).2
  rw [show m - 1 + 1 = m by omega] at hscale
  refine hscale.trans (mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (Scales.eps_pos hβ hβ' hΛ).le _))
  exact add_le_add (le_refl 1) (mul_le_of_le_one_right hA (Scales.eps_le_one hβ hβ' hΛ))

/-- `ε_m^{β-γ} ≤ (1+A)^{β-γ} ε_{m-1}^{β+γ}`. -/
theorem Scales.length_power_pred (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {m : ℕ} (hm : 2 ≤ m) :
    epsilon β Λ m ^ (β - gamma β) ≤
      (1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) *
        epsilon β Λ (m - 1) ^ (β + gamma β) := by
  have hp : 0 ≤ β - gamma β := sub_nonneg.mpr (Scales.gamma_lt_beta hβ hβ').le
  have hA := Scales.supergeoConstant_nonneg hβ hβ'
  have hbal := q_gamma_balance hβ hβ'
  have heprev := Scales.eps_pos hβ hβ' hΛ (m := m - 1)
  calc
    _ ≤ ((1 + Infra.Ingredients.supergeoConstant β) * epsilon β Λ (m - 1) ^ q β) ^
          (β - gamma β) :=
        Real.rpow_le_rpow (Scales.eps_pos hβ hβ' hΛ).le (Scales.eps_le_const_mul_pred_pow hβ hβ'
            hΛ hm) hp
    _ = _ := by
      rw [Real.mul_rpow (by linarith only [hA]) (Real.rpow_nonneg heprev.le _),
        ← Real.rpow_mul heprev.le, hbal]

end Elementary

section Core

variable {β : ℝ}

/-- The explicit scale constant of `left_to_show_scales`, depending only on `β` and the
`l_recurse` constants `c < C`. -/
def Scales.scalesK (β c C : ℝ) : ℝ :=
  1 + C + (1 / min c (1 / 2)) * ((1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) / c) +
    1 / min c (1 / 2) + kappaPrimeEndpointExpratConstant β +
      (1 + Infra.Ingredients.supergeoConstant β)

theorem Scales.kappaPrimeEndpointExpratConstant_nonneg (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 ≤ kappaPrimeEndpointExpratConstant β := by
  have hA := Scales.supergeoConstant_nonneg hβ hβ'
  unfold kappaPrimeEndpointExpratConstant
  positivity

theorem Scales.scalesK_ge_one (hβ : 1 < β) (hβ' : β < 4 / 3) {c C : ℝ} (hc : 0 < c)
    (hcC : c < C) : 1 ≤ Scales.scalesK β c C := by
  have hA := Scales.supergeoConstant_nonneg hβ hβ'
  have hC : 0 < C := hc.trans hcC
  have hE := Scales.kappaPrimeEndpointExpratConstant_nonneg hβ hβ'
  have hc1 : 0 < min c (1 / 2) := lt_min hc (by norm_num)
  unfold Scales.scalesK
  have : 0 ≤ (1 / min c (1 / 2)) *
      ((1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) / c) := by positivity
  have : 0 ≤ 1 / min c (1 / 2) := by positivity
  linarith

variable {Λ : ℕ}

/-- Core estimates at one scale `2 ≤ m ≤ M`, from the diffusivity bounds for `m < M` and the
    one-sided
terminal bounds at `m = M`. -/
theorem Scales.scales_core (I : Ingredients β) {c C : ℝ} (hc : 0 < c) (hcC : c < C)
    {κ : ℝ} (hκ : 0 < κ) {M : ℕ} (hM : 1 ≤ M) (hperm : κ ∈ permittedInterval β I.Λ M)
    (hA5 : ∀ m : ℕ, 1 ≤ m → m < M →
      c * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)) ≤ I.kappaAt κ m (M - m) ∧
      I.kappaAt κ m (M - m) ≤ C * (a β I.Λ m * epsilon β I.Λ m ^ (2 + gamma β)))
    (hA5' : ∀ m : ℕ, 2 ≤ m → m < M →
      epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m) ≤
        C * epsilon β I.Λ (m - 1) ^ (4 * delta β))
    {m : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M) :
    0 < I.kappaSeq κ M m ∧
    I.kappaSeq κ M m ≤ I.kappaSeq κ M (m - 1) ∧
    I.kappaSeq κ M (m - 1) ≤ Scales.scalesK β c C ∧
    a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m ≤
      Scales.scalesK β c C * I.kappaSeq κ M (m - 1) ∧
    epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) ≤
      Scales.scalesK β c C * epsilon β I.Λ (m - 1) ^ (2 * delta β) ∧
    a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m ≤
      Scales.scalesK β c C * epsilon β I.Λ m ^ (-gamma β) ∧
    epsilon β I.Λ m ≤ Scales.scalesK β c C * epsilon β I.Λ (m - 1) ^ q β := by
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hΛ := I.two_pow_seven_le
  have hA := Scales.supergeoConstant_nonneg hβ hβ'
  have hC : 0 < C := hc.trans hcC
  have hE := Scales.kappaPrimeEndpointExpratConstant_nonneg hβ hβ'
  have hc1 : 0 < min c (1 / 2) := lt_min hc (by norm_num)
  have hγ := Infra.Ingredients.gamma_pos hβ hβ'
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hpow0 : 0 ≤ (1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) :=
    Real.rpow_nonneg (by linarith only [hA]) _
  -- the individual constants are nonnegative and bounded by `scalesK`
  have hT1 : 0 ≤ (1 / min c (1 / 2)) *
      ((1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) / c) := by positivity
  have hT2 : 0 ≤ 1 / min c (1 / 2) := by positivity
  have hKC : C ≤ Scales.scalesK β c C := by unfold Scales.scalesK; linarith
  have hKT1 : (1 / min c (1 / 2)) *
      ((1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) / c) ≤ Scales.scalesK β c C := by
    unfold Scales.scalesK; linarith
  have hKT2 : 1 / min c (1 / 2) ≤ Scales.scalesK β c C := by unfold Scales.scalesK; linarith
  have hKE : kappaPrimeEndpointExpratConstant β ≤ Scales.scalesK β c C := by
    unfold Scales.scalesK; linarith
  have hKS : 1 + Infra.Ingredients.supergeoConstant β ≤ Scales.scalesK β c C := by
    unfold Scales.scalesK; linarith
  have hK1 : 1 ≤ Scales.scalesK β c C := Scales.scalesK_ge_one hβ hβ' hc hcC
  have heps : ∀ n : ℕ, 0 < epsilon β I.Λ n := fun n => Scales.eps_pos hβ hβ' hΛ
  have hε1 : ∀ n : ℕ, epsilon β I.Λ n ≤ 1 := fun n => Scales.eps_le_one hβ hβ' hΛ
  have hpos : ∀ n, 0 < I.kappaSeq κ M n := fun n => kappaAt_pos I hκ n (M - n)
  -- lower bound for all scales `1 ≤ n ≤ M`
  have top := l_recurse_top hβ hβ' hΛ hκ hperm hM
  have hlowc : ∀ n : ℕ, 1 ≤ n → n < M →
      c * epsilon β I.Λ n ^ (β + gamma β) ≤ I.kappaSeq κ M n := by
    intro n hn hlt
    have h := (hA5 n hn hlt).1
    rw [Scales.a_mul_rpow_eq (heps n)] at h
    exact h
  have hlow : ∀ n : ℕ, 1 ≤ n → n ≤ M →
      min c (1 / 2) * epsilon β I.Λ n ^ (β + gamma β) ≤ I.kappaSeq κ M n := by
    intro n hn hnM
    have hen := heps n
    have hrp : 0 < epsilon β I.Λ n ^ (β + gamma β) := Real.rpow_pos_of_pos hen _
    rcases Nat.lt_or_ge n M with hlt | hge
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hrp.le) (hlowc n hn hlt)
    · obtain rfl : n = M := le_antisymm hnM hge
      have h := top.1
      have hk : I.kappaSeq κ n n = κ := by simp [Ingredients.kappaSeq, Ingredients.kappaAt]
      rw [hk]
      rw [mul_assoc, Scales.a_mul_rpow_eq hen] at h
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hrp.le) h
  -- upper bound for `1 ≤ n < M`
  have hup : ∀ n : ℕ, 1 ≤ n → n < M → I.kappaSeq κ M n ≤ C := by
    intro n hn hlt
    have hen := heps n
    have h := (hA5 n hn hlt).2
    rw [Scales.a_mul_rpow_eq hen] at h
    have hb : epsilon β I.Λ n ^ (β + gamma β) ≤ 1 :=
      Real.rpow_le_one hen.le (hε1 n) (by linarith)
    exact le_trans h (mul_le_of_le_one_right hC.le hb)
  have hpredpos := hpos (m - 1)
  have hpredM : m - 1 < M := by omega
  have hpredge : 1 ≤ m - 1 := by omega
  have hen := heps m
  have hem1 := heps (m - 1)
  have hκm := hpos m
  have hlow_m := hlow m (by omega) hmM
  have hlow_p := hlowc (m - 1) hpredge hpredM
  have hrp : 0 < epsilon β I.Λ m ^ (β + gamma β) := Real.rpow_pos_of_pos hen _
  have hrp1 : 0 < epsilon β I.Λ (m - 1) ^ (β + gamma β) := Real.rpow_pos_of_pos hem1 _
  refine ⟨hκm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- κ_m ≤ κ_{m-1}
    have h := khomScalar_ge_input I (m := m) (by omega) (I.kappaSeq κ M m) hκm
    rw [← I.kappaSeq_pred κ (by omega) hmM] at h
    exact h
  · exact (hup (m - 1) hpredge hpredM).trans hKC
  · -- a² ε⁴ / κ_m ≤ K κ_{m-1}
    have h1 : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m ≤
        a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 /
          (min c (1 / 2) * epsilon β I.Λ m ^ (β + gamma β)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hc1 hrp) hlow_m
    have h2 : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 /
          (min c (1 / 2) * epsilon β I.Λ m ^ (β + gamma β)) =
        (1 / min c (1 / 2)) * epsilon β I.Λ m ^ (β - gamma β) := by
      unfold a
      exact Scales.amplitude_div_scale hen hc1
    have hsPrev : epsilon β I.Λ (m - 1) ^ (β + gamma β) ≤
        I.kappaSeq κ M (m - 1) / c :=
      (le_div_iff₀ hc).2 (by simpa [mul_comm] using hlow_p)
    have h3 := Scales.length_power_pred hβ hβ' hΛ hm
    have h4 : (1 / min c (1 / 2)) * epsilon β I.Λ m ^ (β - gamma β) ≤
        ((1 / min c (1 / 2)) * ((1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) / c)) *
          I.kappaSeq κ M (m - 1) := by
      calc
        _ ≤ (1 / min c (1 / 2)) * ((1 + Infra.Ingredients.supergeoConstant β) ^ (β - gamma β) *
            (I.kappaSeq κ M (m - 1) / c)) :=
          mul_le_mul_of_nonneg_left
            (h3.trans (mul_le_mul_of_nonneg_left hsPrev hpow0)) hT2
        _ = _ := by ring
    exact (h1.trans_eq h2).trans (h4.trans (mul_le_mul_of_nonneg_right hKT1 hpredpos.le))
  · -- ε² / (κ_m τ_m) ≤ K ε_{m-1}^{2δ}
    have hexp : epsilon β I.Λ (m - 1) ^ (4 * delta β) ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
      Real.rpow_le_rpow_of_exponent_ge hem1 (hε1 _) (by linarith only [hδ])
    have hpw : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) := Real.rpow_nonneg hem1.le _
    rcases Nat.lt_or_ge m M with hlt | hge
    · have h := hA5' m hm hlt
      exact h.trans ((mul_le_mul_of_nonneg_left hexp hC.le).trans
        (mul_le_mul_of_nonneg_right hKC hpw))
    · obtain rfl : m = M := le_antisymm hmM hge
      have h := top.2
      have hk : I.kappaSeq κ m m = κ := by simp [Ingredients.kappaSeq, Ingredients.kappaAt]
      rw [hk]
      exact h.trans (mul_le_mul_of_nonneg_right hKE hpw)
  · -- a ε² / κ_m ≤ K ε^{-γ}
    have h1 : a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m ≤
        a β I.Λ m * epsilon β I.Λ m ^ 2 /
          (min c (1 / 2) * epsilon β I.Λ m ^ (β + gamma β)) :=
      div_le_div_of_nonneg_left (by unfold a; positivity) (mul_pos hc1 hrp) hlow_m
    have h2 : a β I.Λ m * epsilon β I.Λ m ^ 2 /
          (min c (1 / 2) * epsilon β I.Λ m ^ (β + gamma β)) =
        (1 / min c (1 / 2)) * epsilon β I.Λ m ^ (-gamma β) := by
      rw [Scales.a_mul_sq_eq hen]
      have : epsilon β I.Λ m ^ (-gamma β) =
          epsilon β I.Λ m ^ β / epsilon β I.Λ m ^ (β + gamma β) := by
        rw [← Real.rpow_sub hen]
        congr 1
        ring
      rw [this]
      field_simp
    have hpw : 0 ≤ epsilon β I.Λ m ^ (-gamma β) := Real.rpow_nonneg hen.le _
    exact (h1.trans_eq h2).trans (mul_le_mul_of_nonneg_right hKT2 hpw)
  · -- ε_m ≤ K ε_{m-1}^q
    exact (Scales.eps_le_const_mul_pred_pow hβ hβ' hΛ hm).trans
      (mul_le_mul_of_nonneg_right hKS (Real.rpow_nonneg hem1.le _))

/-- Scale package (e.kappam, e.expqunt, e.corrm, s.indy#flux-size) for 2 ≤ m ≤ M, with the
one-sided handling at m = M. -/
theorem left_to_show_scales (β C₀ : ℝ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
    ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
    ∀ m : ℕ, 2 ≤ m → m ≤ M →
      0 < I.kappaSeq κ M m ∧
      I.kappaSeq κ M m ≤ I.kappaSeq κ M (m - 1) ∧
      I.kappaSeq κ M (m - 1) ≤ K ∧
      a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaSeq κ M m ≤ K * I.kappaSeq κ M (m - 1) ∧
      epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) ≤
        K * epsilon β I.Λ (m - 1) ^ (2 * delta β) ∧
      a β I.Λ m * epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m ≤ K * epsilon β I.Λ m ^ (-gamma β) ∧
      epsilon β I.Λ m ≤ K * epsilon β I.Λ (m - 1) ^ q β := by
  obtain ⟨c, C, hc, hcC, hL⟩ := l_recurse β C₀
  by_cases hb : 1 < β ∧ β < 4 / 3
  · refine ⟨Scales.scalesK β c C, Scales.scalesK_ge_one hb.1 hb.2 hc hcC, ?_⟩
    intro I hz hx hh κ hκp M hM hperm m hm hmM
    have hκ : 0 < κ := by
      have hlow := (Set.mem_Icc.mp hperm).1
      have hpos : 0 < (1 / 2 : ℝ) * epsilon β I.Λ M ^ (2 * β / (q β + 1)) :=
        mul_pos (by norm_num) (Real.rpow_pos_of_pos (Scales.eps_pos hb.1 hb.2 I.two_pow_seven_le) _)
      exact lt_of_lt_of_le hpos hlow
    obtain ⟨h1, h2⟩ := hL I hz hx hh κ hκp M hM hperm
    exact Scales.scales_core I hc hcC hκ hM hperm h1 (fun n hn hlt => (h2 n hn hlt).2) hm hmM
  · exact ⟨1, le_rfl, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb⟩

end Core

section Smallness

variable {β : ℝ} {Λ : ℕ}

/-- ε_{m-1} is small for Λ large (m ≥ 2). -/
theorem epsilon_le_inv_Lambda {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {m : ℕ} (hm : 1 ≤ m) : epsilon β Λ m ≤ (Λ : ℝ)⁻¹ := by
  have hε := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ (m := m)
  have hΛone : (1 : ℝ) ≤ (Λ : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7) hΛ)
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp : -(m : ℝ) ≤ (-1 : ℝ) := by linarith
  have hpow : (Λ : ℝ) ^ (-(m : ℝ)) ≤ (Λ : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hΛone hexp
  rw [Real.rpow_neg_one] at hpow
  exact hε.trans hpow

theorem Scales.eps_le_inv_128 (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ}
    (hm : 1 ≤ m) : epsilon β Λ m ≤ 1 / 128 := by
  have h := epsilon_le_inv_Lambda hβ hβ' hΛ hm
  have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have : (Λ : ℝ)⁻¹ ≤ 1 / 128 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hΛ128
  exact h.trans this

/-- Lower supergeometric bound (from epsilon_supergeo, using ε_{m-1} ≤ 1/128). -/
theorem epsilon_pred_pow_q_div_two_le {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} (hm : 2 ≤ m) :
    epsilon β Λ (m - 1) ^ q β / 2 ≤ epsilon β Λ m := by
  have hscale := (Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ (m := m - 1) (by omega)).1
  rw [show m - 1 + 1 = m by omega] at hscale
  have hsmall := Scales.eps_le_inv_128 hβ hβ' hΛ (m := m - 1) (by omega)
  have hpow : 0 ≤ epsilon β Λ (m - 1) ^ q β := Real.rpow_nonneg (Scales.eps_pos hβ hβ' hΛ).le _
  have hfac : 1 / 2 ≤ 1 - 10 * epsilon β Λ (m - 1) := by linarith only [hsmall]
  calc
    epsilon β Λ (m - 1) ^ q β / 2 = (1 / 2) * epsilon β Λ (m - 1) ^ q β := by ring
    _ ≤ (1 - 10 * epsilon β Λ (m - 1)) * epsilon β Λ (m - 1) ^ q β :=
      mul_le_mul_of_nonneg_right hfac hpow
    _ ≤ epsilon β Λ m := hscale

/-- e.condition for κ = κ_m once Λ is large (needed by l.flux.to.energy). -/
theorem left_to_show_condition (β C₀ : ℝ) : ∃ Λ₀ : ℝ,
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₀ ≤ (I.Λ : ℝ) →
    ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
    ∀ m : ℕ, 2 ≤ m → m ≤ M →
      epsilon β I.Λ m ^ 2 ≤ I.kappaSeq κ M m * tau β I.Λ m / 2 := by
  obtain ⟨K, hK1, hK⟩ := left_to_show_scales β C₀
  by_cases hb : 1 < β ∧ β < 4 / 3
  · have hδ := Infra.Ingredients.delta_pos hb.1 hb.2
    refine ⟨max 128 ((2 * K) ^ (1 / (2 * delta β))), ?_⟩
    intro I hz hx hh hΛ₀ κ hκp M hM hperm m hm hmM
    have hΛ128 : (128 : ℝ) ≤ (I.Λ : ℝ) := le_trans (le_max_left _ _) hΛ₀
    have hΛ : 2 ^ 7 ≤ I.Λ := by exact_mod_cast hΛ128
    have hΛbig : (2 * K) ^ (1 / (2 * delta β)) ≤ (I.Λ : ℝ) := le_trans (le_max_right _ _) hΛ₀
    obtain ⟨hκm, -, -, -, hexp, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
    have hτ : 0 < tau β I.Λ m := Infra.Ingredients.tau_pos hb.1 hb.2 hΛ
    have hΛpos : (0 : ℝ) < I.Λ := by linarith only [hΛ128]
    -- K ε_{m-1}^{2δ} ≤ 1/2
    have hεΛ : epsilon β I.Λ (m - 1) ≤ (I.Λ : ℝ)⁻¹ :=
      epsilon_le_inv_Lambda hb.1 hb.2 hΛ (by omega)
    have hpw : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ ((I.Λ : ℝ)⁻¹) ^ (2 * delta β) :=
      Real.rpow_le_rpow (Scales.eps_pos hb.1 hb.2 hΛ).le hεΛ (by positivity)
    have hΛδ : 2 * K ≤ (I.Λ : ℝ) ^ (2 * delta β) := by
      have h2K : 0 ≤ 2 * K := by linarith only [hK1]
      have := Real.rpow_le_rpow (Real.rpow_nonneg h2K _) hΛbig (by positivity : 0 ≤ 2 * delta β)
      rwa [← Real.rpow_mul h2K, one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one] at this
    have hinv : ((I.Λ : ℝ)⁻¹) ^ (2 * delta β) = ((I.Λ : ℝ) ^ (2 * delta β))⁻¹ :=
      Real.inv_rpow hΛpos.le _
    have hsmall : K * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 / 2 := by
      have hpowpos : 0 < (I.Λ : ℝ) ^ (2 * delta β) := Real.rpow_pos_of_pos hΛpos _
      calc
        K * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ K * ((I.Λ : ℝ) ^ (2 * delta β))⁻¹ := by
          rw [← hinv]
          exact mul_le_mul_of_nonneg_left hpw (by linarith only [hK1])
        _ = K / (I.Λ : ℝ) ^ (2 * delta β) := by rw [div_eq_mul_inv]
        _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hpowpos (by norm_num)]
          linarith only [hΛδ]
    have hratio : epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) ≤ 1 / 2 :=
      hexp.trans hsmall
    have hden : 0 < I.kappaSeq κ M m * tau β I.Λ m := mul_pos hκm hτ
    rw [div_le_iff₀ hden] at hratio
    linarith only [hratio]
  · exact ⟨0, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb⟩

end Smallness

section TimeScales

variable {β : ℝ} {Λ : ℕ}

/-- `τ''_m / τ'_m = 4 ⌈ε_{m-1}^{-δ}⌉ + 1`. -/
theorem tauPP_div_tauP_eq (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (m : ℕ) :
    tauPP β Λ m / tauP β Λ m = 4 * (⌈epsilon β Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) + 1 := by
  have hPP : 0 < tauPP β Λ m := Infra.Cutoff.tauPP_pos hβ hβ' hΛ
  have hF : 0 < 4 * (⌈epsilon β Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) + 1 := by positivity
  unfold tauP
  field_simp

/-- Elementary ceiling estimate: `4⌈x⌉ + 1 ≤ 6x` once `x ≥ 5/2`. -/
theorem Scales.four_ceil_add_one_le {x : ℝ} (hx : 5 / 2 ≤ x) :
    4 * (⌈x⌉₊ : ℝ) + 1 ≤ 6 * x := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith only [hx])
  linarith only [h, hx]

/-- 1 is an integer number of periods 4τ''_m of JHat_m. -/
theorem four_tauPP_reciprocal_nat {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) * (4 * tauPP β Λ m) = 1 := by
  obtain ⟨n, hn⟩ := Infra.Ingredients.tauPP_reciprocal_multiple_four hβ hβ' hΛ hm
  have hPP : 0 < tauPP β Λ m := Infra.Cutoff.tauPP_pos hβ hβ' hΛ
  have hn' : 1 / tauPP β Λ m = 4 * (n : ℝ) := by rw [hn]; push_cast; ring
  refine ⟨n, ?_, ?_⟩
  · have hpos : 0 < 1 / tauPP β Λ m := by positivity
    rw [hn'] at hpos
    have : (0 : ℝ) < n := by linarith only [hpos]
    exact_mod_cast this
  · have : (1 : ℝ) = (4 * (n : ℝ)) * tauPP β Λ m := by
      rw [← hn']; field_simp
    linarith only [this]

/-- 4τ''_m is a multiple of 4τ_m (period of 𝐣_{m,n}). -/
theorem four_tauPP_eq_nat_mul_four_tau {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ n : ℕ, 4 * tauPP β Λ m = (n : ℝ) * (4 * tau β Λ m) := by
  obtain ⟨hratio, -⟩ := Infra.Ingredients.tauPP_ratio_and_tau_reciprocal hβ hβ' hΛ hm
  have hτ : 0 < tau β Λ m := Infra.Ingredients.tau_pos hβ hβ' hΛ
  refine ⟨Infra.Ingredients.tauCellCount β Λ m, ?_⟩
  rw [← hratio]
  field_simp

end TimeScales

section Analytic

/-- Exponent gap of the ergodic frequency: q - 1 - γ/2 = (q-1)(1 - β/(2(q+1))) > 0. -/
theorem ergodic_gap_pos {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 0 < q β - 1 - gamma β / 2 := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hden : 0 < 2 * (q β + 1) := by linarith only [hq]
  have hkey : q β - 1 - gamma β / 2 = (q β - 1) * (2 * (q β + 1) - β) / (2 * (q β + 1)) := by
    unfold gamma
    field_simp
  rw [hkey]
  apply div_pos _ hden
  exact mul_pos (by linarith only [hq]) (by linarith only [hq, hβ'])

/-- e^{-y} ≤ n!/yⁿ. -/
theorem exp_neg_le_factorial_div_pow {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.exp (-y) ≤ (n.factorial : ℝ) / y ^ n := by
  have h := Real.pow_div_factorial_le_exp y hy.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hyn : 0 < y ^ n := pow_pos hy n
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) hyn]
  rw [div_le_iff₀ hf] at h
  linarith only [h]

/-- Super-polynomial smallness: for p > 0, the factor e^{-ε^{-p}/K} beats any power. -/
theorem exp_neg_rpow_le_rpow {p K P : ℝ} (hp : 0 < p) (hK : 0 < K) (_hP : 0 ≤ P) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Real.exp (-(ε ^ (-p) / K)) ≤ K' * ε ^ P := by
  set n : ℕ := ⌈P / p⌉₊ with hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  refine ⟨n.factorial * K ^ n, by positivity, ?_⟩
  intro ε hε hε1
  have hy : 0 < ε ^ (-p) / K := div_pos (Real.rpow_pos_of_pos hε _) hK
  refine (exp_neg_le_factorial_div_pow hy n).trans ?_
  have hpn : (ε ^ (-p)) ^ n = (ε ^ (p * n))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, show -p * (n : ℝ) = -(p * n) by ring,
      Real.rpow_neg hε.le]
  have hexp : P ≤ p * n := by
    have h := Nat.le_ceil (P / p)
    rw [← hn] at h
    rwa [div_le_iff₀ hp, mul_comm] at h
  have hmono : ε ^ (p * n) ≤ ε ^ P := Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp
  have hεpn : 0 < ε ^ (p * n) := Real.rpow_pos_of_pos hε _
  calc
    (n.factorial : ℝ) / (ε ^ (-p) / K) ^ n
        = n.factorial * K ^ n * ε ^ (p * n) := by
      rw [div_pow, hpn]
      field_simp
    _ ≤ n.factorial * K ^ n * ε ^ P :=
      mul_le_mul_of_nonneg_left hmono (by positivity)

/-- Trading (C x)^N for x when 0 ≤ x ≤ 1 and N ≥ 1 (used for the e.JJhat remainder). -/
theorem mul_pow_le_pow_mul_self {C x : ℝ} {N : ℕ} (hC : 0 ≤ C) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hN : 1 ≤ N) : (C * x) ^ N ≤ C ^ N * x := by
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC N)
  calc
    x ^ N ≤ x ^ 1 := pow_le_pow_of_le_one hx0 hx1 hN
    _ = x := pow_one x

end Analytic

end AVenhance.Infra.Section5.LeftToShow

end
