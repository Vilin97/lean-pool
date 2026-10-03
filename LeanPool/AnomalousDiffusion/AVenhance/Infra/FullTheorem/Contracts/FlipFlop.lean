/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.FlipFlopContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.FlipFlop.Top
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LebronStep.KappaBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeqPred

/-! # Proof of the flip-flop statement

`flipFlop_contract β C₀ : FlipFlopContract β C₀`, with `ρ = δ`.  Assembly of
`FlipFlop.top_step` (top level), `FlipFlop.inner_step` (levels `2 ≤ m < M`, with the
    diffusivity-recursion
bounds), and the alternating telescoping `FlipFlop.flipflop_unroll`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem AVenhance.Infra.FullTheorem.FlipFlop

theorem kappaSeq_pred_succ {β : ℝ} (I : Ingredients β) (κ : ℝ) {M n : ℕ} (hn : n + 1 ≤ M) :
    I.kappaSeq κ M n = I.KhomScalar (I.kappaSeq κ M (n + 1)) (n + 1) := by
  have := I.kappaSeq_pred κ (M := M) (m := n + 1) (by omega) hn
  simpa using this

theorem kappaSeq_top_pred {β : ℝ} (I : Ingredients β) (κ : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    I.kappaSeq κ M (M - 1) = I.KhomScalar κ M := by
  have := I.kappaSeq_pred κ (M := M) (m := M) hM le_rfl
  rw [this]
  simp [Ingredients.kappaSeq, Ingredients.kappaAt]

theorem a_mul_eps_pow {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (j : ℕ) :
    a β Λ j * epsilon β Λ j ^ (2 + gamma β) = epsilon β Λ j ^ (β + gamma β) := by
  have hεpos : 0 < epsilon β Λ j := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  unfold a
  rw [← Real.rpow_add hεpos]
  congr 1
  ring

/-- **Flip-flop statement.** -/
theorem flipFlop_contract (β C₀ : ℝ) : FlipFlopContract β C₀ := by
  by_cases hβr : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨1, 0, 0, one_pos, fun I => ?_⟩
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hβr
  obtain ⟨hβ, hβ'⟩ := hβr
  obtain ⟨c, C, hc, hcC, hl⟩ := AVenhance.l_recurse β C₀
  have hC : 0 ≤ C := (hc.trans hcC).le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ hβ'
  have hδ1 := Infra.Ingredients.delta_le_one_sixteenth hβ hβ'
  have hp := beta_sub_gamma_pos hβ hβ'
  have hK10 := ksConst_ge_ten β
  set Ks := ksConst β with hKs
  set Ci := innerC β C₀ C with hCi
  set Kfac := 2 * |Ci| + 4 with hKfac
  have hKfac4 : 4 ≤ Kfac := by have := abs_nonneg Ci; linarith
  set B := 2 * |Ci| + 2 * (β - gamma β) * Ks + 4 with hB
  have hB0 : 0 ≤ B := by
    have := abs_nonneg Ci
    have : 0 ≤ 2 * (β - gamma β) * Ks := by positivity
    linarith
  refine ⟨delta β, B * 2, max (Kfac ^ (1 / delta β)) (2 * Ks), hδ, ?_⟩
  intro I hz hx hh hΛ1 t ht M hM m hm1 hmM
  have hΛ7 := I.two_pow_seven_le
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hz
  have hCi0 : 0 ≤ Ci := innerC_nonneg hC hC₀
  have habsCi : |Ci| = Ci := abs_of_nonneg hCi0
  have hΛpos : (0 : ℝ) < I.Λ := by
    have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast hΛ7
    linarith
  have hΛa : Kfac ^ (1 / delta β) ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ1
  have hΛb : 2 * Ks ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ1
  have hKδ : Kfac * ((I.Λ : ℝ)⁻¹) ^ delta β ≤ 1 :=
    const_mul_inv_rpow_le_one (by linarith) hδ hΛpos hΛa
  -- smallness of the scales
  have hsmδ : ∀ j : ℕ, 1 ≤ j → Kfac * epsilon β I.Λ j ^ delta β ≤ 1 := fun j hj =>
    (mul_le_mul_of_nonneg_left (epsilon_rpow_le_inv_rpow hβ hβ' hΛ7 hj hδ.le)
      (by linarith)).trans hKδ
  have hsmε : ∀ j : ℕ, 1 ≤ j → 2 * Ks * epsilon β I.Λ j ≤ 1 := fun j hj => by
    have h1 := epsilon_rpow_le_inv hβ hβ' hΛ7 hj (s := 1) le_rfl
    rw [Real.rpow_one] at h1
    calc 2 * Ks * epsilon β I.Λ j ≤ 2 * Ks * (I.Λ : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ (I.Λ : ℝ) * (I.Λ : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hΛb (by positivity)
      _ = 1 := by field_simp
  -- the chain top
  set x := epsilon β I.Λ M ^ (2 * β / (q β + 1)) with hx_def
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ hβ' hΛ7).le _
  have hexp : 2 * β / (q β + 1) = β - gamma β := by
    have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
    unfold gamma
    field_simp [ne_of_gt (by linarith : 0 < q β + 1)]
    ring
  have hxpos : 0 < x := Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos hβ hβ' hΛ7) _
  have ht12 : 1 / 2 ≤ t ∧ 0 < t := by rcases ht with rfl | rfl <;> norm_num
  have hκM : t * x ∈ permittedInterval β I.Λ M := by
    unfold permittedInterval
    rw [← hx_def]
    rcases ht with rfl | rfl <;> constructor <;> linarith
  have hκ : t * x ∈ permissibleSet β I.Λ := Set.mem_iUnion₂.2 ⟨M, by omega, hκM⟩
  have hlr := hl I hz hx hh (t * x) hκ M (by omega) hκM
  -- the log sequence
  set u : ℕ → ℝ := fun j => Real.log (I.kappaSeq (t * x) M j /
    (Real.sqrt (9 / 80) * epsilon β I.Λ j ^ (β + gamma β))) with hu
  set e : ℕ → ℝ := fun j => epsilon β I.Λ j ^ delta β with he_def
  have hM1 : M - 1 + 1 = M := by omega
  have htail : ∀ m n : ℕ, ∑ k ∈ Finset.range n, e (m + k) ≤ 2 * e m := by
    intro m n
    have hs := Infra.Construction.epsilon_rpow_sum_bound (β := β) (s := delta β) I hδ m n
    refine hs.trans ?_
    have hq4 : (I.Λ : ℝ) ^ (-delta β) ≤ 1 / 4 := by
      rw [Real.rpow_neg hΛpos.le, ← Real.inv_rpow hΛpos.le]
      have : (4 : ℝ) * ((I.Λ : ℝ)⁻¹) ^ delta β ≤ 1 :=
        (mul_le_mul_of_nonneg_right hKfac4 (by positivity)).trans hKδ
      linarith
    have hpos : 0 < 1 - (I.Λ : ℝ) ^ (-delta β) := by linarith
    rw [div_le_iff₀ hpos]
    have : 0 ≤ epsilon β I.Λ m ^ delta β :=
      Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ hβ' hΛ7).le _
    nlinarith
  have htop : |u (M - 1) - Real.log (t * Real.sqrt (80 / 9))| ≤ B * e (M - 1) := by
    have hs1 := hsmδ (M - 1) (by omega)
    have hs2 := mul_le_mul_of_nonneg_right hKfac4 (Real.rpow_nonneg
      (Infra.Cutoff.epsilon_pos (β := β) (Λ := I.Λ) (m := M - 1) hβ hβ' hΛ7).le (delta β))
    have h := top_step I (m := M - 1) (by omega) ht12.1 (by linarith)
      (hsmε (M - 1) (by omega))
    have hx' : x = epsilon β I.Λ M ^ (β - gamma β) := by rw [hx_def, hexp]
    rw [hM1, ← hx'] at h
    have hK := kappaSeq_top_pred I (t * x) (M := M) (by omega)
    simp only [hu, he_def]
    rw [hK]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
      (Infra.Cutoff.epsilon_pos (β := β) (Λ := I.Λ) (m := M - 1) hβ hβ' hΛ7).le _))
    rw [hB, habsCi, hKs]; linarith
  have hstep : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ M - 1 → |u n + u (n + 1)| ≤ B * e n := by
    intro n hn hnM
    obtain ⟨hk1, hk2⟩ := hlr.1 (n + 1) (by omega) (by omega)
    obtain ⟨hq1, hq2⟩ := hlr.2 (n + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hq2
    have hprod := a_mul_eps_pow hβ hβ' hΛ7 (n + 1)
    rw [hprod] at hk1 hk2
    have hE1 := Real.rpow_pos_of_pos
        (Infra.Cutoff.epsilon_pos (β := β) (Λ := I.Λ) (m := n + 1) hβ hβ' hΛ7) (β + gamma β)
    have hkpos : 0 < I.kappaSeq (t * x) M (n + 1) :=
      lt_of_lt_of_le (mul_pos hc hE1) hk1
    have hen : 0 ≤ epsilon β I.Λ n ^ delta β :=
      Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ hβ' hΛ7).le _
    have h := inner_step (C := C) I hz hh hC (m := n) hn hkpos hk2 hq2
      (by
        have := hsmδ n hn
        have h2 : Ci * epsilon β I.Λ n ^ delta β ≤ |Ci| * epsilon β I.Λ n ^ delta β :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hen
        have h3 : (2 * |Ci| + 4) * epsilon β I.Λ n ^ delta β ≤ 1 := this
        nlinarith)
      (hsmε n hn)
    have hK := kappaSeq_pred_succ I (t * x) (M := M) (n := n) (by omega)
    simp only [hu, he_def]
    rw [hK]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hen)
    rw [hB, habsCi, hKs, hCi]; rw [hCi] at hCi0; linarith
  have key := flipflop_unroll u e (Real.log (t * Real.sqrt (80 / 9))) B 2 M hB0 htail htop hstep
    m hm1 hmM
  simpa only [hu, he_def, mul_assoc] using key

end AVenhance.Infra.FullTheorem.Contracts
