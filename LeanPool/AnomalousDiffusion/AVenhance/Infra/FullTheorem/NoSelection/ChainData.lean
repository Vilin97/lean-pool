/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.Steps
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.Chain

/-! # The telescoped classical chain

`chain_data`: for a datum with `mTheta0 R ≤ m₀ + 1`, a chain topped at any `κ ∈ permittedInterval M`
(`m₀ < M`), the classical iterates exist at levels `m₀, …, M` and
`‖θ_M(t) − θ_{m₀}(t)‖ ≤ 2 C₈ ε_{m₀}^δ ‖θ₀‖`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSel

open AVenhance AVenhance.Infra.FullTheorem

/-- `ε_{k+1}^δ ≤ ½ ε_k^δ` for `k ≥ 1` once `Λ` is large. -/
theorem eps_succ_half {β : ℝ} (I : Ingredients β) {s : ℝ} (hs : 0 < s) {k : ℕ} (hk : 1 ≤ k)
    (hg : (1 + Infra.Ingredients.supergeoConstant β) ^ s *
      ((I.Λ : ℝ)⁻¹) ^ ((q β - 1) * s) ≤ 1 / 2) :
    epsilon β I.Λ (k + 1) ^ s ≤ epsilon β I.Λ k ^ s / 2 := by
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ1 hβ2
  have hE : 0 < epsilon β I.Λ k := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hA := Infra.Section5.RelativeError.supergeoConstant_nonneg' hβ1 hβ2
  have h1 := Infra.Section5.RelativeError.epsilon_succ_le hβ1 hβ2 hΛ7 hk
  have h2 : epsilon β I.Λ (k + 1) ^ s ≤ ((1 + Infra.Ingredients.supergeoConstant β) *
      epsilon β I.Λ k ^ q β) ^ s :=
    Real.rpow_le_rpow (Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7).le h1 hs.le
  have h3 : ((1 + Infra.Ingredients.supergeoConstant β) * epsilon β I.Λ k ^ q β) ^ s =
      (1 + Infra.Ingredients.supergeoConstant β) ^ s *
        (epsilon β I.Λ k ^ s * epsilon β I.Λ k ^ ((q β - 1) * s)) := by
    rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hE.le _), ← Real.rpow_mul hE.le,
      ← Real.rpow_add hE]
    congr 3
    ring
  have h4 : epsilon β I.Λ k ^ ((q β - 1) * s) ≤ ((I.Λ : ℝ)⁻¹) ^ ((q β - 1) * s) :=
    epsilon_rpow_le_inv_rpow hβ1 hβ2 hΛ7 hk (mul_nonneg (by linarith) hs.le)
  have h5 : 0 ≤ epsilon β I.Λ k ^ s := Real.rpow_nonneg hE.le _
  have h6 : 0 ≤ (1 + Infra.Ingredients.supergeoConstant β) ^ s :=
    Real.rpow_nonneg (by linarith) _
  calc epsilon β I.Λ (k + 1) ^ s ≤ _ := h2
    _ = _ := h3
    _ ≤ (1 + Infra.Ingredients.supergeoConstant β) ^ s *
        (epsilon β I.Λ k ^ s * ((I.Λ : ℝ)⁻¹) ^ ((q β - 1) * s)) := by gcongr
    _ = ((1 + Infra.Ingredients.supergeoConstant β) ^ s *
        ((I.Λ : ℝ)⁻¹) ^ ((q β - 1) * s)) * epsilon β I.Λ k ^ s := by ring
    _ ≤ 1 / 2 * epsilon β I.Λ k ^ s := mul_le_mul_of_nonneg_right hg h5
    _ = _ := by ring

theorem chain_data (β C₀ : ℝ) :
    ∃ C₈ Λc : ℝ, 0 ≤ C₈ ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λc ≤ (I.Λ : ℝ) → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ κ : ℝ, ∀ M : ℕ, κ ∈ permittedInterval β I.Λ M →
      ∀ m₀ : ℕ, 2 ≤ m₀ → m₀ < M →
      ∀ R : ℝ, 0 < R → ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ →
        MeanZeroOn unitCube θ₀ → IsThetaAnalytic R θ₀ → mTheta0 β I.Λ R ≤ m₀ + 1 →
      (∀ j, m₀ ≤ j → j ≤ M → 0 < I.kappaSeq κ M j) ∧
      ∃ θs : ℕ → ℝ → Vec 2 → ℝ,
        (∀ j, m₀ ≤ j → j ≤ M →
          IsClassicalSol (streamVel (Φ j)) (I.kappaSeq κ M j) (fun _ _ => 0) θ₀ (θs j)) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          Real.sqrt (l2NormSq (fun x => θs M t x - θs m₀ t x)) ≤
            2 * C₈ * epsilon β I.Λ m₀ ^ delta β * Real.sqrt (l2NormSq θ₀) := by
  by_cases hβr : 1 < β ∧ β < 4 / 3
  swap
  · exact ⟨0, 0, le_rfl, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hβr⟩
  obtain ⟨hβ1, hβ2⟩ := hβr
  obtain ⟨c_w, Λ_w, hcw, hW⟩ := kappaSeq_window β C₀
  obtain ⟨C₈, hC₈0, hstep⟩ := step_sup β C₀
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ1 hβ2
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ1 hβ2
  obtain ⟨Λ_g, hΛg⟩ := exists_big ((1 + Infra.Ingredients.supergeoConstant β) ^ delta β) (1 / 2)
    ((q β - 1) * delta β) (mul_pos (by linarith) hδ) (by norm_num)
  refine ⟨C₈, max (max C₈ Λ_w) Λ_g, hC₈0, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ M hκM m₀ hm₀ hm₀M R hR θ₀ hθ₀ hper hmean han hmT
  have hC₈Λ : C₈ ≤ (I.Λ : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hΛ
  have hΛw : Λ_w ≤ (I.Λ : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hΛ
  have hΛg' : Λ_g ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ
  have hM1 : 1 ≤ M := by omega
  have hκ : κ ∈ permissibleSet β I.Λ := Set.mem_iUnion₂.2 ⟨M, hM1, hκM⟩
  have hpos : ∀ j, m₀ ≤ j → j ≤ M → 0 < I.kappaSeq κ M j := by
    intro j h1 h2
    have := (hW I hz hx hh hΛw κ hκ M hM1 hκM j (by omega) h2 j (Or.inr rfl)).1
    exact lt_of_lt_of_le (by
      have := Infra.Cutoff.epsilon_pos hβ1 hβ2 I.two_pow_seven_le (m := j - 1)
      have := Real.rpow_pos_of_pos this (lebronP β)
      positivity) this
  obtain ⟨θs, hθs⟩ := exists_classical_chain hΦ hpos hθ₀ hper
  refine ⟨hpos, θs, hθs, ?_⟩
  intro t ht
  have hsm := telescope_l2 (θs := θs) (n₀ := m₀) (M := M) (t := t)
    (a := fun l => C₈ * epsilon β I.Λ (l - 1) ^ delta β * Real.sqrt (l2NormSq θ₀))
    (fun j h1 h2 => IsClassicalSol.continuous_slice (hθs j h1 h2) ht.1)
    (by
      intro l hl1 hl2
      exact hstep I hz hx hh hC₈Λ Φ hΦ κ hκ M hM1 hκM R hR θ₀ hθ₀ hper hmean han l
        (by omega) hl2 (hpos l (by omega) hl2) (hpos (l - 1) (by omega) (by omega))
        (θs l) (θs (l - 1)) (hθs l (by omega) hl2) (hθs (l - 1) (by omega) (by omega)) t ht)
    M (by omega) le_rfl
  refine hsm.trans ?_
  have hg := hΛg (I.Λ : ℝ) hΛg'
  have hgeo := geom_sum_le (a := fun k => epsilon β I.Λ k ^ delta β) (n₀ := m₀)
    (fun k hk => eps_succ_half I hδ (by omega) hg) M (by omega)
  have hN0 : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hEM : 0 ≤ epsilon β I.Λ M ^ delta β :=
    Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ1 hβ2 I.two_pow_seven_le).le _
  have e : ∑ l ∈ Finset.Ioc m₀ M, C₈ * epsilon β I.Λ (l - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) =
      C₈ * Real.sqrt (l2NormSq θ₀) * ∑ l ∈ Finset.Ioc m₀ M, epsilon β I.Λ (l - 1) ^ delta β := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  calc C₈ * Real.sqrt (l2NormSq θ₀) * ∑ l ∈ Finset.Ioc m₀ M, epsilon β I.Λ (l - 1) ^ delta β
      ≤ C₈ * Real.sqrt (l2NormSq θ₀) * (2 * epsilon β I.Λ m₀ ^ delta β) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC₈0 hN0)
    _ = _ := by ring

end AVenhance.Infra.FullTheorem.NoSel
