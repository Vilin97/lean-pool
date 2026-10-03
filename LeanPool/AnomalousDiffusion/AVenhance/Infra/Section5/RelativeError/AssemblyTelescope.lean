/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesLMNSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesForcingSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesExist
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Statements

/-! # the telescoping chain from the later start to the terminal level("Multiplying just the
lower inequalities in (9),
or using `∏(1-e_j) ≥ 1 - ∑ e_j`, gives `a_M ≥ a_{j*}/2`").  Uses only conjunct (ii) of the
Step-down body `Integration.IndyStepDownStatement`, the later scale condition `later_scale_of_le`,
    and
the construction of the `T` iterates `exists_TIterates`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance Homogenization

/-- The coarse diffusivities `κ_k` are positive for `j ≤ k ≤ M` once `1 ≤ j < M`. -/
theorem kappaSeq_pos_of_ge {β C₀ : ℝ} (hβ1 : 1 < β) (hb : β < 4 / 3) (I : Ingredients β)
    (hz : I.Czeta ≤ C₀) (hx : I.Cxi ≤ C₀) (hh : I.Chat ≤ C₀) {κ : ℝ}
    (hκp : κ ∈ permissibleSet β I.Λ) {M : ℕ} (hM : 1 ≤ M) (hperm : κ ∈ permittedInterval β I.Λ M)
    {j k : ℕ} (hj1 : 1 ≤ j) (hjM : j < M) (hjk : j ≤ k) (hkM : k ≤ M) :
    0 < I.kappaSeq κ M k := by
  obtain ⟨K, -, hK⟩ := Infra.Section5.LeftToShow.left_to_show_scales β C₀
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk1 : k = 1 := by omega
    subst hk1
    obtain ⟨c₀, C, hc₀, -, hL⟩ := l_recurse β C₀
    obtain ⟨hA5, -⟩ := hL I hz hx hh κ hκp M hM hperm
    have h := (hA5 1 le_rfl (by omega)).1
    have hε := Infra.Cutoff.epsilon_pos hβ1 hb I.two_pow_seven_le (m := 1)
    rw [a_mul_eps_pow_eq hε] at h
    exact lt_of_lt_of_le (mul_pos hc₀ (Real.rpow_pos_of_pos hε _)) h
  · exact (hK I hz hx hh κ hκp M hM hperm k hk hkM).1

/-- Item 13, chain step: below a Λ-threshold, for a classical solution at every level `j* ≤ k ≤ M`
(`j* = laterStart β Λ R < M`), the dissipation at the later start is at most twice the terminal
dissipation. -/
theorem chain_lower_bound (β C₀ : ℝ) (hβ : 6 / 5 ≤ β)
    (hA8 : Integration.IndyStepDownStatement β C₀) :
    ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      (∀ j : ℕ, ClassicalSolvable (streamVel (Φ j))) →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R → laterStart β I.Λ R < M →
      ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → IsZ2Periodic g → MeanZeroOn unitCube g →
        IsThetaAnalytic R g →
      ∃ θj θM : ℝ → Vec 2 → ℝ,
        IsClassicalSol (streamVel (Φ (laterStart β I.Λ R)))
          (I.kappaSeq κ M (laterStart β I.Λ R)) (fun _ _ => 0) g θj ∧
        IsClassicalSol (streamVel (Φ M)) κ (fun _ _ => 0) g θM ∧
        I.kappaSeq κ M (laterStart β I.Λ R) * spaceTimeGradNormSq (fun t x => spaceGrad (θj t) x) ≤
          2 * (κ * spaceTimeGradNormSq (fun t x => spaceGrad (θM t) x)) := by
  by_cases hb : β < 4 / 3
  swap
  · exact ⟨0, fun I => absurd I.beta_lt hb⟩
  have hβ1 : 1 < β := by linarith
  obtain ⟨C, hC⟩ := hA8
  obtain ⟨Λ₀, hΛ₀⟩ := exists_lambda_threshold β (max C 1) hβ1 hb (le_max_right _ _)
  refine ⟨Λ₀, ?_⟩
  intro I hz hx hh hΛ Φ hΦ hsolv κ hκp M hM hperm R hR hjM g hg hgp hgm hga
  obtain ⟨h7, hCΛ, hsum⟩ := hΛ₀ I.Λ hΛ
  have hCΛ' : C ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hCΛ
  obtain ⟨⟨hj1, -⟩, -⟩ := laterStart_isLeast hβ1 hb h7 hR
  set j := laterStart β I.Λ R with hj
  have hpos : ∀ k, j ≤ k → k ≤ M → 0 < I.kappaSeq κ M k := fun k h1 h2 =>
    kappaSeq_pos_of_ge hβ1 hb I hz hx hh hκp hM hperm hj1 hjM h1 h2
  have hex : ∀ k : ℕ, ∃ u : ℝ → Vec 2 → ℝ, (j ≤ k → k ≤ M →
      IsClassicalSol (streamVel (Φ k)) (I.kappaSeq κ M k) (fun _ _ => 0) g u) := by
    intro k
    by_cases hk : j ≤ k ∧ k ≤ M
    · obtain ⟨u, hu⟩ := hsolv k _ (hpos k hk.1 hk.2) g hg hgp (fun _ _ => 0)
        contDiffOn_const (fun _ _ _ _ => rfl)
      exact ⟨u, fun _ _ => hu⟩
    · exact ⟨fun _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose θ hθ using hex
  have hκM : I.kappaSeq κ M M = κ := by simp [Ingredients.kappaSeq, Ingredients.kappaAt]
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k, s k = I.kappaSeq κ M k *
      spaceTimeGradNormSq (fun t x => spaceGrad (θ k t) x) := ⟨_, fun _ => rfl⟩
  have hs0 : ∀ k, j ≤ k → k ≤ M → 0 ≤ s k := fun k h1 h2 => by
    rw [hs]; exact mul_nonneg (hpos k h1 h2).le (spaceTimeGradNormSq_nonneg' _)
  have he0 : ∀ k, 0 ≤ max C 1 * epsilon β I.Λ k ^ delta β := fun k =>
    mul_nonneg (by linarith [le_max_right C 1])
      (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ1 hb h7).le _)
  have he1 : ∀ k, 1 ≤ k → max C 1 * epsilon β I.Λ k ^ delta β ≤ 1 := fun k hk => by
    have := hsum k hk 1
    simp only [Finset.sum_range_one, add_zero] at this
    linarith
  have hstep : ∀ k, j ≤ k → k < M →
      (1 - max C 1 * epsilon β I.Λ k ^ delta β) * s k ≤ s (k + 1) := by
    intro k hjk hkM
    obtain ⟨T, hT⟩ := exists_TIterates I hΦ (m := k + 1) (by omega)
      (hpos (k + 1) (by omega) hkM) (hpos k hjk hkM.le) (hsolv k) hg hgp (hθ k hjk hkM.le)
    obtain ⟨hscale, hm0⟩ := later_scale_of_le hβ1 hb h7 hR (m := k + 1) (by omega)
    have h := (hC I hz hx hh hCΛ' Φ hΦ κ hκp M hM hperm R hR g hg hgp hgm hga (k + 1) hm0
      (by omega) (θ (k + 1)) (θ k) T (hθ (k + 1) (by omega) hkM) (hθ k hjk hkM.le) hT).2 hβ hscale
    simp only [Nat.add_sub_cancel] at h
    have hsk := hs0 k hjk hkM.le
    have hεδ : 0 ≤ epsilon β I.Λ k ^ delta β :=
      Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ1 hb h7).le _
    have hl := (abs_le.1 h).1
    have hCC : (max C 1 - C) * (epsilon β I.Λ k ^ delta β * s k) ≥ 0 :=
      mul_nonneg (by linarith [le_max_left C 1]) (mul_nonneg hεδ hsk)
    rw [hs (k + 1), hs k] at *
    nlinarith only [hl, hCC]
  have htel := telescope_lower (s := s) (e := fun k => max C 1 * epsilon β I.Λ k ^ delta β)
    (j := j) (N := M) (hs0 j le_rfl hjM.le) (fun i _ _ => he0 i)
    (fun i hi _ => he1 i (by omega)) hstep (M - j) (by omega)
  have hsumM : ∑ i ∈ Finset.range (M - j), max C 1 * epsilon β I.Λ (j + i) ^ delta β ≤ 1 / 2 := by
    rw [← Finset.mul_sum]
    exact hsum j hj1 (M - j)
  rw [show j + (M - j) = M by omega] at htel
  have hsj := hs0 j le_rfl hjM.le
  have hfin : s j / 2 ≤ s M := by
    have : 1 / 2 * s j ≤ (1 - ∑ i ∈ Finset.range (M - j),
        max C 1 * epsilon β I.Λ (j + i) ^ delta β) * s j :=
      mul_le_mul_of_nonneg_right (by linarith) hsj
    linarith
  have hM' := hθ M hjM.le le_rfl
  rw [hκM] at hM'
  refine ⟨θ j, θ M, hθ j le_rfl hjM.le, hM', ?_⟩
  rw [hs j, hs M, hκM] at hfin
  linarith

end AVenhance.Infra.Section5.RelativeError

end
