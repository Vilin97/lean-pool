/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.LebronStepAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.CaseBig
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.LimitFieldRegular

/-! # Sup-in-time pieces for the no-selection limit

* `tail_sup`: `sup_t ‖θ(t) − θ_M(t)‖ ≤ 2 C_t (1+A)^β ε_M^{a} ‖θ₀‖` for a weak solution `θ` (limit
    drift)
  and the classical solution `θ_M` (drift `Φ_M`) with the same diffusivity;
* `step_sup`: sup form of the step-down estimate (i): `sup_t ‖θ_m − θ_{m-1}‖ ≤ C ε_{m-1}^δ ‖θ₀‖`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem tail_sup {β Ct Bφ : ℝ} (hCt : 0 ≤ Ct) {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {φ : ℝ → Vec 2 → ℝ}
    (htail : ∀ (M : ℕ) (t : ℝ) (x : Vec 2),
      |φ t x - Φ M t x| ≤ Ct * epsilon β I.Λ (M + 1) ^ β)
    (hφ_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hφ_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ t))
    (hφ_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t))
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (streamVel φ t))
    (hdiv : IsDivFree (streamVel φ))
    (hb_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ t x‖ ≤ Bφ)
    {κ : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hκlo : (1 / 2) * epsilon β I.Λ M ^ (β - gamma β) ≤ κ)
    {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀)
    {θ : ℝ → Vec 2 → ℝ} (hθ : IsWeakSolution (streamVel φ) κ θ₀ θ)
    {θM : ℝ → Vec 2 → ℝ}
    (hθM : IsClassicalSol (streamVel (Φ M)) κ (fun _ _ => 0) θ₀ θM) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (fun x => θ t x - θM t x)) ≤
      (2 * Ct * (1 + Infra.Ingredients.supergeoConstant β) ^ β * epsilon β I.Λ M ^ tailExp β) *
        Real.sqrt (l2NormSq θ₀) := by
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  obtain ⟨Dθ, hDθ⟩ := hθ
  have hE : 0 < epsilon β I.Λ M := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκlo
  have hγ := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hγβ := gamma_lt_beta hβ1 hβ2
  have hA := Infra.Section5.RelativeError.supergeoConstant_nonneg' hβ1 hβ2
  intro t ht
  have h1 := Contracts.forcedEnergySup_contract hb_meas ⟨Bφ, hb_bdd⟩ hb_per hdiv hφ_meas hφ_per
    hφ_diff (fun t _ x => rfl) (streamSeq_isAdmissible hΦ M) hκ0
    (hθ₀) hper hθM hDθ (η := Ct * epsilon β I.Λ (M + 1) ^ β)
    (fun t _ x => htail M t x) t ht
  have h2 := classical_sqrt_energy_le hΦ M hκ0 hθ₀ hθM
  have hη0 : 0 ≤ Ct * epsilon β I.Λ (M + 1) ^ β :=
    mul_nonneg hCt (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7).le _)
  have hratio := tail_ratio_le (Ct := Ct) (A := Infra.Ingredients.supergeoConstant β)
    (E' := epsilon β I.Λ (M + 1)) (q := q β) (β := β) (s := β - gamma β) hE
    (Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7).le
    (Infra.Section5.RelativeError.epsilon_succ_le hβ1 hβ2 hΛ7 hM) hA hCt (by linarith) hκlo
  have h3 : 0 ≤ Ct * epsilon β I.Λ (M + 1) ^ β / κ := div_nonneg hη0 hκ0.le
  calc _ ≤ _ := h1
    _ ≤ (Ct * epsilon β I.Λ (M + 1) ^ β / κ) * Real.sqrt (l2NormSq θ₀) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ ≤ _ := by
        have : Ct * epsilon β I.Λ (M + 1) ^ β / κ ≤
            2 * Ct * (1 + Infra.Ingredients.supergeoConstant β) ^ β *
              epsilon β I.Λ M ^ tailExp β := by
          have := hratio
          unfold tailExp
          simpa using this
        exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)

/-- Sup form of the step-down estimate (i) at one level of the chain. -/
theorem step_sup (β C₀ : ℝ) :
    ∃ C Λ₀ : ℝ, 0 ≤ C ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ θm θprev : ℝ → Vec 2 → ℝ,
        IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) θ₀ θm →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤
            C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by
  obtain ⟨C₈, hA8⟩ := AVenhance.indystepdown β C₀
  obtain ⟨c₁, Λ₁, hc₁, hκw⟩ := kappaSeq_window β C₀
  refine ⟨max C₈ 0, max C₈ Λ₁, le_max_right _ _, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hκM R hR θ₀ hθ₀ hper hmean han m hm1 hmM θm θprev
    hθm hθprev
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hC₈Λ : C₈ ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ
  have hΛ₁ : Λ₁ ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ
  have hm2 : 2 ≤ m := by
    have := (mTheta0_isLeast hβ1 hβ2 hΛ7 hR).1.1
    omega
  have hEpos : 0 < epsilon β I.Λ (m - 1) := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  obtain ⟨hκp1, -⟩ := hκw I hz hx hh hΛ₁ κ hκ M hM hκM m hm2 hmM (m - 1) (Or.inl rfl)
  obtain ⟨hκm1, -⟩ := hκw I hz hx hh hΛ₁ κ hκ M hM hκM m hm2 hmM m (Or.inr rfl)
  have hκppos : 0 < I.kappaSeq κ M (m - 1) := lt_of_lt_of_le (by positivity) hκp1
  have hκmpos : 0 < I.kappaSeq κ M m := lt_of_lt_of_le (by positivity) hκm1
  have hsolv : ∀ j : ℕ, Infra.Section5.RelativeError.ClassicalSolvable (streamVel (Φ j)) := by
    intro j ν hν g hg hgp F hF hFp
    exact (AVenhance.classical_wellposed (Φ j) (streamSeq_isAdmissible hΦ j)
      ν hν F hF hFp g hg hgp).imp fun θ hθ => hθ.1
  obtain ⟨T, hT⟩ := Infra.Section5.RelativeError.exists_TIterates I hΦ (m := m) (by omega) hκmpos
      hκppos
    (hsolv (m - 1)) hθ₀ hper hθprev
  have hsup8 := (hA8 I hz hx hh hC₈Λ Φ hΦ κ hκ M hM hκM R hR θ₀ hθ₀ hper hmean han m hm1 hmM
    θm θprev T hθm hθprev hT).1
  intro t ht
  have h1 := hsup8 t ht
  have h2 : 0 ≤ Real.sqrt (I.kappaSeq κ M m) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θm s) x -
        spaceGrad (I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h3 : Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤
      C₈ * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by linarith
  have hEd : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β := Real.rpow_nonneg hEpos.le _
  calc _ ≤ _ := h3
    _ ≤ _ := by
        gcongr; exact le_max_left _ _

end AVenhance.Infra.FullTheorem
