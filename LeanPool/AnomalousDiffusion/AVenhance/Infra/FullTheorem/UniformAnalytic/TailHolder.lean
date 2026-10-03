/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformAnalytic.Tail

/-! # Hölder bound of the tail piece `w = θ − θ_M`

Uniform in `κ` and `M`: `‖w(t) − w(s)‖ ≤ K_w ‖θ₀‖_{H¹} |t − s|^{μ_w}`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The exponent `a = qβ − (β − γ)` of the tail decay. -/
def tailExp (β : ℝ) : ℝ := q β * β - (β - gamma β)

theorem tailExp_pos {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 0 < tailExp β := by
  have := Infra.Section5.RelativeError.stream_tail_exponent_pos hβ hβ'
  rw [two_beta_div_eq hβ hβ'] at this
  unfold tailExp
  exact this

/-- The Hölder exponent of the tail piece. -/
def tailMu (β : ℝ) : ℝ := lebronMu (tailExp β) (β - gamma β)

/-- The constant of the tail piece. -/
def tailK (β CU Ct Bm : ℝ) : ℝ :=
  (2 * (2 * Ct * (1 + Infra.Ingredients.supergeoConstant β) ^ β)) ^ (1 - 4 * tailMu β) *
    (2 * CU * (1 + Bm) * (1 / Real.sqrt (1 / 2))) ^ (4 * tailMu β)

theorem tailK_nonneg {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) {CU Ct Bm : ℝ} (hCU : 0 ≤ CU)
    (hCt : 0 ≤ Ct) (hBm : 0 ≤ Bm) : 0 ≤ tailK β CU Ct Bm := by
  unfold tailK
  have hA := Infra.Section5.RelativeError.supergeoConstant_nonneg' hβ hβ'
  positivity

theorem w_holder {β CU Ct Bφ : ℝ} (hU : LemmaUWith CU) (hCU : 0 < CU) (hCt : 0 ≤ Ct)
    (hBφ : 0 ≤ Bφ) {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {φ : ℝ → Vec 2 → ℝ}
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
    (hκlo : (1 / 2) * epsilon β I.Λ M ^ (β - gamma β) ≤ κ) (hκ1 : κ ≤ 1)
    {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀)
    {θ : ℝ → Vec 2 → ℝ} (hθ : IsWeakSolution (streamVel φ) κ θ₀ θ)
    {θM : ℝ → Vec 2 → ℝ}
    (hθM : IsClassicalSol (streamVel (Φ M)) κ (fun _ _ => 0) θ₀ θM) :
    IsHolderTimeL2 (tailMu β)
      (tailK β CU Ct (max Bφ (velBound β)) *
        Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)))
      (fun t x => θ t x - θM t x) := by
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  obtain ⟨Dθ, hDθ⟩ := hθ
  set E := epsilon β I.Λ M with hEdef
  have hE : 0 < E := Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hE1 : E ≤ 1 := Infra.Construction.epsilon_le_one hβ1 hβ2 hΛ7
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκlo
  have hγ := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hγβ := gamma_lt_beta hβ1 hβ2
  have ha : 0 < tailExp β := tailExp_pos hβ1 hβ2
  set N := Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hmc : MeasurableSet unitCube := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hgn : 0 ≤ gradNormSq (spaceGrad θ₀) :=
    setIntegral_nonneg hmc fun x _ => vecNormSq_nonneg _
  have hl2 : 0 ≤ l2NormSq θ₀ := setIntegral_nonneg hmc fun x _ => sq_nonneg _
  have hn0N : Real.sqrt (l2NormSq θ₀) ≤ N := Real.sqrt_le_sqrt (by linarith)
  have hA := Infra.Section5.RelativeError.supergeoConstant_nonneg' hβ1 hβ2
  set C₈ := 2 * Ct * (1 + Infra.Ingredients.supergeoConstant β) ^ β with hC₈
  have hC₈0 : 0 ≤ C₈ := by positivity
  -- slices
  have hcM : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (θM t) := fun t ht =>
    IsClassicalSol.continuous_slice hθM ht.1
  have hmM : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θM t) := fun t ht =>
    Infra.Section5.Integration.memL2On_unitCube_of_continuous (hcM t ht)
  have hmθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ t) := fun t ht => (hDθ.1 t ht).2
  have hmw : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (fun x => θ t x - θM t x) :=
    fun t ht => (hmθ t ht).sub (hmM t ht)
  -- sup bound
  have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ t x - θM t x)) ≤ (C₈ * E ^ tailExp β) * N := by
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
      _ ≤ (Ct * epsilon β I.Λ (M + 1) ^ β / κ) * N := by
          exact mul_le_mul_of_nonneg_left (h2.trans hn0N) h3
      _ ≤ (C₈ * E ^ tailExp β) * N := by
          have : Ct * epsilon β I.Λ (M + 1) ^ β / κ ≤ C₈ * E ^ tailExp β := by
            have := hratio
            unfold tailExp
            simpa [hC₈] using this
          exact mul_le_mul_of_nonneg_right this hN0
  -- seminorm of `w`
  intro s hs t ht
  set h := |t - s| with hh
  have hh0 : 0 ≤ h := abs_nonneg _
  have hx0 : 0 ≤ Real.sqrt (l2NormSq (fun x => (θ t x - θM t x) - (θ s x - θM s x))) :=
    Real.sqrt_nonneg _
  have hx1 : Real.sqrt (l2NormSq (fun x => (θ t x - θM t x) - (θ s x - θM s x))) ≤
      2 * (C₈ * E ^ tailExp β * N) := by
    have := sqrt_l2NormSq_sub_le_memL2 (hmw t ht) (hmw s hs)
    have h1 := hsup t ht
    have h2 := hsup s hs
    linarith
  have hx2 : Real.sqrt (l2NormSq (fun x => (θ t x - θM t x) - (θ s x - θM s x))) ≤
      (2 * CU * (1 + max Bφ (velBound β)) * (1 / Real.sqrt (1 / 2))) *
        E ^ (-((β - gamma β) / 2)) * N * h ^ ((1 : ℝ) / 4) := by
    have e : (fun x => (θ t x - θM t x) - (θ s x - θM s x)) =
        fun x => (θ t x - θ s x) - (θM t x - θM s x) := by
      funext x; ring
    rw [e]
    have htr := sqrt_l2NormSq_sub_le_memL2 ((hmθ t ht).sub (hmθ s hs)) ((hmM t ht).sub (hmM s hs))
    have hu1 := hU (streamVel φ) hb_meas hb_per hdiv Bφ hBφ hb_bdd κ hκ0 hκ1 θ₀
      (fun x => spaceGrad θ₀ x)
      (Infra.Section5.RelativeError.isPeriodicH1With_of_contDiff
        (hθ₀.of_le (by exact_mod_cast le_top)) hper) θ Dθ hDθ s hs t ht
    have hu2 := classical_quarter hU hΦ M hκ0 hκ1 hθ₀ hper hθM s hs t ht
    have hκ' := one_div_sqrt_le (c := 1 / 2) (by norm_num) hE (P := β - gamma β) hκlo
    have hh4 : 0 ≤ h ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hh0 _
    have hBv : 0 ≤ velBound β := velBound_nonneg hβ1
    have hm1 : 1 + Bφ ≤ 1 + max Bφ (velBound β) := by
      have := le_max_left Bφ (velBound β); linarith
    have hm2 : 1 + velBound β ≤ 1 + max Bφ (velBound β) := by
      have := le_max_right Bφ (velBound β); linarith
    have hs0 : 0 ≤ 1 / Real.sqrt κ := by positivity
    have hEp : 0 ≤ E ^ (-((β - gamma β) / 2)) := Real.rpow_nonneg hE.le _
    calc _ ≤ _ := htr
      _ ≤ CU * (1 + Bφ) / Real.sqrt κ * h ^ ((1 : ℝ) / 4) * N +
          CU * (1 + velBound β) / Real.sqrt κ * h ^ ((1 : ℝ) / 4) * N := add_le_add hu1 hu2
      _ = CU * ((1 + Bφ) + (1 + velBound β)) * (1 / Real.sqrt κ) * N * h ^ ((1 : ℝ) / 4) := by
          ring
      _ ≤ CU * (2 * (1 + max Bφ (velBound β))) * ((1 / Real.sqrt (1 / 2)) *
            E ^ (-((β - gamma β) / 2))) * N * h ^ ((1 : ℝ) / 4) := by
          have : (1 + Bφ) + (1 + velBound β) ≤ 2 * (1 + max Bφ (velBound β)) := by linarith
          gcongr
      _ = _ := by ring
  have hS0 : 0 ≤ 2 * CU * (1 + max Bφ (velBound β)) * (1 / Real.sqrt (1 / 2)) := by
    have : 0 ≤ max Bφ (velBound β) := hBφ.trans (le_max_left _ _)
    positivity
  have hstep := holder_step (ε := E) (δ := tailExp β) (P := β - gamma β) hE ha
    (by linarith) hC₈0 hS0 hN0 hh0 hx0 hx1 hx2
  refine hstep.trans ?_
  have hEa : E ^ (tailExp β / 2) ≤ 1 := Real.rpow_le_one hE.le hE1 (by linarith)
  have hK : 0 ≤ (2 * C₈) ^ (1 - 4 * lebronMu (tailExp β) (β - gamma β)) *
      (2 * CU * (1 + max Bφ (velBound β)) * (1 / Real.sqrt (1 / 2))) ^
        (4 * lebronMu (tailExp β) (β - gamma β)) := by positivity
  have hhm : 0 ≤ h ^ lebronMu (tailExp β) (β - gamma β) := Real.rpow_nonneg hh0 _
  unfold tailK tailMu
  calc _ ≤ ((2 * C₈) ^ (1 - 4 * lebronMu (tailExp β) (β - gamma β)) *
      (2 * CU * (1 + max Bφ (velBound β)) * (1 / Real.sqrt (1 / 2))) ^
        (4 * lebronMu (tailExp β) (β - gamma β))) * 1 * N *
          h ^ lebronMu (tailExp β) (β - gamma β) := by
        gcongr
    _ = _ := by rw [hC₈]; ring

end AVenhance.Infra.FullTheorem
