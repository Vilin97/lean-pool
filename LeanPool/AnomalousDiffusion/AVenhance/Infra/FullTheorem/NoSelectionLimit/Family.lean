/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Pair
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Upgrade
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.TransportLimit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.UniformHolder

/-! # The limit of one vanishing-viscosity family

For the family `κ_j = t ε_{2j+1}^p` of weak solutions with cosine data: uniformly Cauchy in sup-`L²`
(`pair_bound`), hence convergent to a transport weak solution `Θ` (`transportLimit_contract`),
and `HolderTimeL2Le (μ/2) η`-close for large `j` (`uniformHolder_contract` and interpolation). -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem eps_rpow_tendsto {β : ℝ} {Λ : ℕ} (hβ1 : 1 < β) (hβ2 : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {x : ℝ} (hx : 0 < x) {u : ℕ → ℕ} (hu : Tendsto u atTop atTop) :
    Tendsto (fun j => epsilon β Λ (u j) ^ x) atTop (𝓝 0) := by
  have h := ((Infra.Section5.RelativeError.epsilon_tendsto_zero hβ1 hβ2 hΛ).comp hu).rpow_const
    (Or.inr hx.le)
  simpa [Real.zero_rpow hx.ne'] using h

theorem uniform_cauchy_of_pair {f : ℕ → ℝ → Vec 2 → ℝ} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) {J : ℕ}
    (hpair : ∀ j ≥ J, ∀ j' ≥ j, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => f j s x - f j' s x)) ≤ g j) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => f j s x - f k s x)) ≤ η := by
  intro η hη
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((hg.eventually (ge_mem_nhds hη)))
  refine ⟨max J N₀, fun j hj k hk s hs => ?_⟩
  rcases le_total j k with hjk | hkj
  · exact (hpair j (le_trans (le_max_left _ _) hj) k hjk s hs).trans
      (hN₀ j (le_trans (le_max_right _ _) hj))
  · rw [sqrt_l2_comm]
    exact (hpair k (le_trans (le_max_left _ _) hk) j hkj s hs).trans
      (hN₀ k (le_trans (le_max_right _ _) hk))

theorem family_limit (β C₀ : ℝ) :
    ∃ μ Λ₄ : ℝ, 0 < μ ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₄ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
      ∀ n : ℕ, 1 ≤ n → ∀ c : ℝ,
      ∀ t : ℝ, (t = 1 / 2 ∨ t = 2) →
      ∀ θ : ℝ → ℝ → Vec 2 → ℝ,
        (∀ j : ℕ, IsWeakSolution (streamVel φ) (kfam β I.Λ t j)
          (fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) (θ (kfam β I.Λ t j))) →
      ∃ Θ : ℝ → Vec 2 → ℝ,
        IsTransportWeakSolution (streamVel φ)
          (fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0)) Θ ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (Θ s)) ∧
        (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          Real.sqrt (l2NormSq (fun x => θ (kfam β I.Λ t j) s x - Θ s x)) ≤ η) ∧
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, HolderTimeL2Le (μ / 2) η
          (fun s x => θ (kfam β I.Λ t j) s x - Θ s x)) := by
  obtain ⟨Λc, ρ, hρ, hpair⟩ := pair_bound β C₀
  obtain ⟨μ, Λ₃, hμ, hUH⟩ := Contracts.uniformHolder_contract β C₀
  refine ⟨μ, max Λc Λ₃, hμ, ?_⟩
  intro I hz hx hh hΛ Φ hΦ φ htend n hn c t ht θ hθ
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hΛc : Λc ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ
  have hΛ₃ : Λ₃ ≤ (I.Λ : ℝ) := (le_max_right _ _).trans hΛ
  obtain ⟨K, hK, hKb⟩ := hpair I hz hx hh hΛc Φ hΦ φ htend
  obtain ⟨C, hC, hCb⟩ := hUH I hz hx hh hΛ₃ Φ hΦ φ htend
  obtain ⟨Ct, Bφ, hCt, hBφ, htail, hφm, hφp, hφd, hbm, hbp, hdiv, hbb⟩ := limit_package hΦ htend
  obtain ⟨hsm, hpr, hmean, -, -, -, -, han⟩ := Contracts.cosineDatum_contract n hn (c)
  set θ₀ : Vec 2 → ℝ := fun x => c * Real.cos (2 * Real.pi * (n : ℝ) * x 0) with hθ₀def
  have hR : 0 < 1 / (2 * Real.pi * (n : ℝ)) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hε : ∀ m, 0 < epsilon β I.Λ m := fun m => Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hmθ₀ : MemL2On unitCube θ₀ :=
    Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On hsm.continuous
  have hu : Tendsto (fun j : ℕ => 2 * j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by simp only [id]; omega) tendsto_id
  have hu2 : Tendsto (fun j : ℕ => 2 * j) atTop atTop :=
    tendsto_atTop_mono (fun j => by simp only [id]; omega) tendsto_id
  have hρ' := eps_rpow_tendsto (Λ := I.Λ) hβ1 hβ2 hΛ7 hρ hu2
  have hδ' := eps_rpow_tendsto (Λ := I.Λ) hβ1 hβ2 hΛ7
    (Infra.Ingredients.delta_pos hβ1 hβ2) hu2
  have ha' := eps_rpow_tendsto (Λ := I.Λ) hβ1 hβ2 hΛ7 (tailExp_pos hβ1 hβ2) hu2
  -- uniform Cauchy
  have hsmall : ∀ᶠ j in atTop, K * epsilon β I.Λ (2 * j) ^ ρ ≤ 2 := by
    have h := hρ'.const_mul K
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hsmall.and (eventually_ge_atTop (mTheta0 β I.Λ
    (1 / (2 * Real.pi * (n : ℝ))) + 1)))
  have hcauchy := uniform_cauchy_of_pair (f := fun j => θ (kfam β I.Λ t j))
    (g := fun j => K * (epsilon β I.Λ (2 * j) ^ tailExp β + epsilon β I.Λ (2 * j) ^ delta β +
      epsilon β I.Λ (2 * j) ^ ρ) * Real.sqrt (l2NormSq θ₀))
    (by simpa using (((ha'.add hδ').add hρ').const_mul K).mul_const (Real.sqrt (l2NormSq θ₀)))
    (J := J + 1) (fun j hj j' hj' s hs => by
      have h1 := hJ j (by omega)
      have h2 := h1.2
      exact hKb t ht (1 / (2 * Real.pi * (n : ℝ))) hR θ₀ hsm hpr hmean han θ hθ j (by omega)
        (by omega) h1.1 j' hj' s hs)
  -- transport limit
  have hκpos : ∀ j, 0 < kfam β I.Λ t j := by
    intro j
    have := hε (2 * j + 1)
    unfold kfam
    rcases ht with rfl | rfl <;> positivity
  have hκtend : Tendsto (fun j => kfam β I.Λ t j) atTop (𝓝 0) := by
    have hp : 0 < 2 * β / (q β + 1) := by
      have := Infra.Ingredients.one_lt_q hβ1 hβ2
      positivity
    have := (eps_rpow_tendsto (Λ := I.Λ) hβ1 hβ2 hΛ7 hp hu).const_mul t
    simpa [kfam] using this
  obtain ⟨Θ, hΘ, hmΘ, hconv⟩ := Contracts.transportLimit_contract (streamVel φ) hbm
    ⟨Bφ, hbb⟩ hbp hdiv θ₀ hmθ₀ (fun j => kfam β I.Λ t j) hκpos hκtend
    (fun j => θ (kfam β I.Λ t j)) hθ hcauchy
  refine ⟨Θ, hΘ, hmΘ, hconv, ?_⟩
  -- Hölder upgrade
  have hmf : ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ (kfam β I.Λ t j) s) := by
    intro j s hs
    obtain ⟨Dθ, hDθ⟩ := hθ j
    exact (hDθ.1 s hs).2
  set H := C * Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)) with hHdef
  have hH0 : 0 ≤ H := by positivity
  have hhol : ∀ j, IsHolderTimeL2 μ H (fun s x => θ (kfam β I.Λ t j) s x) := by
    intro j
    exact holderTimeL2Le_isHolder (hCb θ₀ (spaceGrad θ₀)
      (Infra.Section5.RelativeError.isPeriodicH1With_of_contDiff
        (hsm.of_le (by exact_mod_cast le_top)) hpr) hmean _
      (kfam_mem_permissible ht j (hε _).le) _ (hθ j))
  have hholΘ := holder_of_limit (f := fun j => θ (kfam β I.Λ t j)) hmf hmΘ hconv hhol
  have hhol2 : ∀ j, IsHolderTimeL2 μ (2 * H) (fun s x => θ (kfam β I.Λ t j) s x - Θ s x) := by
    intro j s hs t' ht'
    have e : (fun x => (θ (kfam β I.Λ t j) t' x - Θ t' x) - (θ (kfam β I.Λ t j) s x - Θ s x)) =
        fun x => (θ (kfam β I.Λ t j) t' x - θ (kfam β I.Λ t j) s x) - (Θ t' x - Θ s x) := by
      funext x; ring
    rw [e]
    have hf : MemL2On unitCube (fun x => θ (kfam β I.Λ t j) t' x - θ (kfam β I.Λ t j) s x) :=
      (hmf j t' ht').sub (hmf j s hs)
    have hg : MemL2On unitCube (fun x => Θ t' x - Θ s x) := (hmΘ t' ht').sub (hmΘ s hs)
    have h1 := sqrt_l2NormSq_sub_le_memL2 hf hg
    have h2 : Real.sqrt (l2NormSq (fun x => θ (kfam β I.Λ t j) t' x -
        θ (kfam β I.Λ t j) s x)) ≤ H * |t' - s| ^ μ := hhol j s hs t' ht'
    have h3 := hholΘ s hs t' ht'
    linarith
  intro η hη
  obtain ⟨α, hα, hαη⟩ := exists_small_alpha (by positivity : 0 ≤ 2 * H) hη
  obtain ⟨N, hN⟩ := hconv α hα
  refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
  have h := holderL2Le_of_small (μ := μ) (H := 2 * H) (α := α)
    (f := fun s x => θ (kfam β I.Λ t j) s x - Θ s x)
    (fun s hs => (hmf j s hs).sub (hmΘ s hs)) (fun s hs => hN j hj s hs) (hhol2 j)
  obtain ⟨hm, A, B, hAB, hA, hB⟩ := h
  exact ⟨hm, A, B, hAB.trans hαη, hA, hB⟩

end AVenhance.Infra.FullTheorem
