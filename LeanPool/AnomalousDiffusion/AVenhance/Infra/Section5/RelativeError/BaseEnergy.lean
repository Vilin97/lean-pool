/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergyClassical
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds

/-! # base energy at the later start("The coarse diffusivity satisfies ...",
"Poincaré at 9166–9190 gives ...") and §6 item 11.  For `j = laterStart β Λ R < M`:

* `κ_j ≥ c R^{p₊}` (from the diffusivity lower bound `κ_j ≥ c₀ ε_j^{β+γ}`, the minimality of `j`,
    and, for
  `j = 1`, the radius bound `R ≤ 1/(√2 π)`);
* `κ_j ‖∇θ_j‖² ≥ c R^{p₊} ‖g‖²` from the energy identity and Poincaré.

The `κ` conjunct is stated for nonzero data (`0 < l2NormSq g →`): for `g = 0` and large `R` the
index `j = 1` is the later start while `R^{p₊}` is unbounded, so it cannot hold uniformly.
-/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance Homogenization MeasureTheory

/-- `a_m ε_m^{2+γ} = ε_m^{β+γ}`. -/
theorem a_mul_eps_pow_eq {β : ℝ} {Λ m : ℕ} (hx : 0 < epsilon β Λ m) (γ : ℝ) :
    a β Λ m * epsilon β Λ m ^ (2 + γ) = epsilon β Λ m ^ (β + γ) := by
  unfold a
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- `1/(√2 π) ≤ 1`. -/
theorem inv_sqrt_two_mul_pi_le_one : 1 / (Real.sqrt 2 * Real.pi) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  rw [div_le_one (by positivity)]
  exact one_le_mul_of_one_le_of_one_le h1 (by linarith only [h2])

/-- The abstract lower bound for `κ_j` at the later start, in terms of a constant `c₁`. -/
theorem kappa_lower_of_cases {c₀ e₁ p R Kj eJ : ℝ} {j : ℕ} (hc₀ : 0 < c₀) (he₁ : 0 < e₁)
    (hp : 0 < p) (hR : 0 < R) {h : ℝ}
    (hKj : c₀ * eJ ≤ Kj)
    (hj1 : j = 1 → eJ = e₁) (hj2 : 2 ≤ j → (1 / 2) ^ h * R ^ p ≤ eJ)
    (hj0 : 1 ≤ j) (hR1 : j = 1 → R ≤ 1) :
    min (c₀ * e₁) (c₀ * (1 / 2) ^ h) * R ^ p ≤ Kj := by
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  rcases Nat.lt_or_ge j 2 with hj | hj
  · have hj' : j = 1 := by omega
    have hRp1 : R ^ p ≤ 1 := Real.rpow_le_one hR.le (hR1 hj') hp.le
    calc min (c₀ * e₁) (c₀ * (1 / 2) ^ h) * R ^ p ≤ (c₀ * e₁) * 1 :=
          mul_le_mul (min_le_left _ _) hRp1 hRp.le (by positivity)
      _ = c₀ * eJ := by rw [hj1 hj']; ring
      _ ≤ Kj := hKj
  · have := hj2 hj
    calc min (c₀ * e₁) (c₀ * (1 / 2) ^ h) * R ^ p ≤ (c₀ * (1 / 2) ^ h) * R ^ p :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hRp.le
      _ = c₀ * ((1 / 2) ^ h * R ^ p) := by ring
      _ ≤ c₀ * eJ := mul_le_mul_of_nonneg_left this hc₀.le
      _ ≤ Kj := hKj

/-- Item 11: base energy at the later start, with `c` after β, C₀, Λ and before κ, M, R, g.
The `κ` conjunct is for nonzero data (see the module docstring). -/
theorem later_base_energy (β C₀ : ℝ) (hβ : 6 / 5 ≤ β) :
    ∀ Λ : ℕ, 2 ^ 7 ≤ Λ → ∃ c : ℝ, 0 < c ∧
      ∀ I : Ingredients β, I.Λ = Λ → I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R → laterStart β I.Λ R < M →
      ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → IsZ2Periodic g → MeanZeroOn unitCube g →
        IsThetaAnalytic R g →
      ∀ θ : ℝ → Vec 2 → ℝ,
        IsClassicalSol (streamVel (Φ (laterStart β I.Λ R)))
          (I.kappaSeq κ M (laterStart β I.Λ R)) (fun _ _ => 0) g θ →
        (0 < l2NormSq g → c * R ^ pPlus β ≤ I.kappaSeq κ M (laterStart β I.Λ R)) ∧
        c * R ^ pPlus β * l2NormSq g ≤
          I.kappaSeq κ M (laterStart β I.Λ R) *
            spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x) := by
  intro Λ hΛ
  by_cases hb : β < 4 / 3
  swap
  · refine ⟨1, one_pos, fun I => absurd I.beta_lt hb⟩
  have hβ1 : 1 < β := by linarith
  obtain ⟨c₀, C, hc₀, hcC, hL⟩ := l_recurse β C₀
  obtain ⟨K, hK1, hKs⟩ := Infra.Section5.LeftToShow.left_to_show_scales β C₀
  have hγ := Infra.Ingredients.gamma_pos hβ1 hb
  have hh : 0 < β + gamma β := by linarith
  have he₁ : 0 < epsilon β Λ 1 ^ (β + gamma β) :=
    Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos hβ1 hb hΛ) _
  have hc₁ : 0 < min (c₀ * epsilon β Λ 1 ^ (β + gamma β)) (c₀ * (1 / 2) ^ (β + gamma β)) :=
    lt_min (mul_pos hc₀ he₁) (mul_pos hc₀ (Real.rpow_pos_of_pos (by norm_num) _))
  have hpp := pPlus_pos_lt_two hβ hb
  refine ⟨min (c₀ * epsilon β Λ 1 ^ (β + gamma β)) (c₀ * (1 / 2) ^ (β + gamma β)) / (4 * K),
    div_pos hc₁ (by linarith), ?_⟩
  intro I hIΛ hz hx hhat Φ hΦ κ hκp M hM hperm R hR hjM g hg hgp hgm hga θ hθ
  subst hIΛ
  set j := laterStart β I.Λ R with hj_def
  obtain ⟨⟨hj1, _⟩, _⟩ := laterStart_isLeast hβ1 hb I.two_pow_seven_le hR
  obtain ⟨hA5, _⟩ := hL I hz hx hhat κ hκp M hM hperm
  have hA5j := (hA5 j hj1 hjM).1
  have hεj : 0 < epsilon β I.Λ j := Infra.Cutoff.epsilon_pos hβ1 hb I.two_pow_seven_le
  rw [a_mul_eps_pow_eq hεj] at hA5j
  have hKj : c₀ * epsilon β I.Λ j ^ (β + gamma β) ≤ I.kappaSeq κ M j := hA5j
  have hκj : 0 < I.kappaSeq κ M j :=
    lt_of_lt_of_le (mul_pos hc₀ (Real.rpow_pos_of_pos hεj _)) hKj
  have hKupper : I.kappaSeq κ M j ≤ K := by
    have := (hKs I hz hx hhat κ hκp M hM hperm (j + 1) (by omega) (by omega)).2.2.1
    simpa using this
  -- the κ lower bound for nonzero data
  have hkappa : 0 < l2NormSq g →
      min (c₀ * epsilon β I.Λ 1 ^ (β + gamma β)) (c₀ * (1 / 2) ^ (β + gamma β)) * R ^ pPlus β ≤
        I.kappaSeq κ M j := by
    intro hg0
    refine kappa_lower_of_cases hc₀ he₁ hpp.1 hR hKj ?_ ?_ hj1 ?_
    · intro h1
      exact congrArg (fun e => epsilon β I.Λ e ^ (β + gamma β)) h1
    · intro h2
      exact later_eps_pow_lower hβ1 hb I.two_pow_seven_le hR h2
    · intro _
      exact (analytic_radius_le hR hg hgp hgm hga hg0).trans inv_sqrt_two_mul_pi_le_one
  have hRp : 0 ≤ R ^ pPlus β := Real.rpow_nonneg hR.le _
  have hc4 : min (c₀ * epsilon β I.Λ 1 ^ (β + gamma β)) (c₀ * (1 / 2) ^ (β + gamma β)) / (4 * K) ≤
      min (c₀ * epsilon β I.Λ 1 ^ (β + gamma β)) (c₀ * (1 / 2) ^ (β + gamma β)) :=
    div_le_self hc₁.le (by linarith)
  have hS : 0 ≤ spaceTimeGradNormSq (fun t x => spaceGrad (θ t) x) :=
    integral_nonneg fun p => by
      unfold vecNormSq vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hN : 0 ≤ l2NormSq g := integral_nonneg fun x => sq_nonneg _
  refine ⟨fun hg0 => ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right hc4 hRp) (hkappa hg0)
  · rcases hN.eq_or_lt with h0 | hg0
    · rw [← h0, mul_zero]
      exact mul_nonneg hκj.le hS
    · have hφ := streamSeq_isAdmissible hΦ j
      have hlow := classical_dissipation_lower hφ hκj hθ hgm
      have hmin : I.kappaSeq κ M j / (4 * K) ≤
          min (1 / 4) (2 * Real.pi ^ 2 * I.kappaSeq κ M j) := by
        apply le_min
        · rw [div_le_iff₀ (by linarith)]
          linarith only [hKupper]
        · rw [div_le_iff₀ (by linarith)]
          have hp : (1 : ℝ) ≤ Real.pi ^ 2 :=
            one_le_pow₀ (le_trans (by norm_num) Real.pi_gt_three.le)
          have hpK := one_le_mul_of_one_le_of_one_le hp hK1
          have : 1 ≤ 2 * Real.pi ^ 2 * (4 * K) := by linarith only [hpK]
          have hκ := mul_le_mul_of_nonneg_left this hκj.le
          linarith only [hκ]
      have hk := hkappa hg0
      calc min (c₀ * epsilon β I.Λ 1 ^ (β + gamma β)) (c₀ * (1 / 2) ^ (β + gamma β)) / (4 * K) *
            R ^ pPlus β * l2NormSq g
          ≤ (I.kappaSeq κ M j / (4 * K)) * l2NormSq g := by
            apply mul_le_mul_of_nonneg_right _ hN
            rw [div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right hk (by linarith)
        _ ≤ min (1 / 4) (2 * Real.pi ^ 2 * I.kappaSeq κ M j) * l2NormSq g :=
            mul_le_mul_of_nonneg_right hmin hN
        _ ≤ _ := hlow

end AVenhance.Infra.Section5.RelativeError
